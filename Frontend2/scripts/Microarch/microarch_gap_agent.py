#!/usr/bin/env python3
"""
+======================================================================+
|     MICROARCH AGENT -- SPEC-GAP MODE (LLM, human-confirmed)         |
|                                                                      |
|  The other half of microarch_agent.py. The English path can only set |
|  the compiler's CHOICES (speed grade, queue depth, ...). Many        |
|  Validation findings are about spec CONTENT the compiler hardcodes:  |
|  a field it never emits (unmapped-read behavior, DM polarity,        |
|  tMRD/tMOD), a failure-taxonomy id, a field width. No choice fixes   |
|  those, so this mode reads the finding, proposes a patch to          |
|  microarch_compiler.py, and recompiles the spec.                     |
|                                                                      |
|  Same discipline as the Phase 1/2 fix agents:                        |
|    - the patch is shown as a diff; nothing is written until you      |
|      type 'a'                                                        |
|    - the compiler stays deterministic and the gate is deterministic: |
|      --selftest must still reproduce the golden spec, every preset   |
|      must compile to the same spec as before apart from ADDED        |
|      fields, and every spec path the agent says it added must really |
|      be in the new compiled spec. Any failure restores the file.     |
|    - it does NOT invent values. A finding that needs an owner's      |
|      decision (no proposed value, a real design trade-off) gets a    |
|      needs_owner_decision answer, not a guess.                       |
|                                                                      |
|  Input comes from the Frontend Orchestrator, which forwards          |
|  Validation's findings verbatim -- it never paraphrases them and     |
|  never edits anything itself.                                        |
|                                                                      |
|  Usage:                                                              |
|    python3 microarch_gap_agent.py --findings F.json --spec S.json \\  |
|        --out-dir DIR [--choices CHOICES.json]                        |
|  --choices defaults to resolved_choices from a microarch_report.json |
|  next to the spec (or one directory up).                             |
|  Needs ANTHROPIC_API_KEY (Frontend2/.env).                           |
+======================================================================+
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))


def _load_dotenv() -> None:
    for env_path in (HERE.parents[1] / ".env", HERE.parents[2] / ".env"):
        if not env_path.is_file():
            continue
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, _, v = line.partition("=")
            k = k.strip()
            if k and k not in os.environ:
                os.environ[k] = v.strip().strip('"').strip("'")


_load_dotenv()

MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-5-5")
MAX_TOKENS = 32000
MAX_ATTEMPTS = 3
COMPILER = HERE / "microarch_compiler.py"

PATCH_TOOL = {
    "name": "propose_compiler_patch",
    "description": "Propose edits to microarch_compiler.py that resolve the spec-gap finding(s).",
    "input_schema": {
        "type": "object",
        "required": ["root_cause", "edits", "expected_spec_paths", "explanation", "confidence"],
        "properties": {
            "root_cause": {"type": "string",
                           "description": "1-3 sentences: what the compiler fails to state or derive."},
            "edits": {
                "type": "array",
                "description": "Exact-text replacements applied in order to microarch_compiler.py. "
                               "Each `old` must appear EXACTLY ONCE in the current file.",
                "items": {"type": "object", "required": ["old", "new"],
                          "properties": {"old": {"type": "string"}, "new": {"type": "string"}}},
            },
            "expected_spec_paths": {
                "type": "array", "items": {"type": "string"},
                "description": "Dotted paths that must exist in the recompiled spec, e.g. "
                               "'csr_register_map.unmapped_read_data'. Checked mechanically.",
            },
            "explanation": {"type": "string"},
            "confidence": {"type": "string", "enum": ["high", "medium", "low"]},
        },
    },
}

DECISION_TOOL = {
    "name": "needs_owner_decision",
    "description": "Use instead of guessing when a finding needs a design decision no one has made "
                   "(no proposed value, or a genuine trade-off between options).",
    "input_schema": {
        "type": "object", "required": ["finding_ids", "question", "options"],
        "properties": {"finding_ids": {"type": "array", "items": {"type": "string"}},
                       "question": {"type": "string"},
                       "options": {"type": "array", "items": {"type": "string"}}},
    },
}

SYSTEM_PROMPT = """You maintain microarch_compiler.py, the deterministic compiler that \
turns a handful of choices into a complete DDR3 controller microarchitecture spec JSON. \
Validation reports gaps in that spec. You are given the findings verbatim, the compiler \
source, and the current spec. Resolve each finding by editing the compiler so the \
spec it emits states what the finding says is missing, by calling propose_compiler_patch.

Rules:
- A finding where the compiler's output disagrees with the shared schema (Spec/\
llmmc_microarchitecture.schema.json), such as a type or enum mismatch, is a decision about \
which side changes. You must not edit the schema and must not silently change the \
compiler's output type: answer needs_owner_decision with both options.
- Never invent a design value. If the finding (or the file) supplies a value -- e.g. a \
"Validation proposes ..." line -- use it. If it needs a decision with no proposed value \
or a real trade-off (a field width vs. a cap, a new section whose shape nobody has \
agreed), call needs_owner_decision for those findings instead. You may call both: \
patch what is decidable, ask about the rest.
- Changes must be additive and minimal. Do not alter any existing emitted value, timing \
table, register reset value, preset, or consistency check: the selftest compares the golden \
spec, and every preset's compiled spec must be identical apart from added fields/list items. Do not touch unrelated code.
- Put new standard-determined constants (JEDEC) in the same style as the existing ones; \
put new spec fields in the section the finding names (its `scope`).
- failure_taxonomy is NOT in this file: _load_failure_taxonomy() copies it from the \
golden spec JSON, which is a shared contract you must not edit. Add new taxonomy ids by \
merging additions inside the compiler (e.g. in _load_failure_taxonomy), keeping every \
existing id and entry unchanged.
- Each edit's `old` must match the file exactly once. Keep edits small.
- List every new spec field you add in expected_spec_paths (dotted path from the spec root).
"""


def _client():
    try:
        import anthropic
    except ImportError:
        raise SystemExit("pip install anthropic")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        raise SystemExit("ANTHROPIC_API_KEY not set (checked Frontend2/.env and repo-root .env)")
    return anthropic.Anthropic()


def _ask(client, findings: list, spec: dict, feedback: str | None) -> dict:
    user = (f"SPEC-GAP FINDINGS (verbatim from Validation):\n{json.dumps(findings, indent=2)}\n\n"
            f"CURRENT COMPILER SOURCE (microarch_compiler.py):\n```python\n{COMPILER.read_text()}\n```\n\n"
            f"CURRENT SPEC (sections: {', '.join(spec)}):\n```json\n{json.dumps(spec, indent=1)[:60000]}\n```\n")
    if feedback:
        user += f"\nYOUR PREVIOUS ATTEMPT WAS REJECTED:\n{feedback}\nFix that and propose again.\n"
    with client.messages.stream(model=MODEL, max_tokens=MAX_TOKENS, system=SYSTEM_PROMPT,
                                tools=[PATCH_TOOL, DECISION_TOOL], tool_choice={"type": "any"},
                                messages=[{"role": "user", "content": user}]) as st:
        resp = st.get_final_message()
    if resp.stop_reason == "max_tokens":
        raise RuntimeError("response hit max_tokens before finishing")
    out = {"patch": None, "decisions": []}
    for b in resp.content:
        if getattr(b, "type", None) != "tool_use":
            continue
        if b.name == "propose_compiler_patch":
            out["patch"] = dict(b.input)
        elif b.name == "needs_owner_decision":
            out["decisions"].append(dict(b.input))
    return out


def _apply_edits(src: str, edits: list) -> str:
    for i, e in enumerate(edits, 1):
        n = src.count(e["old"])
        if n != 1:
            raise ValueError(f"edit {i}: `old` text appears {n} times (must be exactly 1)")
        src = src.replace(e["old"], e["new"], 1)
    return src


def _preset_specs() -> dict:
    """{preset: compiled spec, or None if the compiler rejects it}, taken in a
    fresh interpreter so a patched file is what actually gets imported."""
    code = ("import json,microarch_compiler as m;"
            "print(json.dumps({p:(r['spec'] if (r:=m.compile_spec(c))['ok'] else None)"
            " for p,c in m.PRESETS.items()},default=str))")
    r = subprocess.run([sys.executable, "-c", code], cwd=HERE, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"preset check failed to run: {r.stderr[-400:]}")
    return json.loads(r.stdout.strip().splitlines()[-1])


def _additive(old, new, path="") -> str | None:
    """None if `new` only ADDS to `old` (new dict keys, items appended to the
    end of a list); else a description of the first changed/removed value."""
    if isinstance(old, dict):
        if not isinstance(new, dict):
            return f"{path}: dict became {type(new).__name__}"
        for k, v in old.items():
            if k not in new:
                return f"{path}.{k}: removed"
            d = _additive(v, new[k], f"{path}.{k}")
            if d:
                return d
        return None
    if isinstance(old, list):
        if not isinstance(new, list) or len(new) < len(old):
            return f"{path}: list shrank or changed type"
        for i, v in enumerate(old):
            d = _additive(v, new[i], f"{path}[{i}]")
            if d:
                return d
        return None
    return None if old == new else f"{path}: {old!r} -> {new!r}"


def _selftest() -> tuple[bool, str]:
    r = subprocess.run([sys.executable, str(COMPILER), "--selftest"], capture_output=True, text=True)
    return r.returncode == 0, (r.stdout + r.stderr)[-1500:]


def _has_path(obj, dotted: str) -> bool:
    for part in dotted.split("."):
        if not isinstance(obj, dict) or part not in obj:
            return False
        obj = obj[part]
    return True


def _choices_for(spec_path: Path, explicit: str | None, out_dir: Path) -> dict | None:
    cands = [Path(explicit)] if explicit else [spec_path.parent / "microarch_report.json",
                                               spec_path.parent.parent / "microarch_report.json",
                                               out_dir.parent / "microarch_report.json"]
    for c in cands:
        if c.is_file():
            d = json.loads(c.read_text())
            return d.get("resolved_choices", d)
    return None


def _verify(patched_src: str, original_src: str, before: dict, expected: list,
            choices: dict | None) -> tuple[bool, str, dict | None]:
    """Write the patched compiler, run the deterministic gates, restore the
    original on any failure. Returns (ok, message, recompiled_spec)."""
    COMPILER.write_text(patched_src)
    try:
        try:
            compile(patched_src, str(COMPILER), "exec")
        except SyntaxError as e:
            raise RuntimeError(f"patched compiler has a syntax error: {e}")
        ok, out = _selftest()
        if not ok:
            raise RuntimeError(f"--selftest failed after the patch:\n{out}")
        after = _preset_specs()
        for name, old in before.items():
            if old is None:
                continue
            if after.get(name) is None:
                raise RuntimeError(f"preset {name!r} compiled before the patch and is rejected now")
            d = _additive(old, after[name])
            if d:
                raise RuntimeError(f"preset {name!r}: patch changed an existing spec value "
                                   f"(must be additive only): {d}")
        spec = None
        if choices is not None:
            code = ("import json,sys,microarch_compiler as m;r=m.compile_spec(json.load(sys.stdin));"
                    "print(json.dumps({'ok':r['ok'],'errors':r['errors'],'spec':r.get('spec')}))")
            r = subprocess.run([sys.executable, "-c", code], cwd=HERE, input=json.dumps(choices),
                               capture_output=True, text=True)
            res = json.loads(r.stdout.strip().splitlines()[-1]) if r.returncode == 0 else {"ok": False, "errors": [r.stderr[-400:]]}
            if not res["ok"]:
                raise RuntimeError(f"current choices no longer compile: {res['errors']}")
            spec = res["spec"]
            missing = [p for p in expected if not _has_path(spec, p)]
            if missing:
                raise RuntimeError(f"expected spec path(s) missing from the recompiled spec: {missing}")
        return True, "selftest, preset regression and expected-path checks all passed", spec
    except Exception as e:
        COMPILER.write_text(original_src)
        return False, str(e), None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--findings", required=True, help="JSON list of spec-gap findings, verbatim")
    ap.add_argument("--spec", required=True)
    ap.add_argument("--out-dir", required=True, help="where the revised spec + report go")
    ap.add_argument("--choices", help="choices JSON; default: resolved_choices of a nearby microarch_report.json")
    a = ap.parse_args()

    findings = json.loads(Path(a.findings).read_text())
    spec_path, out_dir = Path(a.spec), Path(a.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    spec = json.loads(spec_path.read_text())
    choices = _choices_for(spec_path, a.choices, out_dir)
    if choices is None:
        print("  NOTE: no resolved choices found (--choices / microarch_report.json); the "
              "compiler can be patched but no revised spec will be written.")

    client = _client()
    before = _preset_specs()
    original = COMPILER.read_text()
    feedback, report = None, {"findings": [f.get("id") for f in findings], "attempts": [],
                              "decisions": [], "model": MODEL,
                              "generated_utc": datetime.now(timezone.utc).isoformat()}
    status, new_spec = "no_patch", None

    for attempt in range(1, MAX_ATTEMPTS + 1):
        print(f"\n{'#' * 62}\n#  spec-gap attempt {attempt}/{MAX_ATTEMPTS}\n{'#' * 62}")
        try:
            ans = _ask(client, findings, spec, feedback)
        except Exception as e:
            print(f"  ERROR: {e}")
            report["attempts"].append({"attempt": attempt, "status": "llm_error", "error": str(e)})
            break
        for d in ans["decisions"]:
            report["decisions"].append(d)
            print(f"\n  OWNER DECISION NEEDED for {d['finding_ids']}:\n    {d['question']}")
            for o in d["options"]:
                print(f"      - {o}")
        patch = ans["patch"]
        if not patch:
            print("\n  No patch proposed.")
            break
        try:
            patched = _apply_edits(original, patch["edits"])
        except ValueError as e:
            feedback = str(e)
            report["attempts"].append({"attempt": attempt, "status": "bad_edit", "error": feedback})
            print(f"  proposal rejected before review: {feedback}")
            continue

        print(f"\n  root cause: {patch['root_cause']}\n  confidence: {patch['confidence']}")
        print(f"  {patch['explanation']}\n")
        print("".join(difflib.unified_diff(original.splitlines(True), patched.splitlines(True),
                                           "microarch_compiler.py (current)",
                                           "microarch_compiler.py (proposed)")))
        choice = input("  [a]pply / [r]etry with feedback / [s]kip: ").strip().lower()
        if choice == "s":
            report["attempts"].append({"attempt": attempt, "status": "skipped"})
            break
        if choice != "a":
            feedback = input("  what should change? ").strip() or "the human rejected the proposal"
            report["attempts"].append({"attempt": attempt, "status": "rejected", "feedback": feedback})
            continue

        ok, msg, spec2 = _verify(patched, original, before, patch["expected_spec_paths"], choices)
        print(f"  {'OK' if ok else 'FAILED'}: {msg}")
        report["attempts"].append({"attempt": attempt, "status": "applied" if ok else "verify_failed",
                                   "message": msg, "root_cause": patch["root_cause"],
                                   "expected_spec_paths": patch["expected_spec_paths"]})
        if ok:
            status, new_spec = "applied", spec2
            break
        feedback = msg

    out_spec = None
    if new_spec is not None:
        n = len(list(out_dir.glob("spec_rev*.json"))) + 1
        out_spec = out_dir / f"spec_rev{n}.json"
        out_spec.write_text(json.dumps(new_spec, indent=2))
        print(f"\n  wrote revised spec: {out_spec}")
    report.update(status=status, revised_spec=str(out_spec) if out_spec else None)
    rp = out_dir / "microarch_gap_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"  wrote {rp}")
    return 0 if status == "applied" or (report["decisions"] and status == "no_patch") else 1


if __name__ == "__main__":
    sys.exit(main())
