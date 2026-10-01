#!/usr/bin/env python3
"""
+======================================================================+
|      TESTBENCH FIX AGENT -- LLM-driven, human-confirmed, spec-only   |
|                                                                      |
|  Reads VALIDATIONREPORT/tb_audit_report.json (testbench_auditor.py's |
|  deterministic findings, not Xcelium's) and proposes a patch to      |
|  tb_generator.py so the flagged checks derive their expected values  |
|  from the spec correctly.                                            |
|                                                                      |
|  DELIBERATELY SEPARATE from phase1_validation_agent.py, and never    |
|  given RTL source, RTL sim results, or any way to reach a module's   |
|  own generator -- on purpose. The circular-dependency risk with a    |
|  fix agent is that if the same agent can edit both the RTL and the   |
|  test that grades it, "make the failure go away" has no honest       |
|  preference for which side actually gets fixed. This agent sidesteps |
|  that by construction: it only ever acts on a finding that           |
|  testbench_auditor.py already established disagrees with the SPEC   |
|  directly (not with the RTL) -- there is no "which side is wrong"    |
|  question left open by the time this agent sees it, only "how do I   |
|  make this check derive from the spec instead of a stale/unsound     |
|  literal." It cannot touch RTL even if it wanted to: nothing in its  |
|  context or its tool schema lets it.                                 |
|                                                                      |
|  Hard constraint enforced in the tool schema and system prompt: this |
|  agent may only CORRECT a flagged check's expected value or input    |
|  data. It may never weaken, remove, or delete a check, or touch any  |
|  check the auditor didn't flag.                                      |
|                                                                      |
|  Re-verification here is fast and local: after applying a patch, it  |
|  re-runs testbench_auditor.py itself (no LLM, no SSH) and confirms   |
|  the flagged findings are actually gone. The authoritative real-sim  |
|  verdict is still whatever full_pipeline.py gets by re-running the   |
|  whole phase afterward, same as the RTL fix agent.                   |
|                                                                      |
|  Usage:                                                              |
|    python3 Frontend2/scripts/Phase1/testbench_fix_agent.py           |
|      [--output-dir DIR] [--spec PATH]                                |
+======================================================================+
"""
from __future__ import annotations

import argparse
import ast
import difflib
import importlib
import importlib.util
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from manifest_stamp import _git_commit  # noqa: E402
from testbench_auditor import audit as audit_testbenches  # noqa: E402


def _load_dotenv() -> None:
    here = Path(__file__).resolve()
    for env_path in (here.parents[1] / ".env", here.parents[2] / ".env"):
        if not env_path.is_file():
            continue
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, _, val = line.partition("=")
            key, val = key.strip(), val.strip().strip('"').strip("'")
            if key and key not in os.environ:
                os.environ[key] = val


_load_dotenv()

MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-5")
MAX_TOKENS = 32000
MAX_ATTEMPTS_PER_MODULE = 3

P1_MODULES = ("init_fsm", "config_regs", "wb_port")
PHASE1_RTL_SUBDIR = "PHASE1RTL"
VALIDATION_SUBDIR = "VALIDATIONREPORT"

TB_GENERATOR_PATH_STEM = "tb_generator"
TB_GENERATOR_CLASS = "TestbenchGenerator"

_REQUIRED_PROPOSAL_KEYS = ("corrected_generator_source", "explanation",
                           "shift_left_recommendations", "confidence")


PROPOSE_TB_FIX_TOOL = {
    "name": "propose_testbench_fix",
    "description": (
        "Propose a fix to tb_generator.py so the flagged check(s) derive "
        "their expected values from the spec, matching what an independent "
        "auditor already determined the spec requires."
    ),
    "input_schema": {
        "type": "object",
        "required": list(_REQUIRED_PROPOSAL_KEYS),
        "properties": {
            "corrected_generator_source": {
                "type": "string",
                "description": (
                    "The COMPLETE corrected contents of tb_generator.py, ready "
                    "to write to disk as-is. Must remain valid Python. Preserve "
                    "the class name, constructor signature, and every public "
                    "method exactly -- other code imports this by name. Change "
                    "ONLY what's needed to fix the flagged finding(s): either "
                    "correct a hardcoded/stale expected value to match the "
                    "spec-derived one, or, for a write/readback test whose "
                    "chosen test value hits a register's reserved bits, either "
                    "pick a test value that doesn't, or generalize the masked-"
                    "comparison pattern this file already uses for CTRL_CONFIG "
                    "(comparing against a computed writable mask instead of an "
                    "exact match) to the flagged register too. Do not touch "
                    "any check the finding(s) didn't name. Do not weaken, "
                    "loosen, remove, or delete any check, including the ones "
                    "you're fixing -- they must still test the same thing, "
                    "just against a correct expected value."
                ),
            },
            "explanation": {
                "type": "string",
                "description": "Plain-English: what changed, and how it makes "
                                "each flagged finding's check agree with the "
                                "spec-derived value it was given.",
            },
            "shift_left_recommendations": {
                "type": "array", "items": {"type": "string"},
                "description": "Systemic suggestions -- e.g. if the bug came "
                                "from a generic loop not knowing about "
                                "per-register reserved bits, suggest making "
                                "that loop mask-aware for every register, not "
                                "just the one instance being fixed here.",
            },
            "confidence": {
                "type": "string", "enum": ["high", "medium", "low"],
                "description": "high: certain this makes the flagged check(s) "
                                "agree with the spec-derived value with no side "
                                "effects on other checks. medium/low: less sure "
                                "-- re-audit result is the real answer either way.",
            },
        },
    },
}

SYSTEM_PROMPT = """You are fixing a deterministic Python testbench generator in a \
DDR3 memory controller project (tb_generator.py). It builds SystemVerilog \
testbenches as Python strings from a loaded spec JSON. You are given \
finding(s) from testbench_auditor.py -- a separate, deterministic tool \
that independently re-derives what each flagged check's expected value \
SHOULD be, straight from the spec, and compares that against what this \
generator actually emits. Every finding you're given is a confirmed \
disagreement between the generated testbench and the spec -- not a \
hypothesis, not something you need to re-diagnose.

You are NOT given the RTL, the RTL generator, or any simulation result, on \
purpose. Whether the RTL is correct or buggy is completely out of scope \
for you -- you are only reconciling this testbench against the spec it \
was supposed to be generated from. Do not reason about what the RTL might \
do; you don't have that information and shouldn't need it.

Hard rules:
- Fix ONLY the check(s) named in the finding(s). Do not touch any other \
check, comment, or unrelated code.
- Never weaken a check: no loosening a comparison, removing an assertion, \
deleting a test case, or making a check vacuous. The only valid edit is \
correcting what a check compares against so it matches the spec-derived \
value, while still checking the same thing it always was.
- Preserve the class name, constructor signature, and every public method \
name exactly -- other code imports this class by name.
- Prefer deriving the corrected value the same way this file's OWN correct \
patterns already do (e.g. the A-series reset checks pull reset_value \
straight from csr_register_map at generation time) over hardcoding a new \
literal that happens to be right for one spec instance.
- Call propose_testbench_fix exactly once, with the complete corrected file.
"""


def _anthropic_client():
    try:
        import anthropic
    except ImportError:
        raise RuntimeError("pip install anthropic")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        raise RuntimeError("ANTHROPIC_API_KEY not set (checked Frontend2/.env "
                            "and the repo-root .env)")
    return anthropic.Anthropic()


def _propose_fix(client, context: dict) -> dict:
    user_msg = f"""FAILING MODULE: {context['module']}

AUDITOR FINDINGS (testbench_auditor.py -- confirmed spec disagreements, not \
simulation results):
{json.dumps(context['findings'], indent=2)}

CURRENT TESTBENCH GENERATOR SOURCE (tb_generator.py):
```python
{context['generator_source']}
```

CURRENTLY EMITTED TESTBENCH ({context['module']}_tb.sv, containing the \
flagged check(s) as actually generated):
```systemverilog
{context['tb_source']}
```

FULL SPEC JSON (the design this was generated against):
```json
{context['spec_source']}
```
"""
    # Streamed, not .create(): at MAX_TOKENS this large the SDK refuses a
    # non-streaming call outright ("Streaming is required for operations
    # that may take longer than 10 minutes"). get_final_message() returns
    # the same Message shape .create() would have, so nothing below changes.
    with client.messages.stream(
        model=MODEL,
        max_tokens=MAX_TOKENS,
        system=SYSTEM_PROMPT,
        tools=[PROPOSE_TB_FIX_TOOL],
        tool_choice={"type": "tool", "name": "propose_testbench_fix"},
        messages=[{"role": "user", "content": user_msg}],
    ) as stream:
        resp = stream.get_final_message()
    if resp.stop_reason == "max_tokens":
        raise RuntimeError(
            f"response hit max_tokens ({MAX_TOKENS}) before finishing -- the "
            f"proposal (which includes the full generator file) got cut off.")
    for block in resp.content:
        if getattr(block, "type", None) == "tool_use" and block.name == "propose_testbench_fix":
            proposal = dict(block.input)
            missing = [k for k in _REQUIRED_PROPOSAL_KEYS if k not in proposal]
            if missing:
                raise RuntimeError(
                    f"model's propose_testbench_fix call is missing required "
                    f"field(s): {', '.join(missing)} (stop_reason={resp.stop_reason!r})")
            return proposal
    raise RuntimeError(f"model did not call propose_testbench_fix "
                        f"(stop_reason={resp.stop_reason!r})")


def _invalidate_pyc(source_path: Path) -> None:
    """Delete the cached bytecode for a .py file we just overwrote.
    Observed in practice: this agent's own process re-imports the patched
    module seconds later (fine, del sys.modules + re-import re-reads the
    source), but a SEPARATE subprocess spawned right after this one exits
    (full_pipeline.py re-running the whole phase) can load a stale
    __pycache__/*.pyc if the filesystem's mtime resolution is coarse
    enough that the new write and the subprocess launch land in the same
    tick -- Python's import system then can't tell the source changed.
    Removing the cache file outright removes the ambiguity entirely."""
    try:
        cached = importlib.util.cache_from_source(str(source_path))
        Path(cached).unlink(missing_ok=True)
    except Exception:
        pass  # best-effort; a missing/unwritable cache is not fatal either way


def _regenerate_testbenches(spec_path: str, output_dir: str) -> None:
    """Reload the (just-patched) tb_generator.py fresh and re-run it for
    all of Phase 1 -- it writes all three testbenches in one call, there's
    no per-module entry point."""
    if TB_GENERATOR_PATH_STEM in sys.modules:
        del sys.modules[TB_GENERATOR_PATH_STEM]
    module_obj = importlib.import_module(TB_GENERATOR_PATH_STEM)
    cls = getattr(module_obj, TB_GENERATOR_CLASS)
    rtl_dir = str(Path(output_dir) / PHASE1_RTL_SUBDIR)
    cls(spec_path).write_phase1(rtl_dir)


def _fix_one_module(module: str, findings: list, spec_path: str, output_dir: str,
                     client) -> dict:
    gen_path = HERE / f"{TB_GENERATOR_PATH_STEM}.py"
    rtl_dir = Path(output_dir) / PHASE1_RTL_SUBDIR
    record = {"module": module, "attempts": []}

    for attempt in range(1, MAX_ATTEMPTS_PER_MODULE + 1):
        print(f"\n{'#' * 62}")
        print(f"#  {module} testbench: fix attempt {attempt}/{MAX_ATTEMPTS_PER_MODULE}")
        print(f"{'#' * 62}")

        context = {
            "module": module,
            "findings": findings,
            "generator_source": gen_path.read_text(),
            "tb_source": (rtl_dir / f"{module}_tb.sv").read_text(),
            "spec_source": Path(spec_path).read_text(),
        }

        print("  asking Claude to propose a testbench fix...")
        try:
            proposal = _propose_fix(client, context)
        except Exception as e:
            print(f"  ERROR: {e}")
            record["attempts"].append({"attempt": attempt, "status": "llm_error", "error": str(e)})
            break

        new_source = proposal["corrected_generator_source"]
        try:
            ast.parse(new_source)
        except SyntaxError as e:
            print(f"  REJECTED: proposed source is not valid Python: {e}")
            record["attempts"].append({"attempt": attempt, "status": "invalid_syntax", "error": str(e)})
            continue

        old_source = context["generator_source"]
        diff = "\n".join(difflib.unified_diff(
            old_source.splitlines(), new_source.splitlines(),
            fromfile="tb_generator.py (current)", tofile="tb_generator.py (proposed)",
            lineterm=""))

        print(f"\n  EXPLANATION ({proposal['confidence']} confidence):")
        print(f"    {proposal['explanation']}")
        print(f"\n  SHIFT-LEFT RECOMMENDATIONS:")
        for r in proposal["shift_left_recommendations"]:
            print(f"    - {r}")
        print(f"\n  PROPOSED DIFF ({gen_path}):")
        print(diff if diff.strip() else "  (no textual diff)")

        choice = input(
            "\n  [a]pply and re-audit / [r]etry (ask again) / "
            "[s]kip this module: ").strip().lower()

        if choice == "s":
            record["attempts"].append({"attempt": attempt, "status": "skipped_by_human"})
            break
        if choice != "a":
            record["attempts"].append({"attempt": attempt, "status": "rejected_by_human"})
            continue

        gen_path.write_text(new_source)
        _invalidate_pyc(gen_path)
        print(f"\n  wrote {gen_path}")
        print(f"  (git-tracked -- 'git diff {gen_path}' shows this change, "
              f"'git checkout -- {gen_path}' reverts it)")

        try:
            _regenerate_testbenches(spec_path, output_dir)
        except Exception as e:
            print(f"  ERROR regenerating: {e}")
            record["attempts"].append({"attempt": attempt, "status": "regen_error",
                                        "error": str(e), "diff": diff})
            break

        print(f"\n  re-auditing {module} (local, no LLM, no SSH)...")
        reaudit = audit_testbenches(spec_path, str(rtl_dir), (module,))
        still_failing = reaudit[module]["status"] == "FAIL"
        remaining = reaudit[module]["findings"]

        record["attempts"].append({
            "attempt": attempt, "status": "applied",
            "explanation": proposal["explanation"],
            "shift_left_recommendations": proposal["shift_left_recommendations"],
            "confidence": proposal["confidence"], "diff": diff,
            "reaudit": reaudit[module], "fixed": not still_failing,
        })

        if not still_failing:
            print(f"\n  {module}: FIXED -- re-audit clean.")
            record["final_status"] = "fixed"
            return record

        print(f"\n  {module}: still flagged after this patch:")
        for f in remaining:
            print(f"    [{f['check']}] {f['register']} ({f['offset']}): {f['detail']}")
        if attempt < MAX_ATTEMPTS_PER_MODULE:
            cont = input("  Try another proposal? (y/N): ").strip().lower()
            if cont != "y":
                break

    record.setdefault("final_status", "unresolved")
    return record


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-dir", help="pipeline output dir (skips the prompt)")
    ap.add_argument("--spec", help="spec JSON path (skips the prompt)")
    args = ap.parse_args()

    output_dir = args.output_dir or input("Output dir: ").strip()
    spec_path = args.spec or input("Spec JSON path: ").strip()
    if not os.path.isfile(spec_path):
        print(f"Not found: {spec_path}")
        return 1

    audit_path = Path(output_dir) / VALIDATION_SUBDIR / "tb_audit_report.json"
    if not audit_path.is_file():
        print(f"Not found: {audit_path}")
        print("(this reads testbench_auditor.py's own report, not Xcelium's -- "
              "run the Phase 1 pipeline first, or testbench_auditor.py directly)")
        return 1

    audit_report = json.loads(audit_path.read_text())
    failing = {m: r["findings"] for m, r in audit_report.items() if r.get("status") == "FAIL"}

    if not failing:
        print("No FAILED modules in tb_audit_report.json -- nothing to fix.")
        return 0

    print(f"Failing module(s): {', '.join(failing)}")

    client = _anthropic_client()

    results = [_fix_one_module(m, findings, spec_path, output_dir, client)
               for m, findings in failing.items()]

    report = {
        "generated_by": "Frontend2/scripts/Phase1/testbench_fix_agent.py",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "git_commit": _git_commit(),
        "model": MODEL,
        "modules": results,
    }
    out_path = Path(output_dir) / VALIDATION_SUBDIR / "testbench_fix_report.json"
    out_path.write_text(json.dumps(report, indent=2))

    print(f"\n{'#' * 62}")
    print("#  SUMMARY")
    print(f"{'#' * 62}")
    for r in results:
        print(f"  {r['module']}: {r['final_status']}")
    print(f"\n  wrote {out_path}")

    return 0 if all(r["final_status"] == "fixed" for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
