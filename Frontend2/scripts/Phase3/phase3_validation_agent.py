#!/usr/bin/env python3
"""
+======================================================================+
|      PHASE 3 VALIDATION AGENT -- LLM-driven, human-confirmed        |
|                                                                      |
|  RTL fix agent for Phase 3: cmd_queue, scheduler, cmd_gen.        |
|  Same shape as Phase1/phase1_validation_agent.py: reads a failure    |
|  (phase3_error_report.json from a real Xcelium failure, or         |
|  Validation's findings via --findings), asks Claude for a patch to   |
|  the GENERATOR script (never the emitted .sv), shows a diff, applies |
|  only on 'a' (or --yes, guarded), then regenerates and re-verifies.  |
|                                                                      |
|  The testbench is a separate, spec-only file (Phase3/tb_generator.py) |
|  that this agent is not given to edit, same as Phase 1/2. It used to  |
|  be emitted by the RTL generator itself; that was moved out so a fix |
|  can't be graded by a test the same code wrote.                      |
|                                                                      |
|  Usage:                                                              |
|    python3 Frontend2/scripts/Phase3/phase3_validation_agent.py   |
|      [--output-dir DIR] [--spec PATH] [--findings F] [--yes]         |
+======================================================================+
"""
from __future__ import annotations

import argparse
import ast
import difflib
import re
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
AUTO_YES = False   # --yes: apply without the human prompt (guardrails below)
MAX_ATTEMPTS_PER_MODULE = 3

P3_MODULES = ("cmd_queue", "scheduler", "cmd_gen")
PHASE3_RTL_SUBDIR = "PHASE3RTL"
VALIDATION_SUBDIR = "VALIDATIONREPORT"


# module -> (generator .py filename stem, class name)
GENERATOR_INFO = {
    "cmd_queue": ("cmd_queue_gen", "CmdQueueGenerator"),
    "scheduler": ("scheduler_gen", "SchedulerGenerator"),
    "cmd_gen": ("cmd_gen_gen", "CmdGenGenerator"),
}

_REQUIRED_PROPOSAL_KEYS = ("root_cause", "corrected_generator_source", "explanation",
                           "shift_left_recommendations", "confidence")

PROPOSE_FIX_TOOL = {
    "name": "propose_fix",
    "description": (
        "Propose a fix to a deterministic RTL generator script that caused "
        "a real Xcelium simulation failure. The fix must edit the GENERATOR "
        "(Python source that emits SystemVerilog as text), never the "
        "emitted .sv directly."
    ),
    "input_schema": {
        "type": "object",
        "required": list(_REQUIRED_PROPOSAL_KEYS),
        "properties": {
            "root_cause": {
                "type": "string",
                "description": "1-3 sentences: the specific logic error in the "
                                "generator that produced the failing test(s). "
                                "Name the exact variable/line pattern, not a "
                                "vague category.",
            },
            "corrected_generator_source": {
                "type": "string",
                "description": (
                    "The COMPLETE corrected contents of the generator .py file, "
                    "ready to write to disk as-is. Must remain syntactically "
                    "valid Python. Preserve the class's name, constructor "
                    "signature, and all public method names exactly -- it must "
                    "stay a drop-in replacement other code imports by name. "
                    "Change only what's needed to fix the diagnosed root cause; "
                    "do not refactor, reformat, or touch unrelated logic/"
                    "comments. Prefer deriving any width/mask/value that was "
                    "wrong from self.p / self.spec over hardcoding a literal "
                    "that happens to work for this one spec instance -- a fix "
                    "that only works for this spec's current parameter values "
                    "is not actually fixed."
                ),
            },
            "explanation": {
                "type": "string",
                "description": "Plain-English: what changed and why it fixes "
                                "the specific failing test(s) named in the "
                                "failure report.",
            },
            "shift_left_recommendations": {
                "type": "array",
                "items": {"type": "string"},
                "description": (
                    "One entry per failing test (or per root cause if they "
                    "share one): a concrete, specific suggestion for a cheaper "
                    "or earlier check that could have caught this bug class "
                    "without needing a full remote Xcelium simulation -- e.g. "
                    "a generator-internal self-check comparing a port width "
                    "against self.p[...] before writing the file, a Verilator "
                    "lint rule, or a golden-value assertion in the testbench "
                    "itself. Be specific about WHERE the check would live and "
                    "WHAT it would compare -- not 'add more tests.'"
                ),
            },
            "confidence": {
                "type": "string",
                "enum": ["high", "medium", "low"],
                "description": "high: certain this resolves the failing "
                                "test(s) with no side effects. medium: "
                                "plausible but the failure mode isn't fully "
                                "pinned down. low: best guess, needs a human "
                                "to dig further regardless of what re-sim says.",
            },
        },
    },
}

SYSTEM_PROMPT = """You are fixing a deterministic Python RTL generator in a DDR3 \
memory controller project. The generator is a plain class whose methods \
(generate_rtl, generate_manifest, run) build up SystemVerilog \
and a JSON manifest as Python strings from self.p (derived parameters, a \
dict computed from the spec) and self.spec (the loaded microarchitecture \
spec JSON). Its RTL output was uploaded to Cadence Xcelium on a real \
cluster and simulated against the testbench from Phase3/tb_generator.py \
(a SEPARATE, spec-only testbench -- not written by this generator); you are given the real, actual failure \
output below -- not a hypothetical.

Ground rules:
- Edit the GENERATOR source, never the emitted .sv. The .sv is a build \
artifact regenerated from the generator every run; a fix that only lives \
in the .sv would be silently overwritten and the bug would resurface the \
next time anyone runs this pipeline.
- The testbench (Phase3/tb_generator.py) is a separate file you are not \
given and cannot edit here -- if the failure looks like the testbench's \
expected value is wrong rather than this module's RTL, say so plainly in \
root_cause and set confidence to low rather than forcing an RTL-side fix \
that doesn't actually address the real problem.
- The fix must generalize: this generator runs against many different \
specs (different speed grades, densities, device widths, geometries). A \
fix that hardcodes a value that happens to be correct only for the spec \
attached to THIS failure is not a real fix -- prefer deriving from \
self.p or self.spec over a new literal constant, exactly the way the \
surrounding code already does for parameters that vary by spec.
- A manifest port's `source` is exactly `<block>.<port>` of a port that exists, or omitted. \
Never put prose in it. If an input has no single direct driver, omit `source` or give the \
expression in `source_expr` ("a.x && b.y"); the integration map refuses anything else.
- Preserve the class's public interface exactly (name, __init__ signature, \
method names) -- other code imports and instantiates this class by name.
- Minimal, targeted change. Do not refactor, reformat, or touch logic \
unrelated to the diagnosed root cause.
- Call propose_fix exactly once, with the complete corrected file contents.
"""


def _load_external_findings(path: str) -> dict:
    """Validation-subsystem findings handed over by the Frontend
    Orchestrator (--findings). Accepts {module: [failed_check, ...]} or a
    retry_instructions.json-shaped file. Returns {module: entry} where entry
    carries 'external_findings' (formatted lines) and no sim stats -- this
    path is for defects Validation found that the local Xcelium gate did not.
    """
    raw = json.loads(Path(path).read_text())
    per_mod = raw.get("retry_instructions", raw)
    out = {}
    for module, v in per_mod.items():
        checks = v.get("failed_checks", v) if isinstance(v, dict) else v
        lines = []
        for c in checks:
            if not isinstance(c, dict):
                lines.append(str(c))
                continue
            anchors = "; ".join(f"{a.get('file')}:{a.get('line')}" for a in c.get("anchor", [])[:3])
            lines.append(f"[{c.get('severity', '?')}/{c.get('confidence', '?')}] {c.get('id')}: {c.get('name', '')} | "
                         f"expected={c.get('expected')} actual={c.get('actual')}"
                         + (f" | anchors: {anchors}" if anchors else "")
                         + (f" | Validation's proven repair hint: {c['fix']}" if c.get("fix") else ""))
        out[module] = {"external_findings": lines,
                       "confirmed": any(isinstance(c, dict) and c.get("confidence") == "confirmed"
                                        for c in checks)}
    return out


def _anthropic_client():
    try:
        import anthropic
    except ImportError:
        raise RuntimeError("pip install anthropic")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        raise RuntimeError("ANTHROPIC_API_KEY not set (checked Frontend2/.env "
                            "and the repo-root .env)")
    return anthropic.Anthropic()


def _previous_block(context: dict) -> str:
    """What happened to the previous attempt in this same run, so the model can
    tell a wrong fix from a typo (a patch that does not compile re-sims as
    '0 passed, 0 failed', which looks like nothing at all)."""
    prev = context.get("previous_attempt")
    if not prev:
        return ""
    return ("YOUR PREVIOUS ATTEMPT DID NOT VERIFY (under --yes it was reverted and the generator "
            "below is the original; otherwise the generator below already contains it):\n"
            f"  {prev}\n\n")


_SOURCE_RE = re.compile(r"^[A-Za-z0-9_]+\.[A-Za-z0-9_]+$")


def _manifest_source_problems(rtl_dir: Path, module: str) -> list:
    """Every consumer port's `source` must be <block>.<port> (the integration
    map refuses anything else), or absent."""
    try:
        m = json.loads((rtl_dir / f"{module}_manifest.json").read_text())
    except Exception as e:
        return [f"manifest unreadable: {e}"]
    out = []
    for group, plist in m.get("ports", {}).items():
        for port in plist:
            src = port.get("source")
            if src is not None and not _SOURCE_RE.match(str(src)):
                out.append(f"{module}.{port['name']}: source {src!r} is not <block>.<port>")
    return out


def _failure_block(context: dict) -> str:
    if context.get("external_findings"):
        return ("VALIDATION-SUBSYSTEM FINDINGS (system-level checks from the Validation\n"
                "team's drop; the local Xcelium unit sim for this module PASSED, so the\n"
                "defect is a behavior the unit testbench does not cover):\n"
                + "\n".join("    " + l for l in context["external_findings"]))
    return (f"SIMULATION FAILURE (from phase3_error_report.json):\n"
            f"  {context['pass_count']}/{context['test_count']} tests passed.\n"
            "  Failing test lines:\n"
            + "\n".join("    " + l for l in context["fail_lines"]) + "\n"
            "  Assertion errors:\n"
            + ("\n".join("    " + l for l in context["assertion_errors"]) or "    (none)"))


def _propose_fix(client, context: dict) -> dict:
    user_msg = f"""FAILING MODULE: {context['module']}

{_previous_block(context)}{_failure_block(context)}

CURRENT GENERATOR SOURCE ({context['generator_path']}):
```python
{context['generator_source']}
```

EMITTED RTL ({context['module']}.sv, what was actually simulated):
```systemverilog
{context['rtl_source']}
```

TESTBENCH ({context['module']}_tb.sv, written by Phase3/tb_generator.py, NOT \
by the generator you're fixing):
```systemverilog
{context['tb_source']}
```

CURRENT MANIFEST ({context['module']}_manifest.json):
```json
{context['manifest_source']}
```

FULL SPEC JSON (the design this was generated against):
```json
{context['spec_source']}
```
"""
    with client.messages.stream(
        model=MODEL,
        max_tokens=MAX_TOKENS,
        system=SYSTEM_PROMPT,
        tools=[PROPOSE_FIX_TOOL],
        tool_choice={"type": "tool", "name": "propose_fix"},
        messages=[{"role": "user", "content": user_msg}],
    ) as stream:
        resp = stream.get_final_message()
    if resp.stop_reason == "max_tokens":
        raise RuntimeError(
            f"response hit max_tokens ({MAX_TOKENS}) before finishing -- the "
            f"proposal (which includes a full generator file) got cut off "
            f"mid-generation. Raise MAX_TOKENS further if this keeps happening.")
    for block in resp.content:
        if getattr(block, "type", None) == "tool_use" and block.name == "propose_fix":
            proposal = dict(block.input)
            missing = [k for k in _REQUIRED_PROPOSAL_KEYS if k not in proposal]
            if missing:
                raise RuntimeError(
                    f"model's propose_fix call is missing required field(s): "
                    f"{', '.join(missing)} (stop_reason={resp.stop_reason!r})")
            return proposal
    raise RuntimeError(f"model did not call propose_fix (stop_reason={resp.stop_reason!r})")


# ======================================================================
# re-verification: single-module lint + sim, mirroring phase3_pipeline.py
# ======================================================================
_SUMMARY_RE = re.compile(r"==\s*(\d+)/(\d+)\s*passed\s*==")


def _parse_xrun_output(stdout: str):
    """Mirrors the Phase 3/4 pipelines: their testbenches report
    'V T01 PASS: ...' / 'X T01 FAIL: ...' / '== N/M passed ==', and the
    spec-only convention '[PASS]' / '[FAIL]' / 'ALL N TESTS PASSED'."""
    pass_lines, fail_lines, assertion_errors = [], [], []
    for line in stdout.split("\n"):
        stripped = line.strip()
        if "[PASS]" in stripped or re.match(r"V T\d+ PASS:", stripped):
            pass_lines.append(stripped)
        elif "[FAIL]" in stripped or re.match(r"X T\d+ FAIL:", stripped):
            fail_lines.append(stripped)
        elif "*E,ASRTST" in stripped or "*E," in stripped:
            assertion_errors.append(stripped)
    passed_legacy = "ALL" in stdout and "TESTS PASSED" in stdout and not fail_lines
    m = _SUMMARY_RE.search(stdout)
    passed_own = bool(m) and m.group(1) == m.group(2) and not fail_lines
    test_count = len(pass_lines) + len(fail_lines)
    return (passed_legacy or passed_own), test_count, pass_lines, fail_lines, assertion_errors


def _reverify_module(rtl_dir: Path, module: str) -> dict:
    sys.path.insert(0, str(SCRIPTS_DIR))
    from verilator_lint import VerilatorLint
    from simulator import XceliumSimulator, SSH_CONFIG

    cfg = dict(SSH_CONFIG)
    cfg["username"] = os.environ.get("OLYMPUS_USER", cfg["username"])
    cfg["key_path"] = os.environ.get("OLYMPUS_KEY", cfg["key_path"])

    print(f"\n  re-linting {module}...")
    lint_result = VerilatorLint(cfg).run(str(rtl_dir), [module])
    lint_mod = lint_result.get("modules", {}).get(module, {"status": lint_result.get("status")})
    print(f"    lint: {lint_mod.get('status')}")

    print(f"  re-simulating {module} on Olympus...")
    sim = XceliumSimulator(ssh_config=cfg)
    try:
        sim.connect()
    except Exception as e:
        print(f"    SKIP: SSH failed: {e}")
        return {"lint": lint_mod, "sim": {"status": "SKIPPED", "reason": f"SSH failed: {e}"}}

    try:
        sv_file, tb_file, log_file = f"{module}.sv", f"{module}_tb.sv", f"{module}_xrun.log"
        sim.upload_files([str(rtl_dir / sv_file), str(rtl_dir / tb_file)])
        xrun_cmd = (
            f"cd {sim.work_dir} && xrun {sv_file} {tb_file} "
            f"-timescale 1ns/1ps -sysv -access +rw -Q -unbuffered "
            f"> {log_file} 2>&1 ; echo '===XRUN_LOG_START===' ; cat {log_file} ; "
            f"echo '===XRUN_LOG_END==='"
        )
        result = sim.srun(xrun_cmd, timeout=300)
        raw = result["stdout"]
        if "===XRUN_LOG_START===" in raw and "===XRUN_LOG_END===" in raw:
            stdout = raw[raw.index("===XRUN_LOG_START===") + len("===XRUN_LOG_START===")
                          :raw.index("===XRUN_LOG_END===")].strip()
        else:
            stdout = raw
        passed, test_count, pass_lines, fail_lines, assertion_errors = _parse_xrun_output(stdout)
        sim.clean_work_dir()
        print(f"    sim: {'PASS' if passed else 'FAIL'} -- "
              f"{len(pass_lines)} passed, {len(fail_lines)} failed")
        for line in fail_lines[:10]:
            print(f"      | {line}")
        log_head = "\n".join([l for l in stdout.splitlines()
                              if "*E" in l or "rror" in l][:12])
        return {
            "lint": lint_mod,
            "sim": {"status": "PASS" if passed else "FAIL", "test_count": test_count,
                    "log_head": log_head,
                    "pass_count": len(pass_lines), "fail_count": len(fail_lines),
                    "fail_lines": fail_lines, "assertion_errors": assertion_errors},
        }
    finally:
        sim.disconnect()


# ======================================================================
# generator regeneration
# ======================================================================
def _invalidate_pyc(source_path: Path) -> None:
    """See testbench_fix_agent.py's copy of this for the full story --
    observed in practice for a different generator, same class of risk."""
    try:
        cached = importlib.util.cache_from_source(str(source_path))
        Path(cached).unlink(missing_ok=True)
    except Exception:
        pass


def _regenerate(module: str, spec_path: str, output_dir: str) -> None:
    mod_name, class_name = GENERATOR_INFO[module]
    if mod_name in sys.modules:
        del sys.modules[mod_name]
    module_obj = importlib.import_module(mod_name)
    cls = getattr(module_obj, class_name)
    # The generators write into the directory they are given; the pipeline gives
    # them PHASE3RTL/, and re-verification reads PHASE3RTL/ -- so regenerate there,
    # not into the pipeline root (which would leave re-verify looking at stale RTL).
    cls(spec_path, str(Path(output_dir) / PHASE3_RTL_SUBDIR)).run()


# ======================================================================
# per-module fix flow
# ======================================================================
def _revert(gen_path, old_source, module, spec_path, output_dir) -> None:
    """--yes guardrail: a patch that did not verify is undone, and the module
    is regenerated from the restored generator so the RTL matches it again."""
    gen_path.write_text(old_source)
    _invalidate_pyc(gen_path)
    print(f"  --yes: patch did not verify; restored {gen_path.name}")
    try:
        _regenerate(module, spec_path, output_dir)
    except Exception as e:
        print(f"  WARNING: regenerating from the restored generator failed: {e}")


def _fix_one_module(module: str, entry: dict, spec_path: str, output_dir: str,
                     client) -> dict:
    rtl_dir = Path(output_dir) / PHASE3_RTL_SUBDIR
    gen_stem, _ = GENERATOR_INFO[module]
    gen_path = HERE / f"{gen_stem}.py"

    record = {"module": module, "attempts": []}
    prev_feedback = None

    for attempt in range(1, MAX_ATTEMPTS_PER_MODULE + 1):
        print(f"\n{'#' * 62}")
        print(f"#  {module}: fix attempt {attempt}/{MAX_ATTEMPTS_PER_MODULE}")
        print(f"{'#' * 62}")

        context = {
            "module": module,
            "test_count": entry.get("test_count", 0),
            "pass_count": entry.get("pass_count", 0),
            "fail_lines": entry.get("fail_lines", []),
            "assertion_errors": entry.get("assertion_errors", []),
            "external_findings": entry.get("external_findings", []),
            "generator_path": str(gen_path),
            "generator_source": gen_path.read_text(),
            "rtl_source": (rtl_dir / f"{module}.sv").read_text(),
            "tb_source": (rtl_dir / f"{module}_tb.sv").read_text(),
            "manifest_source": (rtl_dir / f"{module}_manifest.json").read_text(),
            "spec_source": Path(spec_path).read_text(),
            "previous_attempt": prev_feedback,
        }

        print("  asking Claude to diagnose + propose a fix...")
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
            prev_feedback = f"the proposed generator was not valid Python: {e}"
            record["attempts"].append({"attempt": attempt, "status": "invalid_syntax",
                                        "error": str(e), "root_cause": proposal.get("root_cause")})
            continue

        old_source = context["generator_source"]
        diff = "\n".join(difflib.unified_diff(
            old_source.splitlines(), new_source.splitlines(),
            fromfile=f"{gen_stem}.py (current)", tofile=f"{gen_stem}.py (proposed)",
            lineterm=""))

        print(f"\n  ROOT CAUSE ({proposal['confidence']} confidence):")
        print(f"    {proposal['root_cause']}")
        print(f"\n  EXPLANATION:")
        print(f"    {proposal['explanation']}")
        print(f"\n  SHIFT-LEFT RECOMMENDATIONS:")
        for r in proposal["shift_left_recommendations"]:
            print(f"    - {r}")
        print(f"\n  PROPOSED DIFF ({gen_path}):")
        print(diff if diff.strip() else "  (no textual diff -- proposal is identical to current source)")

        if AUTO_YES:
            choice = "a"
            print("\n  --yes: applying without review (diff logged, re-verify on, reverts on failure)")
        else:
            choice = input(
                "\n  [a]pply and re-verify / [r]etry (ask again) / "
                "[s]kip this module: ").strip().lower()

        if choice == "s":
            record["attempts"].append({"attempt": attempt, "status": "skipped_by_human",
                                        "root_cause": proposal.get("root_cause")})
            break
        if choice != "a":
            record["attempts"].append({"attempt": attempt, "status": "rejected_by_human",
                                        "root_cause": proposal.get("root_cause")})
            continue

        if AUTO_YES:
            log_dir = Path(output_dir) / VALIDATION_SUBDIR / "auto_patches"
            log_dir.mkdir(parents=True, exist_ok=True)
            (log_dir / f"phase3_{module}_attempt{attempt}.diff").write_text(diff + "\n")

        gen_path.write_text(new_source)
        _invalidate_pyc(gen_path)
        print(f"\n  wrote {gen_path}")
        print(f"  (git-tracked -- 'git diff {gen_path}' shows this change, "
              f"'git checkout -- {gen_path}' reverts it)")

        try:
            _regenerate(module, spec_path, output_dir)
        except Exception as e:
            print(f"  ERROR regenerating: {e}")
            if AUTO_YES:
                _revert(gen_path, old_source, module, spec_path, output_dir)
            record["attempts"].append({"attempt": attempt, "status": "regen_error",
                                        "error": str(e), "diff": diff,
                                        "root_cause": proposal.get("root_cause")})
            break

        bad_src = _manifest_source_problems(rtl_dir, module)
        if bad_src:
            print("  REJECTED: the regenerated manifest has invalid `source` fields:")
            for b in bad_src:
                print(f"    {b}")
            _revert(gen_path, old_source, module, spec_path, output_dir)
            prev_feedback = ("the regenerated manifest had invalid `source` fields (must be "
                             "<block>.<port> or omitted; use `source_expr` for expressions): "
                             + "; ".join(bad_src[:5]))
            record["attempts"].append({"attempt": attempt, "status": "bad_manifest_source",
                                        "problems": bad_src, "reverted": True,
                                        "root_cause": proposal.get("root_cause")})
            continue

        reverify = _reverify_module(rtl_dir, module)
        sim_status = reverify["sim"].get("status")
        lint_status = reverify["lint"].get("status")
        fixed = sim_status == "PASS" and lint_status in ("PASS", "SKIPPED")

        record["attempts"].append({
            "attempt": attempt, "status": "applied",
            "root_cause": proposal["root_cause"], "explanation": proposal["explanation"],
            "shift_left_recommendations": proposal["shift_left_recommendations"],
            "confidence": proposal["confidence"], "diff": diff,
            "reverification": reverify, "fixed": fixed,
        })

        if not fixed:
            sim_info = reverify["sim"]
            prev_feedback = (
                f"the patch was applied, then lint {lint_status}, sim {sim_status} "
                f"({sim_info.get('pass_count', 0)} passed, {sim_info.get('fail_count', 0)} failed). "
                + ("NO tests ran, which usually means the patched RTL or testbench did not "
                   "compile. First errors from the simulator log:\n" + sim_info.get("log_head", "")
                   if sim_info.get("test_count", 0) == 0 else
                   "Failing lines: " + " | ".join(sim_info.get("fail_lines", [])[:6]))
                + (" Lint errors: " + "; ".join(map(str, reverify["lint"].get("errors", [])[:4]))
                   if reverify["lint"].get("status") == "FAIL" else ""))
        if AUTO_YES and not fixed:
            _revert(gen_path, old_source, module, spec_path, output_dir)
            record["attempts"][-1]["reverted"] = True

        if fixed:
            print(f"\n  {module}: FIXED -- lint {lint_status}, sim PASS on re-verification.")
            record["final_status"] = "fixed"
            return record

        print(f"\n  {module}: still failing after this patch (lint {lint_status}, "
              f"sim {sim_status}).")
        if AUTO_YES:
            continue   # next attempt, from the restored source
        if attempt < MAX_ATTEMPTS_PER_MODULE:
            cont = input("  Try another proposal? (y/N): ").strip().lower()
            if cont != "y":
                break

    record.setdefault("final_status", "unresolved")
    return record


# ======================================================================
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-dir", help="pipeline output dir (skips the prompt)")
    ap.add_argument("--spec", help="spec JSON path (skips the prompt)")
    ap.add_argument("--yes", action="store_true",
                    help="apply patches without the human prompt. Guardrails: diffs are logged to "
                         "VALIDATIONREPORT/auto_patches/, every patch is re-verified, a patch that "
                         "does not verify is reverted, and with --findings only modules with a "
                         "'confirmed' check are patched ('observed' ones are reported)")
    ap.add_argument("--findings", help="Validation findings JSON from the Frontend Orchestrator; "
                                       "replaces the Xcelium error-report precondition")
    args = ap.parse_args()
    global AUTO_YES
    AUTO_YES = args.yes

    output_dir = args.output_dir or input("Output dir: ").strip()
    spec_path = args.spec or input("Spec JSON path: ").strip()
    if not os.path.isfile(spec_path):
        print(f"Not found: {spec_path}")
        return 1

    if args.findings:
        modules = _load_external_findings(args.findings)
        failing = [m for m in P3_MODULES if m in modules]
        if not failing:
            print("No findings for a Phase 3 module in --findings -- nothing to fix.")
            return 0
        if AUTO_YES:
            observed_only = [m for m in failing if not modules[m].get("confirmed")]
            failing = [m for m in failing if modules[m].get("confirmed")]
            for m in observed_only:
                print(f"  --yes: {m} has only 'observed' findings (a predictor's word, not model-free "
                      f"evidence) -- reported, not auto-patched. Run without --yes to review it.")
            if not failing:
                return 0
    else:
        err_path = Path(output_dir) / VALIDATION_SUBDIR / "phase3_error_report.json"
        if not err_path.is_file():
            print(f"Not found: {err_path}")
            print("(this reads the failure report a real Phase 3 sim-gate FAIL leaves behind)")
            return 1

        error_report = json.loads(err_path.read_text())
        failure_stage = error_report.get("failure_stage")
        if failure_stage != "BEHAVIORAL_SIMULATION":
            print(f"This phase failed at {failure_stage or 'an earlier stage'}, not "
                  f"BEHAVIORAL_SIMULATION -- this agent only patches RTL generators in "
                  f"response to a real sim failure, and only understands sim_result's shape.")
            return 1

        modules = error_report.get("sim_result", {}).get("modules", {})
        failing = [m for m in P3_MODULES if modules.get(m, {}).get("status") == "FAIL"]

        if not failing:
            print("No FAILED modules in phase3_error_report.json -- nothing to fix.")
            return 0

    print(f"Failing module(s): {', '.join(failing)}")

    client = _anthropic_client()

    results = [_fix_one_module(m, modules[m], spec_path, output_dir, client) for m in failing]

    report = {
        "generated_by": "Frontend2/scripts/Phase3/phase3_validation_agent.py",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "git_commit": _git_commit(),
        "model": MODEL,
        "modules": results,
    }
    out_path = Path(output_dir) / VALIDATION_SUBDIR / "phase3_fix_report.json"
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
