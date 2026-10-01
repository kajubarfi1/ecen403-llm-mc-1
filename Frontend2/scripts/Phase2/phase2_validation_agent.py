#!/usr/bin/env python3
"""
+======================================================================+
|      PHASE 2 VALIDATION AGENT -- LLM-driven, human-confirmed          |
|                                                                      |
|  Direct port of Phase1/phase1_validation_agent.py for Phase 2's 4    |
|  modules (addr_decoder, calibration, refresh_ctrl, bank_tracker).    |
|  Same design, same reasoning -- see that file's docstring for the    |
|  full rationale. Short version: reads phase2_error_report.json for a |
|  real Xcelium BEHAVIORAL_SIMULATION failure, sends Claude the        |
|  failure + the generator source + the emitted RTL/testbench/manifest |
|  + the spec, and proposes a patch to the GENERATOR (never the        |
|  emitted .sv directly -- it's a build artifact, regenerated every    |
|  run). Human must type 'apply' before anything is written. On apply: |
|  regenerate, re-lint, re-sim just that module to confirm the fix     |
|  actually holds, not just that the LLM said so.                      |
|                                                                      |
|  NOTE: unlike Phase 1, there is no Phase 2 testbench-audit gate or   |
|  testbench fix agent -- investigated on 2026-09-29 and Phase 2's     |
|  testbenches (Phase2/tb_generator.py) don't have the bug class that  |
|  motivated Phase 1's (no spec-derived-then-hardcoded-stale literals; |
|  timing checks drive their own directed constants as runtime inputs, |
|  self-consistent by construction). A hollow auditor that always      |
|  passes isn't worth building. If that ever changes, testbench_fix_   |
|  agent.py and testbench_auditor.py are the templates to port.        |
|                                                                      |
|  Usage:                                                              |
|    python3 Frontend2/scripts/Phase2/phase2_validation_agent.py       |
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

P2_MODULES = ("addr_decoder", "calibration", "refresh_ctrl", "bank_tracker")
PHASE2_RTL_SUBDIR = "PHASE2RTL"
VALIDATION_SUBDIR = "VALIDATIONREPORT"

# module -> (generator .py filename stem, class name)
GENERATOR_INFO = {
    "addr_decoder": ("addr_decoder_gen", "AddrDecoderGenerator"),
    "calibration": ("calibration_gen", "CalibrationGenerator"),
    "refresh_ctrl": ("refresh_ctrl_gen", "RefreshCtrlGenerator"),
    "bank_tracker": ("bank_tracker_gen", "BankTrackerGenerator"),
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
(generate_rtl, generate_tb, generate_manifest, run) build up SystemVerilog \
and a JSON manifest as Python strings from self.p (derived parameters, a \
dict computed from the spec) and self.spec (the loaded microarchitecture \
spec JSON). Its RTL output was uploaded to Cadence Xcelium on a real \
cluster and simulated against Phase2/tb_generator.py's testbench for this \
module (a SEPARATE, spec-only, independently-derived testbench -- not \
written by this generator); you are given the real, actual failure output \
below -- not a hypothetical.

Ground rules:
- Edit the GENERATOR source, never the emitted .sv. The .sv is a build \
artifact regenerated from the generator every run; a fix that only lives \
in the .sv would be silently overwritten and the bug would resurface the \
next time anyone runs this pipeline.
- The testbench (Phase2/tb_generator.py) is a separate file you are not \
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
- Preserve the class's public interface exactly (name, __init__ signature, \
method names) -- other code imports and instantiates this class by name.
- Minimal, targeted change. Do not refactor, reformat, or touch logic \
unrelated to the diagnosed root cause.
- Call propose_fix exactly once, with the complete corrected file contents.
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

SIMULATION FAILURE (from phase2_error_report.json):
  {context['pass_count']}/{context['test_count']} tests passed.
  Failing test lines:
{chr(10).join('    ' + l for l in context['fail_lines'])}
  Assertion errors:
{chr(10).join('    ' + l for l in context['assertion_errors']) or '    (none)'}

CURRENT GENERATOR SOURCE ({context['generator_path']}):
```python
{context['generator_source']}
```

EMITTED RTL ({context['module']}.sv, what was actually simulated):
```systemverilog
{context['rtl_source']}
```

TESTBENCH ({context['module']}_tb.sv, written by Phase2/tb_generator.py, NOT \
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
# re-verification: single-module lint + sim, mirroring phase2_pipeline.py
# ======================================================================
def _parse_xrun_output(stdout: str):
    """Mirrors Phase2/phase2_pipeline.py's _parse_xrun_output exactly."""
    pass_lines, fail_lines, assertion_errors = [], [], []
    for line in stdout.split("\n"):
        stripped = line.strip()
        if "[PASS]" in stripped:
            pass_lines.append(stripped)
        elif "[FAIL]" in stripped:
            fail_lines.append(stripped)
        elif "*E,ASRTST" in stripped or "*E," in stripped:
            assertion_errors.append(stripped)
    passed = "ALL" in stdout and "TESTS PASSED" in stdout and not fail_lines
    test_count = len(pass_lines) + len(fail_lines)
    return passed, test_count, pass_lines, fail_lines, assertion_errors


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
        return {
            "lint": lint_mod,
            "sim": {"status": "PASS" if passed else "FAIL", "test_count": test_count,
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
    cls(spec_path, output_dir).run()


# ======================================================================
# per-module fix flow
# ======================================================================
def _fix_one_module(module: str, entry: dict, spec_path: str, output_dir: str,
                     client) -> dict:
    rtl_dir = Path(output_dir) / PHASE2_RTL_SUBDIR
    gen_stem, _ = GENERATOR_INFO[module]
    gen_path = HERE / f"{gen_stem}.py"

    record = {"module": module, "attempts": []}

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
            "generator_path": str(gen_path),
            "generator_source": gen_path.read_text(),
            "rtl_source": (rtl_dir / f"{module}.sv").read_text(),
            "tb_source": (rtl_dir / f"{module}_tb.sv").read_text(),
            "manifest_source": (rtl_dir / f"{module}_manifest.json").read_text(),
            "spec_source": Path(spec_path).read_text(),
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

        gen_path.write_text(new_source)
        _invalidate_pyc(gen_path)
        print(f"\n  wrote {gen_path}")
        print(f"  (git-tracked -- 'git diff {gen_path}' shows this change, "
              f"'git checkout -- {gen_path}' reverts it)")

        try:
            _regenerate(module, spec_path, output_dir)
        except Exception as e:
            print(f"  ERROR regenerating: {e}")
            record["attempts"].append({"attempt": attempt, "status": "regen_error",
                                        "error": str(e), "diff": diff,
                                        "root_cause": proposal.get("root_cause")})
            break

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

        if fixed:
            print(f"\n  {module}: FIXED -- lint {lint_status}, sim PASS on re-verification.")
            record["final_status"] = "fixed"
            return record

        print(f"\n  {module}: still failing after this patch (lint {lint_status}, "
              f"sim {sim_status}).")
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
    args = ap.parse_args()

    output_dir = args.output_dir or input("Output dir: ").strip()
    spec_path = args.spec or input("Spec JSON path: ").strip()
    if not os.path.isfile(spec_path):
        print(f"Not found: {spec_path}")
        return 1

    err_path = Path(output_dir) / VALIDATION_SUBDIR / "phase2_error_report.json"
    if not err_path.is_file():
        print(f"Not found: {err_path}")
        print("(this reads the failure report a real Phase 2 sim-gate FAIL leaves behind)")
        return 1

    error_report = json.loads(err_path.read_text())
    failure_stage = error_report.get("failure_stage")
    if failure_stage != "BEHAVIORAL_SIMULATION":
        print(f"This phase failed at {failure_stage or 'an earlier stage'}, not "
              f"BEHAVIORAL_SIMULATION -- this agent only patches RTL generators in "
              f"response to a real sim failure, and only understands sim_result's shape.")
        return 1

    modules = error_report.get("sim_result", {}).get("modules", {})
    failing = [m for m in P2_MODULES if modules.get(m, {}).get("status") == "FAIL"]

    if not failing:
        print("No FAILED modules in phase2_error_report.json -- nothing to fix.")
        return 0

    print(f"Failing module(s): {', '.join(failing)}")

    client = _anthropic_client()

    results = [_fix_one_module(m, modules[m], spec_path, output_dir, client) for m in failing]

    report = {
        "generated_by": "Frontend2/scripts/Phase2/phase2_validation_agent.py",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "git_commit": _git_commit(),
        "model": MODEL,
        "modules": results,
    }
    out_path = Path(output_dir) / VALIDATION_SUBDIR / "phase2_fix_report.json"
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
