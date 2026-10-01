#!/usr/bin/env python3
"""
+======================================================================+
|        PHASE 1 VALIDATION AGENT -- LLM-driven, human-confirmed        |
|                                                                      |
|  Reads VALIDATIONREPORT/phase1_error_report.json for a FAILED sim   |
|  gate, diagnoses the root cause with Claude, and proposes a fix --   |
|  but the fix targets the GENERATOR SCRIPT (e.g. config_regs_gen.py), |
|  never the emitted .sv directly: the .sv is a build artifact that    |
|  gets silently overwritten the next time the generator runs, so a    |
|  hand-patch to it would be lost and nobody would notice. The         |
|  generator is this project's actual source of truth (same discipline|
|  used earlier this session fixing the cmd_gen manifest/RTL desync -- |
|  fix the generator, regenerate, re-verify; never hand-edit output).  |
|                                                                      |
|  This is explicitly NOT an autonomous retry loop -- Frontend2's      |
|  phase pipelines deliberately have none of those, because retrying a |
|  deterministic generator reproduces the same bug. This is a          |
|  different thing: read the failure, read the code, propose a patch, |
|  a human reviews an actual diff and must type 'apply' before         |
|  anything is written. On apply: regenerate, re-lint, re-sim just     |
|  that module to confirm the fix actually holds, and write a report   |
|  of what was diagnosed/changed/verified plus concrete "shift left"   |
|  suggestions -- cheaper checks that could have caught this class of  |
|  bug before an expensive remote Xcelium run was ever needed.         |
|                                                                      |
|  Usage:                                                              |
|    python3 Frontend2/scripts/Phase1/phase1_validation_agent.py       |
|    (prompts for output dir + spec path, then walks every FAILED      |
|     module in that output dir's phase1_error_report.json)            |
|                                                                      |
|  Needs ANTHROPIC_API_KEY (Frontend2/.env, same as Microarch/).       |
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
import re
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
    """Same minimal loader as Microarch/microarch_agent.py: Frontend2/.env
    then repo-root .env, real shell exports always win."""
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
MAX_TOKENS = 32000  # corrected_generator_source alone can be a 750+ line file;
                     # 16000 was observed truncating mid-file in practice.
_REQUIRED_PROPOSAL_KEYS = ("root_cause", "corrected_generator_source", "explanation",
                           "shift_left_recommendations", "confidence")
MAX_ATTEMPTS_PER_MODULE = 3   # each attempt still requires a human 'apply'

P1_MODULES = ("init_fsm", "config_regs", "wb_port")
PHASE1_RTL_SUBDIR = "PHASE1RTL"
VALIDATION_SUBDIR = "VALIDATIONREPORT"

# module -> (generator .py filename stem, class name)
GENERATOR_INFO = {
    "init_fsm": ("init_fsm_gen", "InitFsmGenerator"),
    "config_regs": ("config_regs_gen", "ConfigRegsGenerator"),
    "wb_port": ("wb_port_gen", "WishbonePortGenerator"),
}


# ======================================================================
# LLM tool schema
# ======================================================================
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
        "required": ["root_cause", "corrected_generator_source", "explanation",
                     "shift_left_recommendations", "confidence"],
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
                    "do not refactor, reformat, or touch unrelated registers/"
                    "logic/comments. Prefer deriving any width/mask/value that "
                    "was wrong from self.p / self.spec over hardcoding a literal "
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
                    "lint rule, a manifest-vs-spec cross-check in a validation "
                    "agent, or a golden-value assertion in the testbench "
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
cluster and simulated against its own generated testbench; you are given \
the real, actual failure output below -- not a hypothetical.

Ground rules:
- Edit the GENERATOR source, never the emitted .sv. The .sv is a build \
artifact regenerated from the generator every run; a fix that only lives \
in the .sv would be silently overwritten and the bug would resurface the \
next time anyone runs this pipeline.
- The fix must generalize: this generator runs against many different \
specs (different speed grades, densities, device widths, address widths). \
A fix that hardcodes a value that happens to be correct only for the \
spec attached to THIS failure is not a real fix -- prefer deriving from \
self.p or self.spec over a new literal constant, exactly the way the \
surrounding code already does for parameters that vary by spec.
- Preserve the class's public interface exactly (name, __init__ signature, \
method names) -- other code imports and instantiates this class by name.
- Minimal, targeted change. Do not refactor, reformat, or touch registers/ \
logic/ports unrelated to the diagnosed root cause.
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
        out[module] = {"external_findings": lines}
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


def _failure_block(context: dict) -> str:
    if context.get("external_findings"):
        return ("VALIDATION-SUBSYSTEM FINDINGS (system-level checks from the Validation\n"
                "team's drop; the local Xcelium unit sim for this module PASSED, so the\n"
                "defect is a behavior the unit testbench does not cover):\n"
                + "\n".join("    " + l for l in context["external_findings"]))
    return (f"SIMULATION FAILURE (from phase1_error_report.json):\n"
            f"  {context['pass_count']}/{context['test_count']} tests passed.\n"
            "  Failing test lines:\n"
            + "\n".join("    " + l for l in context["fail_lines"]) + "\n"
            "  Assertion errors:\n"
            + ("\n".join("    " + l for l in context["assertion_errors"]) or "    (none)"))


def _propose_fix(client, context: dict) -> dict:
    user_msg = f"""FAILING MODULE: {context['module']}

{_failure_block(context)}

CURRENT GENERATOR SOURCE ({context['generator_path']}):
```python
{context['generator_source']}
```

EMITTED RTL ({context['module']}.sv, what was actually simulated):
```systemverilog
{context['rtl_source']}
```

TESTBENCH ({context['module']}_tb.sv):
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
    # Streamed, not .create(): at MAX_TOKENS this large the SDK refuses a
    # non-streaming call outright ("Streaming is required for operations
    # that may take longer than 10 minutes"). get_final_message() returns
    # the same Message shape .create() would have, so nothing below changes.
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
# re-verification: single-module lint + sim, mirroring phase1_pipeline.py
# ======================================================================
_EXIT_SUMMARY_RE = re.compile(r"^%Error:\s*Exiting due to \d+ (error|warning)\(s\)")


def _parse_xrun_output(stdout: str):
    """Mirrors Phase1/phase1_pipeline.py's _parse_xrun_output exactly --
    kept as a local copy rather than importing that module, since it pulls
    in the whole LangGraph pipeline definition for one utility function."""
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
    """Real Verilator lint + a real single-module Xcelium sim on Olympus.
    Returns {"lint": {...}, "sim": {...}}."""
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
    """Delete the cached bytecode for a .py file we just overwrote --
    otherwise a SEPARATE subprocess spawned right after this one exits
    (full_pipeline.py re-running the whole phase) can load a stale
    __pycache__/*.pyc if the write and the subprocess launch land in the
    same filesystem-mtime tick. See testbench_fix_agent.py's copy of this
    for the full story; observed in practice, not hypothetical."""
    try:
        cached = importlib.util.cache_from_source(str(source_path))
        Path(cached).unlink(missing_ok=True)
    except Exception:
        pass


def _regenerate(module: str, spec_path: str, output_dir: str) -> None:
    """Reload the (just-patched) generator module fresh and re-run it, so
    .sv / _tb.sv / manifest.json all reflect the applied fix."""
    mod_name, class_name = GENERATOR_INFO[module]
    if mod_name in sys.modules:
        del sys.modules[mod_name]  # force re-import of the file we just edited
    module_obj = importlib.import_module(mod_name)
    cls = getattr(module_obj, class_name)
    cls(spec_path, output_dir).run()


# ======================================================================
# per-module fix flow
# ======================================================================
def _fix_one_module(module: str, entry: dict, spec_path: str, output_dir: str,
                     client) -> dict:
    rtl_dir = Path(output_dir) / PHASE1_RTL_SUBDIR
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
            "external_findings": entry.get("external_findings", []),
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
    ap.add_argument("--findings", help="Validation findings JSON from the Frontend Orchestrator; "
                                       "replaces the Xcelium error-report precondition")
    args = ap.parse_args()

    # full_pipeline.py drives this with both flags set, since it already
    # knows them; run standalone with neither and it prompts like every
    # other script in this project.
    output_dir = args.output_dir or input("Output dir: ").strip()
    spec_path = args.spec or input("Spec JSON path: ").strip()
    if not os.path.isfile(spec_path):
        print(f"Not found: {spec_path}")
        return 1

    if args.findings:
        modules = _load_external_findings(args.findings)
        failing = [m for m in P1_MODULES if m in modules]
        if not failing:
            print("No findings for a Phase 1 module in --findings -- nothing to fix.")
            return 0
    else:
        err_path = Path(output_dir) / VALIDATION_SUBDIR / "phase1_error_report.json"
        if not err_path.is_file():
            print(f"Not found: {err_path}")
            print("(this reads the failure report a real Phase 1 sim-gate FAIL leaves behind)")
            return 1

        error_report = json.loads(err_path.read_text())
        failure_stage = error_report.get("failure_stage")
        if failure_stage != "BEHAVIORAL_SIMULATION":
            print(f"This phase failed at {failure_stage or 'an earlier stage'}, not "
                  f"BEHAVIORAL_SIMULATION -- this agent only patches RTL generators in "
                  f"response to a real sim failure, and only understands sim_result's "
                  f"shape.")
            if failure_stage == "TESTBENCH_AUDIT":
                print("(That's testbench_auditor.py's report, not Xcelium's -- it's "
                      "telling you the testbench disagrees with the spec on its own, "
                      "independent of the RTL. This agent doesn't yet act on those "
                      "findings -- see tb_audit_report.json and fix tb_generator.py by "
                      "hand for now.)")
            return 1

        modules = error_report.get("sim_result", {}).get("modules", {})
        failing = [m for m in P1_MODULES if modules.get(m, {}).get("status") == "FAIL"]

        if not failing:
            print("No FAILED modules in phase1_error_report.json -- nothing to fix.")
            return 0

    print(f"Failing module(s): {', '.join(failing)}")

    client = _anthropic_client()

    results = []
    for module in failing:
        results.append(_fix_one_module(module, modules[module], spec_path, output_dir, client))

    report = {
        "generated_by": "Frontend2/scripts/Phase1/phase1_validation_agent.py",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "git_commit": _git_commit(),
        "model": MODEL,
        "modules": results,
    }
    out_path = Path(output_dir) / VALIDATION_SUBDIR / "phase1_fix_report.json"
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
