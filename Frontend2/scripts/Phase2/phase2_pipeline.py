#!/usr/bin/env python3
"""
+======================================================================+
|        DDR3 MEMORY CONTROLLER -- PHASE 2 PIPELINE (Frontend2)        |
|                                                                      |
|  Flow:                                                               |
|    4 RTL generation scripts + 1 testbench generator (all parallel,   |
|    all deterministic, zero LLM calls) -> generation check            |
|        -> Testbench Audit Gate (local, spec-only, no LLM/SSH)        |
|        -> Lint Gate (real Verilator via SSH/Slurm)                   |
|        -> Sim Gate (real Xcelium via SSH/Slurm) -> Success           |
|                                                                      |
|  No retry loop. Nothing here is LLM-driven, so a failure is a real   |
|  bug in a generator or the spec -- retrying would just reproduce the |
|  identical failure. See Frontend2/IMPLEMENTATION_PLAN.md.            |
|                                                                      |
|  Output:                                                             |
|    PHASE2RTL/          .sv + _tb.sv + _manifest.json per module      |
|    VALIDATIONREPORT/   audit + lint + sim reports                      |
|                                                                      |
|  Modules: addr_decoder, calibration, refresh_ctrl, bank_tracker --   |
|  all deterministic now. (In Frontend/, refresh_ctrl and bank_tracker |
|  were still LLM agents.)                                             |
+======================================================================+
"""

import json
import os
import sys
import traceback
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime
import operator

HERE = os.path.dirname(os.path.abspath(__file__))
AGENTS_DIR = os.path.dirname(HERE)
for p in (HERE, AGENTS_DIR):
    if p not in sys.path:
        sys.path.insert(0, p)

from langgraph.graph import StateGraph, END
from gate_policy import gate_passes
from addr_decoder_gen import AddrDecoderGenerator
from calibration_gen import CalibrationGenerator
from refresh_ctrl_gen import RefreshCtrlGenerator
from bank_tracker_gen import BankTrackerGenerator
from tb_generator import TestbenchGenerator
from testbench_auditor import audit as audit_testbenches

try:
    from verilator_lint import VerilatorLint
    HAS_LINT = True
except ImportError:
    HAS_LINT = False

try:
    from simulator import XceliumSimulator
    HAS_SIM = True
except ImportError:
    HAS_SIM = False

PHASE2_RTL_DIR = "PHASE2RTL"
VALIDATION_DIR = "VALIDATIONREPORT"
P2_MODULES = ("addr_decoder", "calibration", "refresh_ctrl", "bank_tracker")

SIM_CONFIG = {
    "hostname": os.environ.get("OLYMPUS_HOST", "olympus.ece.tamu.edu"),
    "port": 22,
    "username": os.environ.get("OLYMPUS_USER", ""),
    "key_path": os.environ.get("OLYMPUS_KEY", None),
}


def setup_output_dirs(base_dir):
    dirs = {"phase2_rtl": str(Path(base_dir) / PHASE2_RTL_DIR),
            "validation": str(Path(base_dir) / VALIDATION_DIR)}
    for d in dirs.values():
        os.makedirs(d, exist_ok=True)
    return dirs


class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    phase2_rtl_dir: str
    validation_dir: str
    modules: Annotated[dict, operator.or_]
    tb_audit_result: dict
    lint_result: dict
    sim_result: dict
    pipeline_status: str
    ssh_password: str


# ===================================================
# START NODE (fans out to all 5 generators in parallel)
# ===================================================
def start(state: GraphState) -> dict:
    print("\n  Starting Phase 2 generation (deterministic, no LLM)...")
    return {}


# ===================================================
# RTL + TESTBENCH GENERATION (all deterministic, all parallel)
# ===================================================
def gen_addr_decoder(state: GraphState) -> dict:
    print("\n  +- Generating addr_decoder (script)")
    r = AddrDecoderGenerator(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"addr_decoder": r}}


def gen_calibration(state: GraphState) -> dict:
    print("\n  +- Generating calibration (script)")
    r = CalibrationGenerator(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"calibration": r}}


def gen_refresh_ctrl(state: GraphState) -> dict:
    print("\n  +- Generating refresh_ctrl (script)")
    r = RefreshCtrlGenerator(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"refresh_ctrl": r}}


def gen_bank_tracker(state: GraphState) -> dict:
    print("\n  +- Generating bank_tracker (script)")
    r = BankTrackerGenerator(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"bank_tracker": r}}


def gen_testbenches(state: GraphState) -> dict:
    print("\n  +- Generating testbenches (spec-only, independent of RTL)")
    try:
        tbg = TestbenchGenerator(state["spec_path"])
        written = tbg.write_phase2(state["phase2_rtl_dir"])
        return {"modules": {"testbenches": {"status": "success", "files": written}}}
    except Exception as e:
        return {"modules": {"testbenches": {"status": "error", "errors": [str(e)]}}}


# ===================================================
# GENERATION CHECK (no retry -- a failure here is a real bug)
# ===================================================
def check_generation(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print("  GENERATION CHECK")
    print(f"{'=' * 62}")

    failed = []
    for name, result in state["modules"].items():
        status = result.get("status", "unknown")
        sym = "OK" if status == "success" else "FAIL"
        print(f"  {sym:4s} {name:15s} {status}")
        if status != "success":
            failed.append(name)

    return {"pipeline_status": "generation_failed" if failed else "generation_ok"}


def route_after_generation(state: GraphState) -> Literal["tb_audit_gate", "generation_failure"]:
    return "generation_failure" if state.get("pipeline_status") == "generation_failed" else "tb_audit_gate"


# ===================================================
# TESTBENCH AUDIT GATE (deterministic, local, no LLM, no SSH --
# see testbench_auditor.py. Cross-checks the testbench tb_generator.py
# just wrote against the spec independently of what the RTL generators
# decided, catching bugs like a stale hardcoded golden value before an
# expensive remote Xcelium job would otherwise be spent finding it.)
# ===================================================
def tb_audit_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print("  TESTBENCH AUDIT GATE -- deterministic, local, spec-derived")
    print(f"{'=' * 62}")

    result = audit_testbenches(state["spec_path"], state["phase2_rtl_dir"], P2_MODULES)
    all_ok = True
    for mod, r in result.items():
        status = r["status"]
        if status == "FAIL" or (status == "SKIPPED" and not gate_passes("SKIPPED")):
            all_ok = False
        sym = {"PASS": "OK", "NO_CHECKS": "--", "SKIPPED": "--", "FAIL": "FAIL"}[status]
        print(f"  {sym:4s} {mod:15s} {status}")
        for f in r.get("findings", []):
            print(f"    [{f['check']}] {f['register']} ({f['offset']})")
            print(f"      {f['detail']}")

    vd = Path(state["validation_dir"])
    report_path = vd / "phase2_tb_audit_report.json"
    report_path.write_text(json.dumps(result, indent=2))
    print(f"\n  Report: {report_path}")

    return {"tb_audit_result": {"status": "PASS" if all_ok else "FAIL", "modules": result}}


def route_after_tb_audit(state: GraphState) -> Literal["lint_gate", "tb_audit_failure"]:
    status = state.get("tb_audit_result", {}).get("status", "PASS")
    return "lint_gate" if status == "PASS" else "tb_audit_failure"


# ===================================================
# LINT GATE (real Verilator --lint-only via SSH/Slurm)
# ===================================================
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print("  LINT GATE -- Verilator Static Analysis")
    print(f"{'=' * 62}")

    if not HAS_LINT:
        print("  SKIP: verilator_lint.py not importable -- lint skipped")
        return {"lint_result": {"status": "SKIPPED", "reason": "verilator_lint not available"}}

    username = SIM_CONFIG.get("username", "")
    if not username:
        print("  SKIP: no OLYMPUS_USER configured")
        return {"lint_result": {"status": "SKIPPED", "reason": "no SSH username"}}

    lint = VerilatorLint(SIM_CONFIG)
    result = lint.run(state["phase2_rtl_dir"], list(P2_MODULES))

    if result["status"] == "SKIPPED":
        print(f"  SKIP: {result.get('reason', 'unknown reason')}")
        return {"lint_result": result}

    for mod, mr in result.get("modules", {}).items():
        sym = "OK" if mr.get("status") == "PASS" else "FAIL"
        n_err = len(mr.get("errors", []))
        n_warn = len(mr.get("warnings", []))
        print(f"  {sym:4s} {mod:15s} {n_err} error(s), {n_warn} warning(s)")
        for e in mr.get("errors", []):
            print(f"    ERR:  {e}")
        for w in mr.get("warnings", []):
            print(f"    WARN: {w}")

    val_dir = Path(state["validation_dir"])
    (val_dir / "phase2_lint_report.json").write_text(json.dumps(result, indent=2))
    print(f"\n  Report: {val_dir / 'phase2_lint_report.json'}")

    return {"lint_result": result}


def route_after_lint(state: GraphState) -> Literal["sim_gate", "lint_failure"]:
    status = state.get("lint_result", {}).get("status", "SKIPPED")
    return "sim_gate" if gate_passes(status) else "lint_failure"


# ===================================================
# SIM GATE (real Xcelium via SSH/Slurm)
# ===================================================
def _parse_xrun_output(stdout: str):
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


def sim_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print("  SIM GATE -- Cadence Xcelium Behavioral Simulation")
    print(f"{'=' * 62}")

    rtl_dir = Path(state["phase2_rtl_dir"])
    val_dir = Path(state["validation_dir"])

    if not HAS_SIM:
        print("  SKIP: paramiko not installed -- simulation skipped")
        return {"sim_result": {"status": "SKIPPED", "reason": "paramiko not installed"}}

    username = SIM_CONFIG.get("username", "")
    if not username:
        print("  SKIP: no OLYMPUS_USER configured")
        return {"sim_result": {"status": "SKIPPED", "reason": "no SSH username"}}

    sim = XceliumSimulator(ssh_config=SIM_CONFIG)
    try:
        print(f"  Connecting to {SIM_CONFIG['hostname']} as {username}...")
        sim.connect(password=state.get("ssh_password", "") or None)
        print(f"  Connected. Work dir: {sim.work_dir}")
    except Exception as e:
        print(f"  SKIP: SSH connection failed -- {e}")
        return {"sim_result": {"status": "SKIPPED", "reason": f"SSH failed: {e}"}}

    sim_results = {}
    all_passed = True

    try:
        files_to_upload = []
        for mod in P2_MODULES:
            sv_path, tb_path = rtl_dir / f"{mod}.sv", rtl_dir / f"{mod}_tb.sv"
            if sv_path.exists():
                files_to_upload.append(str(sv_path))
            if tb_path.exists():
                files_to_upload.append(str(tb_path))

        if files_to_upload:
            print(f"\n  Uploading {len(files_to_upload)} files...")
            sim.upload_files(files_to_upload)

        for mod in P2_MODULES:
            sv_file, tb_file, log_file = f"{mod}.sv", f"{mod}_tb.sv", f"{mod}_xrun.log"

            check = sim._head_exec(f"ls {sim.work_dir}/{sv_file} {sim.work_dir}/{tb_file} 2>/dev/null")
            if check["exit_code"] != 0:
                print(f"  SKIP: {mod} -- missing files")
                sim_results[mod] = {"status": "SKIPPED", "reason": "missing files"}
                continue

            print(f"\n  Running {mod}...")
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
            sym = "OK" if passed else "FAIL"
            print(f"    {sym}: {mod} -- {len(pass_lines)} passed, {len(fail_lines)} failed")
            if not passed:
                all_passed = False
                for line in fail_lines[:10]:
                    print(f"    | {line}")

            sim_results[mod] = {
                "status": "PASS" if passed else "FAIL",
                "test_count": test_count, "pass_count": len(pass_lines),
                "fail_count": len(fail_lines), "pass_lines": pass_lines,
                "fail_lines": fail_lines, "assertion_errors": assertion_errors,
                "full_output": stdout, "log_file": log_file,
            }

        sim.clean_work_dir()
    except Exception as e:
        print(f"  ERROR during simulation: {e}")
        traceback.print_exc()
        all_passed = False
        sim_results["_error"] = str(e)
    finally:
        sim.disconnect()

    sim_report = {
        "status": "PASS" if all_passed else "FAIL",
        "modules": {m: {k: v for k, v in r.items() if k != "full_output"}
                    for m, r in sim_results.items() if isinstance(r, dict)},
        "timestamp": datetime.now().isoformat(),
        "server": SIM_CONFIG["hostname"],
    }
    report_path = val_dir / "phase2_sim_report.json"
    report_path.write_text(json.dumps(sim_report, indent=2))
    print(f"\n  Report: {report_path}")

    return {"sim_result": sim_report}


def route_after_sim(state: GraphState) -> Literal["success", "sim_failure"]:
    status = state.get("sim_result", {}).get("status", "SKIPPED")
    return "success" if gate_passes(status) else "sim_failure"


# ===================================================
# TERMINAL NODES
# ===================================================
def success(state: GraphState) -> dict:
    print(f"\n{'=' * 62}\n  PHASE 2 PIPELINE -- ALL CHECKS PASSED\n{'=' * 62}\n")
    lint = state.get("lint_result", {})
    sim = state.get("sim_result", {})
    print(f"  Lint: {lint.get('status', 'N/A')}")
    print(f"  Sim:  {sim.get('status', 'N/A')}")
    skipped = [g for g, r in (("lint", lint), ("sim", sim)) if r.get("status") == "SKIPPED"]
    if skipped:
        print(f"\n  WARNING: {' and '.join(skipped)} SKIPPED (ALLOW_SKIPPED_GATES) -- this phase is UNVERIFIED.")

    rd = Path(state["phase2_rtl_dir"])
    vd = Path(state["validation_dir"])
    for mod in P2_MODULES:
        sv_ok = "OK" if (rd / f"{mod}.sv").exists() else "--"
        tb_ok = "OK" if (rd / f"{mod}_tb.sv").exists() else "--"
        print(f"    {sv_ok} {mod}.sv  {tb_ok} {mod}_tb.sv")

    report = {
        "status": "PASS_UNVERIFIED" if skipped else "PASS", "pipeline": "phase2",
        "skipped_gates": skipped,
        "lint_status": lint.get("status"),
        "sim_status": sim.get("status"),
        "modules": list(P2_MODULES),
        "timestamp": datetime.now().isoformat(),
    }
    (vd / "phase2_final_report.json").write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {vd / 'phase2_final_report.json'}")
    return {"pipeline_status": "pass"}


def generation_failure(state: GraphState) -> dict:
    print(f"\n{'=' * 62}\n  PHASE 2 PIPELINE FAILED -- GENERATOR BUG\n{'=' * 62}")
    print("\n  Nothing here is LLM-driven -- this is a real bug in a")
    print("  deterministic generator (or the spec/spec compiler), not a")
    print("  sampling fluke. Triage per Frontend2/IMPLEMENTATION_PLAN.md:")
    print("    1. Generator bug     -> fix the Python generator directly")
    print("    2. Spec/compiler bug -> fix microarch_compiler.py's validity matrix")
    print("    3. Validator bug     -> fix the check itself")

    failures = {name: r for name, r in state["modules"].items() if r.get("status") != "success"}
    for name, r in failures.items():
        print(f"\n  {name}: {r.get('errors', r)}")

    report = {
        "status": "FAIL", "pipeline": "phase2", "failure_stage": "GENERATION",
        "failed_modules": list(failures.keys()),
        "details": failures,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    vd = Path(state["validation_dir"])
    (vd / "phase2_error_report.json").write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {vd / 'phase2_error_report.json'}")
    return {"pipeline_status": "fail"}


def tb_audit_failure(state: GraphState) -> dict:
    print(f"\n{'=' * 62}\n  PHASE 2 PIPELINE FAILED AT TESTBENCH AUDIT GATE\n{'=' * 62}")
    print("\n  The testbench disagrees with the spec, independent of anything")
    print("  the RTL generators decided -- see phase2_tb_audit_report.json. This is")
    print("  NOT necessarily an RTL bug: it means tb_generator.py's expected")
    print("  value for a check doesn't match what the spec derives, which is")
    print("  usually a testbench bug (stale hardcoded literal, or a generic")
    print("  round-trip test that doesn't know a register has reserved bits).")
    print("  Lint/sim were skipped -- no point spending a remote Xcelium job")
    print("  simulating against a testbench already known to disagree with spec.")

    tb = state.get("tb_audit_result", {})
    failed_mods = [m for m, r in tb.get("modules", {}).items() if r.get("status") == "FAIL"]

    report = {
        "status": "FAIL", "pipeline": "phase2", "failure_stage": "TESTBENCH_AUDIT",
        "tb_audit_result": tb, "failed_modules": failed_mods,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    vd = Path(state["validation_dir"])
    (vd / "phase2_error_report.json").write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {vd / 'phase2_error_report.json'}")
    return {"pipeline_status": "fail"}


def lint_failure(state: GraphState) -> dict:
    print(f"\n{'=' * 62}\n  PHASE 2 PIPELINE FAILED AT LINT GATE\n{'=' * 62}")
    print("\n  Generation succeeded, but Verilator found a real static")
    print("  issue (width mismatch, syntax error, etc.) -- not a retry-able")
    print("  fluke. Fix the generator directly; see phase2_lint_report.json.")

    lint = state.get("lint_result", {})
    if lint.get("status") == "SKIPPED":
        print(f"\n  NOTE: this gate was SKIPPED ({lint.get('reason')}), not run. A skipped gate")
        print("  is not a pass: export OLYMPUS_USER / OLYMPUS_KEY, or set")
        print("  ALLOW_SKIPPED_GATES=1 to proceed explicitly unverified.")
    failed_mods = [m for m, r in lint.get("modules", {}).items()
                   if isinstance(r, dict) and r.get("status") == "FAIL"]
    for mod in failed_mods:
        print(f"    FAIL {mod}:")
        for e in lint["modules"][mod].get("errors", []):
            print(f"      {e}")

    report = {
        "status": "FAIL", "pipeline": "phase2", "failure_stage": "LINT",
        "lint_result": lint, "failed_modules": failed_mods,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    vd = Path(state["validation_dir"])
    (vd / "phase2_error_report.json").write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {vd / 'phase2_error_report.json'}")
    return {"pipeline_status": "fail"}


def sim_failure(state: GraphState) -> dict:
    print(f"\n{'=' * 62}\n  PHASE 2 PIPELINE FAILED AT SIM GATE\n{'=' * 62}")
    print("\n  Generation succeeded -- the RTL structure is correct.")
    print("  The failure is in BEHAVIORAL SIMULATION: a real functional")
    print("  bug in a generator's logic (or the testbench). No retry will fix this.")

    sim = state.get("sim_result", {})
    if sim.get("status") == "SKIPPED":
        print(f"\n  NOTE: this gate was SKIPPED ({sim.get('reason')}), not run. A skipped gate")
        print("  is not a pass: export OLYMPUS_USER / OLYMPUS_KEY, or set")
        print("  ALLOW_SKIPPED_GATES=1 to proceed explicitly unverified.")
    failed_mods = [m for m, r in sim.get("modules", {}).items()
                   if isinstance(r, dict) and r.get("status") == "FAIL"]
    for mod in failed_mods:
        print(f"    FAIL {mod} -- see {mod}_xrun.log")

    report = {
        "status": "FAIL", "pipeline": "phase2", "failure_stage": "BEHAVIORAL_SIMULATION",
        "sim_result": sim, "failed_modules": failed_mods,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    vd = Path(state["validation_dir"])
    (vd / "phase2_error_report.json").write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {vd / 'phase2_error_report.json'}")
    return {"pipeline_status": "fail"}


# ===================================================
# BUILD GRAPH
# ===================================================
def build_graph():
    g = StateGraph(GraphState)

    g.add_node("start", start)
    g.add_node("gen_addr_decoder", gen_addr_decoder)
    g.add_node("gen_calibration", gen_calibration)
    g.add_node("gen_refresh_ctrl", gen_refresh_ctrl)
    g.add_node("gen_bank_tracker", gen_bank_tracker)
    g.add_node("gen_testbenches", gen_testbenches)
    g.add_node("check_generation", check_generation)
    g.add_node("tb_audit_gate", tb_audit_gate)
    g.add_node("lint_gate", lint_gate)
    g.add_node("sim_gate", sim_gate)
    g.add_node("success", success)
    g.add_node("generation_failure", generation_failure)
    g.add_node("tb_audit_failure", tb_audit_failure)
    g.add_node("lint_failure", lint_failure)
    g.add_node("sim_failure", sim_failure)

    g.set_entry_point("start")
    g.add_edge("start", "gen_addr_decoder")
    g.add_edge("start", "gen_calibration")
    g.add_edge("start", "gen_refresh_ctrl")
    g.add_edge("start", "gen_bank_tracker")
    g.add_edge("start", "gen_testbenches")

    g.add_edge("gen_addr_decoder", "check_generation")
    g.add_edge("gen_calibration", "check_generation")
    g.add_edge("gen_refresh_ctrl", "check_generation")
    g.add_edge("gen_bank_tracker", "check_generation")
    g.add_edge("gen_testbenches", "check_generation")

    g.add_conditional_edges("check_generation", route_after_generation,
        {"tb_audit_gate": "tb_audit_gate", "generation_failure": "generation_failure"})

    g.add_conditional_edges("tb_audit_gate", route_after_tb_audit,
        {"lint_gate": "lint_gate", "tb_audit_failure": "tb_audit_failure"})

    g.add_conditional_edges("lint_gate", route_after_lint,
        {"sim_gate": "sim_gate", "lint_failure": "lint_failure"})

    g.add_conditional_edges("sim_gate", route_after_sim,
        {"success": "success", "sim_failure": "sim_failure"})

    g.add_edge("success", END)
    g.add_edge("generation_failure", END)
    g.add_edge("tb_audit_failure", END)
    g.add_edge("lint_failure", END)
    g.add_edge("sim_failure", END)

    return g.compile()


# ===================================================
# MAIN
# ===================================================
if __name__ == "__main__":
    print("+========================================================+")
    print("|   DDR3 Controller -- Phase 2 Pipeline (Frontend2)       |")
    print("|                                                         |")
    print("|   5 deterministic scripts -> Lint Gate -> Sim Gate      |")
    print("|   No LLM calls. No retry loop.                          |")
    print("+========================================================+\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    dirs = setup_output_dirs(out)

    ssh_password = ""
    if HAS_SIM and not SIM_CONFIG.get("key_path"):
        username = SIM_CONFIG.get("username", "")
        if not username:
            username = input("Olympus username (Enter to skip sim): ").strip()
            SIM_CONFIG["username"] = username
        if username:
            import getpass
            ssh_password = getpass.getpass(f"Password for {username}@{SIM_CONFIG['hostname']}: ")

    app = build_graph()
    result = app.invoke({
        "spec_path": spec, "output_dir": out,
        "phase2_rtl_dir": dirs["phase2_rtl"], "validation_dir": dirs["validation"],
        "modules": {}, "tb_audit_result": {}, "lint_result": {}, "sim_result": {}, "pipeline_status": "running",
        "ssh_password": ssh_password,
    })

    sys.exit(0 if result.get("pipeline_status") == "pass" else 1)
