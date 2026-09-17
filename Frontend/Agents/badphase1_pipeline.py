#!/usr/bin/env python3
"""
+======================================================================+
|        DDR3 MEMORY CONTROLLER -- PHASE 1 PIPELINE (BAD AGENTS)       |
|                                                                      |
|  Flow:                                                               |
|    3 bad agents (parallel, inject bugs) -> Validation (94 checks)    |
|        -> On failure: good agents with retry_instructions             |
|        -> Lint Gate -> Sim Gate (Xcelium) -> Success                 |
|        retry loop (max 4) on validation failures                     |
|                                                                      |
|  First pass uses BAD agents (sabotaged prompts).                     |
|  Retries use GOOD agents with failure feedback.                      |
+======================================================================+
"""
import json, os, sys, shutil, operator, glob, getpass, traceback
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
for _rel in [".", "Agents/Phase_1_Agents", "Agents/Phase_2_Agents",
             "Agents", "..", "../Phase_1_Agents", "../..",
             "Phase_1_Agents"]:
    _p = os.path.normpath(os.path.join(HERE, _rel))
    if os.path.isdir(_p) and _p not in sys.path:
        sys.path.insert(0, _p)

from langgraph.graph import StateGraph, END

# BAD agents — used for first pass (attempt 1)
from badport_wb_port_agent import BadportWbPortAgent
from badport_configreg_agent import BadportConfigRegsAgent
from badport_init_fsm_agent import BadportInitFsmAgent

# GOOD agents — used for retries (attempt 2+)
from config_regs_agent import ConfigRegsAgent as GoodConfigRegsAgent
from init_fsm_agent import InitFsmAgent as GoodInitFsmAgent
from wb_port_agent import WishbonePortAgent as GoodWbPortAgent

from phase1_validation_agent import ValidationAgent as Phase1ValidationAgent
from lint_agent import LintAgent

try:
    from cadence_ssh_agent import CadenceSSHAgent
    HAS_SIM_AGENT = True
except ImportError:
    HAS_SIM_AGENT = False

MAX_RETRIES = 4
PHASE1_RTL_DIR = "PHASE1RTL"
VALIDATION_DIR = "VALIDATIONREPORT"
P1_MODULES = ("init_fsm", "config_regs", "wb_port")

SSH_CONFIG = {
    "hostname": os.environ.get("OLYMPUS_HOST", "olympus.ece.tamu.edu"),
    "port": 22,
    "username": os.environ.get("OLYMPUS_USER", ""),
    "key_path": os.environ.get("OLYMPUS_KEY", None),
}

def setup_output_dirs(base_dir):
    dirs = {"phase1_rtl": str(Path(base_dir) / PHASE1_RTL_DIR),
            "validation": str(Path(base_dir) / VALIDATION_DIR)}
    for d in dirs.values():
        os.makedirs(d, exist_ok=True)
    return dirs


class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    phase1_rtl_dir: str
    validation_dir: str
    modules: Annotated[dict, operator.or_]
    rtl_files: Annotated[dict, operator.or_]
    attempt: int
    validation_result: dict
    failed_modules: list
    retry_instructions: Annotated[dict, operator.or_]
    history: Annotated[list, operator.add]
    lint_result: dict
    sim_result: dict
    pipeline_status: str
    ssh_password: str


# ===================================================
# START NODE (fans out to 3 generators in parallel)
# ===================================================
def start(state: GraphState) -> dict:
    """No-op entry node. Exists solely so the three generators
    can be reached via parallel edges from a single entry point."""
    attempt = state.get("attempt", 1)
    print(f"\n  Starting Phase 1 generation (attempt {attempt}, {'BAD' if attempt == 1 else 'GOOD'} agents)...")
    return {}


# ===================================================
# RTL GENERATION (3 agents, parallel)
# ===================================================
def _log_gen(mod, attempt, instr):
    if instr:
        print(f"\n  +- [P1 Attempt {attempt}] REGENERATING {mod} (GOOD agent + retry feedback)")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  |    x [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  +- [P1 Attempt {attempt}] Generating {mod} (BAD agent)")


def gen_init_fsm(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    retry_instr = state.get("retry_instructions", {}).get("init_fsm")
    _log_gen("init_fsm", attempt, retry_instr)

    if attempt == 1 or not retry_instr:
        # First pass: use BAD agent (sabotaged prompt)
        r = BadportInitFsmAgent(state["spec_path"], state["phase1_rtl_dir"]).run()
    else:
        # Retry: use GOOD agent with failure feedback
        r = GoodInitFsmAgent(
            state["spec_path"], state["phase1_rtl_dir"],
            retry_instructions=retry_instr,
        ).run()

    return {"modules": {"init_fsm": r.get("manifest", {})},
            "rtl_files": {"init_fsm": r.get("rtl_path", str(Path(state["phase1_rtl_dir"]) / "init_fsm.sv"))}}


def gen_config_regs(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    retry_instr = state.get("retry_instructions", {}).get("config_regs")
    _log_gen("config_regs", attempt, retry_instr)

    if attempt == 1 or not retry_instr:
        # First pass: use BAD agent (sabotaged prompt)
        r = BadportConfigRegsAgent(state["spec_path"], state["phase1_rtl_dir"]).run()
    else:
        # Retry: use GOOD agent with failure feedback
        r = GoodConfigRegsAgent(
            state["spec_path"], state["phase1_rtl_dir"],
            retry_instructions=retry_instr,
        ).run()

    return {"modules": {"config_regs": r.get("manifest", {})},
            "rtl_files": {"config_regs": r.get("rtl_path", str(Path(state["phase1_rtl_dir"]) / "config_regs.sv"))}}


def gen_wb_port(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    retry_instr = state.get("retry_instructions", {}).get("wb_port")
    _log_gen("wb_port", attempt, retry_instr)

    if attempt == 1 or not retry_instr:
        # First pass: use BAD agent (no retry_instructions needed)
        r = BadportWbPortAgent(state["spec_path"], state["phase1_rtl_dir"]).run()
    else:
        # Retry: use GOOD agent with failure feedback
        r = GoodWbPortAgent(state["spec_path"], state["phase1_rtl_dir"]).run()

    return {"modules": {"wb_port": r.get("manifest", {})},
            "rtl_files": {"wb_port": r.get("rtl_path", str(Path(state["phase1_rtl_dir"]) / "wb_port.sv"))}}


# ===================================================
# VALIDATION (94 static checks)
# ===================================================
def _remove_validation_tbs(validation_dir: str):
    removed = []
    for tb_file in glob.glob(os.path.join(validation_dir, "*_tb.sv")):
        os.remove(tb_file)
        removed.append(os.path.basename(tb_file))
    makefile = os.path.join(validation_dir, "Makefile.sim")
    if os.path.isfile(makefile):
        os.remove(makefile)
        removed.append("Makefile.sim")
    if removed:
        print(f"  Cleaned {len(removed)} redundant file(s) from {VALIDATION_DIR}/")


def validate_p1(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'=' * 62}")
    print(f"  PHASE 1 VALIDATION -- Attempt {attempt} of {MAX_RETRIES}")
    print(f"  (94 static checks + testbench generation)")
    print(f"{'=' * 62}")

    va = Phase1ValidationAgent(
        state["spec_path"], state["phase1_rtl_dir"], state["validation_dir"],
        attempt=attempt, max_retries=MAX_RETRIES,
        history=[h for h in state.get("history", [])])
    result = va.run()

    _remove_validation_tbs(state["validation_dir"])

    failed_modules, retry_instructions, all_failed = [], {}, []
    for mod, mr in result["modules"].items():
        if mr["status"] != "PASS" and mod in P1_MODULES:
            failed_modules.append(mod)
            fc = [c for c in mr["checks"] if not c["pass"]]
            all_failed.extend(fc)
            retry_instructions[mod] = {
                "module": mod, "attempt": attempt,
                "failed_checks": fc,
                "validation_failures": fc,   # ConfigRegsAgent uses this key
                "message": f"{len(fc)} checks failed",
            }

    history_entry = {
        "phase": 1, "attempt": attempt,
        "timestamp": datetime.now().isoformat(),
        "overall": result["overall"]["status"],
        "passed": result["overall"]["total_passed"],
        "total": result["overall"]["total_checks"],
        "failed_modules": failed_modules,
        "failed_checks": all_failed,
    }

    print(f"\n  +- PHASE 1 ATTEMPT {attempt} RESULTS:")
    for mod, mr in result["modules"].items():
        sym = "OK" if mr["status"] == "PASS" else "FAIL"
        print(f"  |  {sym:4s} {mod:20s} {mr['status']}  ({mr['passed']}/{mr['total']})")
    if failed_modules:
        print(f"  |\n  |  FAILURES:")
        for mod in failed_modules:
            for chk in retry_instructions[mod]["failed_checks"][:5]:
                print(f"  |    x [{chk['id']}] {chk['name']}")
        if attempt < MAX_RETRIES:
            print(f"  |  -> Routing {len(failed_modules)} module(s) back to GOOD agents for repair")
        else:
            print(f"  |  x MAX RETRIES EXHAUSTED")
    print(f"  +{'=' * 50}")

    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }


# ===================================================
# ROUTING + RETRY
# ===================================================
def route_after_validation(state: GraphState) -> Literal[
    "p1_increment_retry", "lint_gate", "final_failure"
]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed:
        return "lint_gate"
    elif attempt < MAX_RETRIES:
        return "p1_increment_retry"
    else:
        return "final_failure"


def p1_increment_retry(state: GraphState) -> dict:
    n = state.get("attempt", 1) + 1
    print(f"\n  -> Phase 1: Incrementing to attempt {n} (switching to GOOD agents)...")
    return {"attempt": n}


# ===================================================
# LINT GATE
# ===================================================
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print(f"  LINT AGENT -- Phase 1 Port Consistency")
    print(f"{'=' * 62}")

    lint = LintAgent(state["phase1_rtl_dir"], state["validation_dir"])
    result = lint.run()

    if result["status"] == "PASS":
        print(f"\n  OK: LINT PASSED")
    else:
        print(f"\n  FAIL: LINT FAILED -- {result['summary']['errors']} errors")

    return {"lint_result": result}


def route_after_lint(state: GraphState) -> Literal["sim_gate", "final_failure"]:
    return "sim_gate" if state.get("lint_result", {}).get("status") == "PASS" else "final_failure"


# ===================================================
# BEHAVIORAL SIMULATION REPORT (.txt)
# ===================================================
def _write_behavioral_report(val_dir, sim_results, all_passed):
    txt_path = Path(val_dir) / "behavioral_sim_report.txt"
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    lines = []
    L = lines.append

    L(f"================================================================")
    L(f"  DDR3 PHASE 1 -- BEHAVIORAL SIMULATION REPORT")
    L(f"  Generated: {ts}")
    L(f"  Simulator: Cadence Xcelium (xrun) via Olympus cluster")
    L(f"  Overall:   {'PASS' if all_passed else 'FAIL'}")
    L(f"================================================================")
    L(f"")

    total_pass = 0
    total_fail = 0
    total_tests = 0

    for mod, result in sim_results.items():
        if mod.startswith("_") or not isinstance(result, dict):
            continue

        status = result.get("status", "UNKNOWN")
        p_count = result.get("pass_count", 0)
        f_count = result.get("fail_count", 0)
        t_count = result.get("test_count", 0)
        pass_lines = result.get("pass_lines", [])
        fail_lines = result.get("fail_lines", [])
        assertion_errors = result.get("assertion_errors", [])
        exit_code = result.get("exit_code", -1)

        total_pass += p_count
        total_fail += f_count
        total_tests += t_count

        sym = "PASS" if status == "PASS" else "FAIL" if status == "FAIL" else "SKIP"

        L(f"================================================================")
        L(f"  MODULE: {mod}")
        L(f"  Status: {sym}    Tests: {p_count} passed / {f_count} failed / {t_count} total")
        L(f"  Exit code: {exit_code}")
        L(f"  Log file:  {result.get('log_file', 'N/A')}")
        L(f"================================================================")
        L(f"")

        if status == "SKIPPED":
            L(f"  (skipped -- {result.get('reason', 'unknown reason')})")
            L(f"")
            continue

        if pass_lines:
            L(f"  PASSING TESTS ({len(pass_lines)}):")
            L(f"  ----------------------------------------------------------------")
            for line in pass_lines:
                L(f"    + {line}")
            L(f"")

        if fail_lines:
            L(f"  FAILING TESTS ({len(fail_lines)}):")
            L(f"  ****************************************************************")
            for line in fail_lines:
                L(f"  >>> {line}")
            L(f"  ****************************************************************")
            L(f"")

        if assertion_errors:
            L(f"  XCELIUM ASSERTION ERRORS ({len(assertion_errors)}):")
            L(f"  ----------------------------------------------------------------")
            for line in assertion_errors:
                L(f"    ! {line}")
            L(f"")

        if status == "FAIL" and not fail_lines:
            full = result.get("full_output", "")
            if full:
                tail = full.strip().split("\n")[-30:]
                L(f"  RAW OUTPUT (last 30 lines):")
                L(f"  ----------------------------------------------------------------")
                for line in tail:
                    L(f"    {line}")
                L(f"")

        L(f"")

    L(f"================================================================")
    L(f"  SUMMARY")
    L(f"================================================================")
    L(f"")
    L(f"  {'Module':<20s} {'Status':<8s} {'Passed':<8s} {'Failed':<8s} {'Total':<8s}")
    L(f"  {'-' * 52}")
    for mod, result in sim_results.items():
        if mod.startswith("_") or not isinstance(result, dict):
            continue
        st = result.get("status", "?")
        pc = result.get("pass_count", 0)
        fc = result.get("fail_count", 0)
        tc = result.get("test_count", 0)
        L(f"  {mod:<20s} {st:<8s} {pc:<8d} {fc:<8d} {tc:<8d}")
    L(f"  {'-' * 52}")
    L(f"  {'TOTAL':<20s} {'PASS' if all_passed else 'FAIL':<8s} {total_pass:<8d} {total_fail:<8d} {total_tests:<8d}")
    L(f"")

    if total_fail > 0:
        L(f"  ****************************************************************")
        L(f"  *  {total_fail} TEST(S) FAILED -- HUMAN REVIEW REQUIRED             *")
        L(f"  ****************************************************************")
    else:
        L(f"  All {total_tests} behavioral tests passed successfully.")

    txt_path.write_text("\n".join(lines))
    print(f"  Behavioral report: {txt_path}")


# ===================================================
# SIM GATE (Cadence Xcelium via SSH)
# ===================================================
def sim_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print(f"  SIM GATE -- Cadence Xcelium Behavioral Simulation")
    print(f"{'=' * 62}")

    rtl_dir = Path(state["phase1_rtl_dir"])
    val_dir = Path(state["validation_dir"])

    if not HAS_SIM_AGENT:
        print(f"  SKIP: paramiko not installed -- simulation skipped")
        return {"sim_result": {"status": "SKIPPED", "reason": "paramiko not installed"}}

    password = state.get("ssh_password", "")
    username = SSH_CONFIG.get("username", "")
    if not username:
        print(f"  SKIP: No SSH username configured")
        return {"sim_result": {"status": "SKIPPED", "reason": "no SSH username"}}

    agent = CadenceSSHAgent(ssh_config=SSH_CONFIG)
    try:
        print(f"  Connecting to {SSH_CONFIG['hostname']} as {username}...")
        agent.connect(password=password)
        print(f"  Connected. Work dir: {agent.work_dir}")
    except Exception as e:
        print(f"  SKIP: SSH connection failed -- {e}")
        return {"sim_result": {"status": "SKIPPED", "reason": f"SSH failed: {e}"}}

    sim_results = {}
    all_passed = True

    try:
        print(f"\n  Uploading files...")
        files_to_upload = []
        for mod in P1_MODULES:
            sv_path = rtl_dir / f"{mod}.sv"
            tb_path = rtl_dir / f"{mod}_tb.sv"
            if sv_path.exists():
                files_to_upload.append(str(sv_path))
            if tb_path.exists():
                files_to_upload.append(str(tb_path))

        if files_to_upload:
            agent.upload_files(files_to_upload)
            print(f"  Uploaded {len(files_to_upload)} files")

        for mod in P1_MODULES:
            sv_file = f"{mod}.sv"
            tb_file = f"{mod}_tb.sv"
            log_file = f"{mod}_xrun.log"

            check = agent._head_exec(f"ls {agent.work_dir}/{sv_file} {agent.work_dir}/{tb_file} 2>/dev/null")
            if check["exit_code"] != 0:
                print(f"  SKIP: {mod} -- missing files on remote")
                sim_results[mod] = {"status": "SKIPPED", "reason": "missing files"}
                continue

            print(f"\n  Running {mod}...")

            xrun_cmd = (
                f"cd {agent.work_dir} && "
                f"xrun {sv_file} {tb_file} "
                f"-timescale 1ns/1ps -sysv -access +rw "
                f"-Q -unbuffered "
                f"> {log_file} 2>&1 ; "
                f"echo '===XRUN_EXIT===' ; "
                f"echo $? ; "
                f"echo '===XRUN_LOG_START===' ; "
                f"cat {log_file} ; "
                f"echo '===XRUN_LOG_END==='"
            )

            result = agent.srun(xrun_cmd, timeout=300)
            raw = result["stdout"]

            exit_code = 1
            stdout = ""

            if "===XRUN_LOG_START===" in raw and "===XRUN_LOG_END===" in raw:
                log_start = raw.index("===XRUN_LOG_START===") + len("===XRUN_LOG_START===")
                log_end = raw.index("===XRUN_LOG_END===")
                stdout = raw[log_start:log_end].strip()
                if "===XRUN_EXIT===" in raw:
                    exit_section = raw[raw.index("===XRUN_EXIT===") + len("===XRUN_EXIT==="):log_start - len("===XRUN_LOG_START===")]
                    for line in exit_section.strip().split("\n"):
                        line = line.strip()
                        if line.isdigit():
                            exit_code = int(line)
            else:
                stdout = raw

            passed = False
            test_count = 0
            fail_count = 0
            pass_lines = []
            fail_lines = []
            assertion_errors = []

            if "ALL" in stdout and "PASSED" in stdout:
                passed = True
            if "TESTS FAILED" in stdout:
                passed = False

            for line in stdout.split("\n"):
                stripped = line.strip()
                if "[PASS]" in stripped:
                    pass_lines.append(stripped)
                elif "[FAIL]" in stripped:
                    fail_lines.append(stripped)
                elif "*E,ASRTST" in stripped or "*E," in stripped:
                    assertion_errors.append(stripped)
                if "ALL" in stripped and "TESTS PASSED" in stripped:
                    parts = stripped.split()
                    for i, p in enumerate(parts):
                        if p == "ALL" and i + 1 < len(parts):
                            try: test_count = int(parts[i + 1])
                            except ValueError: pass
                elif "TESTS FAILED" in stripped:
                    parts = stripped.split()
                    for i, p in enumerate(parts):
                        if p == "of" and i + 1 < len(parts):
                            try: test_count = int(parts[i + 1])
                            except ValueError: pass

            fail_count = len(fail_lines)
            if test_count == 0:
                test_count = len(pass_lines) + len(fail_lines)

            sym = "OK" if passed else "FAIL"
            print(f"    {sym}: {mod} -- {len(pass_lines)} passed, {fail_count} failed, exit={exit_code}")
            if not passed:
                all_passed = False
                for line in fail_lines[:10]:
                    print(f"    | {line}")

            sim_results[mod] = {
                "status": "PASS" if passed else "FAIL",
                "exit_code": exit_code,
                "test_count": test_count,
                "pass_count": len(pass_lines),
                "fail_count": fail_count,
                "pass_lines": pass_lines,
                "fail_lines": fail_lines,
                "assertion_errors": assertion_errors,
                "full_output": stdout,
                "log_file": f"{mod}_xrun.log",
            }

        agent.clean_work_dir()

    except Exception as e:
        print(f"  ERROR during simulation: {e}")
        traceback.print_exc()
        all_passed = False
        sim_results["_error"] = str(e)
    finally:
        agent.disconnect()

    sim_report = {
        "status": "PASS" if all_passed else "FAIL",
        "modules": {m: {k: v for k, v in r.items() if k != "full_output"}
                    for m, r in sim_results.items() if isinstance(r, dict)},
        "timestamp": datetime.now().isoformat(),
        "server": SSH_CONFIG["hostname"],
    }
    report_path = val_dir / "sim_report.json"
    report_path.write_text(json.dumps(sim_report, indent=2))

    _write_behavioral_report(val_dir, sim_results, all_passed)

    print(f"\n  {'=' * 50}")
    if all_passed:
        print(f"  SIM GATE PASSED")
    else:
        failed_mods = [m for m, r in sim_results.items()
                       if isinstance(r, dict) and r.get("status") == "FAIL"]
        print(f"  SIM GATE FAILED -- {len(failed_mods)} module(s) failed")
    print(f"  {'=' * 50}")

    return {"sim_result": sim_report}


def route_after_sim(state: GraphState) -> Literal["success", "sim_failure"]:
    sim = state.get("sim_result", {})
    status = sim.get("status", "SKIPPED")
    if status in ("PASS", "SKIPPED"):
        return "success"
    else:
        return "sim_failure"


# ===================================================
# TERMINAL NODES
# ===================================================
def success(state: GraphState) -> dict:
    history = state.get("history", [])
    lint = state.get("lint_result", {})
    sim = state.get("sim_result", {})

    print(f"\n{'=' * 62}")
    print(f"  PHASE 1 PIPELINE -- ALL CHECKS PASSED")
    print(f"{'=' * 62}\n")

    if history:
        last = history[-1]
        print(f"  Phase 1:  {last['passed']}/{last['total']} checks "
              f"({len(history)} attempt{'s' if len(history) > 1 else ''})")

    if lint:
        s = lint.get("summary", {})
        print(f"  Lint:     {s.get('passed', '?')} passed  "
              f"{s.get('errors', '?')} errors  {s.get('warnings', '?')} warnings")

    sim_status = sim.get("status", "N/A")
    print(f"  Sim:      {sim_status}")

    if len(history) > 1:
        print(f"\n  Retry history:")
        for h in history:
            sym = "OK" if h["overall"] == "PASS" else "FAIL"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) -- failed: {fails}")

    report = {
        "status": "PASS", "pipeline": "phase1",
        "attempts": len(history),
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase1_final_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {rp}")
    print(f"{'=' * 62}")
    return {"pipeline_status": "pass"}


def final_failure(state: GraphState) -> dict:
    failed = state.get("failed_modules", [])
    history = state.get("history", [])
    ri = state.get("retry_instructions", {})

    print(f"\n{'=' * 62}")
    print(f"  PHASE 1 PIPELINE FAILED")
    print(f"{'=' * 62}")

    if failed:
        print(f"\n  VALIDATION FAILURES (final attempt):")
        for mod in failed:
            instr = ri.get(mod, {})
            fc = instr.get("failed_checks", [])
            print(f"\n  Module: {mod} ({len(fc)} failing checks)")
            for chk in fc[:10]:
                print(f"    x [{chk['id']}] {chk['name']}")
                print(f"      Expected: {chk['expected']}")
                print(f"      Actual:   {chk['actual']}")

    if history:
        print(f"\n  RETRY HISTORY ({len(history)} attempts):")
        for h in history:
            sym = "OK" if h["overall"] == "PASS" else "FAIL"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) -- failed: {fails}")

    report = {
        "status": "FAIL", "pipeline": "phase1",
        "failed_modules": failed,
        "history": history,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase1_error_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {rp}")
    return {"pipeline_status": "fail"}


def sim_failure(state: GraphState) -> dict:
    sim = state.get("sim_result", {})

    print(f"\n{'=' * 62}")
    print(f"  PHASE 1 PIPELINE FAILED AT SIM GATE")
    print(f"{'=' * 62}")
    print(f"\n  Validation and lint PASSED but behavioral sim FAILED.")
    print(f"  This requires manual debugging.")

    failed_mods = []
    if "modules" in sim:
        for mod, result in sim["modules"].items():
            if isinstance(result, dict) and result.get("status") == "FAIL":
                failed_mods.append(mod)
                print(f"    FAIL: {mod}")

    report = {
        "status": "FAIL", "pipeline": "phase1",
        "failure_stage": "BEHAVIORAL_SIMULATION",
        "failed_modules": failed_mods,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase1_error_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {rp}")
    return {"pipeline_status": "fail"}


# ===================================================
# BUILD GRAPH
# ===================================================
def build_graph():
    g = StateGraph(GraphState)

    # Nodes
    g.add_node("start", start)
    g.add_node("gen_init_fsm", gen_init_fsm)
    g.add_node("gen_config_regs", gen_config_regs)
    g.add_node("gen_wb_port", gen_wb_port)
    g.add_node("validate_p1", validate_p1)
    g.add_node("p1_increment_retry", p1_increment_retry)
    g.add_node("lint_gate", lint_gate)
    g.add_node("sim_gate", sim_gate)
    g.add_node("success", success)
    g.add_node("final_failure", final_failure)
    g.add_node("sim_failure", sim_failure)

    # Single entry point fans out to 3 generators in parallel
    g.set_entry_point("start")
    g.add_edge("start", "gen_init_fsm")
    g.add_edge("start", "gen_config_regs")
    g.add_edge("start", "gen_wb_port")

    # All 3 generators converge into validation
    g.add_edge("gen_init_fsm", "validate_p1")
    g.add_edge("gen_config_regs", "validate_p1")
    g.add_edge("gen_wb_port", "validate_p1")

    # Route after validation
    g.add_conditional_edges("validate_p1", route_after_validation,
        {"lint_gate": "lint_gate",
         "p1_increment_retry": "p1_increment_retry",
         "final_failure": "final_failure"})

    # Retry -> fan out to all 3 generators in parallel
    g.add_edge("p1_increment_retry", "gen_init_fsm")
    g.add_edge("p1_increment_retry", "gen_config_regs")
    g.add_edge("p1_increment_retry", "gen_wb_port")

    # Lint -> sim gate or failure
    g.add_conditional_edges("lint_gate", route_after_lint,
        {"sim_gate": "sim_gate", "final_failure": "final_failure"})

    # Sim -> success or sim_failure
    g.add_conditional_edges("sim_gate", route_after_sim,
        {"success": "success", "sim_failure": "sim_failure"})

    g.add_edge("success", END)
    g.add_edge("final_failure", END)
    g.add_edge("sim_failure", END)

    return g.compile()


# ===================================================
# MAIN
# ===================================================
if __name__ == "__main__":
    print("+========================================================+")
    print("|   DDR3 Controller -- Phase 1 Pipeline (BAD AGENTS)      |")
    print("|                                                         |")
    print("|   Bad agents (pass 1) -> Validate -> Good agents (retry)|")
    print("|   -> Lint Gate -> Sim Gate -> Done                      |")
    print("+========================================================+\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    dirs = setup_output_dirs(out)

    ssh_password = ""
    if HAS_SIM_AGENT:
        username = SSH_CONFIG.get("username", "")
        if not username:
            username = input("Olympus username (Enter to skip sim): ").strip()
            SSH_CONFIG["username"] = username
        if username:
            ssh_password = getpass.getpass(f"Password for {username}@{SSH_CONFIG['hostname']}: ")

    app = build_graph()

    result = app.invoke({
        "spec_path": spec,
        "output_dir": out,
        "phase1_rtl_dir": dirs["phase1_rtl"],
        "validation_dir": dirs["validation"],
        "modules": {},
        "rtl_files": {},
        "attempt": 1,
        "validation_result": {},
        "failed_modules": [],
        "retry_instructions": {},
        "history": [],
        "lint_result": {},
        "sim_result": {},
        "pipeline_status": "running",
        "ssh_password": ssh_password,
    })

    sys.exit(0 if result.get("pipeline_status") == "pass" else 1)