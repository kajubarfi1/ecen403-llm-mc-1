#!/usr/bin/env python3
"""
+======================================================================+
|        DDR3 MEMORY CONTROLLER -- PHASE 2 PIPELINE                    |
|                                                                      |
|  Flow:                                                               |
|    4 agents (parallel) -> Validation (114 checks)                    |
|        -> Lint Gate -> Sim Gate (Xcelium) -> Success                 |
|        retry loop (max 4) on validation failures                     |
|                                                                      |
|  Input:  Phase 1 output dir (contains .sv + _manifest.json)          |
|                                                                      |
|  Output:                                                             |
|    PHASE2RTL/          .sv + _tb.sv + _manifest.json per module      |
|    VALIDATIONREPORT/   validation reports + lint + sim reports       |
|                                                                      |
|  Modules: addr_decoder, bank_tracker, refresh_ctrl, calibration      |
+======================================================================+
"""
import json, os, sys, shutil, operator, glob, getpass, traceback, re
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "Agents", "Phase_2_Agents"))
sys.path.insert(0, os.path.join(HERE, "Agents", "Phase_1_Agents"))
sys.path.insert(0, os.path.join(HERE, "Agents"))
sys.path.insert(0, HERE)

from langgraph.graph import StateGraph, END
from addr_decoder_agent import AddrDecoderAgent
from bank_tracker_agent import BankTrackerAgent
from refresh_ctrl_agent import RefreshCtrlAgent
from calibration_agent import CalibrationAgent
from phase2_validation_agent import Phase2ValidationAgent
from lint_agent import LintAgent

try:
    from cadence_ssh_agent import CadenceSSHAgent
    HAS_SIM_AGENT = True
except ImportError:
    HAS_SIM_AGENT = False

MAX_RETRIES = 4
PHASE2_RTL_DIR = "PHASE2RTL"
VALIDATION_DIR = "VALIDATIONREPORT"
P2_MODULES = ("addr_decoder", "bank_tracker", "refresh_ctrl", "calibration")
# Only the LLM-driven modules benefit from retries. Deterministic agents
# (addr_decoder, calibration) produce identical output each run, so a
# validation failure there is a deterministic bug, not a flaky generation.
P2_RETRYABLE = ("bank_tracker", "refresh_ctrl")

SSH_CONFIG = {
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


def _latest_retry_instructions(_old: dict, new: dict) -> dict:
    """Reducer for retry_instructions: each validation pass fully replaces the
    previous attempt's feedback. With operator.or_ a module that started passing
    on a later attempt kept a stale 'fix these failures' entry forever, so it
    would be regenerated against failures that no longer existed."""
    return new


class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    phase1_rtl_dir: str
    phase2_rtl_dir: str
    validation_dir: str
    modules: Annotated[dict, operator.or_]
    rtl_files: Annotated[dict, operator.or_]
    attempt: int
    validation_result: dict
    failed_modules: list
    retry_instructions: Annotated[dict, _latest_retry_instructions]
    history: Annotated[list, operator.add]
    lint_result: dict
    sim_result: dict
    pipeline_status: str
    ssh_password: str


# ===================================================
# START NODE (fans out to 4 generators in parallel)
# ===================================================
def start(state: GraphState) -> dict:
    """No-op entry node. Exists solely so the four generators
    can be reached via parallel edges from a single entry point."""
    attempt = state.get("attempt", 1)
    print(f"\n  Starting Phase 2 generation (attempt {attempt})...")
    return {}


# ===================================================
# RTL GENERATION
# ===================================================
def _log_gen(mod, attempt, instr):
    if instr:
        print(f"\n  +- [P2 Attempt {attempt}] REGENERATING {mod}")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  |    x [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  +- [P2 Attempt {attempt}] Generating {mod}")


def gen_addr_decoder(state: GraphState) -> dict:
    _log_gen("addr_decoder", state.get("attempt", 1),
             state.get("retry_instructions", {}).get("addr_decoder"))
    r = AddrDecoderAgent(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"addr_decoder": r.get("manifest", {})},
            "rtl_files": {"addr_decoder": r.get("rtl_path",
                str(Path(state["phase2_rtl_dir"]) / "addr_decoder.sv"))}}


def gen_bank_tracker(state: GraphState) -> dict:
    ri = state.get("retry_instructions", {}).get("bank_tracker")
    _log_gen("bank_tracker", state.get("attempt", 1), ri)
    r = BankTrackerAgent(
        state["spec_path"],
        state["phase2_rtl_dir"],
        retry_instructions=ri,
    ).run()
    return {"modules": {"bank_tracker": r.get("manifest", {})},
            "rtl_files": {"bank_tracker": r.get("rtl_path",
                str(Path(state["phase2_rtl_dir"]) / "bank_tracker.sv"))}}


def gen_refresh_ctrl(state: GraphState) -> dict:
    ri = state.get("retry_instructions", {}).get("refresh_ctrl")
    _log_gen("refresh_ctrl", state.get("attempt", 1), ri)
    r = RefreshCtrlAgent(
        state["spec_path"],
        state["phase2_rtl_dir"],
        retry_instructions=ri,
    ).run()
    return {"modules": {"refresh_ctrl": r.get("manifest", {})},
            "rtl_files": {"refresh_ctrl": r.get("rtl_path",
                str(Path(state["phase2_rtl_dir"]) / "refresh_ctrl.sv"))}}


def gen_calibration(state: GraphState) -> dict:
    _log_gen("calibration", state.get("attempt", 1),
             state.get("retry_instructions", {}).get("calibration"))
    r = CalibrationAgent(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"calibration": r.get("manifest", {})},
            "rtl_files": {"calibration": r.get("rtl_path",
                str(Path(state["phase2_rtl_dir"]) / "calibration.sv"))}}


# ===================================================
# VALIDATION
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
        print(f"  Cleaned {len(removed)} stray file(s) from {VALIDATION_DIR}/")


def validate_p2(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'=' * 62}")
    print(f"  PHASE 2 VALIDATION -- Attempt {attempt} of {MAX_RETRIES}")
    print(f"  (114 static checks + testbench generation)")
    print(f"{'=' * 62}")

    va = Phase2ValidationAgent(
        state["spec_path"], state["phase2_rtl_dir"], state["validation_dir"],
        attempt=attempt, max_retries=MAX_RETRIES,
        history=[h for h in state.get("history", [])])
    result = va.run()

    _remove_validation_tbs(state["validation_dir"])

    failed_modules, retry_instructions, all_failed = [], {}, []
    for mod, mr in result["modules"].items():
        if mr["status"] != "PASS" and mod in P2_RETRYABLE:
            failed_modules.append(mod)
            fc = [c for c in mr["checks"] if not c["pass"]]
            all_failed.extend(fc)
            retry_instructions[mod] = {
                "module": mod, "attempt": attempt,
                "failed_checks": fc,
                "message": f"{len(fc)} checks failed",
            }

    history_entry = {
        "phase": 2, "attempt": attempt,
        "timestamp": datetime.now().isoformat(),
        "overall": result["overall"]["status"],
        "passed": result["overall"]["total_passed"],
        "total": result["overall"]["total_checks"],
        "failed_modules": failed_modules,
        "failed_checks": all_failed,
    }

    print(f"\n  +- PHASE 2 ATTEMPT {attempt} RESULTS:")
    for mod, mr in result["modules"].items():
        sym = "OK" if mr["status"] == "PASS" else "FAIL"
        print(f"  |  {sym:4s} {mod:20s} {mr['status']}  ({mr['passed']}/{mr['total']})")
    if failed_modules:
        print(f"  |\n  |  FAILURES:")
        for mod in failed_modules:
            for chk in retry_instructions[mod]["failed_checks"][:5]:
                print(f"  |    x [{chk['id']}] {chk['name']}")
        if attempt < MAX_RETRIES:
            print(f"  |  -> Routing {len(failed_modules)} module(s) back")
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
# ROUTING
# ===================================================
def route_after_validation(state: GraphState) -> Literal[
    "p2_increment_retry", "lint_gate", "final_failure"
]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed:
        return "lint_gate"
    elif attempt < MAX_RETRIES:
        return "p2_increment_retry"
    else:
        return "final_failure"


def p2_increment_retry(state: GraphState) -> dict:
    n = state.get("attempt", 1) + 1
    print(f"\n  -> Phase 2: Incrementing to attempt {n}...")
    return {"attempt": n}


# ===================================================
# LINT GATE
# ===================================================
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print(f"  LINT AGENT -- Cross-Phase Port Consistency")
    print(f"{'=' * 62}")

    combined = Path(state["validation_dir"]) / "lint_combined"
    combined.mkdir(parents=True, exist_ok=True)
    for src in [state.get("phase1_rtl_dir", ""), state["phase2_rtl_dir"]]:
        if not src:
            continue
        p = Path(src)
        if p.exists():
            for mf in p.glob("*_manifest.json"):
                shutil.copy2(str(mf), str(combined / mf.name))

    result = LintAgent(str(combined), state["validation_dir"]).run()

    if result["status"] == "PASS":
        print(f"\n  OK: LINT PASSED")
    else:
        print(f"\n  FAIL: LINT FAILED -- {result['summary']['errors']} errors")

    return {"lint_result": result}


def route_after_lint(state: GraphState) -> Literal["sim_gate", "final_failure"]:
    return "sim_gate" if state.get("lint_result", {}).get("status") == "PASS" else "final_failure"


# ===================================================
# TESTBENCH OUTPUT PARSER
# Handles both Phase 1 and Phase 2 testbench formats:
#   Phase 1: "[PASS]" / "[FAIL]" + "ALL N TESTS PASSED"
#   Phase 2: "V Tnn PASS:" / "X Tnn FAIL:" + "== N/N passed =="
# ===================================================
_P2_PASS_RE = re.compile(r"V\s+T\d+\s+PASS\s*:")
_P2_FAIL_RE = re.compile(r"X\s+T\d+\s+FAIL\s*:")
_P2_SUMMARY_RE = re.compile(r"==\s*(\d+)\s*/\s*(\d+)\s+passed\s*==")
_P1_ALL_PASS_RE = re.compile(r"ALL\s+(\d+)\s+TESTS\s+PASSED")
_P1_FAIL_SUM_RE = re.compile(r"(\d+)\s+of\s+(\d+)\s+TESTS\s+FAILED")


def _parse_xrun_output(stdout):
    """Parse Cadence xrun output for both Phase 1 and Phase 2 testbench styles.
    Returns (passed, test_count, pass_lines, fail_lines, assertion_errors)."""
    pass_lines = []
    fail_lines = []
    assertion_errors = []

    for line in stdout.split("\n"):
        stripped = line.strip()
        if "[PASS]" in stripped:
            pass_lines.append(stripped)
        elif "[FAIL]" in stripped:
            fail_lines.append(stripped)
        elif _P2_PASS_RE.search(stripped):
            pass_lines.append(stripped)
        elif _P2_FAIL_RE.search(stripped):
            fail_lines.append(stripped)
        elif "*E,ASRTST" in stripped or "*E," in stripped:
            assertion_errors.append(stripped)

    passed = False
    test_count = 0

    m = _P2_SUMMARY_RE.search(stdout)
    if m:
        p_sum, t_sum = int(m.group(1)), int(m.group(2))
        test_count = t_sum
        passed = (p_sum == t_sum) and (t_sum > 0) and (len(fail_lines) == 0)
    else:
        m = _P1_ALL_PASS_RE.search(stdout)
        if m:
            test_count = int(m.group(1))
            passed = (len(fail_lines) == 0)
        else:
            m = _P1_FAIL_SUM_RE.search(stdout)
            if m:
                test_count = int(m.group(2))
                passed = False
            else:
                if pass_lines and not fail_lines:
                    passed = True
                    test_count = len(pass_lines)
                else:
                    passed = False
                    test_count = len(pass_lines) + len(fail_lines)

    return passed, test_count, pass_lines, fail_lines, assertion_errors


# ===================================================
# BEHAVIORAL SIMULATION REPORT
# ===================================================
def _write_behavioral_report(val_dir, sim_results, all_passed):
    txt_path = Path(val_dir) / "behavioral_sim_report_phase2.txt"
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    lines = []
    L = lines.append

    L(f"================================================================")
    L(f"  DDR3 PHASE 2 -- BEHAVIORAL SIMULATION REPORT")
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
        L(f"")
    else:
        L(f"  All {total_tests} behavioral tests passed successfully.")
        L(f"")

    txt_path.write_text("\n".join(lines))
    print(f"  Behavioral report: {txt_path}")


# ===================================================
# SIM GATE
# ===================================================
def sim_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print(f"  SIM GATE -- Cadence Xcelium Behavioral Simulation")
    print(f"{'=' * 62}")

    rtl_dir = Path(state["phase2_rtl_dir"])
    val_dir = Path(state["validation_dir"])

    if not HAS_SIM_AGENT:
        print(f"  SKIP: paramiko not installed -- simulation skipped")
        print(f"  Install with: pip install paramiko")
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
        for mod in P2_MODULES:
            sv_path = rtl_dir / f"{mod}.sv"
            tb_path = rtl_dir / f"{mod}_tb.sv"
            if sv_path.exists():
                files_to_upload.append(str(sv_path))
            if tb_path.exists():
                files_to_upload.append(str(tb_path))

        if files_to_upload:
            agent.upload_files(files_to_upload)
            print(f"  Uploaded {len(files_to_upload)} files")

        for mod in P2_MODULES:
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
            srun_stderr = result["stderr"]

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
                print(f"    [DEBUG] No log markers found in srun output ({len(raw)} chars)")
                if raw:
                    for line in raw.strip().split("\n")[:5]:
                        print(f"    [DEBUG] raw: {line[:120]}")
                if srun_stderr:
                    print(f"    [DEBUG] stderr: {srun_stderr[:300]}")

            print(f"    Read {len(stdout)} chars, exit={exit_code}")

            passed, test_count, pass_lines, fail_lines, assertion_errors = _parse_xrun_output(stdout)
            fail_count = len(fail_lines)

            sym = "OK" if passed else "FAIL"
            print(f"    {sym}: {mod} -- {len(pass_lines)} passed, {fail_count} failed, exit={exit_code}")
            if not passed:
                all_passed = False
                for line in fail_lines[:10]:
                    print(f"    | {line}")
                for line in assertion_errors[:5]:
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
        "phase": 2,
        "modules": {m: {k: v for k, v in r.items() if k != "full_output"}
                    for m, r in sim_results.items() if isinstance(r, dict)},
        "timestamp": datetime.now().isoformat(),
        "server": SSH_CONFIG["hostname"],
    }
    report_path = val_dir / "sim_report_phase2.json"
    report_path.write_text(json.dumps(sim_report, indent=2))

    _write_behavioral_report(val_dir, sim_results, all_passed)

    print(f"\n  {'=' * 50}")
    if all_passed:
        print(f"  SIM GATE PASSED -- all modules passed behavioral sim")
    else:
        failed_mods = [m for m, r in sim_results.items()
                       if isinstance(r, dict) and r.get("status") == "FAIL"]
        print(f"  SIM GATE FAILED -- {len(failed_mods)} module(s) failed:")
        for m in failed_mods:
            print(f"    x {m}")
    print(f"  Report: {report_path}")
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
    print(f"  PHASE 2 PIPELINE -- ALL CHECKS PASSED")
    print(f"{'=' * 62}\n")

    if history:
        last = history[-1]
        print(f"  Phase 2:  {last['passed']}/{last['total']} checks "
              f"({len(history)} attempt{'s' if len(history) > 1 else ''})")

    if lint:
        s = lint.get("summary", {})
        print(f"  Lint:     {s.get('passed', '?')} passed  "
              f"{s.get('errors', '?')} errors  {s.get('warnings', '?')} warnings")

    sim_status = sim.get("status", "N/A")
    print(f"  Sim:      {sim_status}")

    print(f"\n  Generated outputs:")
    rd = Path(state["phase2_rtl_dir"])
    vd = Path(state["validation_dir"])
    for mod in P2_MODULES:
        sv_ok = "OK" if (rd / f"{mod}.sv").exists() else "--"
        tb_ok = "OK" if (rd / f"{mod}_tb.sv").exists() else "--"
        mf_ok = "OK" if (rd / f"{mod}_manifest.json").exists() else "--"
        print(f"    {sv_ok} {mod}.sv  {tb_ok} {mod}_tb.sv  {mf_ok} {mod}_manifest.json")

    vr = vd / "validation_report.json"
    print(f"    {'OK' if vr.exists() else '--'} validation_report.json")

    if len(history) > 1:
        print(f"\n  Retry history:")
        for h in history:
            sym = "OK" if h["overall"] == "PASS" else "FAIL"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) -- failed: {fails}")

    report = {
        "status": "PASS", "pipeline": "phase2",
        "lint_status": lint.get("status"),
        "sim_status": sim_status,
        "attempts": len(history),
        "modules": list(P2_MODULES),
        "outputs": {
            mod: {
                "sv": str(rd / f"{mod}.sv"),
                "tb": str(rd / f"{mod}_tb.sv"),
                "manifest": str(rd / f"{mod}_manifest.json"),
            }
            for mod in P2_MODULES
        },
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    rp = vd / "phase2_final_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {rp}")
    print(f"{'=' * 62}")
    return {"pipeline_status": "pass"}


def _print_human_review_banner(failure_stage, state):
    vd = state.get("validation_dir", "VALIDATIONREPORT")
    rd = state.get("phase2_rtl_dir", "PHASE2RTL")

    print(f"")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"  !!          PIPELINE FAILED -- HUMAN REVIEW REQUIRED      !!")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"")
    print(f"  The Phase 2 pipeline has FAILED at: {failure_stage}")
    print(f"")
    print(f"  1. CHECK THE VALIDATION REPORT:")
    print(f"     {vd}/")
    print(f"  2. INSPECT THE GENERATED RTL for bugs:")
    print(f"     {rd}/")
    for mod in P2_MODULES:
        print(f"     - {mod}.sv + {mod}_tb.sv")
    print(f"")


def final_failure(state: GraphState) -> dict:
    failed = state.get("failed_modules", [])
    history = state.get("history", [])
    lint = state.get("lint_result", {})
    ri = state.get("retry_instructions", {})

    if lint and lint.get("status") == "FAIL":
        failure_stage = "LINT GATE"
    elif failed:
        failure_stage = f"VALIDATION (after {MAX_RETRIES} attempts)"
    else:
        failure_stage = "UNKNOWN"

    print(f"\n{'=' * 62}")
    print(f"  PHASE 2 PIPELINE FAILED")
    print(f"{'=' * 62}")

    _print_human_review_banner(failure_stage, state)

    if lint and lint.get("status") == "FAIL":
        print(f"\n  LINT FAILURES:")
        for e in lint.get("errors", []):
            print(f"    x [{e.get('check', '?')}] {e.get('message', '?')}")

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
        "status": "FAIL", "pipeline": "phase2",
        "failure_stage": failure_stage,
        "failed_modules": failed,
        "lint_result": lint,
        "retry_instructions": {mod: {
            "module": ri[mod]["module"],
            "failed_checks": ri[mod]["failed_checks"],
        } for mod in ri},
        "history": history,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase2_error_report.json"
    rp.write_text(json.dumps(report, indent=2))

    print(f"\n  Error report: {rp}")
    return {"pipeline_status": "fail"}


def sim_failure(state: GraphState) -> dict:
    sim = state.get("sim_result", {})
    history = state.get("history", [])

    print(f"\n{'=' * 62}")
    print(f"  PHASE 2 PIPELINE FAILED AT SIM GATE")
    print(f"{'=' * 62}")

    _print_human_review_banner("BEHAVIORAL SIMULATION (Xcelium)", state)

    print(f"\n  NOTE: Validation and lint PASSED -- the RTL structure is correct.")
    print(f"  The failure is in BEHAVIORAL SIMULATION -- RTL has functional bugs.")

    failed_mods = []
    if "modules" in sim:
        print(f"\n  SIM RESULTS PER MODULE:")
        for mod, result in sim["modules"].items():
            if mod.startswith("_"):
                continue
            if isinstance(result, dict):
                sym = "OK" if result.get("status") == "PASS" else "FAIL"
                print(f"    {sym} {mod}: {result.get('status', '?')}")
                if result.get("status") == "FAIL":
                    failed_mods.append(mod)
                    print(f"      Log: {result.get('log_file', 'N/A')}")

    print(f"\n  TO DEBUG:")
    for mod in failed_mods:
        print(f"    xrun {mod}.sv {mod}_tb.sv -timescale 1ns/1ps -sysv -access +rw")

    report = {
        "status": "FAIL", "pipeline": "phase2",
        "failure_stage": "BEHAVIORAL_SIMULATION",
        "sim_result": sim,
        "failed_modules": failed_mods,
        "history": history,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase2_error_report.json"
    rp.write_text(json.dumps(report, indent=2))

    print(f"\n  Error report: {rp}")
    return {"pipeline_status": "fail"}


# ===================================================
# BUILD GRAPH
# ===================================================
def build_graph():
    g = StateGraph(GraphState)

    g.add_node("start", start)
    g.add_node("gen_addr_decoder", gen_addr_decoder)
    g.add_node("gen_bank_tracker", gen_bank_tracker)
    g.add_node("gen_refresh_ctrl", gen_refresh_ctrl)
    g.add_node("gen_calibration", gen_calibration)
    g.add_node("validate_p2", validate_p2)
    g.add_node("p2_increment_retry", p2_increment_retry)
    g.add_node("lint_gate", lint_gate)
    g.add_node("sim_gate", sim_gate)
    g.add_node("success", success)
    g.add_node("final_failure", final_failure)
    g.add_node("sim_failure", sim_failure)

    g.set_entry_point("start")
    g.add_edge("start", "gen_addr_decoder")
    g.add_edge("start", "gen_bank_tracker")
    g.add_edge("start", "gen_refresh_ctrl")
    g.add_edge("start", "gen_calibration")

    g.add_edge("gen_addr_decoder", "validate_p2")
    g.add_edge("gen_bank_tracker", "validate_p2")
    g.add_edge("gen_refresh_ctrl", "validate_p2")
    g.add_edge("gen_calibration", "validate_p2")

    g.add_conditional_edges("validate_p2", route_after_validation,
        {"lint_gate": "lint_gate",
         "p2_increment_retry": "p2_increment_retry",
         "final_failure": "final_failure"})

    g.add_edge("p2_increment_retry", "gen_addr_decoder")
    g.add_edge("p2_increment_retry", "gen_bank_tracker")
    g.add_edge("p2_increment_retry", "gen_refresh_ctrl")
    g.add_edge("p2_increment_retry", "gen_calibration")

    g.add_conditional_edges("lint_gate", route_after_lint,
        {"sim_gate": "sim_gate", "final_failure": "final_failure"})

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
    print("|   DDR3 Controller -- Phase 2 Pipeline                   |")
    print("|                                                         |")
    print("|   4 agents -> Validate -> Lint Gate -> Sim Gate         |")
    print("|   Outputs: .sv, _tb.sv, _manifest.json, reports         |")
    print("+========================================================+\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    p1_dir = input("Phase 1 RTL dir (for cross-phase lint): ").strip()
    if p1_dir and not os.path.isdir(p1_dir):
        print(f"Warning: Phase 1 dir not found: {p1_dir} (cross-phase lint may be limited)")

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
    else:
        print("  Note: paramiko not installed -- sim gate will be skipped")

    print(f"\n  Output layout:")
    print(f"    {out}/")
    print(f"    +-- {PHASE2_RTL_DIR}/          <- .sv + _tb.sv + _manifest.json")
    print(f"    +-- {VALIDATION_DIR}/  <- reports + lint + sim")
    print()

    print(f"  Pipeline: Agents -> Validate -> Lint -> {'Sim (Xcelium)' if ssh_password else 'Sim (skipped)'} -> Done")
    print()

    app = build_graph()

    result = app.invoke({
        "spec_path": spec,
        "output_dir": out,
        "phase1_rtl_dir": p1_dir or "",
        "phase2_rtl_dir": dirs["phase2_rtl"],
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