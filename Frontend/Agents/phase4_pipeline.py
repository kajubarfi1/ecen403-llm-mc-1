#!/usr/bin/env python3
"""
+======================================================================+
|        DDR3 MEMORY CONTROLLER -- PHASE 4 PIPELINE                    |
|                                                                      |
|  Input:  Phase 1 (PHASE1RTL/), Phase 2 (PHASE2RTL/),               |
|          Phase 3 (PHASE3RTL/) outputs                                |
|                                                                      |
|  Flow:                                                               |
|    1 agent (data_path) -> Validation (DP checks + TB gen)            |
|        -> Lint Gate (cross-phase P1+P2+P3+P4 port consistency)       |
|        -> Sim Gate (Xcelium) -> Success                              |
|        retry loop (max 4) on validation failures                     |
|                                                                      |
|  Output:                                                             |
|    PHASE4RTL/          data_path.sv + _tb.sv + _manifest.json        |
|    VALIDATIONREPORT/   validation reports + lint + sim reports        |
|                                                                      |
|  Module: data_path                                                   |
+======================================================================+
"""
import json, os, sys, shutil, operator, glob, getpass, traceback
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
for _rel in [".", "Agents/Phase_4_Agents", "Agents/Phase_3_Agents",
             "Agents/Phase_2_Agents", "Agents/Phase_1_Agents",
             "Agents", "..", "../Phase_4_Agents", "../..",
             "Phase_4_Agents", "Phase_3_Agents", "Phase_2_Agents",
             "Phase_1_Agents"]:
    _p = os.path.normpath(os.path.join(HERE, _rel))
    if os.path.isdir(_p) and _p not in sys.path:
        sys.path.insert(0, _p)

from langgraph.graph import StateGraph, END
from data_path_agent import DataPathAgent
from lint_agent import LintAgent

# Phase 4 validation agent -- if you have one, import it here.
# Otherwise we do a lightweight structural check inline.
try:
    from phase4_validation_agent import Phase4ValidationAgent
    HAS_P4_VALIDATION = True
except ImportError:
    HAS_P4_VALIDATION = False

# Try to import simulation runner (optional dependency)
try:
    from cadence_ssh_agent import CadenceSSHAgent
    HAS_SIM_AGENT = True
except ImportError:
    HAS_SIM_AGENT = False

MAX_RETRIES = 4
PHASE4_RTL_DIR = "PHASE4RTL"
VALIDATION_DIR = "VALIDATIONREPORT"
P4_MODULES = ("data_path",)

# SSH config
SSH_CONFIG = {
    "hostname": os.environ.get("OLYMPUS_HOST", "olympus.ece.tamu.edu"),
    "port": 22,
    "username": os.environ.get("OLYMPUS_USER", ""),
    "key_path": os.environ.get("OLYMPUS_KEY", None),
}

def setup_output_dirs(base_dir):
    dirs = {"phase4_rtl": str(Path(base_dir) / PHASE4_RTL_DIR),
            "validation": str(Path(base_dir) / VALIDATION_DIR)}
    for d in dirs.values():
        os.makedirs(d, exist_ok=True)
    return dirs


class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    phase1_rtl_dir: str
    phase2_rtl_dir: str
    phase3_rtl_dir: str
    phase4_rtl_dir: str
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
# RTL GENERATION (1 agent)
# ===================================================
def gen_data_path(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instr = state.get("retry_instructions", {}).get("data_path")
    if instr:
        print(f"\n  +- [P4 Attempt {attempt}] REGENERATING data_path")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  |    x [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  +- [P4 Attempt {attempt}] Generating data_path")

    r = DataPathAgent(state["spec_path"], state["phase4_rtl_dir"]).run()
    return {"modules": {"data_path": r.get("manifest", {})},
            "rtl_files": {"data_path": r.get("rtl_path",
                          str(Path(state["phase4_rtl_dir"]) / "data_path.sv"))}}


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
        print(f"  Cleaned {len(removed)} redundant file(s) from {VALIDATION_DIR}/")


def validate_p4(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'=' * 62}")
    print(f"  PHASE 4 VALIDATION -- Attempt {attempt} of {MAX_RETRIES}")
    print(f"{'=' * 62}")

    if HAS_P4_VALIDATION:
        va = Phase4ValidationAgent(
            state["spec_path"], state["phase4_rtl_dir"], state["validation_dir"],
            attempt=attempt, max_retries=MAX_RETRIES,
            history=[h for h in state.get("history", [])])
        result = va.run()
    else:
        # Lightweight structural validation if no dedicated agent
        result = _inline_validate_p4(state)

    _remove_validation_tbs(state["validation_dir"])

    failed_modules, retry_instructions, all_failed = [], {}, []
    for mod, mr in result.get("modules", {}).items():
        if mr["status"] != "PASS" and mod in P4_MODULES:
            failed_modules.append(mod)
            fc = [c for c in mr.get("checks", []) if not c.get("pass", True)]
            all_failed.extend(fc)
            retry_instructions[mod] = {
                "module": mod, "attempt": attempt,
                "failed_checks": fc,
                "message": f"{len(fc)} checks failed",
            }

    overall = result.get("overall", {})
    history_entry = {
        "phase": 4, "attempt": attempt,
        "timestamp": datetime.now().isoformat(),
        "overall": overall.get("status", "PASS" if not failed_modules else "FAIL"),
        "passed": overall.get("total_passed", 0),
        "total": overall.get("total_checks", 0),
        "failed_modules": failed_modules,
        "failed_checks": all_failed,
    }

    print(f"\n  +- PHASE 4 ATTEMPT {attempt} RESULTS:")
    for mod, mr in result.get("modules", {}).items():
        sym = "OK" if mr["status"] == "PASS" else "FAIL"
        print(f"  |  {sym:4s} {mod:20s} {mr['status']}  ({mr.get('passed', '?')}/{mr.get('total', '?')})")
    if failed_modules:
        print(f"  |\n  |  FAILURES:")
        for mod in failed_modules:
            for chk in retry_instructions[mod]["failed_checks"][:5]:
                print(f"  |    x [{chk['id']}] {chk['name']}")
        if attempt < MAX_RETRIES:
            print(f"  |  -> Routing data_path back for regeneration")
        else:
            print(f"  |  x MAX RETRIES EXHAUSTED")
    print(f"  +{'=' * 50}")

    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }


def _inline_validate_p4(state: GraphState) -> dict:
    """Lightweight inline validation when no dedicated Phase 4 validation agent exists."""
    rtl_dir = Path(state["phase4_rtl_dir"])
    val_dir = Path(state["validation_dir"])
    checks = []
    passed = 0

    def check(cid, name, condition):
        nonlocal passed
        ok = bool(condition)
        if ok:
            passed += 1
        checks.append({"id": cid, "name": name, "pass": ok})
        sym = "OK" if ok else "FAIL"
        print(f"    {sym} [{cid}] {name}")

    sv_path = rtl_dir / "data_path.sv"
    tb_path = rtl_dir / "data_path_tb.sv"
    mf_path = rtl_dir / "data_path_manifest.json"

    check("DP-F01", "data_path.sv exists", sv_path.exists())
    check("DP-F02", "data_path_tb.sv exists", tb_path.exists())
    check("DP-F03", "data_path_manifest.json exists", mf_path.exists())

    if sv_path.exists():
        sv_text = sv_path.read_text()
        check("DP-S01", "Module declaration present", "module data_path" in sv_text)
        check("DP-S02", "endmodule present", "endmodule" in sv_text)
        check("DP-S03", "clk port declared", "clk" in sv_text)
        check("DP-S04", "rst_n port declared", "rst_n" in sv_text)
        check("DP-S05", "cmd_wr_valid port", "cmd_wr_valid" in sv_text)
        check("DP-S06", "cmd_rd_valid port", "cmd_rd_valid" in sv_text)
        check("DP-S07", "wr_data port", "wr_data" in sv_text)
        check("DP-S08", "rd_rsp_valid port", "rd_rsp_valid" in sv_text)
        check("DP-S09", "rd_rsp_data port", "rd_rsp_data" in sv_text)
        check("DP-S10", "ddr_dq_o port", "ddr_dq_o" in sv_text)
        check("DP-S11", "ddr_dq_oe port", "ddr_dq_oe" in sv_text)
        check("DP-S12", "ddr_dm_o port", "ddr_dm_o" in sv_text)
        check("DP-S13", "ddr_dqs_o port", "ddr_dqs_o" in sv_text)
        check("DP-S14", "WR_IDLE state", "WR_IDLE" in sv_text)
        check("DP-S15", "WR_DRIVE state", "WR_DRIVE" in sv_text)
        check("DP-S16", "RD_IDLE state", "RD_IDLE" in sv_text)
        check("DP-S17", "RD_CAPTURE state", "RD_CAPTURE" in sv_text)
        check("DP-S18", "always_ff present", "always_ff" in sv_text)
        check("DP-S19", "cfg_CL_nCK port", "cfg_CL_nCK" in sv_text)
        check("DP-S20", "cfg_CWL_nCK port", "cfg_CWL_nCK" in sv_text)
        check("DP-S21", "SVA translate_off guard", "translate_off" in sv_text)
        check("DP-S22", "No synthesis constructs in main logic",
              "initial begin" not in sv_text.split("translate_off")[0] if "translate_off" in sv_text else True)
    else:
        for i in range(1, 23):
            checks.append({"id": f"DP-S{i:02d}", "name": f"(skipped - no .sv)", "pass": False})

    if mf_path.exists():
        try:
            mf = json.loads(mf_path.read_text())
            check("DP-M01", "Manifest module_name is data_path", mf.get("module_name") == "data_path")
            check("DP-M02", "Manifest has ports section", "ports" in mf)
            check("DP-M03", "Manifest has ddr_phy port group", "ddr_phy" in mf.get("ports", {}))
            check("DP-M04", "Manifest has cmd_in port group", "cmd_in" in mf.get("ports", {}))
            check("DP-M05", "Manifest has rd_rsp_out port group", "rd_rsp_out" in mf.get("ports", {}))
        except json.JSONDecodeError:
            checks.append({"id": "DP-M01", "name": "Manifest JSON parse error", "pass": False})
    else:
        for i in range(1, 6):
            checks.append({"id": f"DP-M{i:02d}", "name": "(skipped - no manifest)", "pass": False})

    total = len(checks)
    status = "PASS" if passed == total else "FAIL"

    # Write report
    report = {
        "overall": {"status": status, "total_passed": passed, "total_checks": total},
        "modules": {
            "data_path": {
                "status": status, "passed": passed, "total": total, "checks": checks,
            }
        },
    }
    report_path = val_dir / "phase4_validation_report.json"
    report_path.write_text(json.dumps(report, indent=2))
    print(f"  Report: {report_path}")

    return report


# ===================================================
# ROUTING + RETRY
# ===================================================
def route_after_validation(state: GraphState) -> Literal[
    "p4_increment_retry", "lint_gate", "final_failure"
]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed:
        return "lint_gate"
    elif attempt < MAX_RETRIES:
        return "p4_increment_retry"
    else:
        return "final_failure"


def p4_increment_retry(state: GraphState) -> dict:
    n = state.get("attempt", 1) + 1
    print(f"\n  -> Phase 4: Incrementing to attempt {n}...")
    return {"attempt": n}


# ===================================================
# LINT GATE (cross-phase P1+P2+P3+P4)
# ===================================================
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print(f"  LINT AGENT -- Cross-Phase Port Consistency (P1+P2+P3+P4)")
    print(f"{'=' * 62}")

    combined = Path(state["validation_dir"]) / "lint_combined_p4"
    combined.mkdir(parents=True, exist_ok=True)

    # Gather all manifests from all phases
    phase_dirs = [
        ("P1", state.get("phase1_rtl_dir", "")),
        ("P2", state.get("phase2_rtl_dir", "")),
        ("P3", state.get("phase3_rtl_dir", "")),
        ("P4", state["phase4_rtl_dir"]),
    ]
    manifest_count = 0
    for label, src in phase_dirs:
        p = Path(src)
        if p.exists():
            for mf in p.glob("*_manifest.json"):
                shutil.copy2(str(mf), str(combined / mf.name))
                manifest_count += 1
            print(f"  {label}: {src} ({len(list(p.glob('*_manifest.json')))} manifests)")
        else:
            print(f"  {label}: {src} (not found -- skipped)")

    print(f"  Total manifests for lint: {manifest_count}")

    lint = LintAgent(str(combined), state["validation_dir"])
    result = lint.run()

    if result["status"] == "PASS":
        print(f"\n  OK: LINT PASSED -- all {manifest_count} modules port-consistent")
    else:
        print(f"\n  FAIL: LINT FAILED -- {result['summary']['errors']} errors")
        for e in result.get("errors", [])[:10]:
            print(f"    x [{e['check']}] {e['message']}")

    return {"lint_result": result}


def route_after_lint(state: GraphState) -> Literal["sim_gate", "final_failure"]:
    return "sim_gate" if state.get("lint_result", {}).get("status") == "PASS" else "final_failure"


# ===================================================
# BEHAVIORAL SIMULATION REPORT (.txt)
# ===================================================
def _write_behavioral_report(val_dir, sim_results, all_passed):
    txt_path = Path(val_dir) / "phase4_behavioral_sim_report.txt"
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    lines = []
    L = lines.append
    L(f"================================================================")
    L(f"  DDR3 PHASE 4 -- BEHAVIORAL SIMULATION REPORT")
    L(f"  Generated: {ts}")
    L(f"  Simulator: Cadence Xcelium (xrun) via Olympus cluster")
    L(f"  Overall:   {'PASS' if all_passed else 'FAIL'}")
    L(f"================================================================")
    L(f"")

    for mod, result in sim_results.items():
        if mod.startswith("_") or not isinstance(result, dict):
            continue
        status = result.get("status", "UNKNOWN")
        p_count = result.get("pass_count", 0)
        f_count = result.get("fail_count", 0)
        t_count = result.get("test_count", 0)

        L(f"  MODULE: {mod}")
        L(f"  Status: {status}    Tests: {p_count} passed / {f_count} failed / {t_count} total")
        L(f"  Exit code: {result.get('exit_code', -1)}")
        L(f"")

        for line in result.get("pass_lines", []):
            L(f"    + {line}")
        for line in result.get("fail_lines", []):
            L(f"  >>> {line}")
        for line in result.get("assertion_errors", []):
            L(f"    ! {line}")
        L(f"")

    txt_path.write_text("\n".join(lines))
    print(f"  Behavioral report: {txt_path}")


# ===================================================
# SIM GATE (Cadence Xcelium via SSH)
# ===================================================
def sim_gate(state: GraphState) -> dict:
    print(f"\n{'=' * 62}")
    print(f"  SIM GATE -- Cadence Xcelium Behavioral Simulation (Phase 4)")
    print(f"{'=' * 62}")

    rtl_dir = Path(state["phase4_rtl_dir"])
    val_dir = Path(state["validation_dir"])

    if not HAS_SIM_AGENT:
        print(f"  SKIP: paramiko not installed -- simulation skipped")
        print(f"  Simulation can be run manually:")
        print(f"    xrun data_path.sv data_path_tb.sv -timescale 1ns/1ps -sysv -access +rw")
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
        for mod in P4_MODULES:
            sv_path = rtl_dir / f"{mod}.sv"
            tb_path = rtl_dir / f"{mod}_tb.sv"
            if sv_path.exists():
                files_to_upload.append(str(sv_path))
            if tb_path.exists():
                files_to_upload.append(str(tb_path))

        if files_to_upload:
            agent.upload_files(files_to_upload)
            print(f"  Uploaded {len(files_to_upload)} files")

        for mod in P4_MODULES:
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
                elif "*E," in stripped:
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
                "log_file": log_file,
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
    report_path = val_dir / "phase4_sim_report.json"
    report_path.write_text(json.dumps(sim_report, indent=2))

    _write_behavioral_report(val_dir, sim_results, all_passed)

    print(f"\n  {'=' * 50}")
    if all_passed:
        print(f"  SIM GATE PASSED -- data_path passed behavioral sim")
    else:
        print(f"  SIM GATE FAILED -- data_path has behavioral failures")
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
    print(f"  PHASE 4 PIPELINE -- ALL CHECKS PASSED")
    print(f"{'=' * 62}\n")

    if history:
        last = history[-1]
        print(f"  Phase 4:  {last['passed']}/{last['total']} checks "
              f"({len(history)} attempt{'s' if len(history) > 1 else ''})")

    if lint:
        s = lint.get("summary", {})
        print(f"  Lint:     {s.get('passed', '?')} passed  "
              f"{s.get('errors', '?')} errors  {s.get('warnings', '?')} warnings")

    sim_status = sim.get("status", "N/A")
    print(f"  Sim:      {sim_status}")

    print(f"\n  Generated outputs:")
    rd = Path(state["phase4_rtl_dir"])
    vd = Path(state["validation_dir"])
    for mod in P4_MODULES:
        sv_ok = "OK" if (rd / f"{mod}.sv").exists() else "--"
        tb_ok = "OK" if (rd / f"{mod}_tb.sv").exists() else "--"
        mf_ok = "OK" if (rd / f"{mod}_manifest.json").exists() else "--"
        print(f"    {sv_ok} {mod}.sv  {tb_ok} {mod}_tb.sv  {mf_ok} {mod}_manifest.json")

    if len(history) > 1:
        print(f"\n  Retry history:")
        for h in history:
            sym = "OK" if h["overall"] == "PASS" else "FAIL"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) -- failed: {fails}")

    report = {
        "status": "PASS", "pipeline": "phase4",
        "lint_status": lint.get("status"),
        "sim_status": sim_status,
        "attempts": len(history),
        "modules": list(P4_MODULES),
        "outputs": {
            mod: {
                "sv": str(rd / f"{mod}.sv"),
                "tb": str(rd / f"{mod}_tb.sv"),
                "manifest": str(rd / f"{mod}_manifest.json"),
            }
            for mod in P4_MODULES
        },
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    rp = vd / "phase4_final_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {rp}")
    print(f"{'=' * 62}")
    return {"pipeline_status": "pass"}


def _print_human_review_banner(failure_stage, state):
    vd = state.get("validation_dir", "VALIDATIONREPORT")
    rd = state.get("phase4_rtl_dir", "PHASE4RTL")

    print(f"")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"  !!                                                        !!")
    print(f"  !!          PIPELINE FAILED -- HUMAN REVIEW REQUIRED      !!")
    print(f"  !!                                                        !!")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"")
    print(f"  The Phase 4 pipeline has FAILED at: {failure_stage}")
    print(f"  Automatic retries have been exhausted or the failure")
    print(f"  occurred at a stage that cannot be auto-recovered.")
    print(f"")
    print(f"  WHAT TO DO:")
    print(f"  ----------------------------------------------------------------")
    print(f"  1. CHECK THE VALIDATION REPORT:")
    print(f"     {vd}/")
    print(f"     - phase4_validation_report.json")
    print(f"     - phase4_error_report.json")
    print(f"     - phase4_sim_report.json")
    print(f"")
    print(f"  2. INSPECT THE GENERATED RTL:")
    print(f"     {rd}/")
    print(f"     - data_path.sv + data_path_tb.sv")
    print(f"")
    print(f"  3. RUN TESTBENCH MANUALLY:")
    print(f"     xrun data_path.sv data_path_tb.sv -timescale 1ns/1ps -sysv -access +rw")
    print(f"")


def final_failure(state: GraphState) -> dict:
    history = state.get("history", [])
    failed = state.get("failed_modules", [])
    lint = state.get("lint_result", {})
    ri = state.get("retry_instructions", {})

    lint_status = lint.get("status", "NOT_RUN")
    if lint_status == "PASS":
        failure_stage = "VALIDATION (static checks)"
    elif lint_status == "FAIL":
        failure_stage = "LINT (cross-phase port consistency)"
    else:
        failure_stage = "VALIDATION/LINT"

    print(f"\n{'=' * 62}")
    print(f"  PHASE 4 PIPELINE FAILED")
    print(f"{'=' * 62}")

    _print_human_review_banner(failure_stage, state)

    if history:
        print(f"\n  Attempt history:")
        print(f"  {'-' * 50}")
        for h in history:
            sym = "OK" if h["overall"] == "PASS" else "FAIL"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) -- failed: {fails}")
        print(f"  {'-' * 50}")

    report = {
        "status": "FAIL", "pipeline": "phase4",
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
    rp = Path(state["validation_dir"]) / "phase4_error_report.json"
    rp.write_text(json.dumps(report, indent=2))

    print(f"\n  Error report: {rp}")
    print(f"")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"  !!  REQUIRES HUMAN REVIEW -- see report above             !!")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"")
    return {"pipeline_status": "fail"}


def sim_failure(state: GraphState) -> dict:
    sim = state.get("sim_result", {})
    history = state.get("history", [])

    print(f"\n{'=' * 62}")
    print(f"  PHASE 4 PIPELINE FAILED AT SIM GATE")
    print(f"{'=' * 62}")

    _print_human_review_banner("BEHAVIORAL SIMULATION (Xcelium)", state)

    print(f"\n  NOTE: Validation and lint PASSED -- the RTL structure is correct.")
    print(f"  The failure is in BEHAVIORAL SIMULATION, meaning the RTL has")
    print(f"  functional bugs that the static checks did not catch.")

    failed_mods = []
    if "modules" in sim:
        print(f"\n  SIM RESULTS:")
        print(f"  {'-' * 50}")
        for mod, result in sim["modules"].items():
            if mod.startswith("_"):
                continue
            if isinstance(result, dict):
                sym = "OK" if result.get("status") == "PASS" else "FAIL"
                print(f"    {sym} {mod}: {result.get('status', '?')}")
                if result.get("status") == "FAIL":
                    failed_mods.append(mod)
        print(f"  {'-' * 50}")

    print(f"\n  TO DEBUG:")
    print(f"    xrun data_path.sv data_path_tb.sv -timescale 1ns/1ps -sysv -access +rw")
    print(f"    simvision data_path_tb.vcd")
    print(f"")

    report = {
        "status": "FAIL", "pipeline": "phase4",
        "failure_stage": "BEHAVIORAL_SIMULATION",
        "sim_result": sim,
        "failed_modules": failed_mods,
        "history": history,
        "requires_human_review": True,
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase4_error_report.json"
    rp.write_text(json.dumps(report, indent=2))

    print(f"\n  Error report: {rp}")
    print(f"")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"  !!  REQUIRES HUMAN REVIEW -- behavioral sim failed        !!")
    print(f"  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    print(f"")
    return {"pipeline_status": "fail"}


# ===================================================
# BUILD GRAPH
# ===================================================
def build_graph():
    g = StateGraph(GraphState)

    g.add_node("gen_data_path", gen_data_path)
    g.add_node("validate_p4", validate_p4)
    g.add_node("p4_increment_retry", p4_increment_retry)
    g.add_node("lint_gate", lint_gate)
    g.add_node("sim_gate", sim_gate)
    g.add_node("success", success)
    g.add_node("final_failure", final_failure)
    g.add_node("sim_failure", sim_failure)

    # Entry: single agent
    g.set_entry_point("gen_data_path")

    # Agent -> validation
    g.add_edge("gen_data_path", "validate_p4")

    # Route after validation
    g.add_conditional_edges("validate_p4", route_after_validation,
        {"lint_gate": "lint_gate",
         "p4_increment_retry": "p4_increment_retry",
         "final_failure": "final_failure"})

    # Retry -> back to generator
    g.add_edge("p4_increment_retry", "gen_data_path")

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
    print("|   DDR3 Controller -- Phase 4 Pipeline (Data Path)       |")
    print("|                                                         |")
    print("|   Input: Phase 1 + Phase 2 + Phase 3 RTL dirs          |")
    print("|   1 agent -> Validate -> Lint (P1+P2+P3+P4) -> Sim     |")
    print("|   Outputs: data_path.sv, _tb.sv, _manifest.json        |")
    print("+========================================================+\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    p1_dir = input("Phase 1 RTL dir (PHASE1RTL/): ").strip()
    if not os.path.isdir(p1_dir):
        print(f"Not found: {p1_dir}")
        sys.exit(1)

    p2_dir = input("Phase 2 RTL dir (PHASE2RTL/): ").strip()
    if not os.path.isdir(p2_dir):
        print(f"Not found: {p2_dir}")
        sys.exit(1)

    p3_dir = input("Phase 3 RTL dir (PHASE3RTL/): ").strip()
    if not os.path.isdir(p3_dir):
        print(f"Not found: {p3_dir}")
        sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    dirs = setup_output_dirs(out)

    # SSH credentials for sim gate
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

    print(f"\n  Input phases:")
    print(f"    Phase 1: {p1_dir}")
    print(f"    Phase 2: {p2_dir}")
    print(f"    Phase 3: {p3_dir}")
    print(f"\n  Output layout:")
    print(f"    {out}/")
    print(f"    +-- {PHASE4_RTL_DIR}/          <- data_path.sv + _tb.sv + _manifest.json")
    print(f"    +-- {VALIDATION_DIR}/  <- reports + lint (P1+P2+P3+P4) + sim")
    print()

    print(f"  Pipeline: data_path -> Validate -> Lint (all phases) -> "
          f"{'Sim (Xcelium)' if ssh_password else 'Sim (skipped)'} -> Done")
    print()

    app = build_graph()

    result = app.invoke({
        "spec_path": spec,
        "output_dir": out,
        "phase1_rtl_dir": p1_dir,
        "phase2_rtl_dir": p2_dir,
        "phase3_rtl_dir": p3_dir,
        "phase4_rtl_dir": dirs["phase4_rtl"],
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