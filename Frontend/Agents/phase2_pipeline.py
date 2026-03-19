#!/usr/bin/env python3
"""
DDR3 MEMORY CONTROLLER — PHASE 2 PIPELINE

Input:  Phase 1 output dir (contains .sv + _manifest.json)

Flow:
  4 agents (parallel) → Validation (99 checks) → Lint Gate
  retry loop (max 4 attempts)

Output:
  PHASE2RTL/         .sv + _manifest.json per module
  VALIDATIONREPORT/  validation + lint reports

Place this file at Frontend/ alongside your Agents/ directory.
"""

import json, os, sys, shutil, operator
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

MAX_RETRIES = 4
PHASE2_RTL_DIR = "PHASE2RTL"
VALIDATION_DIR = "VALIDATIONREPORT"

def setup_output_dirs(base_dir):
    dirs = {"phase2_rtl": str(Path(base_dir)/PHASE2_RTL_DIR),
            "validation": str(Path(base_dir)/VALIDATION_DIR)}
    for d in dirs.values(): os.makedirs(d, exist_ok=True)
    return dirs

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
    retry_instructions: Annotated[dict, operator.or_]
    history: Annotated[list, operator.add]
    lint_result: dict
    pipeline_status: str

P2_RETRYABLE = ("addr_decoder", "bank_tracker", "refresh_ctrl", "calibration")

# ═══════════════════════════════════════════
# RTL GENERATION (4 agents, parallel)
# ═══════════════════════════════════════════
def _log_gen(mod, attempt, instr):
    if instr:
        print(f"\n  ┌─ [P2 Attempt {attempt}] REGENERATING {mod}")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P2 Attempt {attempt}] Generating {mod}")

def gen_addr_decoder(state: GraphState) -> dict:
    _log_gen("addr_decoder", state.get("attempt",1), state.get("retry_instructions",{}).get("addr_decoder"))
    r = AddrDecoderAgent(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"addr_decoder": r.get("manifest",{})},
            "rtl_files": {"addr_decoder": str(Path(state["phase2_rtl_dir"])/"addr_decoder.sv")}}

def gen_bank_tracker(state: GraphState) -> dict:
    _log_gen("bank_tracker", state.get("attempt",1), state.get("retry_instructions",{}).get("bank_tracker"))
    r = BankTrackerAgent(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"bank_tracker": r.get("manifest",{})},
            "rtl_files": {"bank_tracker": str(Path(state["phase2_rtl_dir"])/"bank_tracker.sv")}}

def gen_refresh_ctrl(state: GraphState) -> dict:
    _log_gen("refresh_ctrl", state.get("attempt",1), state.get("retry_instructions",{}).get("refresh_ctrl"))
    r = RefreshCtrlAgent(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"refresh_ctrl": r.get("manifest",{})},
            "rtl_files": {"refresh_ctrl": str(Path(state["phase2_rtl_dir"])/"refresh_ctrl.sv")}}

def gen_calibration(state: GraphState) -> dict:
    _log_gen("calibration", state.get("attempt",1), state.get("retry_instructions",{}).get("calibration"))
    r = CalibrationAgent(state["spec_path"], state["phase2_rtl_dir"]).run()
    return {"modules": {"calibration": r.get("manifest",{})},
            "rtl_files": {"calibration": str(Path(state["phase2_rtl_dir"])/"calibration.sv")}}

# ═══════════════════════════════════════════
# VALIDATION (99 static checks)
# ═══════════════════════════════════════════
def validate_p2(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'━'*62}\n  PHASE 2 VALIDATION — Attempt {attempt} of {MAX_RETRIES}\n{'━'*62}")
    va = Phase2ValidationAgent(state["spec_path"], state["phase2_rtl_dir"], state["validation_dir"],
                               attempt=attempt, max_retries=MAX_RETRIES,
                               history=[h for h in state.get("history",[])])
    result = va.run()

    failed_modules, retry_instructions, all_failed = [], {}, []
    for mod, mr in result["modules"].items():
        if mr["status"] != "PASS" and mod in P2_RETRYABLE:
            failed_modules.append(mod)
            fc = [c for c in mr["checks"] if not c["pass"]]
            all_failed.extend(fc)
            retry_instructions[mod] = {"module": mod, "attempt": attempt, "failed_checks": fc,
                                       "message": f"{len(fc)} checks failed"}

    history_entry = {"phase": 2, "attempt": attempt, "timestamp": datetime.now().isoformat(),
                     "overall": result["overall"]["status"],
                     "passed": result["overall"]["total_passed"],
                     "total": result["overall"]["total_checks"],
                     "failed_modules": failed_modules, "failed_checks": all_failed}

    # Print summary
    print(f"\n  ┌─ PHASE 2 ATTEMPT {attempt} RESULTS:")
    for mod, mr in result["modules"].items():
        sym = "✓" if mr["status"]=="PASS" else "✗"
        print(f"  │  {sym} {mod:20s} {mr['status']}  ({mr['passed']}/{mr['total']})")
    if failed_modules:
        print(f"  │\n  │  FAILURES:")
        for mod in failed_modules:
            for chk in retry_instructions[mod]["failed_checks"][:5]:
                print(f"  │    ✗ [{chk['id']}] {chk['name']}")
        if attempt < MAX_RETRIES:
            print(f"  │  → Routing {len(failed_modules)} module(s) back")
        else:
            print(f"  │  ✗ MAX RETRIES EXHAUSTED")
    print(f"  └─{'─'*50}")

    return {"validation_result": result, "failed_modules": failed_modules,
            "retry_instructions": retry_instructions, "history": [history_entry]}

# ═══════════════════════════════════════════
# ROUTING
# ═══════════════════════════════════════════
def route_after_validation(state: GraphState) -> Literal["p2_increment_retry","lint_gate","final_failure"]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed: return "lint_gate"
    elif attempt < MAX_RETRIES: return "p2_increment_retry"
    else: return "final_failure"

def p2_increment_retry(state: GraphState) -> dict:
    n = state.get("attempt",1) + 1
    print(f"\n  ↻ Phase 2: Incrementing to attempt {n}...")
    return {"attempt": n}

# ═══════════════════════════════════════════
# LINT GATE
# ═══════════════════════════════════════════
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'━'*62}\n  LINT AGENT — Cross-Phase Port Consistency\n{'━'*62}")
    combined = Path(state["validation_dir"]) / "lint_combined"
    combined.mkdir(parents=True, exist_ok=True)
    for src in [state["phase1_rtl_dir"], state["phase2_rtl_dir"]]:
        p = Path(src)
        if p.exists():
            for mf in p.glob("*_manifest.json"):
                shutil.copy2(str(mf), str(combined/mf.name))
    result = LintAgent(str(combined), state["validation_dir"]).run()
    if result["status"]=="PASS": print(f"\n  \033[92m✓ LINT PASSED\033[0m")
    else: print(f"\n  \033[91m✗ LINT FAILED — {result['summary']['errors']} errors\033[0m")
    return {"lint_result": result}

def route_after_lint(state: GraphState) -> Literal["success","final_failure"]:
    return "success" if state.get("lint_result",{}).get("status")=="PASS" else "final_failure"

# ═══════════════════════════════════════════
# TERMINAL
# ═══════════════════════════════════════════
def success(state: GraphState) -> dict:
    history = state.get("history",[])
    lint = state.get("lint_result",{})
    print(f"\n{'═'*62}\n  ✓ PHASE 2 PIPELINE — ALL CHECKS PASSED\n{'═'*62}\n")
    if history:
        last = history[-1]
        print(f"  Validation: {last['passed']}/{last['total']} ({len(history)} attempts)")
    if lint:
        s = lint.get("summary",{})
        print(f"  Lint:       {s.get('passed','?')} passed  {s.get('errors','?')} errors")
    print(f"\n  Generated RTL:")
    for n,p in sorted(state.get("rtl_files",{}).items()): print(f"    ✓ {n}: {p}")
    rpt = Path(state["validation_dir"])/"phase2_final_report.json"
    rpt.write_text(json.dumps({"status":"PASS","modules":list(P2_RETRYABLE),
                                "history":history,"timestamp":datetime.now().isoformat()},indent=2))
    print(f"\n  Report: {rpt}\n{'═'*62}")
    return {"pipeline_status": "pass"}

def final_failure(state: GraphState) -> dict:
    failed = state.get("failed_modules",[])
    lint = state.get("lint_result",{})
    result = state.get("validation_result",{})
    print(f"\n{'═'*62}\n  ✗ PHASE 2 PIPELINE FAILED\n{'═'*62}")
    if lint and lint.get("status")=="FAIL":
        print(f"\n  Failed at: LINT GATE")
        for e in lint.get("errors",[]): print(f"    ✗ [{e['check']}] {e['message']}")
    elif failed:
        print(f"\n  Failed at: Validation (max retries)")
        for mod in failed:
            mr = result.get("modules",{}).get(mod,{})
            for c in [x for x in mr.get("checks",[]) if not x["pass"]][:5]:
                print(f"    ✗ [{c['id']}] {c['name']}")
    rpt = Path(state["validation_dir"])/"phase2_error_report.json"
    rpt.write_text(json.dumps({"status":"FAIL","failed":failed,"timestamp":datetime.now().isoformat()},indent=2))
    print(f"\n  Error report: {rpt}\n{'═'*62}")
    return {"pipeline_status": "fail"}

# ═══════════════════════════════════════════
# BUILD GRAPH
# ═══════════════════════════════════════════
def build_graph():
    g = StateGraph(GraphState)
    g.add_node("gen_addr_decoder", gen_addr_decoder)
    g.add_node("gen_bank_tracker", gen_bank_tracker)
    g.add_node("gen_refresh_ctrl", gen_refresh_ctrl)
    g.add_node("gen_calibration", gen_calibration)
    g.add_node("validate_p2", validate_p2)
    g.add_node("p2_increment_retry", p2_increment_retry)
    g.add_node("lint_gate", lint_gate)
    g.add_node("success", success)
    g.add_node("final_failure", final_failure)

    # Entry: 4 parallel
    g.set_entry_point("gen_addr_decoder")
    g.set_entry_point("gen_bank_tracker")
    g.set_entry_point("gen_refresh_ctrl")
    g.set_entry_point("gen_calibration")

    # Converge → validation
    g.add_edge("gen_addr_decoder", "validate_p2")
    g.add_edge("gen_bank_tracker", "validate_p2")
    g.add_edge("gen_refresh_ctrl", "validate_p2")
    g.add_edge("gen_calibration", "validate_p2")

    # Route
    g.add_conditional_edges("validate_p2", route_after_validation,
        {"lint_gate":"lint_gate","p2_increment_retry":"p2_increment_retry","final_failure":"final_failure"})

    # Retry → generators
    g.add_edge("p2_increment_retry", "gen_addr_decoder")
    g.add_edge("p2_increment_retry", "gen_bank_tracker")
    g.add_edge("p2_increment_retry", "gen_refresh_ctrl")
    g.add_edge("p2_increment_retry", "gen_calibration")

    # Lint → terminal
    g.add_conditional_edges("lint_gate", route_after_lint,
        {"success":"success","final_failure":"final_failure"})

    g.add_edge("success", END)
    g.add_edge("final_failure", END)
    return g.compile()

# ═══════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════╗")
    print("║   DDR3 Controller — Phase 2 Pipeline                     ║")
    print("║   4 agents → Validate → Lint Gate → retry (max 4)        ║")
    print("╚══════════════════════════════════════════════════════════╝\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec): print(f"Not found: {spec}"); sys.exit(1)

    p1_dir = input("Phase 1 RTL dir: ").strip()
    if not os.path.isdir(p1_dir): print(f"Not found: {p1_dir}"); sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    dirs = setup_output_dirs(out)

    print(f"\n  Phase 1 input: {p1_dir}")
    print(f"  Output: {out}/{PHASE2_RTL_DIR}/ + {out}/{VALIDATION_DIR}/\n")

    app = build_graph()
    result = app.invoke({
        "spec_path": spec, "output_dir": out,
        "phase1_rtl_dir": p1_dir,
        "phase2_rtl_dir": dirs["phase2_rtl"],
        "validation_dir": dirs["validation"],
        "modules": {}, "rtl_files": {},
        "attempt": 1, "validation_result": {},
        "failed_modules": [], "retry_instructions": {},
        "history": [], "lint_result": {},
        "pipeline_status": "running",
    })
    sys.exit(0 if result.get("pipeline_status")=="pass" else 1)