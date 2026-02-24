#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║        DDR3 MEMORY CONTROLLER — UNIFIED PIPELINE                     ║
║                                                                      ║
║  Flow:                                                               ║
║    Phase 1: 3 agents (parallel) → Validation (94 checks)            ║
║        ↓ retry loop (max 4)                                          ║
║    ✓ Phase 1 PASS                                                    ║
║        ↓                                                             ║
║    Lint Agent: inter-module port consistency (8 checks)              ║
║        ↓                                                             ║
║    Phase 2: 4 agents (parallel) → Validation (99 checks)            ║
║        ↓ retry loop (max 4)                                          ║
║    ✓ Phase 2 PASS → Done                                             ║
║                                                                      ║
║    ✗ Any stage FAIL → Error report                                   ║
║                                                                      ║
║  Usage:  python3 unified_pipeline.py                                 ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import os
import sys
import operator
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime

# ── Import paths ──
from Agents.Phase_1_Agents.wb_port_agent import WishbonePortAgent
from Agents.Phase_1_Agents.config_regs_agent import ConfigRegsAgent
from Agents.Phase_1_Agents.init_fsm_agent import InitFsmAgent
from Agents.Phase_1_Agents.validation_agent import ValidationAgent

from Agents.Phase_2_Agents.addr_decoder_agent import AddrDecoderAgent
from Agents.Phase_2_Agents.bank_tracker_agent import BankTrackerAgent
from Agents.Phase_2_Agents.refresh_ctrl_agent import RefreshCtrlAgent
from Agents.Phase_2_Agents.calibration_agent import CalibrationAgent
from Agents.Phase_2_Agents.phase2_validation_agent import Phase2ValidationAgent
# BASE = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))  # up to Frontend/
# sys.path.insert(0, os.path.join(BASE, "Agents", "Phase_1_Agents"))
# sys.path.insert(0, os.path.join(BASE, "Agents", "Phase_2_Agents"))
# sys.path.insert(0, os.path.join(BASE, "Agents"))  # for lint_agent

from langgraph.graph import StateGraph, END

# # Phase 1 agents
# from wb_port_agent import WishbonePortAgent
# from config_regs_agent import ConfigRegsAgent
# from init_fsm_agent import InitFsmAgent
# from phase1_validation_agent import ValidationAgent

# # Lint agent
from lint_agent import LintAgent

# # Phase 2 agents
# from Phase_2_addr_decoder_agent import AddrDecoderAgent
# from bank_tracker_agent import BankTrackerAgent
# from refresh_ctrl_agent import RefreshCtrlAgent
# from calibration_agent import CalibrationAgent
# from phase2_validation_agent import Phase2ValidationAgent


MAX_RETRIES = 4


# ═════════════════════════════════════════════════════════════
# STATE — unified across both phases
# ═════════════════════════════════════════════════════════════
class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    phase: int                                         # 1 or 2
    modules: Annotated[dict, operator.or_]             # module_name → manifest
    rtl_files: Annotated[dict, operator.or_]           # module_name → sv path
    attempt: int                                       # current attempt (1-based)
    validation_result: dict                            # full validation report
    failed_modules: list                               # which modules failed
    retry_instructions: Annotated[dict, operator.or_]  # module_name → error details
    history: Annotated[list, operator.add]             # log of all attempts
    lint_result: dict                                  # lint report
    pipeline_status: str                               # running / pass / fail


# ═════════════════════════════════════════════════════════════
# PHASE 1 — RTL GENERATION (parallel)
# ═════════════════════════════════════════════════════════════
def gen_wb_port(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("wb_port")
    if instructions:
        print(f"\n  ┌─ [P1 Attempt {attempt}] REGENERATING wb_port")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P1 Attempt {attempt}] Generating wb_port")
    r = WishbonePortAgent(state["spec_path"], state["output_dir"]).run()
    return {"modules": {"wb_port": r["manifest"]}, "rtl_files": {"wb_port": r["rtl_path"]}}


def gen_config_regs(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("config_regs")
    if instructions:
        print(f"\n  ┌─ [P1 Attempt {attempt}] REGENERATING config_regs")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P1 Attempt {attempt}] Generating config_regs")
    r = ConfigRegsAgent(state["spec_path"], state["output_dir"]).run()
    return {"modules": {"config_regs": r["manifest"]}, "rtl_files": {"config_regs": r["rtl_path"]}}


def gen_init_fsm(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("init_fsm")
    if instructions:
        print(f"\n  ┌─ [P1 Attempt {attempt}] REGENERATING init_fsm")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P1 Attempt {attempt}] Generating init_fsm")
    r = InitFsmAgent(state["spec_path"], state["output_dir"]).run()
    return {"modules": {"init_fsm": r["manifest"]}, "rtl_files": {"init_fsm": r["rtl_path"]}}


# ═════════════════════════════════════════════════════════════
# PHASE 1 — VALIDATION
# ═════════════════════════════════════════════════════════════
def validate_p1(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'━' * 62}")
    print(f"  PHASE 1 VALIDATION — Attempt {attempt} of {MAX_RETRIES}")
    print(f"{'━' * 62}")

    va = ValidationAgent(state["spec_path"], state["output_dir"], state["output_dir"],
                         attempt=attempt, max_retries=MAX_RETRIES,
                         history=state.get("history", []))
    result = va.run()

    failed_modules = []
    retry_instructions = {}
    all_failed_checks = []

    for mod_name, mod_result in result["modules"].items():
        if mod_result["status"] != "PASS":
            if mod_name in ("init_fsm", "config_regs", "wb_port"):
                failed_modules.append(mod_name)
                failed_checks = [c for c in mod_result["checks"] if not c["pass"]]
                all_failed_checks.extend(failed_checks)
                retry_instructions[mod_name] = {
                    "module": mod_name, "attempt": attempt,
                    "failed_checks": failed_checks,
                    "message": f"{len(failed_checks)} checks failed — regenerate {mod_name}",
                }

    history_entry = {
        "phase": 1, "attempt": attempt,
        "timestamp": datetime.now().isoformat(),
        "overall": result["overall"]["status"],
        "passed": result["overall"]["total_passed"],
        "total": result["overall"]["total_checks"],
        "failed_modules": failed_modules,
        "failed_checks": all_failed_checks,
    }

    _print_attempt_summary(1, attempt, result, failed_modules, retry_instructions)

    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }


def route_after_p1_validation(state: GraphState) -> Literal["p1_increment_retry", "lint_gate", "final_failure"]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed:
        return "lint_gate"
    elif attempt < MAX_RETRIES:
        return "p1_increment_retry"
    else:
        return "final_failure"


def p1_increment_retry(state: GraphState) -> dict:
    new_attempt = state.get("attempt", 1) + 1
    print(f"\n  ↻ Phase 1: Incrementing to attempt {new_attempt}...")
    return {"attempt": new_attempt}


# ═════════════════════════════════════════════════════════════
# LINT GATE — bridge between Phase 1 and Phase 2
# ═════════════════════════════════════════════════════════════
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'━' * 62}")
    print(f"  LINT AGENT — Inter-Module Port Consistency")
    print(f"{'━' * 62}")

    lint = LintAgent(state["output_dir"], state["output_dir"])
    result = lint.run()

    if result["status"] == "PASS":
        print(f"\n  \033[92m✓ LINT PASSED — proceeding to Phase 2\033[0m")
    else:
        print(f"\n  \033[91m✗ LINT FAILED — {result['summary']['errors']} errors\033[0m")

    return {
        "lint_result": result,
        # Reset attempt counter and retry state for Phase 2
        "attempt": 1,
        "phase": 2,
        "failed_modules": [],
        "retry_instructions": {},
        "validation_result": {},
    }


def route_after_lint(state: GraphState) -> Literal["gen_addr_decoder", "final_failure"]:
    lint = state.get("lint_result", {})
    if lint.get("status") == "PASS":
        return "gen_addr_decoder"  # proceed to Phase 2 (all 4 start in parallel)
    else:
        return "final_failure"


# ═════════════════════════════════════════════════════════════
# PHASE 2 — RTL GENERATION (parallel)
# ═════════════════════════════════════════════════════════════
def gen_addr_decoder(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("addr_decoder")
    if instructions:
        print(f"\n  ┌─ [P2 Attempt {attempt}] REGENERATING addr_decoder")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P2 Attempt {attempt}] Generating addr_decoder")
    r = AddrDecoderAgent(state["spec_path"], state["output_dir"]).run()
    sv_path = str(Path(state["output_dir"]) / "addr_decoder.sv")
    return {"modules": {"addr_decoder": r.get("manifest", {})}, "rtl_files": {"addr_decoder": sv_path}}


def gen_bank_tracker(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("bank_tracker")
    if instructions:
        print(f"\n  ┌─ [P2 Attempt {attempt}] REGENERATING bank_tracker")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P2 Attempt {attempt}] Generating bank_tracker")
    r = BankTrackerAgent(state["spec_path"], state["output_dir"]).run()
    sv_path = str(Path(state["output_dir"]) / "bank_tracker.sv")
    return {"modules": {"bank_tracker": r.get("manifest", {})}, "rtl_files": {"bank_tracker": sv_path}}


def gen_refresh_ctrl(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("refresh_ctrl")
    if instructions:
        print(f"\n  ┌─ [P2 Attempt {attempt}] REGENERATING refresh_ctrl")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P2 Attempt {attempt}] Generating refresh_ctrl")
    r = RefreshCtrlAgent(state["spec_path"], state["output_dir"]).run()
    sv_path = str(Path(state["output_dir"]) / "refresh_ctrl.sv")
    return {"modules": {"refresh_ctrl": r.get("manifest", {})}, "rtl_files": {"refresh_ctrl": sv_path}}


def gen_calibration(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("calibration")
    if instructions:
        print(f"\n  ┌─ [P2 Attempt {attempt}] REGENERATING calibration")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P2 Attempt {attempt}] Generating calibration")
    r = CalibrationAgent(state["spec_path"], state["output_dir"]).run()
    sv_path = str(Path(state["output_dir"]) / "calibration.sv")
    return {"modules": {"calibration": r.get("manifest", {})}, "rtl_files": {"calibration": sv_path}}


# ═════════════════════════════════════════════════════════════
# PHASE 2 — VALIDATION
# ═════════════════════════════════════════════════════════════
PHASE2_RETRYABLE = ("addr_decoder", "bank_tracker", "refresh_ctrl", "calibration")


def validate_p2(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'━' * 62}")
    print(f"  PHASE 2 VALIDATION — Attempt {attempt} of {MAX_RETRIES}")
    print(f"{'━' * 62}")

    va = Phase2ValidationAgent(state["spec_path"], state["output_dir"], state["output_dir"],
                               attempt=attempt, max_retries=MAX_RETRIES,
                               history=[h for h in state.get("history", []) if h.get("phase") == 2])
    result = va.run()

    failed_modules = []
    retry_instructions = {}
    all_failed_checks = []

    for mod_name, mod_result in result["modules"].items():
        if mod_result["status"] != "PASS":
            if mod_name in PHASE2_RETRYABLE:
                failed_modules.append(mod_name)
                failed_checks = [c for c in mod_result["checks"] if not c["pass"]]
                all_failed_checks.extend(failed_checks)
                retry_instructions[mod_name] = {
                    "module": mod_name, "attempt": attempt,
                    "failed_checks": failed_checks,
                    "message": f"{len(failed_checks)} checks failed — regenerate {mod_name}",
                }

    history_entry = {
        "phase": 2, "attempt": attempt,
        "timestamp": datetime.now().isoformat(),
        "overall": result["overall"]["status"],
        "passed": result["overall"]["total_passed"],
        "total": result["overall"]["total_checks"],
        "failed_modules": failed_modules,
        "failed_checks": all_failed_checks,
    }

    _print_attempt_summary(2, attempt, result, failed_modules, retry_instructions)

    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }


def route_after_p2_validation(state: GraphState) -> Literal["p2_increment_retry", "success", "final_failure"]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed:
        return "success"
    elif attempt < MAX_RETRIES:
        return "p2_increment_retry"
    else:
        return "final_failure"


def p2_increment_retry(state: GraphState) -> dict:
    new_attempt = state.get("attempt", 1) + 1
    print(f"\n  ↻ Phase 2: Incrementing to attempt {new_attempt}...")
    return {"attempt": new_attempt}


# ═════════════════════════════════════════════════════════════
# TERMINAL NODES
# ═════════════════════════════════════════════════════════════
def success(state: GraphState) -> dict:
    phase = state.get("phase", 2)
    result = state.get("validation_result", {})
    overall = result.get("overall", {})
    history = state.get("history", [])
    lint = state.get("lint_result", {})

    p1_history = [h for h in history if h.get("phase") == 1]
    p2_history = [h for h in history if h.get("phase") == 2]

    print(f"\n{'═' * 62}")
    print(f"  ✓ UNIFIED PIPELINE — ALL PHASES PASSED")
    print(f"{'═' * 62}")
    print(f"")

    # Phase 1 summary
    if p1_history:
        last_p1 = p1_history[-1]
        print(f"  Phase 1:  {last_p1['passed']}/{last_p1['total']} checks  "
              f"({len(p1_history)} attempt{'s' if len(p1_history) > 1 else ''})")

    # Lint summary
    if lint:
        print(f"  Lint:     {lint.get('summary', {}).get('passed', '?')} passed  "
              f"{lint.get('summary', {}).get('errors', '?')} errors  "
              f"{lint.get('summary', {}).get('warnings', '?')} warnings")

    # Phase 2 summary
    if p2_history:
        last_p2 = p2_history[-1]
        print(f"  Phase 2:  {last_p2['passed']}/{last_p2['total']} checks  "
              f"({len(p2_history)} attempt{'s' if len(p2_history) > 1 else ''})")

    print(f"")
    print(f"  Generated modules:")
    for name, path in sorted(state.get("rtl_files", {}).items()):
        print(f"    ✓ {name}: {path}")

    # Full retry history
    if len(history) > 2:
        print(f"\n  Full retry history:")
        for h in history:
            sym = "✓" if h["overall"] == "PASS" else "✗"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Phase {h['phase']} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) — failed: {fails}")

    # Save final report
    report_path = Path(state["output_dir"]) / "unified_final_report.json"
    report = {
        "status": "PASS",
        "phases_completed": [1, 2],
        "lint_status": lint.get("status"),
        "phase1_attempts": len(p1_history),
        "phase2_attempts": len(p2_history),
        "total_modules": list(state.get("rtl_files", {}).keys()),
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    report_path.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {report_path}")
    print(f"{'═' * 62}")
    return {"pipeline_status": "pass"}


def final_failure(state: GraphState) -> dict:
    phase = state.get("phase", 1)
    result = state.get("validation_result", {})
    failed = state.get("failed_modules", [])
    history = state.get("history", [])
    lint = state.get("lint_result", {})

    print(f"\n{'═' * 62}")
    print(f"  ✗ UNIFIED PIPELINE FAILED")
    print(f"{'═' * 62}")

    # Determine failure stage
    if lint and lint.get("status") == "FAIL":
        print(f"\n  Failed at: LINT GATE")
        print(f"  Lint errors:")
        for e in lint.get("errors", []):
            print(f"    ✗ [{e['check']}] {e['message']}")
    elif failed:
        print(f"\n  Failed at: Phase {phase} (max retries exhausted)")
        print(f"  Unresolved modules: {', '.join(failed)}")
        for mod in failed:
            mod_result = result.get("modules", {}).get(mod, {})
            failed_checks = [c for c in mod_result.get("checks", []) if not c["pass"]]
            print(f"\n  ╔═ {mod} ═══════════════════════════════════")
            for chk in failed_checks:
                print(f"  ║  ✗ [{chk['id']}] {chk['name']}")
                print(f"  ║    Expected: {chk['expected']}")
                print(f"  ║    Actual:   {chk['actual']}")
            print(f"  ╚{'═' * 50}")

    # Full history
    if history:
        print(f"\n  Full retry history:")
        for h in history:
            sym = "✓" if h["overall"] == "PASS" else "✗"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Phase {h['phase']} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) — failed: {fails}")

    print(f"\n  RECOMMENDED ACTIONS:")
    print(f"    1. Check the microarchitecture spec for inconsistencies")
    print(f"    2. Review the failing checks above")
    print(f"    3. Inspect generated .sv files in {state['output_dir']}/")
    print(f"    4. Run individual agents standalone for diagnostics")

    report_path = Path(state["output_dir"]) / "unified_error_report.json"
    report = {
        "status": "FAIL",
        "failed_phase": phase,
        "failed_stage": "lint" if (lint and lint.get("status") == "FAIL") else f"phase{phase}_validation",
        "failed_modules": failed,
        "lint_result": lint,
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    report_path.write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {report_path}")
    print(f"{'═' * 62}")
    return {"pipeline_status": "fail"}


# ═════════════════════════════════════════════════════════════
# HELPER
# ═════════════════════════════════════════════════════════════
def _print_attempt_summary(phase, attempt, result, failed_modules, retry_instructions):
    print(f"\n  ┌─ PHASE {phase} ATTEMPT {attempt} RESULTS:")
    for mod_name, mod_result in result["modules"].items():
        sym = "✓" if mod_result["status"] == "PASS" else "✗"
        print(f"  │  {sym} {mod_name:20s} {mod_result['status']}  "
              f"({mod_result['passed']}/{mod_result['total']})")

    if failed_modules:
        print(f"  │")
        print(f"  │  FAILURES requiring regeneration:")
        for mod in failed_modules:
            instr = retry_instructions[mod]
            print(f"  │    {mod}:")
            for chk in instr["failed_checks"]:
                print(f"  │      ✗ [{chk['id']}] {chk['name']}")
                print(f"  │        expected: {chk['expected']}")
                print(f"  │        actual:   {chk['actual']}")
        if attempt < MAX_RETRIES:
            print(f"  │")
            print(f"  │  → Routing {len(failed_modules)} module(s) back for regeneration")
        else:
            print(f"  │")
            print(f"  │  ✗ MAX RETRIES ({MAX_RETRIES}) EXHAUSTED")

    print(f"  └─{'─' * 50}")


# ═════════════════════════════════════════════════════════════
# BUILD GRAPH
# ═════════════════════════════════════════════════════════════
def build_graph():
    graph = StateGraph(GraphState)

    # ── Phase 1 nodes ──
    graph.add_node("gen_wb_port", gen_wb_port)
    graph.add_node("gen_config_regs", gen_config_regs)
    graph.add_node("gen_init_fsm", gen_init_fsm)
    graph.add_node("validate_p1", validate_p1)
    graph.add_node("p1_increment_retry", p1_increment_retry)

    # ── Lint gate ──
    graph.add_node("lint_gate", lint_gate)

    # ── Phase 2 nodes ──
    graph.add_node("gen_addr_decoder", gen_addr_decoder)
    graph.add_node("gen_bank_tracker", gen_bank_tracker)
    graph.add_node("gen_refresh_ctrl", gen_refresh_ctrl)
    graph.add_node("gen_calibration", gen_calibration)
    graph.add_node("validate_p2", validate_p2)
    graph.add_node("p2_increment_retry", p2_increment_retry)

    # ── Terminal nodes ──
    graph.add_node("success", success)
    graph.add_node("final_failure", final_failure)

    # ════════════════════════════════════════════════════
    # EDGES — Phase 1
    # ════════════════════════════════════════════════════

    # Entry: 3 Phase 1 agents in parallel
    graph.set_entry_point("gen_wb_port")
    graph.set_entry_point("gen_config_regs")
    graph.set_entry_point("gen_init_fsm")

    # All 3 converge into Phase 1 validation
    graph.add_edge("gen_wb_port", "validate_p1")
    graph.add_edge("gen_config_regs", "validate_p1")
    graph.add_edge("gen_init_fsm", "validate_p1")

    # Route after Phase 1 validation
    graph.add_conditional_edges(
        "validate_p1",
        route_after_p1_validation,
        {
            "lint_gate": "lint_gate",
            "p1_increment_retry": "p1_increment_retry",
            "final_failure": "final_failure",
        },
    )

    # Phase 1 retry → back to all 3 generators
    graph.add_edge("p1_increment_retry", "gen_wb_port")
    graph.add_edge("p1_increment_retry", "gen_config_regs")
    graph.add_edge("p1_increment_retry", "gen_init_fsm")

    # ════════════════════════════════════════════════════
    # EDGES — Lint → Phase 2
    # ════════════════════════════════════════════════════

    # Lint gate routes to Phase 2 or failure
    graph.add_conditional_edges(
        "lint_gate",
        route_after_lint,
        {
            "gen_addr_decoder": "gen_addr_decoder",
            "final_failure": "final_failure",
        },
    )

    # After lint passes, all 4 Phase 2 agents run in parallel
    # (lint_gate → gen_addr_decoder is the conditional edge above)
    # We also need lint_gate to fan out to the other 3
    graph.add_edge("lint_gate", "gen_bank_tracker")
    graph.add_edge("lint_gate", "gen_refresh_ctrl")
    graph.add_edge("lint_gate", "gen_calibration")

    # All 4 converge into Phase 2 validation
    graph.add_edge("gen_addr_decoder", "validate_p2")
    graph.add_edge("gen_bank_tracker", "validate_p2")
    graph.add_edge("gen_refresh_ctrl", "validate_p2")
    graph.add_edge("gen_calibration", "validate_p2")

    # Route after Phase 2 validation
    graph.add_conditional_edges(
        "validate_p2",
        route_after_p2_validation,
        {
            "success": "success",
            "p2_increment_retry": "p2_increment_retry",
            "final_failure": "final_failure",
        },
    )

    # Phase 2 retry → back to all 4 generators
    graph.add_edge("p2_increment_retry", "gen_addr_decoder")
    graph.add_edge("p2_increment_retry", "gen_bank_tracker")
    graph.add_edge("p2_increment_retry", "gen_refresh_ctrl")
    graph.add_edge("p2_increment_retry", "gen_calibration")

    # ════════════════════════════════════════════════════
    # Terminal
    # ════════════════════════════════════════════════════
    graph.add_edge("success", END)
    graph.add_edge("final_failure", END)

    return graph.compile()


# ═════════════════════════════════════════════════════════════
# MAIN
# ═════════════════════════════════════════════════════════════
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════╗")
    print("║   DDR3 Controller — Unified Pipeline                     ║")
    print("║                                                          ║")
    print("║   Phase 1 (3 agents) → Lint Gate → Phase 2 (4 agents)   ║")
    print("║   Validation + retry at each phase (max 4 attempts)      ║")
    print("╚══════════════════════════════════════════════════════════╝")
    print()

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    os.makedirs(out, exist_ok=True)

    app = build_graph()

    result = app.invoke({
        "spec_path": spec,
        "output_dir": out,
        "phase": 1,
        "modules": {},
        "rtl_files": {},
        "attempt": 1,
        "validation_result": {},
        "failed_modules": [],
        "retry_instructions": {},
        "history": [],
        "lint_result": {},
        "pipeline_status": "running",
    })