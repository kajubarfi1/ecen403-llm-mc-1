#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║        DDR3 MEMORY CONTROLLER — LANGGRAPH PIPELINE                   ║
║                                                                      ║
║  Flow:                                                               ║
║    3 Phase 1 agents (parallel)                                       ║
║        ↓                                                             ║
║    Validation (94 checks: timing, RTL, JEDEC, clocking)             ║
║        ↓                                                             ║
║    ✓ PASS → Done                                                     ║
║    ✗ FAIL → Route failures back to RTL agents (max 4 retries)       ║
║    ✗ FAIL after 4 → Error report with what failed                   ║
║                                                                      ║
║  Requirements: pip install langgraph                                 ║
║  Usage:        python3 langgraph_pipeline.py                         ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import os
import sys
import operator
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime

# Add agents folder to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "Agents", "Phase_1_Agents"))

from langgraph.graph import StateGraph, END
from bad_wb_port_agent import WishbonePortAgent  # BAD FOR TESTING
from bad_config_regs_agent import ConfigRegsAgent  # BAD FOR TESTING
from bad_init_fsm_agent import InitFsmAgent  # BAD FOR TESTING
from validation_agent import ValidationAgent


MAX_RETRIES = 4


# ═════════════════════════════════════════════════════════════
# STATE
# ═════════════════════════════════════════════════════════════
class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    modules: Annotated[dict, operator.or_]       # module_name → manifest
    rtl_files: Annotated[dict, operator.or_]      # module_name → sv path
    attempt: int                                   # current attempt (1-based)
    validation_result: dict                        # full validation report
    failed_modules: list                           # which modules failed
    retry_instructions: Annotated[dict, operator.or_]  # module_name → error details
    history: Annotated[list, operator.add]         # log of all attempts


# ═════════════════════════════════════════════════════════════
# PHASE 1 — RTL GENERATION (parallel)
# Each agent checks retry_instructions for fix guidance
# ═════════════════════════════════════════════════════════════
def gen_wb_port(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("wb_port")

    if instructions:
        print(f"\n  ┌─ [Attempt {attempt}] REGENERATING wb_port")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}: expected {chk['expected']}, got {chk['actual']}")
    else:
        print(f"\n  ┌─ [Attempt {attempt}] Generating wb_port")

    r = WishbonePortAgent(state["spec_path"], state["output_dir"]).run()
    return {
        "modules": {"wb_port": r["manifest"]},
        "rtl_files": {"wb_port": r["rtl_path"]},
    }


def gen_config_regs(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("config_regs")

    if instructions:
        print(f"\n  ┌─ [Attempt {attempt}] REGENERATING config_regs")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}: expected {chk['expected']}, got {chk['actual']}")
    else:
        print(f"\n  ┌─ [Attempt {attempt}] Generating config_regs")

    r = ConfigRegsAgent(state["spec_path"], state["output_dir"]).run()
    return {
        "modules": {"config_regs": r["manifest"]},
        "rtl_files": {"config_regs": r["rtl_path"]},
    }


def gen_init_fsm(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instructions = state.get("retry_instructions", {}).get("init_fsm")

    if instructions:
        print(f"\n  ┌─ [Attempt {attempt}] REGENERATING init_fsm")
        print(f"  │  Fix needed: {len(instructions['failed_checks'])} checks failed")
        for chk in instructions["failed_checks"]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}: expected {chk['expected']}, got {chk['actual']}")
    else:
        print(f"\n  ┌─ [Attempt {attempt}] Generating init_fsm")

    r = InitFsmAgent(state["spec_path"], state["output_dir"]).run()
    return {
        "modules": {"init_fsm": r["manifest"]},
        "rtl_files": {"init_fsm": r["rtl_path"]},
    }


# ═════════════════════════════════════════════════════════════
# VALIDATION NODE
# ═════════════════════════════════════════════════════════════
def validate(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)

    print(f"\n{'━' * 62}")
    print(f"  VALIDATION — Attempt {attempt} of {MAX_RETRIES}")
    print(f"{'━' * 62}")

    va = ValidationAgent(state["spec_path"], state["output_dir"], state["output_dir"],
                         attempt=attempt, max_retries=MAX_RETRIES,
                         history=state.get("history", []))
    result = va.run()

    # Identify which modules failed
    failed_modules = []
    retry_instructions = {}
    all_failed_checks = []  # for history

    for mod_name, mod_result in result["modules"].items():
        if mod_result["status"] != "PASS":
            # Only retry RTL modules, not clocking (clocking is spec-level)
            if mod_name in ("init_fsm", "config_regs", "wb_port"):
                failed_modules.append(mod_name)
                failed_checks = [c for c in mod_result["checks"] if not c["pass"]]
                all_failed_checks.extend(failed_checks)
                retry_instructions[mod_name] = {
                    "module": mod_name,
                    "attempt": attempt,
                    "failed_checks": failed_checks,
                    "message": f"{len(failed_checks)} checks failed — regenerate {mod_name}",
                }

    # Build history entry (includes failed checks for the report)
    history_entry = {
        "attempt": attempt,
        "timestamp": datetime.now().isoformat(),
        "overall": result["overall"]["status"],
        "passed": result["overall"]["total_passed"],
        "total": result["overall"]["total_checks"],
        "failed_modules": failed_modules,
        "failed_checks": all_failed_checks,
    }

    # Print user-visible summary
    print(f"\n  ┌─ ATTEMPT {attempt} RESULTS:")
    for mod_name, mod_result in result["modules"].items():
        sym = "✓" if mod_result["status"] == "PASS" else "✗"
        print(f"  │  {sym} {mod_name:20s} {mod_result['status']}  ({mod_result['passed']}/{mod_result['total']})")

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
            print(f"  │  → Attempt {attempt + 1} of {MAX_RETRIES}")
        else:
            print(f"  │")
            print(f"  │  ✗ MAX RETRIES ({MAX_RETRIES}) EXHAUSTED")

    print(f"  └─{'─' * 50}")

    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }


# ═════════════════════════════════════════════════════════════
# ROUTING DECISION
# ═════════════════════════════════════════════════════════════
def route_after_validation(state: GraphState) -> Literal["increment_and_retry", "success", "final_failure"]:
    """Decide what happens after validation."""
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)

    if not failed:
        return "success"
    elif attempt < MAX_RETRIES:
        return "increment_and_retry"
    else:
        return "final_failure"


# ═════════════════════════════════════════════════════════════
# INCREMENT ATTEMPT COUNTER
# ═════════════════════════════════════════════════════════════
def increment_and_retry(state: GraphState) -> dict:
    new_attempt = state.get("attempt", 1) + 1
    print(f"\n  ↻ Incrementing to attempt {new_attempt}...")
    return {"attempt": new_attempt}


# ═════════════════════════════════════════════════════════════
# SUCCESS NODE
# ═════════════════════════════════════════════════════════════
def success(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    result = state.get("validation_result", {})
    overall = result.get("overall", {})

    print(f"\n{'═' * 62}")
    print(f"  ✓ ALL VALIDATION PASSED")
    print(f"{'═' * 62}")
    print(f"  Attempt:  {attempt} of {MAX_RETRIES}")
    print(f"  Checks:   {overall.get('total_passed', '?')}/{overall.get('total_checks', '?')}")
    print(f"  Modules:")
    for name, path in sorted(state.get("rtl_files", {}).items()):
        print(f"    ✓ {name}: {path}")

    # Print attempt history
    history = state.get("history", [])
    if len(history) > 1:
        print(f"\n  Retry history:")
        for h in history:
            print(f"    Attempt {h['attempt']}: {h['overall']} ({h['passed']}/{h['total']})"
                  f"{' — failed: ' + ', '.join(h['failed_modules']) if h['failed_modules'] else ''}")

    # Save final report
    report_path = Path(state["output_dir"]) / "final_report.json"
    report = {
        "status": "PASS",
        "attempts": attempt,
        "max_retries": MAX_RETRIES,
        "total_checks": overall.get("total_checks"),
        "total_passed": overall.get("total_passed"),
        "modules": list(state.get("rtl_files", {}).keys()),
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    report_path.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {report_path}")
    print(f"{'═' * 62}")
    return {}


# ═════════════════════════════════════════════════════════════
# FINAL FAILURE NODE
# ═════════════════════════════════════════════════════════════
def final_failure(state: GraphState) -> dict:
    result = state.get("validation_result", {})
    failed = state.get("failed_modules", [])
    history = state.get("history", [])

    print(f"\n{'═' * 62}")
    print(f"  ✗ PIPELINE FAILED — MAX RETRIES ({MAX_RETRIES}) EXHAUSTED")
    print(f"{'═' * 62}")
    print(f"")
    print(f"  The following modules could not pass validation")
    print(f"  after {MAX_RETRIES} regeneration attempts:")
    print(f"")

    for mod in failed:
        mod_result = result.get("modules", {}).get(mod, {})
        failed_checks = [c for c in mod_result.get("checks", []) if not c["pass"]]
        print(f"  ╔═ {mod} ═══════════════════════════════════")
        for chk in failed_checks:
            print(f"  ║  ✗ [{chk['id']}] {chk['name']}")
            print(f"  ║    Expected: {chk['expected']}")
            print(f"  ║    Actual:   {chk['actual']}")
        print(f"  ╚{'═' * 50}")
        print(f"")

    # Print full retry history
    print(f"  Retry history:")
    for h in history:
        status_sym = "✓" if h["overall"] == "PASS" else "✗"
        fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
        print(f"    {status_sym} Attempt {h['attempt']}: {h['overall']} "
              f"({h['passed']}/{h['total']}) — failed: {fails}")

    print(f"")
    print(f"  RECOMMENDED ACTIONS:")
    print(f"    1. Check the microarchitecture spec for inconsistencies")
    print(f"    2. Review the failing checks above")
    print(f"    3. Manually inspect the generated .sv files in {state['output_dir']}/")
    print(f"    4. Run validation_agent.py standalone for detailed diagnostics")

    # Save error report
    report_path = Path(state["output_dir"]) / "error_report.json"
    report = {
        "status": "FAIL",
        "attempts": MAX_RETRIES,
        "max_retries": MAX_RETRIES,
        "failed_modules": failed,
        "unresolved_failures": {},
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    for mod in failed:
        mod_result = result.get("modules", {}).get(mod, {})
        report["unresolved_failures"][mod] = [
            c for c in mod_result.get("checks", []) if not c["pass"]
        ]
    report_path.write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {report_path}")
    print(f"{'═' * 62}")
    return {}


# ═════════════════════════════════════════════════════════════
# BUILD GRAPH
# ═════════════════════════════════════════════════════════════
def build_graph():
    graph = StateGraph(GraphState)

    # Nodes
    graph.add_node("gen_wb_port", gen_wb_port)
    graph.add_node("gen_config_regs", gen_config_regs)
    graph.add_node("gen_init_fsm", gen_init_fsm)
    graph.add_node("validate", validate)
    graph.add_node("increment_and_retry", increment_and_retry)
    graph.add_node("success", success)
    graph.add_node("final_failure", final_failure)

    # Entry: 3 agents start in parallel
    graph.set_entry_point("gen_wb_port")
    graph.set_entry_point("gen_config_regs")
    graph.set_entry_point("gen_init_fsm")

    # All 3 converge into validation
    graph.add_edge("gen_wb_port", "validate")
    graph.add_edge("gen_config_regs", "validate")
    graph.add_edge("gen_init_fsm", "validate")

    # Conditional routing after validation
    graph.add_conditional_edges(
        "validate",
        route_after_validation,
        {
            "success": "success",
            "increment_and_retry": "increment_and_retry",
            "final_failure": "final_failure",
        },
    )

    # Retry loops back to all 3 generators (parallel again)
    graph.add_edge("increment_and_retry", "gen_wb_port")
    graph.add_edge("increment_and_retry", "gen_config_regs")
    graph.add_edge("increment_and_retry", "gen_init_fsm")

    # Terminal nodes
    graph.add_edge("success", END)
    graph.add_edge("final_failure", END)

    return graph.compile()


# ═════════════════════════════════════════════════════════════
# MAIN
# ═════════════════════════════════════════════════════════════
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════╗")
    print("║   DDR3 Controller — LangGraph Pipeline              ║")
    print("║   Phase 1 (parallel) + Validation (max 4 retries)  ║")
    print("╚══════════════════════════════════════════════════════╝")
    print()

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    os.makedirs(out, exist_ok=True)

    # Clean attempt trackers from previous runs
    for tracker in [".init_fsm_attempt", ".config_regs_attempt", ".wb_port_attempt"]:
        tf = Path(out) / tracker
        if tf.exists():
            tf.unlink()

    app = build_graph()

    result = app.invoke({
        "spec_path": spec,
        "output_dir": out,
        "modules": {},
        "rtl_files": {},
        "attempt": 1,
        "validation_result": {},
        "failed_modules": [],
        "retry_instructions": {},
        "history": [],
    })