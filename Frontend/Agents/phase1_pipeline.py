#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║        DDR3 MEMORY CONTROLLER — PHASE 1 PIPELINE                     ║
║                                                                      ║
║  Flow:                                                               ║
║    3 agents (parallel) → Validation (94 checks + TB gen)            ║
║        → Lint Gate → retry loop (max 4)                              ║
║                                                                      ║
║  Output:                                                             ║
║    PHASE1RTL/          .sv + _manifest.json per module               ║
║    VALIDATIONREPORT/   _tb.sv + validation reports + lint report     ║
║                                                                      ║
║  Modules: init_fsm, config_regs, wb_port                            ║
╚══════════════════════════════════════════════════════════════════════╝
"""
import json, os, sys, shutil, operator
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
from wb_port_agent import WishbonePortAgent
from config_regs_agent import ConfigRegsAgent
from init_fsm_agent import InitFsmAgent
from phase1_validation_agent import ValidationAgent as Phase1ValidationAgent
from lint_agent import LintAgent

MAX_RETRIES = 4
PHASE1_RTL_DIR = "PHASE1RTL"
VALIDATION_DIR = "VALIDATIONREPORT"
P1_MODULES = ("init_fsm", "config_regs", "wb_port")

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
    pipeline_status: str


# ═══════════════════════════════════════════
# RTL GENERATION (3 agents, parallel)
# ═══════════════════════════════════════════
def _log_gen(mod, attempt, instr):
    if instr:
        print(f"\n  ┌─ [P1 Attempt {attempt}] REGENERATING {mod}")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P1 Attempt {attempt}] Generating {mod}")


def gen_init_fsm(state: GraphState) -> dict:
    _log_gen("init_fsm", state.get("attempt", 1), state.get("retry_instructions", {}).get("init_fsm"))
    r = InitFsmAgent(state["spec_path"], state["phase1_rtl_dir"]).run()
    return {"modules": {"init_fsm": r.get("manifest", {})},
            "rtl_files": {"init_fsm": r.get("rtl_path", str(Path(state["phase1_rtl_dir"]) / "init_fsm.sv"))}}


def gen_config_regs(state: GraphState) -> dict:
    _log_gen("config_regs", state.get("attempt", 1), state.get("retry_instructions", {}).get("config_regs"))
    r = ConfigRegsAgent(state["spec_path"], state["phase1_rtl_dir"]).run()
    return {"modules": {"config_regs": r.get("manifest", {})},
            "rtl_files": {"config_regs": r.get("rtl_path", str(Path(state["phase1_rtl_dir"]) / "config_regs.sv"))}}


def gen_wb_port(state: GraphState) -> dict:
    _log_gen("wb_port", state.get("attempt", 1), state.get("retry_instructions", {}).get("wb_port"))
    r = WishbonePortAgent(state["spec_path"], state["phase1_rtl_dir"]).run()
    return {"modules": {"wb_port": r.get("manifest", {})},
            "rtl_files": {"wb_port": r.get("rtl_path", str(Path(state["phase1_rtl_dir"]) / "wb_port.sv"))}}


# ═══════════════════════════════════════════
# VALIDATION (94 static checks + TB gen)
# ═══════════════════════════════════════════
def validate_p1(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'━' * 62}")
    print(f"  PHASE 1 VALIDATION — Attempt {attempt} of {MAX_RETRIES}")
    print(f"  (94 static checks + testbench generation)")
    print(f"{'━' * 62}")

    # RTL read from phase1_rtl_dir, TBs + reports written to validation_dir
    va = Phase1ValidationAgent(
        state["spec_path"], state["phase1_rtl_dir"], state["validation_dir"],
        attempt=attempt, max_retries=MAX_RETRIES,
        history=[h for h in state.get("history", [])])
    result = va.run()

    failed_modules, retry_instructions, all_failed = [], {}, []
    for mod, mr in result["modules"].items():
        if mr["status"] != "PASS" and mod in P1_MODULES:
            failed_modules.append(mod)
            fc = [c for c in mr["checks"] if not c["pass"]]
            all_failed.extend(fc)
            retry_instructions[mod] = {
                "module": mod, "attempt": attempt,
                "failed_checks": fc,
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

    # Print summary
    print(f"\n  ┌─ PHASE 1 ATTEMPT {attempt} RESULTS:")
    for mod, mr in result["modules"].items():
        sym = "✓" if mr["status"] == "PASS" else "✗"
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
    print(f"  └─{'─' * 50}")

    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }


# ═══════════════════════════════════════════
# ROUTING + RETRY
# ═══════════════════════════════════════════
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
    print(f"\n  ↻ Phase 1: Incrementing to attempt {n}...")
    return {"attempt": n}


# ═══════════════════════════════════════════
# LINT GATE (Phase 1 only)
# ═══════════════════════════════════════════
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'━' * 62}")
    print(f"  LINT AGENT — Phase 1 Port Consistency")
    print(f"{'━' * 62}")

    # Lint reads manifests from PHASE1RTL/
    lint = LintAgent(state["phase1_rtl_dir"], state["validation_dir"])
    result = lint.run()

    if result["status"] == "PASS":
        print(f"\n  \033[92m✓ LINT PASSED — Phase 1 pipeline complete\033[0m")
    else:
        print(f"\n  \033[91m✗ LINT FAILED — {result['summary']['errors']} errors\033[0m")

    return {"lint_result": result}


def route_after_lint(state: GraphState) -> Literal["success", "final_failure"]:
    return "success" if state.get("lint_result", {}).get("status") == "PASS" else "final_failure"


# ═══════════════════════════════════════════
# TERMINAL NODES
# ═══════════════════════════════════════════
def success(state: GraphState) -> dict:
    history = state.get("history", [])
    lint = state.get("lint_result", {})

    print(f"\n{'═' * 62}")
    print(f"  ✓ PHASE 1 PIPELINE — ALL CHECKS PASSED")
    print(f"{'═' * 62}\n")

    if history:
        last = history[-1]
        print(f"  Phase 1:  {last['passed']}/{last['total']} checks "
              f"({len(history)} attempt{'s' if len(history) > 1 else ''})")

    if lint:
        s = lint.get("summary", {})
        print(f"  Lint:     {s.get('passed', '?')} passed  "
              f"{s.get('errors', '?')} errors  {s.get('warnings', '?')} warnings")

    print(f"\n  Generated outputs:")
    rd = Path(state["phase1_rtl_dir"])
    vd = Path(state["validation_dir"])
    for mod in P1_MODULES:
        sv_ok = "✓" if (rd / f"{mod}.sv").exists() else "✗"
        tb_ok = "✓" if (vd / f"{mod}_tb.sv").exists() else "✗"
        mf_ok = "✓" if (rd / f"{mod}_manifest.json").exists() else "✗"
        print(f"    {sv_ok} {mod}.sv  {tb_ok} {mod}_tb.sv  {mf_ok} {mod}_manifest.json")

    vr = vd / "validation_report.json"
    print(f"    {'✓' if vr.exists() else '✗'} validation_report.json")

    if len(history) > 1:
        print(f"\n  Retry history:")
        for h in history:
            sym = "✓" if h["overall"] == "PASS" else "✗"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) — failed: {fails}")

    report = {
        "status": "PASS", "pipeline": "phase1",
        "lint_status": lint.get("status"),
        "attempts": len(history),
        "modules": list(P1_MODULES),
        "outputs": {
            mod: {
                "sv": str(rd / f"{mod}.sv"),
                "tb": str(vd / f"{mod}_tb.sv"),
                "manifest": str(rd / f"{mod}_manifest.json"),
            }
            for mod in P1_MODULES
        },
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    rp = vd / "phase1_final_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {rp}")
    print(f"{'═' * 62}")
    return {"pipeline_status": "pass"}


def final_failure(state: GraphState) -> dict:
    failed = state.get("failed_modules", [])
    history = state.get("history", [])
    lint = state.get("lint_result", {})
    ri = state.get("retry_instructions", {})

    print(f"\n{'═' * 62}")
    print(f"  ✗ PHASE 1 PIPELINE FAILED")
    print(f"{'═' * 62}")

    if lint and lint.get("status") == "FAIL":
        print(f"\n  Failed at: LINT GATE")
        for e in lint.get("errors", []):
            print(f"    ✗ [{e['check']}] {e['message']}")
    elif failed:
        print(f"\n  Failed at: Validation (max retries)")
        for mod in failed:
            instr = ri.get(mod, {})
            print(f"\n  ╔═ {mod} ═══════════════════════════════════")
            for chk in instr.get("failed_checks", [])[:5]:
                print(f"  ║  ✗ [{chk['id']}] {chk['name']}")
                print(f"  ║    Expected: {chk['expected']}")
                print(f"  ║    Actual:   {chk['actual']}")
            print(f"  ╚{'═' * 50}")

    if history:
        print(f"\n  Retry history:")
        for h in history:
            sym = "✓" if h["overall"] == "PASS" else "✗"
            fails = ", ".join(h["failed_modules"]) if h["failed_modules"] else "none"
            print(f"    {sym} Attempt {h['attempt']}: "
                  f"{h['overall']} ({h['passed']}/{h['total']}) — failed: {fails}")

    print(f"\n  Actions:")
    print(f"    1. Review failing checks above")
    print(f"    2. Inspect RTL in {state['phase1_rtl_dir']}/")
    print(f"    3. Review reports in {state['validation_dir']}/")

    report = {
        "status": "FAIL", "pipeline": "phase1",
        "failed_modules": failed,
        "lint_result": lint,
        "history": history,
        "timestamp": datetime.now().isoformat(),
    }
    rp = Path(state["validation_dir"]) / "phase1_error_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {rp}")
    print(f"{'═' * 62}")
    return {"pipeline_status": "fail"}


# ═══════════════════════════════════════════
# BUILD GRAPH
# ═══════════════════════════════════════════
def build_graph():
    g = StateGraph(GraphState)

    g.add_node("gen_init_fsm", gen_init_fsm)
    g.add_node("gen_config_regs", gen_config_regs)
    g.add_node("gen_wb_port", gen_wb_port)
    g.add_node("validate_p1", validate_p1)
    g.add_node("p1_increment_retry", p1_increment_retry)
    g.add_node("lint_gate", lint_gate)
    g.add_node("success", success)
    g.add_node("final_failure", final_failure)

    # Entry: 3 agents parallel
    g.set_entry_point("gen_init_fsm")
    g.set_entry_point("gen_config_regs")
    g.set_entry_point("gen_wb_port")

    # Converge into validation
    g.add_edge("gen_init_fsm", "validate_p1")
    g.add_edge("gen_config_regs", "validate_p1")
    g.add_edge("gen_wb_port", "validate_p1")

    # Route after validation
    g.add_conditional_edges("validate_p1", route_after_validation,
        {"lint_gate": "lint_gate",
         "p1_increment_retry": "p1_increment_retry",
         "final_failure": "final_failure"})

    # Retry → back to generators
    g.add_edge("p1_increment_retry", "gen_init_fsm")
    g.add_edge("p1_increment_retry", "gen_config_regs")
    g.add_edge("p1_increment_retry", "gen_wb_port")

    # Lint → success or failure
    g.add_conditional_edges("lint_gate", route_after_lint,
        {"success": "success", "final_failure": "final_failure"})

    g.add_edge("success", END)
    g.add_edge("final_failure", END)

    return g.compile()


# ═══════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════╗")
    print("║   DDR3 Controller — Phase 1 Pipeline                     ║")
    print("║                                                          ║")
    print("║   3 agents → Validate (94 checks + TB) → Lint Gate      ║")
    print("║   Outputs: .sv, _tb.sv, _manifest.json, reports          ║")
    print("╚══════════════════════════════════════════════════════════╝\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}")
        sys.exit(1)

    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    dirs = setup_output_dirs(out)

    print(f"\n  Output layout:")
    print(f"    {out}/")
    print(f"    ├── {PHASE1_RTL_DIR}/          ← .sv + _manifest.json")
    print(f"    └── {VALIDATION_DIR}/  ← _tb.sv + reports + lint")
    print()

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
        "pipeline_status": "running",
    })

    sys.exit(0 if result.get("pipeline_status") == "pass" else 1)