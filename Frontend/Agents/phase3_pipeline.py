#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║        DDR3 MEMORY CONTROLLER — PHASE 3 PIPELINE                     ║
║                                                                      ║
║  Input:  Phase 1 output (PHASE1RTL/) + Phase 2 output (PHASE2RTL/)   ║
║                                                                      ║
║  Flow:                                                               ║
║    3 agents (parallel) → Validation (port checks + TB gen)           ║
║        → Lint Gate (cross-phase P1+P2+P3 port consistency)           ║
║        ↓ retry loop with fix instructions (max 4)                    ║
║                                                                      ║
║  Output per module:                                                  ║
║    - <module>.sv, <module>_tb.sv, <module>_manifest.json             ║
║    - phase3_validation_report.json                                   ║
║                                                                      ║
║  Modules: cmd_queue, scheduler, cmd_gen                              ║
╚══════════════════════════════════════════════════════════════════════╝
"""
import json, os, sys, operator, shutil
from typing import TypedDict, Annotated, Literal
from pathlib import Path
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
for _rel in [".", "Agents/Phase_3_Agents", "Agents/Phase_2_Agents", "Agents/Phase_1_Agents",
             "Agents", "..", "../Phase_1_Agents", "../Phase_2_Agents", "../..",
             "Phase_3_Agents", "Phase_2_Agents", "Phase_1_Agents"]:
    _p = os.path.normpath(os.path.join(HERE, _rel))
    if os.path.isdir(_p) and _p not in sys.path:
        sys.path.insert(0, _p)

from langgraph.graph import StateGraph, END
from cmd_queue_agent import CmdQueueAgent
from scheduler_agent import SchedulerAgent
from cmd_gen_agent import CmdGenAgent
from phase3_validation_agent import Phase3ValidationAgent
from lint_agent import LintAgent

MAX_RETRIES = 4
PHASE3_RTL_DIR = "PHASE3RTL"
VALIDATION_DIR = "VALIDATIONREPORT"
P3_MODULES = ("cmd_queue", "scheduler", "cmd_gen")

def setup_output_dirs(base_dir):
    dirs = {"phase3_rtl": str(Path(base_dir)/PHASE3_RTL_DIR), "validation": str(Path(base_dir)/VALIDATION_DIR)}
    for d in dirs.values(): os.makedirs(d, exist_ok=True)
    return dirs

class GraphState(TypedDict):
    spec_path: str
    output_dir: str
    phase1_rtl_dir: str
    phase2_rtl_dir: str
    phase3_rtl_dir: str
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

# ── RTL GENERATION ──
def gen_cmd_queue(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instr = state.get("retry_instructions", {}).get("cmd_queue")
    if instr:
        print(f"\n  ┌─ [P3 Attempt {attempt}] REGENERATING cmd_queue")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P3 Attempt {attempt}] Generating cmd_queue")
    r = CmdQueueAgent(state["spec_path"], state["phase3_rtl_dir"]).run()
    return {"modules": {"cmd_queue": r.get("manifest", {})},
            "rtl_files": {"cmd_queue": r.get("rtl_path", "")}}

def gen_scheduler(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instr = state.get("retry_instructions", {}).get("scheduler")
    if instr:
        print(f"\n  ┌─ [P3 Attempt {attempt}] REGENERATING scheduler")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P3 Attempt {attempt}] Generating scheduler")
    r = SchedulerAgent(state["spec_path"], state["phase3_rtl_dir"]).run()
    return {"modules": {"scheduler": r.get("manifest", {})},
            "rtl_files": {"scheduler": r.get("rtl_path", "")}}

def gen_cmd_gen(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    instr = state.get("retry_instructions", {}).get("cmd_gen")
    if instr:
        print(f"\n  ┌─ [P3 Attempt {attempt}] REGENERATING cmd_gen")
        for chk in instr.get("failed_checks", [])[:5]:
            print(f"  │    ✗ [{chk['id']}] {chk['name']}")
    else:
        print(f"\n  ┌─ [P3 Attempt {attempt}] Generating cmd_gen")
    r = CmdGenAgent(state["spec_path"], state["phase3_rtl_dir"]).run()
    return {"modules": {"cmd_gen": r.get("manifest", {})},
            "rtl_files": {"cmd_gen": r.get("rtl_path", "")}}

# ── VALIDATION ──
def validate_p3(state: GraphState) -> dict:
    attempt = state.get("attempt", 1)
    print(f"\n{'━'*62}\n  PHASE 3 VALIDATION — Attempt {attempt} of {MAX_RETRIES}\n{'━'*62}")
    va = Phase3ValidationAgent(state["spec_path"], state["phase3_rtl_dir"], state["validation_dir"],
                                attempt=attempt, max_retries=MAX_RETRIES,
                                history=[h for h in state.get("history", [])])
    result = va.run()

    failed_modules = []
    retry_instructions = {}
    for mod_name, mod_result in result["modules"].items():
        if mod_result["status"] != "PASS" and mod_name in P3_MODULES:
            failed_checks = [c for c in mod_result["checks"] if not c["pass"]]
            failed_modules.append(mod_name)
            retry_instructions[mod_name] = {
                "module": mod_name, "attempt": attempt,
                "failed_checks": failed_checks,
                "message": f"{len(failed_checks)} checks failed",
            }

    val_overall = result.get("overall", {})
    history_entry = {
        "phase": 3, "attempt": attempt, "timestamp": datetime.now().isoformat(),
        "overall": "PASS" if not failed_modules else "FAIL",
        "passed": val_overall.get("total_passed", 0),
        "total": val_overall.get("total_checks", 0),
        "failed_modules": failed_modules,
    }
    return {
        "validation_result": result,
        "failed_modules": failed_modules,
        "retry_instructions": retry_instructions,
        "history": [history_entry],
    }

def route_after_validation(state: GraphState) -> Literal["p3_increment_retry", "lint_gate", "final_failure"]:
    failed = state.get("failed_modules", [])
    attempt = state.get("attempt", 1)
    if not failed: return "lint_gate"
    elif attempt < MAX_RETRIES: return "p3_increment_retry"
    else: return "final_failure"

def p3_increment_retry(state: GraphState) -> dict:
    n = state.get("attempt", 1) + 1
    print(f"\n  ↻ Phase 3: Incrementing to attempt {n}...")
    return {"attempt": n}

# ── LINT GATE (all 3 phases) ──
def lint_gate(state: GraphState) -> dict:
    print(f"\n{'━'*62}\n  LINT AGENT — Cross-Phase Port Consistency (P1+P2+P3)\n{'━'*62}")
    combined = Path(state["validation_dir"]) / "lint_combined_p3"
    combined.mkdir(parents=True, exist_ok=True)
    for src in [state["phase1_rtl_dir"], state["phase2_rtl_dir"], state["phase3_rtl_dir"]]:
        p = Path(src)
        if p.exists():
            for mf in p.glob("*_manifest.json"):
                shutil.copy2(str(mf), str(combined / mf.name))
    lint = LintAgent(str(combined), state["validation_dir"])
    result = lint.run()
    if result["status"] == "PASS":
        print(f"\n  \033[92m✓ LINT PASSED — Phase 3 pipeline complete\033[0m")
    else:
        print(f"\n  \033[91m✗ LINT FAILED — {result['summary']['errors']} errors\033[0m")
    return {"lint_result": result}

def route_after_lint(state: GraphState) -> Literal["success", "final_failure"]:
    return "success" if state.get("lint_result", {}).get("status") == "PASS" else "final_failure"

# ── TERMINAL ──
def success(state: GraphState) -> dict:
    history = state.get("history", [])
    lint = state.get("lint_result", {})
    print(f"\n{'═'*62}\n  ✓ PHASE 3 PIPELINE — ALL CHECKS PASSED\n{'═'*62}\n")
    if history:
        last = history[-1]
        print(f"  Phase 3:  {last['passed']}/{last['total']} checks ({len(history)} attempt{'s' if len(history)>1 else ''})")
    if lint:
        s = lint.get("summary", {})
        print(f"  Lint:     {s.get('passed','?')} passed  {s.get('errors','?')} errors  {s.get('warnings','?')} warnings")
    print(f"\n  Generated outputs:")
    rd = Path(state["phase3_rtl_dir"]); vd = Path(state["validation_dir"])
    for mod in P3_MODULES:
        sv_ok = "✓" if (rd/f"{mod}.sv").exists() else "✗"
        tb_ok = "✓" if (vd/f"{mod}_tb.sv").exists() or (rd/f"{mod}_tb.sv").exists() else "✗"
        mf_ok = "✓" if (rd/f"{mod}_manifest.json").exists() else "✗"
        print(f"    {sv_ok} {mod}.sv  {tb_ok} {mod}_tb.sv  {mf_ok} {mod}_manifest.json")
    report = {"status": "PASS", "pipeline": "phase3", "lint_status": lint.get("status"),
              "attempts": len(history), "modules": list(P3_MODULES), "history": history,
              "timestamp": datetime.now().isoformat()}
    rp = vd / "phase3_final_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Report: {rp}\n{'═'*62}")
    return {"pipeline_status": "pass"}

def final_failure(state: GraphState) -> dict:
    failed = state.get("failed_modules", [])
    history = state.get("history", [])
    lint = state.get("lint_result", {})
    print(f"\n{'═'*62}\n  ✗ PHASE 3 PIPELINE FAILED\n{'═'*62}")
    if lint and lint.get("status") == "FAIL":
        print(f"\n  Failed at: LINT GATE")
        for e in lint.get("errors", []): print(f"    ✗ [{e['check']}] {e['message']}")
    elif failed:
        print(f"\n  Failed at: Validation (max retries)")
        ri = state.get("retry_instructions", {})
        for mod in failed:
            instr = ri.get(mod, {})
            print(f"\n  ╔═ {mod} ═══════════════════════════════════")
            for chk in instr.get("failed_checks", [])[:5]:
                print(f"  ║  ✗ [{chk['id']}] {chk['name']}")
            print(f"  ╚{'═'*50}")
    if history:
        print(f"\n  Retry history:")
        for h in history:
            sym = "✓" if h["overall"]=="PASS" else "✗"
            fails = ", ".join(h.get("failed_modules", [])) or "none"
            print(f"    {sym} Attempt {h['attempt']}: {h['overall']} ({h['passed']}/{h['total']}) — failed: {fails}")
    report = {"status": "FAIL", "pipeline": "phase3", "failed_modules": failed,
              "lint_result": lint, "history": history, "timestamp": datetime.now().isoformat()}
    rp = Path(state["validation_dir"]) / "phase3_error_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n  Error report: {rp}\n{'═'*62}")
    return {"pipeline_status": "fail"}

# ── BUILD GRAPH ──
def build_graph():
    g = StateGraph(GraphState)
    g.add_node("gen_cmd_queue", gen_cmd_queue)
    g.add_node("gen_scheduler", gen_scheduler)
    g.add_node("gen_cmd_gen", gen_cmd_gen)
    g.add_node("validate_p3", validate_p3)
    g.add_node("p3_increment_retry", p3_increment_retry)
    g.add_node("lint_gate", lint_gate)
    g.add_node("success", success)
    g.add_node("final_failure", final_failure)

    # Entry: 3 agents parallel
    g.set_entry_point("gen_cmd_queue")
    g.set_entry_point("gen_scheduler")
    g.set_entry_point("gen_cmd_gen")

    # Converge into validation
    g.add_edge("gen_cmd_queue", "validate_p3")
    g.add_edge("gen_scheduler", "validate_p3")
    g.add_edge("gen_cmd_gen", "validate_p3")

    # Route after validation
    g.add_conditional_edges("validate_p3", route_after_validation,
        {"lint_gate": "lint_gate", "p3_increment_retry": "p3_increment_retry", "final_failure": "final_failure"})

    # Retry → back to generators
    g.add_edge("p3_increment_retry", "gen_cmd_queue")
    g.add_edge("p3_increment_retry", "gen_scheduler")
    g.add_edge("p3_increment_retry", "gen_cmd_gen")

    # Lint → success or failure
    g.add_conditional_edges("lint_gate", route_after_lint,
        {"success": "success", "final_failure": "final_failure"})

    g.add_edge("success", END)
    g.add_edge("final_failure", END)
    return g.compile()

# ── MAIN ──
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════╗")
    print("║   DDR3 Controller — Phase 3 Pipeline                     ║")
    print("║                                                          ║")
    print("║   3 agents → Validate → Lint (P1+P2+P3) → retry loop    ║")
    print("║   Outputs: .sv, _tb.sv, _manifest.json, reports          ║")
    print("╚══════════════════════════════════════════════════════════╝\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec): print(f"Not found: {spec}"); sys.exit(1)
    p1_dir = input("Phase 1 RTL dir (PHASE1RTL/): ").strip()
    if not os.path.isdir(p1_dir): print(f"Not found: {p1_dir}"); sys.exit(1)
    p2_dir = input("Phase 2 RTL dir (PHASE2RTL/): ").strip()
    if not os.path.isdir(p2_dir): print(f"Not found: {p2_dir}"); sys.exit(1)
    out = input("Output dir (Enter for ./output): ").strip() or "./output"
    dirs = setup_output_dirs(out)

    print(f"\n  Input:")
    print(f"    Phase 1: {p1_dir}")
    print(f"    Phase 2: {p2_dir}")
    print(f"\n  Output:")
    print(f"    {out}/{PHASE3_RTL_DIR}/  ← .sv + _manifest.json")
    print(f"    {out}/{VALIDATION_DIR}/  ← _tb.sv + reports + lint\n")

    app = build_graph()
    result = app.invoke({
        "spec_path": spec, "output_dir": out,
        "phase1_rtl_dir": p1_dir, "phase2_rtl_dir": p2_dir,
        "phase3_rtl_dir": dirs["phase3_rtl"], "validation_dir": dirs["validation"],
        "modules": {}, "rtl_files": {}, "attempt": 1,
        "validation_result": {}, "failed_modules": [], "retry_instructions": {},
        "history": [], "lint_result": {}, "pipeline_status": "running",
    })
    sys.exit(0 if result.get("pipeline_status") == "pass" else 1)
