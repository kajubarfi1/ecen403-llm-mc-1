import argparse
import json
import os
import sys
import getpass
import time
import traceback
from datetime import datetime
from typing import Any, Dict, List, Literal, Optional, TypedDict, Annotated
from concurrent.futures import ThreadPoolExecutor, as_completed
import llm_client
from langgraph.graph import StateGraph, START, END

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass
# Scope Configuration 

SCOPE_CONFIG = {
    "config_regs": {
        "rtl_filename": "config_regs.sv",
        "manifest_filename": "config_regs_manifest.json",
    },
    "wb_port": {
        "rtl_filename": "wb_port.sv",
        "manifest_filename": "wb_port_manifest.json",
    },
    "init_sequence": {
        "rtl_filename": "init_fsm.sv",
        "manifest_filename": "init_fsm_manifest.json",
    },
    "path_backpressure": {
        "rtl_filename": [
            "PHASE1RTL/wb_port.sv",
            "PHASE3RTL/cmd_queue.sv",
        ],
        "manifest_filename": [
            "PHASE1RTL/wb_port_manifest.json",
            "PHASE3RTL/cmd_queue_manifest.json",
        ],
        "integration_scope": True,
    },
}


# =============================================================================
# State Definition
# =============================================================================

class PipelineState(TypedDict, total=False):
    """Shared state flowing through the validation pipeline graph."""

    # --- Configuration
    scope: str
    project_root: str
    skip_sim: bool
    start_from: str
    pipeline_mode: str  
    api_key: Optional[str]
    model_id: Optional[str]
    ssh_password: Optional[str]
    max_retries: int

    paths: Dict[str, str]

    agents_loaded: bool

    skip_connectivity: bool

    # --- Per-stage results ---
    connectivity_result: Dict[str, Any]
    refmodel_result: Dict[str, Any]
    vectors_result: Dict[str, Any]
    testbench_result: Dict[str, Any]
    sim_result: Dict[str, Any]
    triage_result: Dict[str, Any]

    # --- Control flow ---
    current_stage: str
    retry_count: int
    retry_target: str           
    pipeline_status: str        # running | passed | failed | error
    error_message: str

    # --- Event log  ---
    events: List[Dict[str, Any]]


# Path Resolution (mirrors original PathResolver)
def resolve_paths(project_root: str, scope: str) -> Dict[str, str]:
    """Compute all file paths for a scope. Returns a flat dict."""
    cfg = SCOPE_CONFIG[scope]
    root = os.path.abspath(project_root)

    frontend_output = os.path.join(root, "Frontend", "Output_Folders", "Phase1_Output")
    frontend_root = os.path.join(root, "Frontend", "OutputFolders")
    validation_dir = os.path.join(root, "Validation")
    agents_dir = os.path.join(validation_dir, "agents")
    spec_dir = os.path.join(validation_dir, "spec")
    refmodel_dir = os.path.join(validation_dir, "reference_models")
    scope_dir = os.path.join(validation_dir, "scopes", scope)
    reports_dir = os.path.join(scope_dir, "reports")

    return {
        "root": root,
        "frontend_output": frontend_output,
        "frontend_root": frontend_root,
        "agents_dir": agents_dir,
        "spec_dir": spec_dir,
        "refmodel_dir": refmodel_dir,
        "scope_dir": scope_dir,
        "reports_dir": reports_dir,
        # Input files
        "spec": os.path.join(spec_dir, "llmmc_microarchitecturespec_filled.json"),
        "path_defs": os.path.join(spec_dir, "path_definitions.json"),
        "rtl": [os.path.join(frontend_root, f) for f in cfg["rtl_filename"]] if isinstance(cfg["rtl_filename"], list) else os.path.join(frontend_root, cfg["rtl_filename"]),
        "manifest": [os.path.join(frontend_root, f) for f in cfg["manifest_filename"]] if isinstance(cfg["manifest_filename"], list) else os.path.join(frontend_root, cfg["manifest_filename"]),
        # Generated outputs
        "refmodel": os.path.join(refmodel_dir, f"{scope}_refmodel.py"),
        "vectors_hex": os.path.join(scope_dir, f"{scope}_vectors.hex"),
        "vectors_json": os.path.join(scope_dir, f"{scope}_vectors.json"),
        "testbench": os.path.join(scope_dir, f"{scope}_tb.sv"),
        "testplan": os.path.join(scope_dir, f"{scope}_testplan.json"),
        # Reports
        "refmodel_report": os.path.join(reports_dir, f"{scope}_refmodel_report.json"),
        "vectorgen_report": os.path.join(reports_dir, f"{scope}_vectorgen_report.json"),
        "tbgen_report": os.path.join(reports_dir, f"{scope}_tbgen_report.json"),
        "sim_report": os.path.join(reports_dir, f"{scope}_sim_report.json"),
        "sim_log": os.path.join(reports_dir, f"{scope}_sim.log"),
        "triage_report": os.path.join(reports_dir, f"{scope}_triage_report.json"),
        "orchestrator_report": os.path.join(reports_dir, f"{scope}_orchestrator_report.json"),
    }



_AGENT_MODULES: Dict[str, Any] = {}


def _ensure_agents_loaded(agents_dir: str):
    """Import agent modules if not already cached."""
    global _AGENT_MODULES
    if _AGENT_MODULES:
        return

    abspath = os.path.abspath(agents_dir)
    if abspath not in sys.path:
        sys.path.insert(0, abspath)

    import refmodel_agent
    import vector_gen_agent
    import testbench_gen_agent
    import sim_runner
    import failure_triage_agent


    try:
        import event_spec_agent
        import event_vector_gen
        import event_tb_codegen
        _event_modules = {
            "event_spec": event_spec_agent,
            "event_vector": event_vector_gen,
            "event_tb": event_tb_codegen,
        }
    except ImportError as _e:
        print(f"[orchestrator] event-mode agents not available: {_e}")
        _event_modules = {}

    _AGENT_MODULES = {
        "refmodel": refmodel_agent,
        "vector_gen": vector_gen_agent,
        "testbench_gen": testbench_gen_agent,
        "sim_runner": sim_runner,
        "failure_triage": failure_triage_agent,
        **_event_modules,
    }


def _set_agent_globals(mod, api_key=None, model_id=None):
    """Override API key / model on the shared LLM client."""
    if api_key:
        llm_client.configure(tamu_key=api_key)
    if model_id:
        llm_client.configure(tamu_model=model_id)
    # Legacy: still set module globals for backward compat
    if api_key and hasattr(mod, "API_KEY"):
        mod.API_KEY = api_key
    if model_id and hasattr(mod, "MODEL_ID"):
        mod.MODEL_ID = model_id


# Event Helpers

def _emit(state: PipelineState, event_type: str, **kwargs) -> List[Dict[str, Any]]:
    """Create a new event and return an updated events list.
    
    Event types for frontend/backend consumption:
      - stage_start:   A pipeline stage is beginning
      - stage_complete: A stage finished (with status)
      - stage_skip:    A stage was skipped
      - triage_start:  Failure triage is beginning
      - triage_complete: Triage finished with diagnosis
      - retry:         Pipeline is retrying a stage
      - pipeline_complete: Entire pipeline finished
      - error:         An error occurred
      - info:          Informational message
    """
    event = {
        "type": event_type,
        "timestamp": datetime.now().isoformat(),
        "scope": state.get("scope", ""),
        "retry_count": state.get("retry_count", 0),
        **kwargs,
    }
    existing = list(state.get("events", []))
    existing.append(event)
    return existing


def _log(state: PipelineState, msg: str):
    """Print a log line with scope context."""
    scope = state.get("scope", "?")
    retry = state.get("retry_count", 0)
    prefix = f"[LG-Orchestrator][{scope}]"
    if retry > 0:
        prefix += f"[retry={retry}]"
    print(f"{prefix} {msg}")


# Graph Nodes

def node_init(state: PipelineState) -> dict:
    """Initialize paths, load agents, validate inputs."""
    scope = state["scope"]
    project_root = state["project_root"]

    _log(state, f"Initializing pipeline for scope: {scope}")
    _log(state, f"Project root: {project_root}")

    # Resolve paths
    paths = resolve_paths(project_root, scope)

    # Create output directories
    for d in [paths["refmodel_dir"], paths["scope_dir"], paths["reports_dir"]]:
        os.makedirs(d, exist_ok=True)

    # Validate inputs exist
    start_from = state.get("start_from", "refmodel")
    missing = []
    if not os.path.exists(paths["spec"]):
        missing.append(f"Spec: {paths['spec']}")
    if isinstance(paths["rtl"], list):
        for rtl_path in paths["rtl"]:
            if not os.path.exists(rtl_path):
                missing.append(f"RTL: {rtl_path}")
    else:
        if not os.path.exists(paths["rtl"]):
            missing.append(f"RTL: {paths['rtl']}")
    if start_from in ("refmodel", "vectors", "testbench"):
        if isinstance(paths["manifest"], list):
            for man_path in paths["manifest"]:
                if not os.path.exists(man_path):
                    missing.append(f"Manifest: {man_path}")
        else:
            if not os.path.exists(paths["manifest"]):
                missing.append(f"Manifest: {paths['manifest']}")
    if start_from == "vectors" and not os.path.exists(paths["refmodel"]):
        missing.append(f"Refmodel: {paths['refmodel']}")
    if start_from == "testbench" and not os.path.exists(paths["vectors_hex"]):
        missing.append(f"Vectors: {paths['vectors_hex']}")
    if start_from == "simulate":
        if not os.path.exists(paths["testbench"]):
            missing.append(f"Testbench: {paths['testbench']}")
        if not os.path.exists(paths["vectors_hex"]):
            missing.append(f"Vectors: {paths['vectors_hex']}")

    if missing:
        _log(state, f"ERROR: Missing input files: {missing}")
        return {
            "paths": paths,
            "pipeline_status": "error",
            "error_message": f"Missing input files: {missing}",
            "events": _emit(state, "error", detail=f"Missing files: {missing}"),
        }

    # Load agent modules
    try:
        _ensure_agents_loaded(paths["agents_dir"])
    except ImportError as e:
        _log(state, f"ERROR: Failed to import agents: {e}")
        return {
            "paths": paths,
            "pipeline_status": "error",
            "error_message": f"Agent import error: {e}",
            "events": _emit(state, "error", detail=str(e)),
        }

    # --- Detect pipeline_mode from path_definitions.json ---
    # Event-mode paths have "mode": "event" in their path def entry.
    # Missing field or any other value defaults to "cycle" (existing behavior).
    pipeline_mode = "cycle"
    try:
        import json as _json
        with open(paths["path_defs"], "r") as _f:
            _pdefs = _json.load(_f)
        for _p in _pdefs.get("paths", []):
            if _p.get("id") == scope:
                pipeline_mode = _p.get("mode", "cycle")
                break
    except (FileNotFoundError, KeyError, ValueError) as _e:
        _log(state, f"[init] Could not read mode from path_definitions.json: {_e}")
        pipeline_mode = "cycle"

    if pipeline_mode == "event":
        _log(state, f"Pipeline mode: EVENT (skipping refmodel + cycle-mode gen)")
        if not _AGENT_MODULES.get("event_spec"):
            _log(state, "ERROR: event-mode path requested but event agents not loaded")
            return {
                "paths": paths,
                "pipeline_mode": pipeline_mode,
                "pipeline_status": "error",
                "error_message": "event-mode agents missing (event_spec_agent, event_vector_gen, event_tb_codegen)",
                "events": _emit(state, "error", detail="event agents missing"),
            }
    else:
        _log(state, f"Pipeline mode: CYCLE (standard refmodel + parallel gen flow)")

    _log(state, "Initialization complete")
    return {
        "paths": paths,
        "pipeline_mode": pipeline_mode,
        "agents_loaded": True,
        "pipeline_status": "running",
        "current_stage": "init",
        "events": _emit(state, "info", detail=f"Initialization complete (mode={pipeline_mode})"),
    }


def node_connectivity_check(state: PipelineState) -> dict:
    """Stage 0: Static connectivity verification (pre-flight check).
    
    Verifies that all inter-block connections defined in path_definitions.json
    actually exist in the frontend-generated manifests with correct port names,
    widths, and directions.
    
    No LLM calls. No simulation. Runs in <1 second.
    
    Outcomes:
      - pass: All connections verified → continue to refmodel
      - warn: Some connections couldn't be checked (missing manifests) → continue
      - fail: Port mismatches found → abort pipeline (wiring bug in RTL)
    """
    paths = state["paths"]
    
    if state.get("skip_connectivity", False):
        _log(state, "Skipping connectivity check (--skip-connectivity)")
        events = _emit(state, "stage_skip", stage="connectivity_check")
        return {
            "connectivity_result": {"status": "skipped"},
            "current_stage": "connectivity_check",
            "events": events,
        }
    
    path_defs_path = paths.get("path_defs", "")
    frontend_root = paths.get("frontend_root", "")
    reports_dir = paths.get("reports_dir", ".")
    
    if not os.path.exists(path_defs_path):
        _log(state, f"WARNING: path_definitions.json not found at {path_defs_path}, skipping check")
        events = _emit(state, "stage_skip", stage="connectivity_check",
                       detail="path_definitions.json not found")
        return {
            "connectivity_result": {"status": "skipped", "reason": "path_defs_not_found"},
            "current_stage": "connectivity_check",
            "events": events,
        }
    
    if not os.path.isdir(frontend_root):
        _log(state, f"WARNING: Frontend root not found at {frontend_root}, skipping check")
        events = _emit(state, "stage_skip", stage="connectivity_check",
                       detail="frontend_root not found")
        return {
            "connectivity_result": {"status": "skipped", "reason": "frontend_root_not_found"},
            "current_stage": "connectivity_check",
            "events": events,
        }
    
    _log(state, "═" * 50)
    _log(state, "STAGE 0: Static Connectivity Check")
    _log(state, "═" * 50)
    
    events = _emit(state, "stage_start", stage="connectivity_check")
    
    try:
        import connectivity_checker as cc_mod
        
        checker = cc_mod.ConnectivityChecker(
            path_defs_path=path_defs_path,
            frontend_root=frontend_root,
            output_dir=reports_dir,
        )
        report = checker.run()
        
        status = report["status"]
        summary = report["summary"]
        
        _log(state, f"Connectivity: {status.upper()} "
             f"({summary['pass']} pass, {summary['fail']} fail, "
             f"{summary['warn']} warn, {summary['skip']} skip)")
        
        _save_report(reports_dir, "connectivity_report.json", report)
        
        events = _emit(
            {**state, "events": events}, "stage_complete",
            stage="connectivity_check", status=status,
            checks_pass=summary["pass"], checks_fail=summary["fail"],
            checks_warn=summary["warn"], checks_skip=summary["skip"],
        )
        
        if status == "fail":
            failed_conns = [cid for cid, s in report["connection_summary"].items()
                            if s == "fail"]
            # Only block if a failed connection is actually used by the current scope
            scope_conns = set()
            try:
                with open(os.path.join(state["paths"]["spec_dir"], "path_definitions.json")) as _f:
                    _pd = json.load(_f)
                for _p in _pd.get("paths", []):
                    if _p.get("id") == state["scope"]:
                        scope_conns = set(_p.get("connections_used", []))
                        break
            except Exception:
                pass
            scope_blockers = [c for c in failed_conns if c in scope_conns]
            if scope_blockers:
                error_msg = (f"Connectivity check failed: {len(scope_blockers)} connections "
                             f"used by this scope have port mismatches: {scope_blockers}")
                _log(state, f"BLOCKING: {error_msg}")
                return {
                    "connectivity_result": report,
                    "current_stage": "connectivity_check",
                    "pipeline_status": "failed",
                    "error_message": error_msg,
                    "events": events,
                }
            _log(state, f"Connectivity has {len(failed_conns)} failures but none affect this scope: {failed_conns}")
        
        return {
            "connectivity_result": report,
            "current_stage": "connectivity_check",
            "events": events,
        }
    
    except Exception as e:
        _log(state, f"Connectivity check ERROR: {e}")
        traceback.print_exc()
        # Non-blocking: if the checker itself crashes, warn but continue
        return {
            "connectivity_result": {"status": "error", "errors": [str(e)]},
            "current_stage": "connectivity_check",
            "events": _emit({**state, "events": events}, "error",
                            stage="connectivity_check", detail=str(e)),
        }


def node_refmodel(state: PipelineState) -> dict:
    """Stage 1: Generate the Python reference model."""
    paths = state["paths"]
    scope = state["scope"]

    _log(state, "═" * 50)
    _log(state, "STAGE 1: Reference Model Generation")
    _log(state, "═" * 50)

    events = _emit(state, "stage_start", stage="refmodel")

    mod = _AGENT_MODULES["refmodel"]
    _set_agent_globals(mod, state.get("api_key"), state.get("model_id"))

    try:
        agent = mod.RefModelAgent(
            spec_path=paths["spec"],
            scope=scope,
            output_dir=paths["refmodel_dir"],
        )
        result = agent.run()

        success = result["status"] in ("success", "success_after_fix")
        _log(state, f"Refmodel: {'PASSED' if success else 'FAILED'} ({result['status']})")

        # Save stage report
        _save_report(paths["reports_dir"], f"{scope}_refmodel_report.json", result)

        events = _emit(
            {**state, "events": events}, "stage_complete",
            stage="refmodel", status=result["status"], success=success,
        )

        if not success:
            return {
                "refmodel_result": result,
                "current_stage": "refmodel",
                "pipeline_status": "failed",
                "error_message": f"Refmodel generation failed: {result.get('errors', [])}",
                "events": events,
            }

        return {
            "refmodel_result": result,
            "current_stage": "refmodel",
            "events": events,
        }

    except Exception as e:
        _log(state, f"Refmodel ERROR: {e}")
        traceback.print_exc()
        return {
            "refmodel_result": {"status": "error", "errors": [str(e)]},
            "current_stage": "refmodel",
            "pipeline_status": "error",
            "error_message": str(e),
            "events": _emit({**state, "events": events}, "error", stage="refmodel", detail=str(e)),
        }


def node_parallel_gen(state: PipelineState) -> dict:
    """Stage 2+3: Run vector generation and testbench generation CONCURRENTLY.
    
    These two stages have no data dependency on each other:
      - Vectors need: spec + refmodel (both available after stage 1)
      - Testbench needs: manifest + spec (both static inputs)
    
    We use ThreadPoolExecutor to run them in parallel, then merge results.
    
    On retries, triage feedback is extracted from state['triage_result'] and
    passed to the testbench generator so the LLM can avoid repeating the
    same mistake.
    """
    paths = state["paths"]
    scope = state["scope"]

    _log(state, "═" * 50)
    _log(state, "STAGE 2+3: Vector Generation ∥ Testbench Generation (PARALLEL)")
    _log(state, "═" * 50)

    events = _emit(state, "stage_start", stage="parallel_gen",
                   detail="Running vectors + testbench concurrently")

    vec_mod = _AGENT_MODULES["vector_gen"]
    tb_mod = _AGENT_MODULES["testbench_gen"]
    _set_agent_globals(vec_mod, state.get("api_key"), state.get("model_id"))
    _set_agent_globals(tb_mod, state.get("api_key"), state.get("model_id"))

    # Check which sub-stages to actually run
    start_from = state.get("start_from", "refmodel")
    start_idx = ["refmodel", "vectors", "testbench", "simulate"].index(start_from)

    run_vectors = start_idx <= 1  # run if starting from refmodel or vectors
    run_testbench = start_idx <= 2  # run if starting from refmodel, vectors, or testbench

    # ── Extract triage feedback for retry context ──────────────────────
    # On retries, the triage agent has diagnosed the root cause. We pass
    # that diagnosis to the testbench generator so the LLM doesn't repeat
    # the same error
    tb_error_context = None
    vec_error_context = None
    triage = state.get("triage_result", {})
    retry_target = state.get("retry_target", "")

    if triage and triage.get("status") == "triaged":
        root_cause = triage.get("primary_root_cause", "")
        guilty = (triage.get("guilty_component") or "").lower()
        compiler_errors = triage.get("compiler_errors", "")
        
        # Build a concise error summary for the LLM
        error_parts = []
        if root_cause:
            error_parts.append(f"Root cause: {root_cause}")
        if compiler_errors:
            error_parts.append(f"Compiler errors:\n{compiler_errors}")
        
        error_summary = "\n".join(error_parts) if error_parts else None

        if retry_target == "testbench" or "testbench" in guilty or "tb" in guilty:
            tb_error_context = error_summary
            _log(state, f"  Injecting triage feedback into testbench gen ({len(tb_error_context or '')} chars)")
        elif retry_target == "vectors" or "vector" in guilty:
            vec_error_context = error_summary
            _log(state, f"  Injecting triage feedback into vector gen ({len(vec_error_context or '')} chars)")

    # Define worker functions
    def _run_vectors():
        if not run_vectors:
            _log(state, "Skipping vectors (start_from is later)")
            return {"status": "skipped"}
        _log(state, "  [Thread] Starting vector generation...")
        agent = vec_mod.VectorGenAgent(
            scope=scope,
            spec_path=paths["spec"],
            model_dir=paths["refmodel_dir"],
            output_dir=paths["scope_dir"],
        )
        return agent.run()

    def _run_testbench():
        if not run_testbench:
            _log(state, "Skipping testbench (start_from is later)")
            return {"status": "skipped"}
        _log(state, "  [Thread] Starting testbench generation...")
        agent = tb_mod.TestbenchGenAgent(
            scope=scope,
            manifest_path=paths["manifest"],
            spec_path=paths["spec"],
            output_dir=paths["scope_dir"],
        )
        return agent.generate(error_context=tb_error_context)

    # Execute in parallel
    vec_result = {"status": "skipped"}
    tb_result = {"status": "skipped"}
    errors = []

    with ThreadPoolExecutor(max_workers=2, thread_name_prefix="gen") as pool:
        futures = {}
        if run_vectors:
            futures[pool.submit(_run_vectors)] = "vectors"
        if run_testbench:
            futures[pool.submit(_run_testbench)] = "testbench"

        for future in as_completed(futures):
            name = futures[future]
            try:
                result = future.result()
                if name == "vectors":
                    vec_result = result
                    success = result["status"] == "success"
                    _log(state, f"  Vectors: {'PASSED' if success else 'FAILED'} "
                         f"({result['status']}, {result.get('vector_count', 0)} vectors)")
                    if not success:
                        errors.append(f"Vector generation failed: {result.get('errors', [])}")
                else:
                    tb_result = result
                    success = result["status"] == "success"
                    _log(state, f"  Testbench: {'PASSED' if success else 'FAILED'} ({result['status']})")
                    if not success:
                        errors.append(f"Testbench generation failed: {result.get('errors', [])}")
            except Exception as e:
                _log(state, f"  {name} ERROR: {e}")
                traceback.print_exc()
                if name == "vectors":
                    vec_result = {"status": "error", "errors": [str(e)]}
                else:
                    tb_result = {"status": "error", "errors": [str(e)]}
                errors.append(f"{name} error: {e}")

    # Save reports
    _save_report(paths["reports_dir"], f"{scope}_vectorgen_report.json", vec_result)
    _save_report(paths["reports_dir"], f"{scope}_tbgen_report.json", tb_result)

    events = _emit(
        {**state, "events": events}, "stage_complete",
        stage="parallel_gen",
        vectors_status=vec_result["status"],
        testbench_status=tb_result["status"],
        vector_count=vec_result.get("vector_count", 0),
    )

    update: dict = {
        "vectors_result": vec_result,
        "testbench_result": tb_result,
        "current_stage": "parallel_gen",
        "events": events,
    }

    if errors:
        update["pipeline_status"] = "failed"
        update["error_message"] = "; ".join(errors)

    return update
    # Define worker functions
    def _run_vectors():
        if not run_vectors:
            _log(state, "Skipping vectors (start_from is later)")
            return {"status": "skipped"}
        _log(state, "  [Thread] Starting vector generation...")
        agent = vec_mod.VectorGenAgent(
            scope=scope,
            spec_path=paths["spec"],
            model_dir=paths["refmodel_dir"],
            output_dir=paths["scope_dir"],
        )
        return agent.run()

    def _run_testbench():
        if not run_testbench:
            _log(state, "Skipping testbench (start_from is later)")
            return {"status": "skipped"}
        _log(state, "  [Thread] Starting testbench generation...")
        agent = tb_mod.TestbenchGenAgent(
            scope=scope,
            manifest_path=paths["manifest"],
            spec_path=paths["spec"],
            output_dir=paths["scope_dir"],
        )
        return agent.generate()

    # Execute in parallel
    vec_result = {"status": "skipped"}
    tb_result = {"status": "skipped"}
    errors = []

    with ThreadPoolExecutor(max_workers=2, thread_name_prefix="gen") as pool:
        futures = {}
        if run_vectors:
            futures[pool.submit(_run_vectors)] = "vectors"
        if run_testbench:
            futures[pool.submit(_run_testbench)] = "testbench"

        for future in as_completed(futures):
            name = futures[future]
            try:
                result = future.result()
                if name == "vectors":
                    vec_result = result
                    success = result["status"] == "success"
                    _log(state, f"  Vectors: {'PASSED' if success else 'FAILED'} "
                         f"({result['status']}, {result.get('vector_count', 0)} vectors)")
                    if not success:
                        errors.append(f"Vector generation failed: {result.get('errors', [])}")
                else:
                    tb_result = result
                    success = result["status"] == "success"
                    _log(state, f"  Testbench: {'PASSED' if success else 'FAILED'} ({result['status']})")
                    if not success:
                        errors.append(f"Testbench generation failed: {result.get('errors', [])}")
            except Exception as e:
                _log(state, f"  {name} ERROR: {e}")
                traceback.print_exc()
                if name == "vectors":
                    vec_result = {"status": "error", "errors": [str(e)]}
                else:
                    tb_result = {"status": "error", "errors": [str(e)]}
                errors.append(f"{name} error: {e}")

    # Save reports
    _save_report(paths["reports_dir"], f"{scope}_vectorgen_report.json", vec_result)
    _save_report(paths["reports_dir"], f"{scope}_tbgen_report.json", tb_result)

    events = _emit(
        {**state, "events": events}, "stage_complete",
        stage="parallel_gen",
        vectors_status=vec_result["status"],
        testbench_status=tb_result["status"],
        vector_count=vec_result.get("vector_count", 0),
    )

    update: dict = {
        "vectors_result": vec_result,
        "testbench_result": tb_result,
        "current_stage": "parallel_gen",
        "events": events,
    }

    if errors:
        update["pipeline_status"] = "failed"
        update["error_message"] = "; ".join(errors)

    return update


def node_simulate(state: PipelineState) -> dict:
    """Stage 4: Upload to Olympus and run Xcelium simulation."""
    paths = state["paths"]
    scope = state["scope"]

    if state.get("skip_sim", False):
        _log(state, "Skipping simulation (--skip-sim)")
        events = _emit(state, "stage_skip", stage="simulate")
        return {
            "sim_result": {"status": "skipped"},
            "current_stage": "simulate",
            "events": events,
        }

    _log(state, "═" * 50)
    _log(state, "STAGE 4: Simulation (Olympus + Xcelium)")
    _log(state, "═" * 50)

    events = _emit(state, "stage_start", stage="simulate")

    mod = _AGENT_MODULES["sim_runner"]

    # Get SSH password
    password = state.get("ssh_password") or os.environ.get("OLYMPUS_PASSWORD")
    if not password:
        password = getpass.getpass("Enter Olympus password: ")

    sim_agent = mod.CadenceSSHAgent()

    try:
        _log(state, "Connecting to Olympus...")
        sim_agent.connect(password=password)
        _log(state, f"Connected. Work dir: {sim_agent.work_dir}")

        result = sim_agent.run_scope(
            scope=scope,
            rtl_files=paths["rtl"] if isinstance(paths["rtl"], list) else [paths["rtl"]],
            tb_file=paths["testbench"],
            vector_file=paths["vectors_hex"],
            timeout=300,
        )

        # Save full log
        os.makedirs(paths["reports_dir"], exist_ok=True)
        with open(paths["sim_log"], "w") as f:
            f.write(result.get("stdout", ""))
            if result.get("stderr"):
                f.write("\n\n=== STDERR ===\n")
                f.write(result["stderr"])
        _log(state, f"Sim log: {paths['sim_log']}")

        # Save report 
        save_result = {k: v for k, v in result.items() if k not in ("stdout", "stderr")}
        _save_report(paths["reports_dir"], f"{scope}_simulate_report.json", save_result)

        success = result["status"] == "pass"
        _log(state, f"Simulation: {'PASSED' if success else 'FAILED'} "
             f"({result['status']}, {result.get('pass_count', 0)}/{result.get('total_tests', 0)})")

        sim_agent.clean_work_dir()

        events = _emit(
            {**state, "events": events}, "stage_complete",
            stage="simulate", status=result["status"], success=success,
            pass_count=result.get("pass_count", 0),
            fail_count=result.get("fail_count", 0),
            total_tests=result.get("total_tests", 0),
        )

        return {
            "sim_result": save_result,
            "current_stage": "simulate",
            "events": events,
        }

    except Exception as e:
        _log(state, f"Simulation ERROR: {e}")
        traceback.print_exc()
        return {
            "sim_result": {"status": "error", "errors": [str(e)]},
            "current_stage": "simulate",
            "pipeline_status": "error",
            "error_message": str(e),
            "events": _emit({**state, "events": events}, "error", stage="simulate", detail=str(e)),
        }
    finally:
        sim_agent.disconnect()


def node_evaluate(state: PipelineState) -> dict:
    """Decision node: check simulation result and decide next step.
    
    This node doesn't route — it just tags the state so the conditional
    edge function can make the routing decision.
    """
    sim_result = state.get("sim_result", {})
    sim_status = sim_result.get("status", "unknown")

    if sim_status == "pass":
        _log(state, "✓ Simulation PASSED — pipeline complete")
        return {
            "pipeline_status": "passed",
            "events": _emit(state, "pipeline_complete", status="passed"),
        }

    if sim_status == "skipped":
        _log(state, "Simulation skipped — marking as generated")
        return {
            "pipeline_status": "generated",
            "events": _emit(state, "pipeline_complete", status="generated"),
        }

    if sim_status in ("error",):
        _log(state, "Simulation had an infrastructure error — no triage possible")
        return {
            "pipeline_status": "error",
            "error_message": f"Simulation error: {sim_result.get('errors', [])}",
            "events": _emit(state, "pipeline_complete", status="error"),
        }

    # Failure — check if we have retries left
    retry_count = state.get("retry_count", 0)
    max_retries = state.get("max_retries", 2)

    if retry_count >= max_retries:
        _log(state, f"✗ Simulation FAILED — no retries remaining ({retry_count}/{max_retries})")
        return {
            "pipeline_status": "failed",
            "events": _emit(state, "pipeline_complete",
                            status="failed", reason="max_retries_exceeded"),
        }

    _log(state, f"✗ Simulation FAILED — will attempt triage (retry {retry_count+1}/{max_retries})")
    return {
        "pipeline_status": "needs_triage",
        "events": _emit(state, "info",
                        detail=f"Simulation failed, initiating triage (attempt {retry_count+1})"),
    }


def node_triage(state: PipelineState) -> dict:
    """Run the failure triage agent to diagnose root cause."""
    paths = state["paths"]
    scope = state["scope"]

    _log(state, "═" * 50)
    _log(state, "TRIAGE: Analyzing simulation failure")
    _log(state, "═" * 50)

    events = _emit(state, "triage_start")

    mod = _AGENT_MODULES["failure_triage"]
    _set_agent_globals(mod, state.get("api_key"), state.get("model_id"))

    try:
        _rtl_paths = paths["rtl"] if isinstance(paths["rtl"], list) else [paths["rtl"]]
        agent = mod.FailureTriageAgent(
            scope=scope,
            sim_log_path=paths["sim_log"],
            sim_report_path=os.path.join(paths["reports_dir"], f"{scope}_simulate_report.json"),
            testbench_path=paths["testbench"],
            refmodel_path=paths["refmodel"],
            vectors_hex_path=paths["vectors_hex"],
            vectors_json_path=paths["vectors_json"],
            spec_path=paths["spec"],
            output_dir=paths["reports_dir"],
            rtl_paths=_rtl_paths,
        )
        triage_report = agent.run()

        _log(state, f"Triage status: {triage_report.get('status', 'unknown')}")
        _log(state, f"Root cause: {triage_report.get('primary_root_cause', 'undetermined')}")
        _log(state, f"Guilty component: {triage_report.get('guilty_component', 'unknown')}")
        _log(state, f"Suggested action: {triage_report.get('suggested_action', 'unknown')}")

        # Determine retry target based on triage diagnosis
        retry_target = _determine_retry_target(triage_report, retry_count=state.get("retry_count", 0))
        _log(state, f"Retry target: {retry_target}")

        events = _emit(
            {**state, "events": events}, "triage_complete",
            root_cause=triage_report.get("primary_root_cause", "undetermined"),
            guilty_component=triage_report.get("guilty_component", "unknown"),
            is_rtl_bug=triage_report.get("is_rtl_bug"),
            retry_target=retry_target,
        )

        return {
            "triage_result": triage_report,
            "retry_target": retry_target,
            "retry_count": state.get("retry_count", 0) + 1,
            "events": events,
        }

    except Exception as e:
        _log(state, f"Triage ERROR: {e}")
        traceback.print_exc()
        return {
            "triage_result": {"status": "error", "error": str(e)},
            "retry_target": "none",
            "pipeline_status": "failed",
            "error_message": f"Triage failed: {e}",
            "events": _emit({**state, "events": events}, "error",
                            stage="triage", detail=str(e)),
        }


def node_route_fix(state: PipelineState) -> dict:
    """Prepare state for the retry loop based on triage diagnosis.
    
    This node emits a retry event. The actual routing back to the
    correct stage is handled by the conditional edge after this node.
    """
    target = state.get("retry_target", "none")
    retry_count = state.get("retry_count", 0)

    _log(state, f"Routing fix to: {target} (retry #{retry_count})")

    return {
        "current_stage": f"retry_{target}",
        "events": _emit(state, "retry", target=target, attempt=retry_count),
    }


# Routing / Conditional Edge Functions

def node_event_gen(state: PipelineState) -> dict:
    """Event-Mode Generation: spec -> vectors -> testbench (sequential).

    Runs the three event-mode agents in order, since they have data
    dependencies:
      1. event_spec_agent   reads path def + manifests + RTL, produces event_spec.json
      2. event_vector_gen   reads event_spec.json, produces <path_id>_vectors.hex
      3. event_tb_codegen   reads event_spec.json + wiring_template.sv, produces <path_id>_tb.sv

    On any stage failure, aborts and reports the error. Does not parallelize
    (the dependencies make it pointless) and does not use triage feedback
    (event-mode failures are typically schema/vector issues the agent-level
    validators catch directly, and the retry loop sends us back here as a
    whole with its own retry budget).
    """
    paths = state["paths"]
    scope = state["scope"]

    _log(state, "═" * 50)
    _log(state, "STAGE 2+3 (EVENT MODE): Spec -> Vectors -> TB Codegen")
    _log(state, "═" * 50)

    events = _emit(state, "stage_start", stage="event_gen",
                   detail="Event-mode generation pipeline")

    spec_mod = _AGENT_MODULES.get("event_spec")
    vec_mod = _AGENT_MODULES.get("event_vector")
    tb_mod = _AGENT_MODULES.get("event_tb")
    if not (spec_mod and vec_mod and tb_mod):
        return {
            "pipeline_status": "error",
            "error_message": "event-mode agents missing in _AGENT_MODULES",
            "events": events + _emit(state, "error", detail="event agents missing"),
            "current_stage": "event_gen",
        }

    generated_dir = os.path.join(paths["scope_dir"], "generated")
    os.makedirs(generated_dir, exist_ok=True)
    event_spec_path = os.path.join(generated_dir, "event_spec.json")
    wiring_path = os.path.join(generated_dir, "wiring_template.sv")

    # --- 1. event_spec_agent ---
    try:
        _log(state, "[event_gen] Running event_spec_agent")
        agent = spec_mod.EventSpecAgent(
            path_id=scope,
            path_defs_path=paths["path_defs"],
            frontend_root=paths["frontend_root"],
            output_dir=generated_dir,
        )
        spec = agent.generate(max_retries=state.get("max_retries", 2))
        agent.write(spec)
    except Exception as e:
        _log(state, f"[event_gen] event_spec_agent failed: {e}")
        return {
            "pipeline_status": "failed",
            "error_message": f"event_spec_agent: {e}",
            "events": events + _emit(state, "stage_fail", stage="event_spec", detail=str(e)),
            "current_stage": "event_gen",
        }

    # --- 2. event_vector_gen ---
    try:
        _log(state, "[event_gen] Running event_vector_gen")
        # RTL hint: first RTL file of the path (e.g. init_fsm.sv for path_08)
        rtl_hint = None
        if isinstance(paths["rtl"], list) and paths["rtl"]:
            rtl_hint = paths["rtl"][0]
        elif isinstance(paths["rtl"], str):
            rtl_hint = paths["rtl"]
        v_agent = vec_mod.EventVectorAgent(
            event_spec_path=event_spec_path,
            output_dir=paths["scope_dir"],
            rtl_hint_path=rtl_hint,
        )
        vectors = v_agent.generate(max_retries=state.get("max_retries", 2))
        v_agent.write(vectors)
    except Exception as e:
        _log(state, f"[event_gen] event_vector_gen failed: {e}")
        return {
            "pipeline_status": "failed",
            "error_message": f"event_vector_gen: {e}",
            "events": events + _emit(state, "stage_fail", stage="event_vector", detail=str(e)),
            "current_stage": "event_gen",
        }

    # --- 3. event_tb_codegen ---
    try:
        _log(state, "[event_gen] Running event_tb_codegen")
        if not os.path.exists(wiring_path):
            raise FileNotFoundError(
                f"wiring_template.sv not found at {wiring_path}. "
                f"Run path_scope_generator for {scope} first."
            )
        with open(event_spec_path) as _f:
            _spec = __import__("json").load(_f)
        with open(wiring_path) as _f:
            _wiring = _f.read()
        tb_sv = tb_mod.build_testbench(_spec, _wiring)
        tb_out = paths["testbench"]
        with open(tb_out, "w") as _f:
            _f.write(tb_sv)
        _log(state, f"[event_gen] Wrote {tb_out} ({len(tb_sv.splitlines())} lines)")
    except Exception as e:
        _log(state, f"[event_gen] event_tb_codegen failed: {e}")
        return {
            "pipeline_status": "failed",
            "error_message": f"event_tb_codegen: {e}",
            "events": events + _emit(state, "stage_fail", stage="event_tb", detail=str(e)),
            "current_stage": "event_gen",
        }

    _log(state, "[event_gen] All three stages complete")
    return {
        "pipeline_status": "running",
        "current_stage": "event_gen",
        "vectors_result": {"status": "generated", "source": "event_vector_gen"},
        "testbench_result": {"status": "generated", "source": "event_tb_codegen"},
        "events": events + _emit(state, "stage_ok", stage="event_gen"),
    }


def route_after_event_gen(state: PipelineState) -> str:
    """After event_gen, proceed to simulation or abort on failure."""
    if state.get("pipeline_status") in ("failed", "error"):
        return "finalize"
    return "simulate"


def route_after_init(state: PipelineState) -> str:
    """After init, always go to connectivity check (unless error)."""
    if state.get("pipeline_status") == "error":
        return "finalize"
    return "connectivity_check"


def route_after_connectivity_check(state: PipelineState) -> str:
    """After connectivity check, route to the appropriate start stage or abort."""
    if state.get("pipeline_status") in ("failed", "error"):
        return "finalize"

    # Event-mode paths skip refmodel + parallel_gen entirely.
    if state.get("pipeline_mode") == "event":
        if state.get("start_from", "refmodel") == "simulate":
            return "simulate"
        return "event_gen"

    start_from = state.get("start_from", "refmodel")
    if start_from == "refmodel":
        return "refmodel"
    elif start_from in ("vectors", "testbench"):
        return "parallel_gen"
    elif start_from == "simulate":
        return "simulate"
    return "refmodel"


def route_after_refmodel(state: PipelineState) -> str:
    """After refmodel, proceed to parallel gen or abort on failure."""
    if state.get("pipeline_status") in ("failed", "error"):
        return "finalize"
    return "parallel_gen"


def route_after_parallel_gen(state: PipelineState) -> str:
    """After parallel gen, proceed to simulation or abort."""
    if state.get("pipeline_status") in ("failed", "error"):
        return "finalize"
    return "simulate"


def route_after_evaluate(state: PipelineState) -> str:
    """After evaluate, decide: finish, triage, or give up."""
    status = state.get("pipeline_status", "")
    if status in ("passed", "generated", "error"):
        return "finalize"
    if status == "needs_triage":
        return "triage"
    # Default: failed with no retries
    return "finalize"


def route_after_triage(state: PipelineState) -> str:
    """After triage, route to the fix target or give up."""
    target = state.get("retry_target", "none")
    if target == "none" or state.get("pipeline_status") in ("failed", "error"):
        return "finalize"
    return "route_fix"


def route_after_fix_event_check(state: PipelineState) -> Optional[str]:
    """Helper: if in event mode, all retries go back to event_gen."""
    if state.get("pipeline_mode") == "event":
        return "event_gen"
    return None


def route_after_fix(state: PipelineState) -> str:
    """After route_fix, go back to the appropriate stage."""
    # Event-mode retries always restart at event_gen (not refmodel/parallel_gen)
    _em_target = route_after_fix_event_check(state)
    if _em_target is not None:
        return _em_target
    target = state.get("retry_target", "none")
    if target == "refmodel":
        return "refmodel"
    elif target in ("vectors", "testbench"):
        return "parallel_gen"
    # If triage couldn't determine target, just re-run parallel_gen
    return "parallel_gen"


# Triage → Retry Target Mapping

def _determine_retry_target(triage_report: dict, retry_count: int = 0) -> str:
    """Map triage diagnosis to the pipeline stage that should be re-run.
    
    Returns: 'refmodel', 'vectors', 'testbench', or 'none'
    """
    if triage_report.get("status") != "triaged":
        return "none"
    # Compile errors: allow one retry (testbench regen may fix it),
    # but if this is already a retry, stop, same error will repeat.
    category = (triage_report.get("category") or "").lower()
    if "compile" in category:
        if retry_count > 0:
            return "none"
    coverage = triage_report.get("coverage", {})
    if coverage.get("validation_level") in ("substantially_validated", "fully_validated"):
        return "none"
        
    guilty = (triage_report.get("guilty_component") or "").lower()
    action = (triage_report.get("suggested_action") or "").lower()
    is_rtl = triage_report.get("is_rtl_bug", False)
    is_verif = triage_report.get("is_verification_bug", False)

    # If it's an RTL bug, goes to frontend
    if is_rtl and not is_verif:
        return "none"

    # Map guilty components to retry targets
    if "refmodel" in guilty or "reference" in guilty:
        return "refmodel"
    if "testbench" in guilty or "tb" in guilty:
        return "testbench"
    if "vector" in guilty or "stimulus" in guilty:
        return "vectors"

    # Map suggested actions
    if "regen_refmodel" in action or "regenerate_refmodel" in action:
        return "refmodel"
    if "regen_testbench" in action or "regenerate_testbench" in action:
        return "testbench"
    if "regen_vectors" in action or "regenerate_vectors" in action:
        return "vectors"

    # Fallback: if it's a verification bug, try regenerating testbench
    if is_verif:
        return "testbench"

    return "none"


# Finalize Node
def node_finalize(state: PipelineState) -> dict:
    """Terminal node: save the orchestrator report and emit final event."""
    paths = state.get("paths", {})
    scope = state.get("scope", "unknown")
    status = state.get("pipeline_status", "unknown")

    _log(state, "═" * 50)
    _log(state, f"PIPELINE COMPLETE — Status: {status}")
    _log(state, "═" * 50)

    # Build final report
    report = {
        "scope": scope,
        "project_root": state.get("project_root", ""),
        "start_from": state.get("start_from", "refmodel"),
        "skip_sim": state.get("skip_sim", False),
        "max_retries": state.get("max_retries", 2),
        "timestamp": datetime.now().isoformat(),
        "overall_status": status,
        "retry_count": state.get("retry_count", 0),
        "stages": {
            "connectivity": state.get("connectivity_result", {}),
            "refmodel": state.get("refmodel_result", {}),
            "vectors": state.get("vectors_result", {}),
            "testbench": state.get("testbench_result", {}),
            "simulate": state.get("sim_result", {}),
            "triage": state.get("triage_result", {}),
        },
        "error_message": state.get("error_message", ""),
    }

    # Save to disk
    if paths.get("orchestrator_report"):
        os.makedirs(os.path.dirname(paths["orchestrator_report"]), exist_ok=True)
        with open(paths["orchestrator_report"], "w") as f:
            json.dump(report, f, indent=2)
        _log(state, f"Report saved: {paths['orchestrator_report']}")

    # Print summary
    _print_summary(state, report)

    return {
        "pipeline_status": status,
        "events": _emit(state, "pipeline_complete",
                        status=status,
                        retry_count=state.get("retry_count", 0),
                        report_path=paths.get("orchestrator_report", "")),
    }


# Report Helpers

def _save_report(reports_dir: str, filename: str, data: dict):
    """Save a JSON report to disk."""
    os.makedirs(reports_dir, exist_ok=True)
    path = os.path.join(reports_dir, filename)
    with open(path, "w") as f:
        json.dump(data, f, indent=2)


def _print_summary(state: PipelineState, report: dict):
    """Print a formatted pipeline summary to console."""
    scope = report.get("scope", "?")
    print()
    print("=" * 70)
    print(f"  LANGGRAPH ORCHESTRATOR SUMMARY — scope: {scope}")
    print("=" * 70)
    print(f"  Overall Status:  {report['overall_status']}")
    print(f"  Timestamp:       {report['timestamp']}")
    print(f"  Retries Used:    {report['retry_count']}/{report['max_retries']}")
    print()

    stage_names = ["connectivity", "refmodel", "vectors", "testbench", "simulate", "triage"]
    for stage in stage_names:
        result = report["stages"].get(stage, {})
        status = result.get("status", "not_run")

        if status in ("success", "success_after_fix", "pass"):
            icon = "✓"
        elif status == "skipped":
            icon = "–"
        elif status == "not_run" or not result:
            icon = " "
        else:
            icon = "✗"

        detail = ""
        if stage == "vectors" and "vector_count" in result:
            detail = f" ({result['vector_count']} vectors)"
        elif stage == "simulate":
            p = result.get("pass_count", 0)
            t = result.get("total_tests", 0)
            f_ = result.get("fail_count", 0)
            if t > 0:
                detail = f" ({p}/{t} passed, {f_} failed)"
        elif stage == "triage" and result.get("primary_root_cause"):
            detail = f" → {result['primary_root_cause'][:50]}"

        print(f"  [{icon}] {stage:12s}  {status}{detail}")

    if report.get("error_message"):
        print(f"\n  Error: {report['error_message']}")

    print()
    print(f"  Reports: {state.get('paths', {}).get('reports_dir', 'N/A')}")
    print("=" * 70)


# Graph Construction

def build_graph() -> StateGraph:
    """Construct and compile the LangGraph validation pipeline.
    
    Returns a compiled StateGraph ready for .invoke() or .stream().
    """
    builder = StateGraph(PipelineState)

    # --- Add nodes ---
    builder.add_node("init", node_init)
    builder.add_node("connectivity_check", node_connectivity_check)
    builder.add_node("refmodel", node_refmodel)
    builder.add_node("event_gen", node_event_gen)
    builder.add_node("parallel_gen", node_parallel_gen)
    builder.add_node("simulate", node_simulate)
    builder.add_node("evaluate", node_evaluate)
    builder.add_node("triage", node_triage)
    builder.add_node("route_fix", node_route_fix)
    builder.add_node("finalize", node_finalize)

    # --- Add edges ---

    # START → init
    builder.add_edge(START, "init")

    # init → (connectivity_check | finalize)
    builder.add_conditional_edges("init", route_after_init, {
        "connectivity_check": "connectivity_check",
        "finalize": "finalize",
    })

    # connectivity_check → (refmodel | event_gen | parallel_gen | simulate | finalize)
    builder.add_conditional_edges("connectivity_check", route_after_connectivity_check, {
        "refmodel": "refmodel",
        "event_gen": "event_gen",
        "parallel_gen": "parallel_gen",
        "simulate": "simulate",
        "finalize": "finalize",
    })

    # event_gen → (simulate | finalize)
    builder.add_conditional_edges("event_gen", route_after_event_gen, {
        "simulate": "simulate",
        "finalize": "finalize",
    })

    # refmodel → (parallel_gen | finalize)
    builder.add_conditional_edges("refmodel", route_after_refmodel, {
        "parallel_gen": "parallel_gen",
        "finalize": "finalize",
    })

    # parallel_gen → (simulate | finalize)
    builder.add_conditional_edges("parallel_gen", route_after_parallel_gen, {
        "simulate": "simulate",
        "finalize": "finalize",
    })

    # simulate → evaluate (always)
    builder.add_edge("simulate", "evaluate")

    # evaluate → (finalize | triage)
    builder.add_conditional_edges("evaluate", route_after_evaluate, {
        "finalize": "finalize",
        "triage": "triage",
    })

    # triage → (route_fix | finalize)
    builder.add_conditional_edges("triage", route_after_triage, {
        "route_fix": "route_fix",
        "finalize": "finalize",
    })

    # route_fix → (refmodel | parallel_gen | event_gen)  — the retry loop
    builder.add_conditional_edges("route_fix", route_after_fix, {
        "refmodel": "refmodel",
        "parallel_gen": "parallel_gen",
        "event_gen": "event_gen",
    })

    # finalize → END
    builder.add_edge("finalize", END)

    return builder.compile()


# =============================================================================
# Public API — for programmatic use by frontend/backend
# =============================================================================

class LangGraphOrchestrator:
    """High-level wrapper around the LangGraph pipeline.
    
    Provides two modes of execution:
      1. run()    — blocking, returns final report dict
      2. stream() — yields JSON events as the pipeline progresses
    
    Usage:
        orchestrator = LangGraphOrchestrator(
            scope="config_regs",
            project_root="~/Capstone/ecen403-llm-mc-1",
        )
        
        # Blocking mode
        report = orchestrator.run()
        
        # Streaming mode (for frontend)
        for event in orchestrator.stream():
            send_to_frontend(event)  # JSON event dict
    """

    def __init__(
        self,
        scope: str,
        project_root: str,
        skip_sim: bool = False,
        skip_connectivity: bool = False,
        start_from: str = "refmodel",
        max_retries: int = 2,
        api_key: Optional[str] = None,
        model_id: Optional[str] = None,
        ssh_password: Optional[str] = None,
    ):
        if scope not in SCOPE_CONFIG:
            # Try loading generated scope config from path_scope_generator output
            gen_config = os.path.join(
                os.path.abspath(project_root), "Validation", "scopes",
                scope, "generated", "scope_config.json"
            )
            if os.path.exists(gen_config):
                with open(gen_config) as f:
                    gen = json.load(f)
                if scope in gen:
                    SCOPE_CONFIG[scope] = gen[scope]
            else:
                raise ValueError(f"Unknown scope '{scope}'. No SCOPE_CONFIG entry and no generated config at {gen_config}")

        self.initial_state: PipelineState = {
            "scope": scope,
            "project_root": project_root,
            "skip_sim": skip_sim,
            "skip_connectivity": skip_connectivity,
            "start_from": start_from,
            "max_retries": max_retries,
            "api_key": api_key,
            "model_id": model_id,
            "ssh_password": ssh_password,
            "retry_count": 0,
            "retry_target": "",
            "pipeline_status": "running",
            "error_message": "",
            "events": [],
            "agents_loaded": False,
            "paths": {},
            "connectivity_result": {},
            "refmodel_result": {},
            "vectors_result": {},
            "testbench_result": {},
            "sim_result": {},
            "triage_result": {},
            "current_stage": "init",
        }

        self.graph = build_graph()

    def run(self) -> dict:
        """Execute the pipeline synchronously. Returns the final state."""
        final_state = self.graph.invoke(
            self.initial_state,
            config={"recursion_limit": 25},
        )
        return self._extract_report(final_state)

    def stream(self):
        """Execute the pipeline and yield events as they occur.
        
        Yields dicts with structure:
            {
                "type": "stage_start" | "stage_complete" | "triage_start" | ...,
                "timestamp": "ISO8601",
                "scope": "config_regs",
                "retry_count": 0,
                ...extra fields...
            }
        
        The frontend can consume these via SSE, WebSocket, or polling.
        """
        seen_events = 0
        for chunk in self.graph.stream(
            self.initial_state,
            config={"recursion_limit": 25},
            stream_mode="updates",
        ):
            # chunk is {node_name: state_update_dict}
            for node_name, update in chunk.items():
                events = update.get("events", [])
                # Yield only new events
                for event in events[seen_events:]:
                    event["_node"] = node_name
                    yield event
                seen_events = max(seen_events, len(events))

    def _extract_report(self, final_state: dict) -> dict:
        """Extract a clean report dict from the final graph state."""
        return {
            "scope": final_state.get("scope"),
            "overall_status": final_state.get("pipeline_status", "unknown"),
            "retry_count": final_state.get("retry_count", 0),
            "stages": {
                "connectivity": final_state.get("connectivity_result", {}),
                "refmodel": final_state.get("refmodel_result", {}),
                "vectors": final_state.get("vectors_result", {}),
                "testbench": final_state.get("testbench_result", {}),
                "simulate": final_state.get("sim_result", {}),
                "triage": final_state.get("triage_result", {}),
            },
            "error_message": final_state.get("error_message", ""),
            "events": final_state.get("events", []),
        }


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="DDR3 Memory Controller Validation — LangGraph Orchestrator",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Full pipeline with triage retries
  python3 langgraph_orchestrator.py --scope config_regs \\
      --project-root ~/Capstone/ecen403-llm-mc-1

  # Skip simulation (generate only)
  python3 langgraph_orchestrator.py --scope wb_port \\
      --project-root ~/path --skip-sim

  # Start from testbench (reuse existing refmodel + vectors)
  python3 langgraph_orchestrator.py --scope config_regs \\
      --project-root ~/path --start-from testbench

  # Stream events as JSON lines (for frontend/backend)
  python3 langgraph_orchestrator.py --scope config_regs \\
      --project-root ~/path --stream

  # Limit retries
  python3 langgraph_orchestrator.py --scope config_regs \\
      --project-root ~/path --max-retries 3
        """
    )

    parser.add_argument("--scope", required=True,
                        help="Validation scope to run")
    parser.add_argument("--project-root", required=True,
                        help="Path to project root (contains Frontend/ and Validation/)")
    parser.add_argument("--skip-sim", action="store_true",
                        help="Skip simulation stage (generate only)")
    parser.add_argument("--skip-connectivity", action="store_true",
                        help="Skip static connectivity check")
    parser.add_argument("--start-from", default="refmodel",
                        choices=["refmodel", "vectors", "testbench", "simulate"],
                        help="Start pipeline from this stage (default: refmodel)")
    parser.add_argument("--max-retries", type=int, default=2,
                        help="Max triage→retry cycles (default: 2)")
    parser.add_argument("--api-key", help="TAMU AI API key override")
    parser.add_argument("--model", help="LLM model ID override")
    parser.add_argument("--stream", action="store_true",
                        help="Output events as JSON lines (for frontend integration)")

    args = parser.parse_args()

    # Get SSH password from env
    ssh_password = os.environ.get("OLYMPUS_PASSWORD")

    orchestrator = LangGraphOrchestrator(
        scope=args.scope,
        project_root=args.project_root,
        skip_sim=args.skip_sim,
        skip_connectivity=args.skip_connectivity,
        start_from=args.start_from,
        max_retries=args.max_retries,
        api_key=args.api_key,
        model_id=args.model,
        ssh_password=ssh_password,
    )

    if args.stream:
        # Streaming mode: emit JSON lines for each event
        for event in orchestrator.stream():
            print(json.dumps(event), flush=True)
    else:
        # Blocking mode: run and print report
        report = orchestrator.run()

        # Exit code: 0 for pass/generated, 1 for failure
        if report["overall_status"] in ("passed", "generated"):
            sys.exit(0)
        else:
            sys.exit(1)


if __name__ == "__main__":
    main()