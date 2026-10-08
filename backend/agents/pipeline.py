#!/usr/bin/env python3
"""
pipeline.py — LangGraph Backend Orchestration
DDR3 Memory Controller: RTL -> GDSII via OpenROAD

Graph flow:
  intake_node -> packager_node -> runner_node -> repair_node -> reporter_node -> validator_node
                                      ^               |               |                |
                                      |         REPAIR_RETRY    NEEDS_TUNING    PASS + slack > 0.5ns
                                      |               |               |                |
                                      └───────────────┘       tuner_node       fmax_tuner_node
                                   (loop max 2x on               (loop            (--optimize_fmax)
                                    fixable errors)            max 3x)

  repair_node: Claude reads the error log, classifies the failure, and applies
               a targeted fix to config.mk before retrying. Max 2 attempts.
               Error classes: unpacked_array_port, pdn_too_small,
               routing_congestion, timing_too_tight, synthesis_error, unknown.

Validator checks (in order):
  1. DRC  -- hard fail: halts pipeline if violations > 0
  2. LVS  -- hard fail: halts pipeline if netlist vs layout mismatch
  3. STA  -- soft fail: logs worst slack, triggers tuner if WNS < STA_WNS_THRESHOLD_NS

Usage:
  python pipeline.py --bundle_dir /path/to/bundle
  python pipeline.py --bundle_dir /path/to/bundle --enable_autotuner
  python pipeline.py --bundle_dir /path/to/bundle --optimize_fmax
  python pipeline.py --bundle_dir /path/to/bundle --out_root /path/to/out --env_file .env
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import textwrap
import time
import urllib.request
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Dict, List, Literal, Optional, Tuple, Annotated
import operator

# ── LangGraph imports ────────────────────────────────────────────────────────
from langgraph.graph import StateGraph, END
from langgraph.graph.message import add_messages
from typing_extensions import TypedDict


# ═══════════════════════════════════════════════════════════════════════════════
# 0.  Shared utilities
# ═══════════════════════════════════════════════════════════════════════════════

def load_env_file(env_path: Path) -> None:
    if not env_path.exists():
        return
    for raw_line in env_path.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        k = k.strip()
        v = v.strip().strip('"').strip("'").strip()
        os.environ.setdefault(k, v)


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2))


def write_text(path: Path, s: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(s if s.endswith("\n") else (s + "\n"), encoding="utf-8")


def call_claude(api_key: str, model: str, system: str, user: str, max_tokens: int = 1000) -> str:
    url = "https://api.anthropic.com/v1/messages"
    payload = {
        "model": model,
        "max_tokens": max_tokens,
        "system": system,
        "messages": [{"role": "user", "content": user}],
    }
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("Content-Type", "application/json")
    req.add_header("x-api-key", api_key)
    req.add_header("anthropic-version", "2023-06-01")
    with urllib.request.urlopen(req, timeout=90) as resp:
        raw = resp.read().decode("utf-8")
    obj = json.loads(raw)
    return "\n".join(b.get("text", "") for b in obj.get("content", []) if b.get("type") == "text").strip()


# ═══════════════════════════════════════════════════════════════════════════════
# 1.  Graph State
# ═══════════════════════════════════════════════════════════════════════════════

class PipelineState(TypedDict):
    # ── Inputs ──────────────────────────────────────────────────────────────
    bundle_dir:         str
    mode:               str                    # contract | synth | build | full; see MODES
    out_root:           str
    env_file:           str
    enable_autotuner:   bool
    # What ties a finding to the RTL it ran on. Both come from the orchestrator; a
    # standalone block run has neither and says so when it emits.
    drop_id:            Optional[str]
    spec_revision:      Optional[str]

    # ── Agent outputs ────────────────────────────────────────────────────────
    intake_report:      Optional[Dict[str, Any]]
    packager_report:    Optional[Dict[str, Any]]
    runner_result:      Optional[Dict[str, Any]]   # exit_code, stage, artifacts, log
    reporter_summary:   Optional[Dict[str, Any]]   # metrics dict + markdown path
    validator_result:   Optional[Dict[str, Any]]   # drc/lvs/sta results
    tuner_config:       Optional[Dict[str, Any]]   # current tuning params
    tuner_history:      List[Dict[str, Any]]        # list of {config, metrics}
    best_result:        Optional[Dict[str, Any]]   # best metrics+config seen across tuner iterations

    # ── Fmax optimization ────────────────────────────────────────────────────
    optimize_fmax:           bool                   # --optimize_fmax flag
    fmax_iteration:          int                    # current Fmax tuner iteration
    fmax_history:            List[Dict[str, Any]]   # [{clock_period_ns, wns_ns, fmax_mhz}]
    current_clock_period_ns: Optional[float]        # active clock period being tried

    # ── Power optimization ────────────────────────────────────────────────────
    optimize_power:          bool                   # --optimize_power flag
    power_iteration:         int                    # current power tuner iteration
    power_history:           List[Dict[str, Any]]   # [{power_mw, wns_ns, changes}]

    # ── Tradeoff mode (both --optimize_fmax and --optimize_power) ────────────
    tradeoff_fmax_result:  Optional[Dict[str, Any]]  # saved Fmax phase results
    tradeoff_power_result: Optional[Dict[str, Any]]  # saved power phase results
    original_clock_period_ns: Optional[float]         # clock period before Fmax tuning

    # ── Repair node ──────────────────────────────────────────────────────────
    repair_iteration:   int                    # current repair attempt (max 2)
    repair_history:     List[Dict[str, Any]]   # [{error_class, fix_applied, result}]

    # ── Control ──────────────────────────────────────────────────────────────
    pipeline_status:    str                         # RUNNING | PASS | FAIL | NEEDS_TUNING
    current_node:       str
    error_message:      Optional[str]
    tuner_iteration:    int
    messages:           Annotated[List[str], operator.add]  # human-readable log


# ── Run modes ────────────────────────────────────────────────────────────────
# Declared tiers so an orchestrator can choose depth by name and know roughly what
# it costs. A full optimization run takes hours, which is far too slow to sit inside
# an automated loop; a contract check takes seconds. Naming the tiers lets the loop
# use a cheap one and keep optimization as a terminal stage.
#
#   contract  seconds   manifest and RTL satisfy the interface. No Docker, no layout.
#   synth     minutes   the RTL synthesizes. Stops after ORFS 'synth'. No sign-off.
#   build     ~1 hour   reaches a clean signed-off layout. DRC, LVS, pin audit, STA.
#   full      hours     build plus PPA optimization. Terminal stage, runs once.
#
# make_target None means the ORFS default (the whole flow through GDSII).
MODES: Dict[str, Dict[str, Any]] = {
    "contract": {"runs_orfs": False, "make_target": None,    "signoff": False,
                 "optimize": False, "cost": "seconds"},
    "synth":    {"runs_orfs": True,  "make_target": "synth", "signoff": False,
                 "optimize": False, "cost": "minutes"},
    "build":    {"runs_orfs": True,  "make_target": None,    "signoff": True,
                 "optimize": False, "cost": "~1 hour for 11 blocks"},
    "full":     {"runs_orfs": True,  "make_target": None,    "signoff": True,
                 "optimize": True,  "cost": "hours"},
}
DEFAULT_MODE = "build"


def mode_of(state: "PipelineState") -> Dict[str, Any]:
    """Mode settings for this run, defaulting to build if unset or unknown."""
    return MODES.get(state.get("mode") or DEFAULT_MODE, MODES[DEFAULT_MODE])


MAX_TUNER_ITERATIONS  = 3     # Max failure-tuner iterations
MAX_FMAX_ITERATIONS   = 3     # Max Fmax-optimization iterations
MAX_REPAIR_ITERATIONS = 2     # Max repair attempts before giving up
MAX_POWER_ITERATIONS  = 3     # Max power-optimization iterations
FMAX_WNS_THRESHOLD_NS = 0.5   # Min positive WNS to trigger Fmax optimization

# STA sign-off threshold: WNS must be >= this value to pass (soft fail below)
STA_WNS_THRESHOLD_NS = 0.0
# OpenSTA reports slack as 1e+39 when there is nothing to time (no clock, or no
# constrained paths). A slack this large means "no timing paths", not a pass.
STA_NO_PATHS_NS = 1e30


# ═══════════════════════════════════════════════════════════════════════════════
# 2.  Node implementations
# ═══════════════════════════════════════════════════════════════════════════════

# ── 2a. Intake Node ──────────────────────────────────────────────────────────

def intake_node(state: PipelineState) -> PipelineState:
    """Run intake_agent.py as a subprocess and capture its report."""
    bundle_dir = Path(state["bundle_dir"])
    out_root   = Path(state["out_root"])
    env_file   = Path(state["env_file"])
    out_dir    = (out_root / "intake" / bundle_dir.name).resolve()

    print("[intake] Running intake validation...")

    result = subprocess.run(
        [
            sys.executable, "intake_agent.py",
            "--bundle_dir", str(bundle_dir),
            "--out_dir",    str(out_dir.resolve()),
            "--env_file",   str(env_file),
        ],
        capture_output=True, text=True,
        cwd=Path(__file__).parent,
    )

    report_path = out_dir / "intake_report.json"
    intake_report: Dict[str, Any] = {}

    if report_path.exists():
        try:
            intake_report = json.loads(report_path.read_text())
        except Exception as e:
            intake_report = {"status": "FAIL", "errors": [{"message": f"Could not parse intake_report.json: {e}"}]}
    else:
        intake_report = {
            "status": "FAIL",
            "errors": [{"message": f"intake_report.json not produced. stderr: {result.stderr[:500]}"}],
        }

    status = intake_report.get("status", "FAIL")
    msg = f"[intake] Status={status}  errors={len(intake_report.get('errors', []))}  warnings={len(intake_report.get('warnings', []))}"
    print(msg)

    pipeline_ok = status in ("PASS", "PASS_WITH_WARNINGS")

    return {
        **state,
        "intake_report":   intake_report,
        "current_node":    "intake",
        "pipeline_status": "RUNNING" if pipeline_ok else "FAIL",
        "error_message":   None if pipeline_ok else f"Intake failed: {status}",
        "messages":        [msg],
    }


# ── 2b. Packager Node ────────────────────────────────────────────────────────

def packager_node(state: PipelineState) -> PipelineState:
    """Run packager_agent.py as a subprocess."""
    bundle_dir      = Path(state["bundle_dir"])
    out_root        = Path(state["out_root"])
    env_file        = Path(state["env_file"])
    intake_out_dir  = (out_root / "intake" / bundle_dir.name).resolve()
    intake_report   = intake_out_dir / "intake_report.json"
    out_dir         = (out_root / "package" / bundle_dir.name).resolve()

    print("[packager] Running packager...")

    result = subprocess.run(
        [
            sys.executable, "packager_agent.py",
            "--bundle_dir",    str(bundle_dir),
            "--intake_report", str(intake_report.resolve()),
            "--out_dir",       str(out_dir.resolve()),
            "--env_file",      str(env_file),
        ],
        capture_output=True, text=True,
        cwd=Path(__file__).parent,
    )

    report_path = out_dir / "packager_report.json"
    packager_report: Dict[str, Any] = {}

    if report_path.exists():
        try:
            packager_report = json.loads(report_path.read_text())
        except Exception as e:
            packager_report = {"status": "FAIL", "errors": [{"message": f"Could not parse packager_report.json: {e}"}]}
    else:
        packager_report = {
            "status": "FAIL",
            "errors": [{"message": f"packager_report.json not produced. stderr: {result.stderr[:500]}"}],
        }

    # Also load the packaged manifest so runner has design_dir
    packaged_manifest_path = out_dir / "packaged_manifest.json"
    if packaged_manifest_path.exists():
        try:
            packaged_manifest = json.loads(packaged_manifest_path.read_text())
            packager_report["packaged_manifest"] = packaged_manifest
        except Exception:
            pass

    status = packager_report.get("status", "FAIL")
    msg = f"[packager] Status={status}  errors={len(packager_report.get('errors', []))}"
    print(msg)

    pipeline_ok = status in ("PASS", "PASS_WITH_WARNINGS")

    return {
        **state,
        "packager_report": packager_report,
        "current_node":    "packager",
        "pipeline_status": "RUNNING" if pipeline_ok else "FAIL",
        "error_message":   None if pipeline_ok else f"Packager failed: {status}",
        "messages":        [msg],
    }


# ── 2c. OpenROAD Runner Node ─────────────────────────────────────────────────

# Host and container clocks are shared under Docker Desktop, but allow a little
# slack so a marginally-early timestamp does not fail an otherwise good run.
GDS_CLOCK_SKEW_S = 120


def _gds_is_from_this_run(gds_path: Path, def_path: Path, run_started: float) -> Tuple[bool, str]:
    """Did THIS run write this GDS?

    Two independent tests, because either alone can be fooled:
      - host clock: a GDS older than the moment make launched is left over.
      - same-run consistency: the GDS is written after 6_final.def, so a GDS
        predating the DEF means the merge step never re-ran. This one survives
        any host/container clock skew, since one container writes both files.
    """
    gds_mtime = gds_path.stat().st_mtime
    if gds_mtime < run_started - GDS_CLOCK_SKEW_S:
        age_min = (run_started - gds_mtime) / 60.0
        return False, f"written {age_min:.0f} min before this run started"
    if def_path.exists() and gds_mtime < def_path.stat().st_mtime:
        return False, f"older than {def_path.name}, so the GDS merge never ran"
    return True, ""


def runner_node(state: PipelineState) -> PipelineState:
    """
    Execute OpenROAD Flow Scripts (ORFS) via Docker.
    Copies key artifacts on success/failure and logs exit status.
    """
    out_root        = Path(state["out_root"])
    packager_report = state.get("packager_report") or {}
    tuner_config    = state.get("tuner_config")

    # Resolve design_dir and ORFS info from packager
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    packager_resolved = packaged_manifest.get("packager", {}).get("resolved", {})

    design_dir  = packager_resolved.get("orfs_design_dir")
    orfs_dir    = packager_resolved.get("orfs_dir") or os.environ.get("ORFS_DIR", "").strip()
    platform    = packager_resolved.get("platform", os.environ.get("PLATFORM", "sky130hd"))
    design_name = packager_resolved.get("design_name", "design")

    runner_out = out_root / "runner" / design_name
    runner_out.mkdir(parents=True, exist_ok=True)

    if not design_dir or not orfs_dir:
        msg = "[runner] ERROR: design_dir or orfs_dir not resolved from packager report."
        print(msg)
        return {
            **state,
            "runner_result":   {"exit_code": -1, "error": msg, "artifacts": {}},
            "current_node":    "runner",
            "pipeline_status": "FAIL",
            "error_message":   msg,
            "messages":        [msg],
        }

    design_dir_path = Path(design_dir)
    orfs_dir_path   = Path(orfs_dir)
    flow_dir        = orfs_dir_path / "flow"
    rel_cfg         = f"designs/{platform}/{design_name}/config.mk"

    # Apply tuner config overrides if present (append to config.mk)
    if tuner_config:
        _apply_tuner_overrides(design_dir_path / "config.mk", tuner_config)

    jobs = (os.environ.get("MAKE_JOBS") or "").strip()
    jobs_arg = jobs if jobs.startswith("-j") else (f"-j{jobs}" if jobs else "-j1")

    # ── Docker command ──────────────────────────────────────────────────────
    docker_image = os.environ.get("ORFS_DOCKER_IMAGE", "openroad/orfs:latest")
    use_docker   = os.environ.get("USE_DOCKER", "1").strip() == "1"

    # An explicit ORFS target stops the flow early; no target means the default,
    # which is the whole flow through GDSII. This is what makes the synth tier
    # minutes rather than an hour.
    make_target = mode_of(state)["make_target"]
    target_arg = f" {make_target}" if make_target else ""

    if use_docker:
        design_mount_src = str(design_dir_path).replace("\\", "/")
        orfs_results = str(orfs_dir_path / "flow" / "results").replace("\\", "/")
        orfs_reports = str(orfs_dir_path / "flow" / "reports").replace("\\", "/")
        orfs_logs = str(orfs_dir_path / "flow" / "logs").replace("\\", "/")
        bash_cmd = (
            f"sed -i 's/\\r//' /OpenROAD-flow-scripts/flow/designs/{platform}/{design_name}/config.mk && "
            f"sed -i 's/\\r//' /OpenROAD-flow-scripts/flow/designs/{platform}/{design_name}/constraint.sdc && "
            f"make {jobs_arg} DESIGN_CONFIG=designs/{platform}/{design_name}/config.mk{target_arg} 2>&1"
        )
        cmd = [
            "docker", "run", "--rm",
            "-v", f"{design_mount_src}:/OpenROAD-flow-scripts/flow/designs/{platform}/{design_name}",
            "-v", f"{orfs_results}:/OpenROAD-flow-scripts/flow/results",
            "-v", f"{orfs_reports}:/OpenROAD-flow-scripts/flow/reports",
            "-v", f"{orfs_logs}:/OpenROAD-flow-scripts/flow/logs",
            "-w", "/OpenROAD-flow-scripts/flow",
            docker_image,
            "bash", "-c", bash_cmd
        ]
    else:
        cmd = ["bash", "-c", f"cd {flow_dir} && make {jobs_arg} DESIGN_CONFIG={rel_cfg}{target_arg} 2>&1"]
    if mode_of(state)["runs_orfs"]:
        print(f"[runner] Executing: {' '.join(cmd[:6])}")

    log_path = runner_out / "run.log"

    # contract mode stops here: the interface has been checked by intake and the
    # packager, and nothing below produces evidence about it. Skipping ORFS is the
    # entire point of the tier — it is what makes it cheap enough for a loop.
    if not mode_of(state)["runs_orfs"]:
        msg = (f"[runner] mode={state.get('mode', DEFAULT_MODE)} — skipping ORFS; "
               f"intake and packaging validated the interface.")
        print(msg)
        write_text(log_path, msg + "\n")
        return {
            **state,
            "runner_result": {"exit_code": 0, "failed_stage": None, "log_path": str(log_path),
                              "artifacts": {}, "tuner_iter": state.get("tuner_iteration", 0),
                              "orfs_dir": str(orfs_dir_path), "platform": platform,
                              "design_name": design_name, "gds_exit_override": None,
                              "skipped": "mode"},
            "current_node": "runner", "pipeline_status": "RUNNING",
            "error_message": None, "messages": [msg],
        }

    run_started = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=7200)
        combined_log = proc.stdout + ("\n" + proc.stderr if proc.stderr else "")
        write_text(log_path, combined_log)
        exit_code = proc.returncode
    except subprocess.TimeoutExpired:
        exit_code = -2
        combined_log = "ERROR: OpenROAD run timed out after 3600s"
        write_text(log_path, combined_log)
    except Exception as e:
        exit_code = -3
        combined_log = f"ERROR launching runner: {e}"
        write_text(log_path, combined_log)

    # ── Ground-truth pass/fail: only a GDS from THIS run overrides the exit code ──
    # ORFS make can exit non-zero from a late cosmetic failure (a log rename, a
    # warning promoted to an error) even though the flow produced a complete
    # layout, so a finished GDS is allowed to override that. A GDS left over from
    # an EARLIER run proves nothing: on 2026-09-17 make died at 3_1_place, the GDS
    # merge never ran, and 10 of 11 blocks were signed off against week-old
    # geometry because this check only asked whether the file existed.
    results_base = orfs_dir_path / "flow" / "results" / platform / design_name / "base"
    gds_path = results_base / "6_final.gds"
    gds_override: Optional[Dict[str, Any]] = None
    # Only a mode that runs the whole flow can be rescued by a finished GDS. In
    # synth mode no GDS is expected, so one on disk is necessarily from an earlier
    # run and must never excuse a failure.
    if make_target is None and exit_code != 0 and gds_path.exists():
        fresh, why = _gds_is_from_this_run(gds_path, results_base / "6_final.def", run_started)
        if fresh:
            gds_override = {"original_exit_code": exit_code, "gds": str(gds_path)}
            print(f"[runner] exit_code={exit_code}, but 6_final.gds was written by this run "
                  f"— flow completed; treating as success.")
            exit_code = 0
        else:
            print(f"[runner] exit_code={exit_code} and 6_final.gds is STALE ({why}) — "
                  f"run FAILED. Refusing to accept a leftover layout as proof of success.")

    # Detect failed stage from log
    failed_stage = _detect_failed_stage(combined_log) if exit_code != 0 else None

    # Copy artifacts
    artifacts = _collect_artifacts(orfs_dir_path, platform, design_name, runner_out, run_started)

    runner_result = {
        "exit_code":    exit_code,
        "failed_stage": failed_stage,
        "log_path":     str(log_path),
        "artifacts":    artifacts,
        "tuner_iter":   state.get("tuner_iteration", 0),
        # Expose resolved names for validator
        "orfs_dir":     str(orfs_dir_path),
        "platform":     platform,
        "design_name":  design_name,
        # Records a non-zero make exit that a this-run GDS overrode, so a run that
        # "passed" this way is never silently indistinguishable from a clean one.
        "gds_exit_override": gds_override,
    }

    pipeline_ok = exit_code == 0
    msg = f"[runner] exit_code={exit_code}  failed_stage={failed_stage}  artifacts={list(artifacts.keys())}"
    print(msg)

    return {
        **state,
        "runner_result":   runner_result,
        "current_node":    "runner",
        "pipeline_status": "RUNNING",  # reporter/validator decide final status
        "error_message":   None if pipeline_ok else f"Runner exit_code={exit_code}, stage={failed_stage}",
        "messages":        [msg],
    }


def _apply_tuner_overrides(config_mk_path: Path, tuner_config: Dict[str, Any]) -> None:
    """Append tuner make variable overrides to config.mk."""
    if not config_mk_path.exists():
        return
    override_lines = ["\n# ── Auto-Tuner overrides ────────────────────────────────"]
    for k, v in tuner_config.items():
        override_lines.append(f"export {k} := {v}")
    with open(config_mk_path, "a") as f:
        f.write("\n".join(override_lines) + "\n")


def _detect_failed_stage(log: str) -> Optional[str]:
    """
    Heuristic stage detection from ORFS log output.
    Requires an error signal (Error/FAILED/cannot/killed) to appear
    within 10 lines of a stage keyword so we don't misfire on stages
    that simply appear in a successful run's output.
    """
    stage_keywords = [
        ("synth",     r"(synthesis|yosys|SYNTH)"),
        ("floorplan", r"(floorplan|FLOORPLAN|initialize_floorplan)"),
        ("place",     r"(placement|PLACE|global_placement|detailed_placement)"),
        ("cts",       r"(clock_tree|CTS|clock_tree_synthesis)"),
        ("route",     r"(routing|ROUTE|global_route|detailed_route)"),
        ("finish",    r"(finish|FINISH|write_gds|gds)"),
    ]
    error_signal = re.compile(
        r"(Error|ERROR|FAILED|fatal|cannot|killed|Segmentation fault|make\[\d+\].*Error)",
        re.IGNORECASE,
    )

    lines = log.splitlines()

    # Scan lines in reverse to find the last error signal, then check
    # which stage keyword appears within a +-10-line window around it.
    for i in range(len(lines) - 1, -1, -1):
        if error_signal.search(lines[i]):
            window = "\n".join(lines[max(0, i - 10): i + 10])
            for stage, pattern in reversed(stage_keywords):
                if re.search(pattern, window, re.IGNORECASE):
                    return stage
            return "unknown"

    return "unknown"


def _collect_artifacts(orfs_dir: Path, platform: str, design_name: str, out_dir: Path,
                       newer_than: Optional[float] = None) -> Dict[str, str]:
    """Copy key ORFS output artifacts to runner_out directory.

    `newer_than` restricts the list to files this run actually wrote. Without it
    the ORFS tree hands back whatever is lying there: a synth-tier run on
    2026-10-01 reported a gds, def and spef from 09-29, because those files
    exist and nothing checked when. An orchestrator reading artifacts.gds would
    have been handed a two-day-old layout.
    """
    artifacts: Dict[str, str] = {}
    cutoff = None if newer_than is None else newer_than - GDS_CLOCK_SKEW_S
    results_base = orfs_dir / "flow" / "results" / platform / design_name / "base"
    reports_base = orfs_dir / "flow" / "reports" / platform / design_name / "base"
    logs_base    = orfs_dir / "flow" / "logs"    / platform / design_name / "base"

    artifact_map = {
        "gds":        results_base / "6_final.gds",
        "def":        results_base / "6_final.def",
        "spef":       results_base / "6_final.spef",
        "synth_v":    results_base / "6_final.v",
        "timing_rpt": reports_base / "6_finish.rpt",
        "area_rpt":   reports_base / "synth_stat.txt",
        "drc_rpt":    reports_base / "5_route_drc.rpt",
        "route_rpt":  reports_base / "5_global_route.rpt",
        "place_rpt":  reports_base / "3_detailed_place.rpt",
    }

    for key, src in artifact_map.items():
        if src.exists():
            if cutoff is not None and src.stat().st_mtime < cutoff:
                print(f"[runner] stale, not an artifact of this run: {key} ({src.name})")
                continue
            dst = out_dir / src.name
            try:
                shutil.copy2(src, dst)
                artifacts[key] = str(dst)
            except Exception as e:
                print(f"[runner] copy failed {key}: {src} -> {dst}: {e}")
        else:
            print(f"[runner] not found {key}: {src}")

    if logs_base.exists():
        for log_file in list(logs_base.glob("*.log")) + list(logs_base.glob("*.json")):
            if cutoff is not None and log_file.stat().st_mtime < cutoff:
                continue
            dst = out_dir / "logs" / log_file.name
            dst.parent.mkdir(parents=True, exist_ok=True)
            try:
                shutil.copy2(log_file, dst)
                artifacts[f"log_{log_file.stem}"] = str(dst)
            except Exception:
                pass

    return artifacts


# ── 2d. Results Reporter Node ────────────────────────────────────────────────

def reporter_node(state: PipelineState) -> PipelineState:
    """
    Parse ORFS outputs into a clean summary.
    Uses Claude to generate a human-readable report.
    Detects common failure modes.
    """
    out_root        = Path(state["out_root"])
    runner_result   = state.get("runner_result") or {}
    packager_report = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    design_name     = packaged_manifest.get("packager", {}).get("resolved", {}).get("design_name", "design")

    reporter_out  = out_root / "reporter" / design_name
    reporter_out.mkdir(parents=True, exist_ok=True)

    artifacts    = runner_result.get("artifacts", {})
    exit_code    = runner_result.get("exit_code", -1)
    failed_stage = runner_result.get("failed_stage")
    log_path     = runner_result.get("log_path")

    # Parse metrics from available reports
    metrics = _parse_metrics(artifacts, log_path)

    # A failed run leaves the PREVIOUS run's reports in the ORFS tree, and
    # _parse_metrics cannot tell the two apart — the numbers it returns look
    # entirely plausible. On 2026-09-29 a Docker outage failed four blocks and the
    # reporter handed back their timing from runs a week earlier, at a different
    # clock period. A run that did not pass has no metrics; say so rather than
    # reporting someone else's. The values are kept under `withheld_values` so the
    # failure is still debuggable, but nothing downstream can mistake them for this
    # run's results.
    # The same hazard from the other direction: a gate tier that runs no ORFS exits 0,
    # so the test above does not fire, while _parse_metrics still finds the previous
    # run's reports in the tree and returns them. On 2026-10-08 a contract-mode run of
    # all 11 blocks reported WNS, area, Fmax and power taken from artifacts dated
    # 2026-09-24 - laundered through a summary file written seconds earlier, so a
    # freshness check on the file cannot catch it. Metrics belong to the run that
    # produced them, and a run that built nothing produced none.
    ran_orfs = mode_of(state)["runs_orfs"]
    if exit_code != 0 or not ran_orfs:
        stale = {k: v for k, v in metrics.items() if v is not None}
        metrics = {k: None for k in metrics}
        if stale:
            metrics["withheld_values"] = stale
        metrics["metrics_withheld"] = (
            "run failed; the ORFS reports on disk may describe an earlier run"
            if exit_code != 0 else
            f"mode '{state.get('mode') or DEFAULT_MODE}' runs no ORFS; "
            f"any reports on disk describe an earlier run")

    metrics["exit_code"]    = exit_code
    metrics["failed_stage"] = failed_stage
    metrics["run_passed"]   = exit_code == 0

    # Detect failure mode
    failure_analysis = _analyze_failure(metrics, log_path) if exit_code != 0 else None

    summary = {
        "design_name":      design_name,
        "run_passed":       exit_code == 0,
        "metrics":          metrics,
        "failure_analysis": failure_analysis,
        "artifacts":        artifacts,
    }

    write_json(reporter_out / "reporter_summary.json", summary)

    # Claude-generated narrative report. Gate tiers exist to be fast and are read by
    # an orchestrator, not a person, so the round trip is skipped there.
    if not mode_of(state)["signoff"]:
        write_text(reporter_out / "report.md", _build_fallback_report(summary))
        return {**state, "reporter_summary": summary, "current_node": "reporter",
                "pipeline_status": "RUNNING",
                "messages": [f"[reporter] run_passed={summary['run_passed']} "
                             f"(mode={state.get('mode', DEFAULT_MODE)}, narrative skipped)"]}

    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model   = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    if api_key:
        system = (
            "You are an ASIC backend results reporter. Produce a concise, professional "
            "markdown report summarizing an OpenROAD flow run. Include: pass/fail status, "
            "key metrics (timing, area, utilization), identified failure modes, and "
            "actionable next steps. Be specific. Do not invent data not present."
        )
        user = f"""
OpenROAD Flow Results:

DESIGN: {design_name}
EXIT CODE: {exit_code}
FAILED STAGE: {failed_stage or 'N/A'}

METRICS:
{json.dumps(metrics, indent=2)}

FAILURE ANALYSIS:
{json.dumps(failure_analysis, indent=2) if failure_analysis else 'N/A - run passed'}

ARTIFACTS AVAILABLE: {list(artifacts.keys())}
""".strip()
        try:
            md = call_claude(api_key, model, system, user, max_tokens=1000)
        except Exception as e:
            md = f"# Reporter Summary\n\n_Claude call failed: {e}_\n\n```json\n{json.dumps(summary, indent=2)}\n```"
    else:
        md = _build_fallback_report(summary)

    write_text(reporter_out / "report.md", md)
    summary["report_md_path"] = str(reporter_out / "report.md")

    msg = f"[reporter] run_passed={exit_code==0}  wns={metrics.get('wns_ns', 'N/A')}  utilization={metrics.get('utilization_pct', 'N/A')}%"
    print(msg)

    # Reporter always passes to validator next; validator owns final status decision
    return {
        **state,
        "reporter_summary": summary,
        "current_node":     "reporter",
        "pipeline_status":  "RUNNING",
        "messages":         [msg],
    }


def _parse_metrics(artifacts: Dict[str, str], log_path: Optional[str]) -> Dict[str, Any]:
    metrics: Dict[str, Any] = {}

    if log_path:
        report_json = Path(log_path).parent / "logs" / "6_report.json"
        if report_json.exists():
            try:
                data = json.loads(report_json.read_text(errors="ignore"))
                # None (not 0) when a key is missing: an unknown slack must not read as
                # 0 ns and pass STA. _check_sta reports it as NOT VERIFIED.
                metrics["wns_ns"]          = data.get("finish__timing__setup__ws")
                metrics["tns_ns"]          = data.get("finish__timing__setup__tns")
                metrics["worst_slack_ns"]  = data.get("finish__timing__setup__ws")
                fmax_hz = data.get("finish__timing__fmax")
                metrics["fmax_mhz"]        = round(fmax_hz / 1e6, 2) if fmax_hz is not None else None
                if metrics["wns_ns"] is not None and metrics["wns_ns"] >= STA_NO_PATHS_NS:
                    # nothing was timed: keep no fake slack or Fmax in the metrics
                    metrics.update(wns_ns=None, tns_ns=None, worst_slack_ns=None,
                                   fmax_mhz=None, timing_paths=False)
                else:
                    metrics["timing_paths"] = True if metrics["wns_ns"] is not None else None
                metrics["utilization_pct"] = round(data.get("finish__design__instance__utilization", 0) * 100, 2)
                metrics["area_um2"]        = data.get("finish__design__core__area", 0)
                metrics["die_area_um2"]    = data.get("finish__design__die__area", 0)
                metrics["cell_count"]      = data.get("finish__design__instance__count__stdcell", 0)
                metrics["power_mw"]        = round(data.get("finish__power__total", 0) * 1000, 4)
                # flow error count only; DRC is checked for real in validator_node
                metrics["flow_errors"]     = data.get("finish__flow__errors__count", 0)
                return metrics
            except Exception as e:
                print(f"[reporter] Could not parse 6_report.json: {e}")

    timing_rpt = artifacts.get("timing_rpt")
    if timing_rpt and Path(timing_rpt).exists():
        text = Path(timing_rpt).read_text(errors="ignore")
        wns   = re.search(r"wns\s+\w+\s+([-]?\d+\.?\d*)", text)
        tns   = re.search(r"tns\s+\w+\s+([-]?\d+\.?\d*)", text)
        slack = re.search(r"worst slack\s+\w+\s+([-]?\d+\.?\d*)", text, re.IGNORECASE)
        fmax  = re.search(r"fmax\s*=\s*([\d.]+)", text)
        for key, match in [("wns_ns", wns), ("tns_ns", tns), ("worst_slack_ns", slack), ("fmax_mhz", fmax)]:
            if match:
                try:
                    metrics[key] = float(match.group(1))
                except ValueError:
                    pass

    area_rpt = artifacts.get("area_rpt")
    if area_rpt and Path(area_rpt).exists():
        text = Path(area_rpt).read_text(errors="ignore")
        area = re.search(r"Chip area for.*?:\s*([\d.]+)", text, re.IGNORECASE)
        if area:
            try:
                metrics["area_um2"] = float(area.group(1))
            except ValueError:
                pass

    return metrics


def _analyze_failure(metrics: Dict[str, Any], log_path: Optional[str]) -> Dict[str, Any]:
    analysis: Dict[str, str] = {}

    wns   = metrics.get("wns_ns")
    util  = metrics.get("utilization_pct")
    stage = metrics.get("failed_stage")

    if wns is not None and wns < 0:
        analysis["timing_violation"] = f"WNS={wns}ns. Consider relaxing clock period or optimizing logic."
    if util is not None and util > 85:
        analysis["high_utilization"] = f"Utilization={util}%. Reduce target density or increase die area."
    if stage == "route":
        analysis["routing_failure"] = "DRC/routing errors. Check congestion and reduce placement density."
    elif stage == "synth":
        analysis["synthesis_failure"] = "Synthesis failed. Check RTL for unsupported constructs."
    elif stage == "cts":
        analysis["cts_failure"] = "CTS failed. Check clock constraints and skew targets."

    if log_path and Path(log_path).exists():
        log_tail = Path(log_path).read_text(errors="ignore")[-4000:]
        if re.search(r"DRC violation", log_tail, re.IGNORECASE):
            analysis["drc_violations"] = "DRC violations detected in final layout."
        if re.search(r"cannot be placed", log_tail, re.IGNORECASE):
            analysis["placement_failure"] = "Cells could not be placed. Floorplan may be too small."

    return analysis


def _build_fallback_report(summary: Dict[str, Any]) -> str:
    m = summary["metrics"]
    status = "✅ PASS" if summary["run_passed"] else "❌ FAIL"
    lines = [
        f"# OpenROAD Results: {summary['design_name']}",
        f"**Status:** {status}",
        "",
        "## Metrics",
        f"- WNS: {m.get('wns_ns', 'N/A')} ns",
        f"- TNS: {m.get('tns_ns', 'N/A')} ns",
        f"- Utilization: {m.get('utilization_pct', 'N/A')} %",
        f"- Area: {m.get('area_um2', 'N/A')} µm²",
    ]
    if summary.get("failure_analysis"):
        lines += ["", "## Failure Analysis"]
        for k, v in summary["failure_analysis"].items():
            lines.append(f"- **{k}**: {v}")
    return "\n".join(lines) + "\n"


# ── 2e. Validator Node ───────────────────────────────────────────────────────

PHASE_DIR_RE = re.compile(r"^PHASE\d+RTL$", re.IGNORECASE)


def _drop_root(bundle: Optional[str]) -> Optional[Path]:
    """The frontend drop this bundle was cut from, if it can be located.

    Three ways, strongest first: stated outright; inferred from the bundle, because
    the orchestrator runs the backend on <drop>/TOPRTL; or the contract's own drop
    root, which is where a standalone block run should look.
    """
    env = (os.environ.get("FRONTEND_DROP_ROOT") or "").strip()
    if env and Path(env).is_dir():
        return Path(env)
    if bundle:
        parent = Path(bundle).resolve().parent
        try:
            if any(PHASE_DIR_RE.match(c.name) for c in parent.iterdir() if c.is_dir()):
                return parent
        except OSError:
            pass
    repo = (os.environ.get("BACKEND_GIT_REPO") or "").strip()
    bases = ([Path(repo)] if repo else []) + list(BACKEND_ROOT.parents)
    for base in bases:
        cand = base / "Frontend2" / "OutputFolders"
        if cand.is_dir():
            return cand
    return None


def _anchor_path(state: PipelineState, resolved: Dict[str, Any]) -> Optional[str]:
    """The file whoever has to fix this RTL would open.

    Settled with Validation 2026-10-08: that is the drop's phase copy
    (Frontend2/OutputFolders/PHASE3RTL/scheduler.sv), not the backend's bundle copy.
    The frontend's phase agents regenerate the phase copy; nobody edits ours, so an
    anchor pointing at it sends the reader to a dead end.

    The phase is found by looking rather than read from the manifest's `phase` field:
    on the 2026-10-08 drop that field still said 3 for data_path, which had moved to
    PHASE4RTL. Per the handoff contract a TOPRTL/ copy is never chosen over a phase
    copy. Falls back to the bundle path when no drop is in reach, which is honest -
    it says where the backend read the file - but it is not routable.
    """
    name = resolved.get("rtl_filename")
    if not name:
        return None
    bundle = state.get("bundle_dir")

    drop = _drop_root(bundle)
    if drop:
        hits = sorted(c / name for c in drop.iterdir()
                      if c.is_dir() and PHASE_DIR_RE.match(c.name) and (c / name).is_file())
        if hits:
            return _repo_relative(hits[0])

    if not bundle:
        return name
    full = (Path(bundle) / name).resolve()
    return _repo_relative(full, fallback_root=BACKEND_ROOT)


def _repo_relative(full: Path, fallback_root: Optional[Path] = None) -> str:
    """A path the team can read, not one from the machine that ran the flow.

    Relative to the enclosing checkout where there is one, forward slashes so it
    reads the same on every platform.
    """
    roots = [p for p in (fallback_root,) if p]
    repo = (os.environ.get("BACKEND_GIT_REPO") or "").strip()
    if repo:
        roots.append(Path(repo))
    roots += [p for p in full.parents if (p / ".git").exists()]
    for root in roots:
        try:
            return full.relative_to(root).as_posix()
        except ValueError:
            continue
    return full.name


def _emit_timing_finding(state: PipelineState, design_name: str,
                         artifacts: Dict[str, str],
                         resolved: Dict[str, Any]) -> None:
    """Write a routable finding for a block that misses its clock target.

    Best effort: a failure to emit must never change the pipeline's verdict, which is
    established by the checks themselves. If this cannot run, say why and carry on.
    """
    try:
        sys.path.insert(0, str(FINDINGS_ROOT))
        import emit_findings as ef                                  # noqa: PLC0415

        rpt = artifacts.get("timing_rpt")
        if not rpt or not Path(rpt).exists():
            print("[findings] no timing report among this run's artifacts - nothing to parse.")
            return
        parsed = ef.parse_timing_report(Path(rpt))
        # The period the design was actually constrained to. current_clock_period_ns
        # is set only once a tuner has moved it, so the packager's resolved value is
        # the authority for an untuned run.
        period = (state.get("current_clock_period_ns")
                  or resolved.get("clock_period_ns"))
        if not period:
            print("[findings] no clock period resolved - cannot state what was missed.")
            return
        # The backend may sit inside the team repo or beside it as a working copy.
        # BACKEND_GIT_REPO covers the second case; without a head the finding cannot
        # be tied to a code state, which is most of its value, so say so.
        env_repo = (os.environ.get("BACKEND_GIT_REPO") or "").strip()
        repo = Path(env_repo) if env_repo else ef.find_repo(FINDINGS_ROOT)
        head = ef.git_head(repo) if repo and Path(repo).exists() else None
        if not head:
            print("[findings] WARNING: no git head resolved - set BACKEND_GIT_REPO to the "
                  "team checkout so findings carry a drop stamp.")
        # The orchestrator names the drop by content; a standalone run has no id and
        # falls back to the git head. SPEC_REVISION has no safe default: the outbox is
        # looked up by it, so a stale one writes where nothing will read.
        rev = (state.get("spec_revision") or os.environ.get("SPEC_REVISION") or "").strip()
        if not rev:
            print("[findings] WARNING: no spec revision - set SPEC_REVISION or pass "
                  "--spec_revision; the orchestrator looks the outbox up by it, so "
                  "this finding may be written where nothing reads it.")
        drop = {"drop_id": state.get("drop_id"),
                "git_head": head,
                "spec_revision": rev or "unknown"}
        f = ef.timing_finding(
            design_name, float(period), parsed,
            rtl_path=_anchor_path(state, resolved),
            repro=f"pipeline_batch.py --bundle_dirs {state.get('bundle_dir', '<bundle>')}",
            drop=drop)
        if not f:
            return
        out = ef.write_outbox([f], FINDINGS_ROOT / "outbox", drop)
        w = f["evidence"]["worst_path"] or {}
        print(f"[findings] emitted {f['id']}  owner={f['owner_module']}  "
              f"severity={f['severity']}")
        if w:
            print(f"[findings] worst path {w.get('startpoint')} -> {w.get('endpoint')}  "
                  f"slack={w.get('slack_ns')}ns  levels={w.get('logic_levels')}")
        print(f"[findings] wrote {out}")
    except Exception as e:
        print(f"[findings] could not emit a timing finding ({type(e).__name__}: {e}) - "
              f"the pipeline verdict is unaffected.")


def validator_node(state: PipelineState) -> PipelineState:
    """
    Post-route sign-off validation. Runs three checks in order:

      1. DRC  — KLayout platform DRC deck on 6_final.gds; hard fail if violations > 0
      2. LVS  — KLayout with signoff/lvs/<platform>_fixed.lylvs plus the pin audit;
                hard fail on mismatch
      (1 and 2 run together in the ORFS container: _run_signoff. If they cannot
       run, the result is ERROR and the pipeline halts. It never reports PASS.)
      3. STA  — reads WNS from reporter metrics; soft fail if WNS < threshold,
                triggers tuner if autotuner enabled

    DRC and LVS failures set pipeline_status=FAIL and route to END.
    STA failure sets pipeline_status=NEEDS_TUNING (triggers tuner) or FAIL
    (if tuner disabled or iterations exhausted).
    All three passing sets pipeline_status=PASS.
    """
    out_root        = Path(state["out_root"])
    runner_result   = state.get("runner_result") or {}
    reporter_summary = state.get("reporter_summary") or {}
    packager_report = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    packager_resolved = packaged_manifest.get("packager", {}).get("resolved", {})

    design_name = runner_result.get("design_name") or packager_resolved.get("design_name", "design")
    platform    = runner_result.get("platform")    or packager_resolved.get("platform", "sky130hd")
    orfs_dir    = runner_result.get("orfs_dir")    or packager_resolved.get("orfs_dir", "")
    artifacts   = runner_result.get("artifacts", {})
    metrics     = reporter_summary.get("metrics", {})

    validator_out = out_root / "validator" / design_name
    validator_out.mkdir(parents=True, exist_ok=True)

    checks: Dict[str, Any] = {}

    # ── If runner itself failed, skip all checks ──────────────────────────────
    if runner_result.get("exit_code", -1) != 0:
        msg = "[validator] Runner did not complete successfully — skipping DRC/LVS/STA checks."
        print(msg)
        validator_result = {
            "skipped": True,
            "reason":  "Runner did not complete (exit_code != 0)",
            "checks":  {},
        }
        write_json(validator_out / "validator_report.json", validator_result)
        return {
            **state,
            "validator_result": validator_result,
            "current_node":     "validator",
            "pipeline_status":  "FAIL",
            "error_message":    state.get("error_message") or "Runner failed before validation.",
            "messages":         [msg],
        }

    # ── Modes below `build` produce no layout, so there is nothing to sign off ──
    # This is a clean PASS for what the tier claims, not a skipped check: the tier
    # never promised DRC/LVS/STA. The report records which mode ran so a reader
    # cannot mistake a contract pass for a signed-off layout.
    m = mode_of(state)
    if not m["signoff"]:
        mode_name = state.get("mode", DEFAULT_MODE)
        msg = (f"[validator] mode={mode_name} ({m['cost']}) — no layout produced, "
               f"so DRC/LVS/STA do not apply. Checks that did run: "
               f"intake, packaging{', synthesis' if m['runs_orfs'] else ''}.")
        print(msg)
        validator_result = {"skipped": False, "mode": mode_name, "checks": {},
                            "reason": "tier does not produce a layout"}
        write_json(validator_out / "validator_report.json", validator_result)
        return {
            **state,
            "validator_result": validator_result,
            "current_node":     "validator",
            "pipeline_status":  "PASS",
            "error_message":    None,
            "messages":         [msg],
        }

    # ── Sign-off: DRC + LVS + pin audit, run once in the ORFS container ────────
    signoff = _run_signoff(orfs_dir, platform, design_name, validator_out)

    # ── 1. DRC ────────────────────────────────────────────────────────────────
    print("[validator] Running DRC check...")
    drc_result = _check_drc(signoff, validator_out)
    checks["drc"] = drc_result

    if drc_result["status"] in ("FAIL", "ERROR"):
        if drc_result["status"] == "FAIL":
            msg = f"[validator] DRC HARD FAIL — {drc_result['violation_count']} violations. Halting pipeline."
        else:
            msg = f"[validator] DRC NOT VERIFIED — {drc_result['detail']} Halting pipeline."
        print(msg)
        _write_validator_report(validator_out, checks, state, "drc")
        _write_validator_markdown(validator_out, checks, design_name, state)
        return {
            **state,
            "validator_result": {"checks": checks, "failed_at": "drc"},
            "current_node":     "validator",
            "pipeline_status":  "FAIL",
            "error_message":    msg,
            "messages":         [msg],
        }

    # ── 2. LVS ────────────────────────────────────────────────────────────────
    print("[validator] Running LVS check...")
    lvs_result = _check_lvs(signoff, validator_out)
    checks["lvs"] = lvs_result

    if lvs_result["status"] in ("FAIL", "ERROR"):
        verb = "HARD FAIL" if lvs_result["status"] == "FAIL" else "NOT VERIFIED"
        msg = f"[validator] LVS {verb} — {lvs_result.get('detail', 'mismatch detected')}. Halting pipeline."
        print(msg)
        _write_validator_report(validator_out, checks, state, "lvs")
        _write_validator_markdown(validator_out, checks, design_name, state)
        return {
            **state,
            "validator_result": {"checks": checks, "failed_at": "lvs"},
            "current_node":     "validator",
            "pipeline_status":  "FAIL",
            "error_message":    msg,
            "messages":         [msg],
        }

    # ── 3. STA sign-off ───────────────────────────────────────────────────────
    print("[validator] Running STA sign-off check...")
    sta_result = _check_sta(metrics, artifacts, validator_out)
    checks["sta"] = sta_result

    _write_validator_report(validator_out, checks, state, None)
    _write_validator_markdown(validator_out, checks, design_name, state)

    if sta_result["status"] == "ERROR":
        # Tuning cannot produce a missing timing report: halt, do not route to the tuner.
        msg = f"[validator] STA NOT VERIFIED — {sta_result['detail']} Halting pipeline."
        print(msg)
        return {
            **state,
            "validator_result": {"checks": checks, "failed_at": "sta"},
            "current_node":     "validator",
            "pipeline_status":  "FAIL",
            "error_message":    msg,
            "messages":         [msg],
        }

    if sta_result["status"] == "FAIL":
        wns = sta_result.get("wns_ns", "N/A")
        if _should_autotune(metrics, state):
            msg = f"[validator] STA soft fail (WNS={wns}ns) — triggering auto-tuner."
            print(msg)
            return {
                **state,
                "validator_result": {"checks": checks, "failed_at": "sta"},
                "current_node":     "validator",
                "pipeline_status":  "NEEDS_TUNING",
                "error_message":    None,
                "messages":         [msg],
            }
        else:
            msg = f"[validator] STA soft fail (WNS={wns}ns) — autotuner disabled or exhausted. Marking FAIL."
            print(msg)
            # The verdict alone tells the backend owner the block is slow; it tells
            # the frontend nothing they can change. Emit a routable finding naming
            # the owning module, the failing path and the deficit, so the failure can
            # travel upstream without a human writing it up.
            _emit_timing_finding(state, design_name, artifacts, packager_resolved)
            return {
                **state,
                "validator_result": {"checks": checks, "failed_at": "sta"},
                "current_node":     "validator",
                "pipeline_status":  "FAIL",
                "error_message":    msg,
                "messages":         [msg],
            }

    # ── All checks passed ─────────────────────────────────────────────────────
    reporter_summary = state.get("reporter_summary") or {}
    metrics_for_fmax = reporter_summary.get("metrics", {})
    in_tradeoff = bool(state.get("tradeoff_fmax_result"))
    fmax_ran     = state.get("fmax_iteration", 0) > 0
    both_flags   = state.get("optimize_fmax", False) and state.get("optimize_power", False)

    sta_label = {"PASS": "STA PASS", "N/A": "STA N/A (no timing paths)"}.get(
        sta_result["status"], f"STA {sta_result['status']}")
    if _should_optimize_fmax(metrics_for_fmax, state):
        final_status = "OPTIMIZE_FMAX"
        msg = f"[validator] DRC PASS | LVS PASS | {sta_label} — routing to Fmax optimizer."
    elif fmax_ran and both_flags and not in_tradeoff:
        # Fmax converged early — transition to power phase before it runs.
        # Capture the final period's result here: the transition resets the clock,
        # after which this observation can no longer be reconstructed.
        final_status = "TRADEOFF_TRANSITION"
        state = {**state, "fmax_history": _with_final_fmax_observation(
            list(state.get("fmax_history", [])),
            state.get("current_clock_period_ns"),
            metrics_for_fmax.get("wns_ns"))}
        msg = f"[validator] DRC PASS | LVS PASS | {sta_label} — Fmax converged, transitioning to power phase."
    elif _should_optimize_power(metrics_for_fmax, state) or \
         (in_tradeoff and state.get("power_iteration", 0) < MAX_POWER_ITERATIONS):
        final_status = "OPTIMIZE_POWER"
        msg = f"[validator] DRC PASS | LVS PASS | {sta_label} — routing to power optimizer."
    else:
        final_status = "PASS"
        msg = f"[validator] DRC PASS | LVS PASS | {sta_label} — pipeline complete."
        out_root = Path(state["out_root"])
        packager_report = state.get("packager_report") or {}
        packaged_manifest = packager_report.get("packaged_manifest") or {}
        design_name = packaged_manifest.get("packager", {}).get("resolved", {}).get("design_name", "design")
        # Tradeoff mode — write combined report if both phases completed
        reporter_summary = state.get("reporter_summary") or {}
        metrics = reporter_summary.get("metrics", {})

        # The last configuration the tuner tried also has a result. It used to be
        # dropped, so the best run could be the one nobody recorded: on 2026-09-24
        # the Fmax tuner closed at 2.561 ns and reported 2.972 ns.
        power_history = _with_final_observation(
            list(state.get("power_history", [])), metrics,
            dict(state.get("power_config_applied") or {}))
        state = {**state, "power_history": power_history}

        # Fmax-only run: the clock still holds the final tightened period, so the
        # last result can be captured here. In tradeoff mode it was captured at the
        # transition, before the clock was reset, and this is a no-op.
        if not in_tradeoff and state.get("fmax_iteration", 0) > 0:
            state = {**state, "fmax_history": _with_final_fmax_observation(
                list(state.get("fmax_history", [])),
                state.get("current_clock_period_ns"),
                metrics.get("wns_ns"))}

        if in_tradeoff and state.get("power_iteration", 0) > 0:
            # Every field below comes from one observation, not several. Mixing them
            # produced a report claiming 0.600 mW beside the area of a 0.753 mW run.
            best_power = _best_power_observation(power_history) or {}
            delivered  = power_history[-1] if power_history else {}
            tradeoff_power = {
                "power_mw":        best_power.get("power_mw"),
                "wns_ns":          best_power.get("wns_ns"),
                "clock_period_ns": state.get("original_clock_period_ns") or 10.0,
                "fmax_mhz":        round(1000.0 / (state.get("original_clock_period_ns") or 10.0), 2),
                "utilization_pct": best_power.get("utilization_pct"),
                "area_um2":        best_power.get("area_um2"),
                "iterations":      state.get("power_iteration", 0),
                "from_iteration":  best_power.get("iteration"),
                # Whether the layout on disk is the one described above.
                "delivered_is_best": best_power.get("iteration") == delivered.get("iteration"),
                "delivered_power_mw": delivered.get("power_mw"),
                "baseline_power_mw":  power_history[0].get("power_mw") if power_history else None,
            }
            updated_state = {**state, "tradeoff_power_result": tradeoff_power}
            _write_tradeoff_report(updated_state, out_root, design_name)

        # Always write these. They used to be skipped in tradeoff mode, which left
        # fmax_summary.json and power_summary.json on disk from an earlier run —
        # months stale and indistinguishable from current results.
        if state.get("fmax_iteration", 0) > 0:
            _write_fmax_summary(state, out_root, design_name)
        if state.get("power_iteration", 0) > 0:
            _write_power_summary(state, out_root, design_name)
    print(msg)
    return {
        **state,
        "validator_result": {"checks": checks, "failed_at": None},
        "current_node":     "validator",
        "pipeline_status":  final_status,
        "error_message":    None,
        "messages":         [msg],
    }


# ── Sign-off (DRC + LVS + pin audit) ─────────────────────────────────────────
# Runs inside the ORFS container via signoff/signoff_runner.py, using the fixed
# KLayout decks in signoff/lvs/. signoff/lvs/README.md documents each deck fix and
# the negative controls proving these checks fail on broken layouts.

BACKEND_ROOT      = Path(__file__).resolve().parent.parent
SIGNOFF_ROOT      = BACKEND_ROOT / "signoff"
FINDINGS_ROOT     = BACKEND_ROOT / "findings"
SIGNOFF_TIMEOUT_S = 3 * 3600


def _run_signoff(orfs_dir: str, platform: str, design_name: str, out_dir: Path) -> Dict[str, Any]:
    """
    Run DRC + LVS + pin audit once in the ORFS container and return the parsed result.

    Never returns a PASS it could not check: if sign-off cannot run, the result is
    {ran: False, error: ...}, which _check_drc / _check_lvs turn into status ERROR.
    """
    so_out = (out_dir / "signoff").resolve()
    so_out.mkdir(parents=True, exist_ok=True)
    result_path = so_out / "signoff_result.json"
    if result_path.exists():
        result_path.unlink()                    # never read a previous run's verdict

    def fail(msg: str) -> Dict[str, Any]:
        print(f"[validator] sign-off could not run: {msg}")
        return {"ran": False, "error": msg}

    if os.environ.get("USE_DOCKER", "1").strip() != "1":
        return fail("USE_DOCKER=0 — sign-off runs inside the ORFS container")
    if not (SIGNOFF_ROOT / "signoff_runner.py").exists():
        return fail(f"sign-off runner missing: {SIGNOFF_ROOT / 'signoff_runner.py'}")
    if not orfs_dir:
        return fail("ORFS_DIR not resolved")
    flow = Path(orfs_dir) / "flow"
    design_dir = flow / "designs" / platform / design_name
    if not (design_dir / "config.mk").exists():
        return fail(f"design config not found: {design_dir / 'config.mk'}")

    fwd = lambda p: str(Path(p).resolve()).replace("\\", "/")
    ctr = "/OpenROAD-flow-scripts/flow"
    cmd = [
        "docker", "run", "--rm", "-e", "KLAYOUT_CMD=/usr/bin/klayout",
        "-v", f"{fwd(design_dir)}:{ctr}/designs/{platform}/{design_name}:ro",
        "-v", f"{fwd(flow / 'results')}:{ctr}/results",
        "-v", f"{fwd(flow / 'logs')}:{ctr}/logs",
        "-v", f"{fwd(SIGNOFF_ROOT)}:/signoff:ro",
        "-v", f"{fwd(so_out)}:/signoff_out",
        "-w", ctr,
        os.environ.get("ORFS_DOCKER_IMAGE", "openroad/orfs:latest"),
        "python3", "/signoff/signoff_runner.py",
        "--design", design_name, "--platform", platform, "--out", "/signoff_out",
    ]
    print(f"[validator] Running sign-off (DRC + LVS + pin audit) for {design_name}...")
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=SIGNOFF_TIMEOUT_S)
        write_text(so_out / "signoff_container.log", proc.stdout + ("\n" + proc.stderr if proc.stderr else ""))
    except subprocess.TimeoutExpired:
        return fail(f"sign-off timed out after {SIGNOFF_TIMEOUT_S}s")
    except Exception as e:
        return fail(f"docker invocation failed: {e}")

    if not result_path.exists():
        return fail(f"sign-off produced no result (docker exit {proc.returncode}); "
                    f"see {so_out / 'signoff_container.log'}")
    try:
        result = json.loads(result_path.read_text())
    except Exception as e:
        return fail(f"unreadable sign-off result {result_path}: {e}")
    result["result_path"] = str(result_path)
    return result


def _check_drc(signoff: Dict[str, Any], out_dir: Path) -> Dict[str, Any]:
    """
    DRC from the platform KLayout deck (run by _run_signoff).

    Returns: {status, violation_count, rules, source, detail, report}
    status: PASS (0 violations) | FAIL (violations) | ERROR (could not be verified)
    """
    d = signoff.get("drc") or {}
    if not signoff.get("ran") or d.get("status") not in ("PASS", "FAIL"):
        why = signoff.get("error") or d.get("detail") or "DRC did not run"
        return {"status": "ERROR", "violation_count": None, "rules": [], "source": "klayout_drc",
                "detail": f"DRC could not be verified: {why}.", "report": d.get("report")}
    n = int(d.get("violations", 0))
    rules = [{"rule": r, "count": c} for r, c in (d.get("by_rule") or {}).items()]
    if n == 0:
        detail = f"0 violations ({Path(d.get('deck', '')).name}, {d.get('seconds')}s)."
    else:
        detail = f"{n} DRC violation(s). Top rules: " + ", ".join(f"{r['rule']}:{r['count']}" for r in rules[:5])
    return {"status": "PASS" if n == 0 else "FAIL", "violation_count": n, "rules": rules,
            "source": "klayout_drc", "detail": detail, "report": d.get("report")}


def _check_lvs(signoff: Dict[str, Any], out_dir: Path) -> Dict[str, Any]:
    """
    LVS = KLayout comparison + pin audit (the audit covers pin-only nets, which
    KLayout's comparison does not check).

    Returns: {status, detail, method, log_path, nets_compared, pins_compared,
              cell_mismatches, blackboxed_instances, audit}
    status: PASS only if the netlists match AND the audit is complete; FAIL on any
            mismatch; ERROR if either part could not run.
    """
    lv, au = signoff.get("lvs") or {}, signoff.get("audit") or {}
    info = {"method": "klayout_lvs+pin_audit", "log_path": lv.get("report"),
            "nets_compared": lv.get("nets_compared"), "pins_compared": lv.get("pins_compared"),
            "cell_mismatches": lv.get("cell_mismatches", []),
            "blackboxed_instances": lv.get("blackboxed_instances"), "audit": au}
    if not signoff.get("ran") or lv.get("status") not in ("PASS", "FAIL"):
        why = signoff.get("error") or lv.get("detail") or "LVS did not run"
        return {**info, "status": "ERROR", "detail": f"LVS could not be verified: {why}"}
    if lv["status"] == "FAIL":
        return {**info, "status": "FAIL", "detail": lv.get("detail", "netlists do not match")}
    if au.get("status") == "FAIL":
        return {**info, "status": "FAIL", "detail": f"pin audit failed: {au.get('detail')}"}
    if au.get("status") != "PASS":
        return {**info, "status": "ERROR", "detail": f"LVS matched but the pin audit could not run: {au.get('detail')}"}
    return {**info, "status": "PASS", "detail": f"{lv.get('detail')}; audit: {au.get('detail')}"}


def _check_sta(
    metrics: Dict[str, Any],
    artifacts: Dict[str, str],
    out_dir: Path,
) -> Dict[str, Any]:
    """
    STA sign-off check.

    Primary source: WNS/TNS already parsed from 6_report.json by reporter.
    Secondary source: parse 6_finish.rpt timing report directly.

    Threshold: WNS >= STA_WNS_THRESHOLD_NS (0.0 ns) to pass.

    Returns: {status, wns_ns, tns_ns, threshold_ns, detail, path_summary}
    """
    result: Dict[str, Any] = {
        "status":       "PASS",
        "wns_ns":       None,
        "tns_ns":       None,
        "threshold_ns": STA_WNS_THRESHOLD_NS,
        "detail":       "",
        "path_summary": [],
    }

    # Pull from reporter metrics first
    wns = metrics.get("wns_ns")
    tns = metrics.get("tns_ns")

    # Nothing to time (no clock, or no constrained paths): not applicable, not a pass
    if metrics.get("timing_paths") is False or (wns is not None and wns >= STA_NO_PATHS_NS):
        result.update(status="N/A", wns_ns=None, tns_ns=None,
                      detail="No timing paths to check: the design has no clock or no constrained "
                             "register paths (OpenSTA reported slack 1e+39). STA does not apply.")
        return result

    # Supplement with per-path detail from timing report
    timing_rpt = artifacts.get("timing_rpt")
    path_summary: List[str] = []
    if timing_rpt and Path(timing_rpt).exists():
        shutil.copy2(timing_rpt, out_dir / "6_finish_sta.rpt")
        text = Path(timing_rpt).read_text(errors="ignore")

        # Extract worst N paths (lines containing "slack" with a value)
        slack_lines = re.findall(r".*(?:slack|WNS|TNS).*?([-]?\d+\.\d+).*", text, re.IGNORECASE)
        path_summary = slack_lines[:10]

        # Fallback WNS/TNS extraction if reporter didn't get them
        if wns is None:
            m = re.search(r"wns\s+([-]?\d+\.?\d*)", text, re.IGNORECASE)
            if m:
                try:
                    wns = float(m.group(1))
                except ValueError:
                    pass
        if tns is None:
            m = re.search(r"tns\s+([-]?\d+\.?\d*)", text, re.IGNORECASE)
            if m:
                try:
                    tns = float(m.group(1))
                except ValueError:
                    pass

    result["wns_ns"]      = wns
    result["tns_ns"]      = tns
    result["path_summary"] = path_summary

    if wns is None:
        result["status"] = "ERROR"
        result["detail"] = ("STA could not be verified: WNS could not be determined — timing report "
                            "missing or unparseable.")
        return result

    tns_s = f"{tns:.3f}ns" if tns is not None else "unknown"
    if wns < STA_WNS_THRESHOLD_NS:
        result["status"] = "FAIL"
        result["detail"] = (
            f"Timing not closed: WNS={wns:.3f}ns, TNS={tns_s}. "
            f"Required WNS >= {STA_WNS_THRESHOLD_NS}ns."
        )
    else:
        result["detail"] = (
            f"Timing closed: WNS={wns:.3f}ns, TNS={tns_s}. "
            f"Threshold: {STA_WNS_THRESHOLD_NS}ns."
        )

    return result


def _write_validator_report(
    out_dir: Path,
    checks: Dict[str, Any],
    state: PipelineState,
    failed_at: Optional[str],
) -> None:
    report = {
        "failed_at": failed_at,
        "checks":    checks,
        "tuner_iteration": state.get("tuner_iteration", 0),
    }
    write_json(out_dir / "validator_report.json", report)


def _write_validator_markdown(
    out_dir: Path,
    checks: Dict[str, Any],
    design_name: str,
    state: PipelineState,
) -> None:
    """Generate a human-readable validator summary using Claude if available."""
    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model   = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    if api_key:
        system = (
            "You are an ASIC sign-off validation reporter. "
            "Produce a concise markdown summary of DRC, LVS, and STA sign-off results. "
            "For each check: state PASS/FAIL/WARN, the key finding, and a specific fix if it failed. "
            "Do not invent data not present in the input."
        )
        user = f"""
Design: {design_name}
Validator checks:
{json.dumps(checks, indent=2)}
""".strip()
        try:
            md = call_claude(api_key, model, system, user, max_tokens=700)
        except Exception as e:
            md = _build_fallback_validator_report(design_name, checks)
    else:
        md = _build_fallback_validator_report(design_name, checks)

    write_text(out_dir / "validator_report.md", md)


def _build_fallback_validator_report(design_name: str, checks: Dict[str, Any]) -> str:
    def status_emoji(s: str) -> str:
        return {"PASS": "✅", "FAIL": "❌", "WARN": "⚠️"}.get(s, "❓")

    lines = [f"# Validator Sign-Off Report: {design_name}", ""]
    for check_name, result in checks.items():
        s = result.get("status", "?")
        lines.append(f"## {check_name.upper()} {status_emoji(s)} {s}")
        lines.append(result.get("detail", "No detail available."))
        lines.append("")
    return "\n".join(lines)


# ── 2f. Auto-Tuner Node ──────────────────────────────────────────────────────

def _pick_best_result(history: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    """Select best result from tuner history: passed runs ranked by WNS, else best WNS among failures."""
    if not history:
        return None
    passed = [h for h in history if h.get("metrics", {}).get("run_passed", False)]
    candidates = passed if passed else history
    def sort_key(h: Dict[str, Any]) -> float:
        wns = h.get("metrics", {}).get("wns_ns")
        return wns if wns is not None else float("-inf")
    return max(candidates, key=sort_key)


def tuner_node(state: PipelineState) -> PipelineState:
    """
    Uses Claude to propose updated ORFS make variables based on current metrics.
    Tracks best result across all iterations. Updates tuner_config and increments counter.
    """
    reporter_summary = state.get("reporter_summary") or {}
    metrics          = reporter_summary.get("metrics", {})
    tuner_history    = state.get("tuner_history", [])
    iteration        = state.get("tuner_iteration", 0) + 1

    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model   = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    current_config = state.get("tuner_config") or {
        "CORE_UTILIZATION":     "40",
        "CORE_ASPECT_RATIO":    "1",
        "CORE_MARGIN":          "2",
        "PLACE_DENSITY":        "0.60",
        "TNS_END_PERCENT":      "100",
        "CTS_CLUSTER_SIZE":     "30",
        "CTS_CLUSTER_DIAMETER": "100",
    }

    # Record this iteration before proposing next config
    this_entry = {"iteration": iteration - 1, "config": current_config, "metrics": metrics}
    new_history = tuner_history + [this_entry]

    # Track best result so far (prefer passed runs, then highest WNS)
    prev_best    = state.get("best_result")
    current_wns  = metrics.get("wns_ns")
    current_pass = metrics.get("run_passed", False)
    if prev_best is None:
        new_best = this_entry
    else:
        prev_pass = prev_best.get("metrics", {}).get("run_passed", False)
        prev_wns  = prev_best.get("metrics", {}).get("wns_ns", float("-inf"))
        if (not prev_pass and current_pass):
            new_best = this_entry
        elif (prev_pass == current_pass) and (current_wns is not None) and (current_wns > (prev_wns or float("-inf"))):
            new_best = this_entry
        else:
            new_best = prev_best

    if api_key:
        system = (
            "You are an ASIC physical design auto-tuner. "
            "Given current OpenROAD flow metrics and a history of attempted configurations, "
            "propose updated ORFS make variable values to improve timing and reduce congestion. "
            "Respond ONLY with a JSON object mapping variable names to string values. "
            "No preamble, no markdown fences."
        )
        user = f"""
Current metrics:
{json.dumps(metrics, indent=2)}

Current configuration:
{json.dumps(current_config, indent=2)}

Tuning history (previous attempts):
{json.dumps(new_history, indent=2)}

Iteration: {iteration} of {MAX_TUNER_ITERATIONS}

Propose updated values for any of these variables (only include ones you want to change):
CORE_UTILIZATION, CORE_ASPECT_RATIO, CORE_MARGIN, PLACE_DENSITY,
TNS_END_PERCENT, CTS_CLUSTER_SIZE, CTS_CLUSTER_DIAMETER

Rules:
- CORE_UTILIZATION: 20-65 (lower = less congestion, but increases area)
- PLACE_DENSITY: 0.40-0.75 (lower = less congestion)
- If timing is the only problem (run passed but WNS < 0), focus on PLACE_DENSITY and TNS_END_PERCENT
- If the run failed entirely, reduce CORE_UTILIZATION and PLACE_DENSITY more aggressively
- Do not repeat a configuration already in the history
""".strip()

        try:
            raw = call_claude(api_key, model, system, user, max_tokens=400)
            raw = re.sub(r"```json|```", "", raw).strip()
            proposed = json.loads(raw)
            new_config = {**current_config, **proposed}
            print(f"[tuner] Claude proposed: {proposed}")
        except Exception as e:
            print(f"[tuner] Claude call failed ({e}), applying default adjustments.")
            new_config = _default_tuner_adjustment(current_config, metrics)
    else:
        new_config = _default_tuner_adjustment(current_config, metrics)

    msg = (
        f"[tuner] Iteration {iteration}/{MAX_TUNER_ITERATIONS}  "
        f"wns={metrics.get('wns_ns', 'N/A')}  "
        f"run_passed={metrics.get('run_passed', False)}  "
        f"best_wns={new_best.get('metrics', {}).get('wns_ns', 'N/A')}"
    )
    print(msg)

    return {
        **state,
        "tuner_config":    new_config,
        "tuner_iteration": iteration,
        "tuner_history":   new_history,
        "best_result":     new_best,
        "current_node":    "tuner",
        "pipeline_status": "RUNNING",
        "messages":        [msg],
    }


def _default_tuner_adjustment(config: Dict[str, Any], metrics: Dict[str, Any]) -> Dict[str, Any]:
    """Fallback heuristic tuner when Claude is unavailable."""
    new        = dict(config)
    wns        = metrics.get("wns_ns", 0)
    run_passed = metrics.get("run_passed", True)

    if not run_passed:
        new["CORE_UTILIZATION"] = str(max(20, int(float(new.get("CORE_UTILIZATION", "40"))) - 10))
        new["PLACE_DENSITY"]    = str(max(0.40, round(float(new.get("PLACE_DENSITY", "0.60")) - 0.08, 2)))

    if wns is not None and wns < -0.5:
        new["TNS_END_PERCENT"] = "100"
        new["PLACE_DENSITY"]   = str(max(0.40, round(float(new.get("PLACE_DENSITY", "0.60")) - 0.05, 2)))

    return new


# ── 2f. Fmax Tuner Node ─────────────────────────────────────────────────────

def fmax_tuner_node(state: PipelineState) -> PipelineState:
    """
    Tightens the clock period toward maximum achievable frequency.
    Each iteration: new_period = current_period - WNS + 0.5 ns (0.5 ns margin).
    Updates config.mk and constraint.sdc in the ORFS design directory.
    """
    reporter_summary  = state.get("reporter_summary") or {}
    metrics           = reporter_summary.get("metrics", {})
    packager_report   = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    packager_resolved = packaged_manifest.get("packager", {}).get("resolved", {})

    fmax_iteration = state.get("fmax_iteration", 0) + 1
    fmax_history   = list(state.get("fmax_history", []))

    wns            = metrics.get("wns_ns", 0.0) or 0.0
    current_period = state.get("current_clock_period_ns") or packager_resolved.get("clock_period_ns") or 10.0
    clock_port     = packager_resolved.get("clock_port") or "clk"
    design_dir     = packager_resolved.get("orfs_design_dir")
    platform       = packager_resolved.get("platform", "sky130hd")
    design_name    = packager_resolved.get("design_name", "design")

    # Record this result before changing period
    fmax_history.append({
        "iteration":       fmax_iteration - 1,
        "clock_period_ns": current_period,
        "wns_ns":          wns,
        "fmax_mhz":        round(1000.0 / current_period, 2) if current_period > 0 else None,
    })

    # Tighten: new_period = current - (WNS - margin), floor at 1.0 ns
    margin_ns  = 0.5
    tighten_by = max(0.0, wns - margin_ns)
    new_period = max(1.0, round(current_period - tighten_by, 3))

    msg = (
        f"[fmax_tuner] Iteration {fmax_iteration}/{MAX_FMAX_ITERATIONS}  "
        f"period {current_period:.3f}ns -> {new_period:.3f}ns  "
        f"(WNS={wns:.3f}ns, tighten={tighten_by:.3f}ns)  "
        f"target_fmax={round(1000.0/new_period,1) if new_period>0 else 'N/A'}MHz"
    )
    print(msg)

    if design_dir:
        _patch_clock_period(Path(design_dir), new_period, clock_port, platform, design_name)
    else:
        print("[fmax_tuner] WARNING: design_dir not resolved, cannot patch config.mk")

    return {
        **state,
        "fmax_iteration":          fmax_iteration,
        "fmax_history":            fmax_history,
        "current_clock_period_ns": new_period,
        "current_node":            "fmax_tuner",
        "pipeline_status":         "RUNNING",
        "messages":                [msg],
    }


def _patch_clock_period(design_dir: Path, new_period: float, clock_port: str, platform: str, design_name: str) -> None:
    """Overwrite CLOCK_PERIOD in config.mk and update create_clock in constraint.sdc."""
    config_mk = design_dir / "config.mk"
    sdc_path  = design_dir / "constraint.sdc"

    if config_mk.exists():
        lines = config_mk.read_text().splitlines()
        new_lines, found = [], False
        for line in lines:
            if line.strip().startswith("export CLOCK_PERIOD"):
                new_lines.append(f"export CLOCK_PERIOD  = {new_period}")
                found = True
            else:
                new_lines.append(line)
        if not found:
            new_lines.append(f"export CLOCK_PERIOD  = {new_period}")
        config_mk.write_text("\n".join(new_lines) + "\n")
        print(f"[fmax_tuner] Patched config.mk: CLOCK_PERIOD={new_period}")

    if sdc_path.exists():
        sdc = sdc_path.read_text()
        # Two SDC styles: a literal "create_clock ... -period <n>" (older packager), or
        # "set clk_period <n>", used by create_clock and the I/O delays (ORFS style).
        sdc_new, n_lit = re.subn(r"(create_clock\s+-name\s+\S+\s+-period\s+)[\d.]+",
                                 lambda m: m.group(1) + str(new_period), sdc)
        sdc_new, n_var = re.subn(r"^(\s*set\s+clk_period\s+)[\d.]+",
                                 lambda m: m.group(1) + str(new_period), sdc_new, flags=re.M)
        if n_lit + n_var == 0:
            print(f"[fmax_tuner] WARNING: no clock period found in {sdc_path}; constraint.sdc NOT "
                  f"changed, so timing still uses the old period")
        else:
            sdc_path.write_text(sdc_new)
            print(f"[fmax_tuner] Patched constraint.sdc: period={new_period}")


def _with_final_fmax_observation(history: List[Dict[str, Any]], period: Optional[float],
                                 wns: Optional[float]) -> List[Dict[str, Any]]:
    """Append the result of the last period the Fmax tuner set.

    The tuner records the period it was given, then tightens. The run at the final
    tightened period therefore has no row. On 2026-09-24 cmd_gen closed at 2.561 ns
    with +0.661 ns of slack and the summary reported 2.972 ns — the previous
    iteration — discarding the best result the flow had actually achieved.

    Must be called while that period is still in effect. In tradeoff mode the clock
    is reset to the original period for the power phase, so this runs at the
    transition, not at the end of the pipeline.
    """
    if not history or not isinstance(period, (int, float)) or period <= 0:
        return history
    if any(h.get("final_observation") for h in history):
        return history
    if not isinstance(wns, (int, float)):
        return history
    if any(abs((h.get("clock_period_ns") or 0) - period) < 1e-9 for h in history):
        return history                      # this period already has a row
    return history + [{
        "iteration":         history[-1]["iteration"] + 1,
        "final_observation": True,
        "clock_period_ns":   period,
        "wns_ns":            wns,
        "fmax_mhz":          round(1000.0 / period, 2),
    }]


def _write_fmax_summary(state: PipelineState, out_root: Path, design_name: str) -> None:
    """Write fmax_summary.json with achieved Fmax and full iteration history."""
    history = state.get("fmax_history", [])
    converged_entries = [h for h in history if h.get("wns_ns", -1) >= 0]
    if converged_entries:
        best = min(converged_entries, key=lambda h: h["clock_period_ns"])
        achieved_fmax_mhz = round(1000.0 / best["clock_period_ns"], 2)
        converged = True
    else:
        best, achieved_fmax_mhz, converged = None, None, False

    summary = {
        "design_name":       design_name,
        "total_iterations":  state.get("fmax_iteration", 0),
        "converged":         converged,
        "achieved_fmax_mhz": achieved_fmax_mhz,
        "best_period_ns":    best["clock_period_ns"] if best else None,
        "best_wns_ns":       best["wns_ns"] if best else None,
        "history":           history,
    }

    out_path = out_root / "fmax" / design_name / "fmax_summary.json"
    write_json(out_path, summary)
    print(f"[fmax_tuner] Fmax summary -> {out_path}")
    if converged:
        print(f"[fmax_tuner] Achieved Fmax = {achieved_fmax_mhz} MHz  (period={best['clock_period_ns']} ns, WNS={best['wns_ns']:.3f} ns)")
    else:
        print(f"[fmax_tuner] Could not converge within {MAX_FMAX_ITERATIONS} iterations.")


# ═══════════════════════════════════════════════════════════════════════════════
# 3.  Routing (conditional edges)
# ═══════════════════════════════════════════════════════════════════════════════

def route_after_intake(state: PipelineState) -> str:
    return "end" if state["pipeline_status"] == "FAIL" else "packager"


def route_after_packager(state: PipelineState) -> str:
    return "end" if state["pipeline_status"] == "FAIL" else "runner"


def route_after_reporter(state: PipelineState) -> str:
    # Reporter always passes to validator — validator owns final status
    return "validator"


def route_after_validator(state: PipelineState) -> str:
    status = state["pipeline_status"]
    if status == "NEEDS_TUNING":
        iteration = state.get("tuner_iteration", 0)
        if iteration >= MAX_TUNER_ITERATIONS:
            _write_tuner_summary(state)
            return "end"
        return "tuner"
    if status == "OPTIMIZE_FMAX":
        fmax_iter = state.get("fmax_iteration", 0)
        if fmax_iter >= MAX_FMAX_ITERATIONS:
            if state.get("optimize_power", False):
                return "tradeoff_transition"
            out_root = Path(state["out_root"])
            packager_report   = state.get("packager_report") or {}
            packaged_manifest = packager_report.get("packaged_manifest") or {}
            design_name = packaged_manifest.get("packager", {}).get("resolved", {}).get("design_name", "design")
            _write_fmax_summary(state, out_root, design_name)
            return "end"
        return "fmax_tuner"
    if status == "TRADEOFF_TRANSITION":
        return "tradeoff_transition"
    if status == "OPTIMIZE_POWER":
        power_iter = state.get("power_iteration", 0)
        if power_iter >= MAX_POWER_ITERATIONS:
            out_root = Path(state["out_root"])
            packager_report   = state.get("packager_report") or {}
            packaged_manifest = packager_report.get("packaged_manifest") or {}
            design_name = packaged_manifest.get("packager", {}).get("resolved", {}).get("design_name", "design")
            if state.get("tradeoff_fmax_result"):
                reporter_summary = state.get("reporter_summary") or {}
                metrics = reporter_summary.get("metrics", {})
                power_history = state.get("power_history", [])
                best_power = min(power_history, key=lambda h: h.get("power_mw", float("inf"))) \
                             if power_history else {}
                tradeoff_power = {
                    "power_mw":        best_power.get("power_mw"),
                    "wns_ns":          best_power.get("wns_ns"),
                    "clock_period_ns": state.get("original_clock_period_ns") or 10.0,
                    "fmax_mhz":        round(1000.0 / (state.get("original_clock_period_ns") or 10.0), 2),
                    "utilization_pct": metrics.get("utilization_pct"),
                    "area_um2":        metrics.get("area_um2"),
                    "iterations":      power_iter,
                }
                updated_state = {**state, "tradeoff_power_result": tradeoff_power}
                _write_tradeoff_report(updated_state, out_root, design_name)
            else:
                _write_power_summary(state, out_root, design_name)
            return "end"
        return "power_tuner"
    return "end"  # PASS or FAIL both terminate


def _write_tuner_summary(state: PipelineState) -> None:
    """Write tuner_summary.json when failure-tuner loop closes."""
    out_root          = Path(state["out_root"])
    packager_report   = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    design_name = packaged_manifest.get("packager", {}).get("resolved", {}).get("design_name", "design")

    history = state.get("tuner_history", [])
    best    = state.get("best_result") or (_pick_best_result(history) if history else None)

    summary = {
        "design_name":      design_name,
        "total_iterations": state.get("tuner_iteration", 0),
        "converged":        False,
        "best_result":      best,
        "full_history":     history,
    }

    out_path = out_root / "tuner" / design_name / "tuner_summary.json"
    write_json(out_path, summary)
    print(f"[tuner] Exhausted {MAX_TUNER_ITERATIONS} iterations. Best result → {out_path}")
    if best:
        print(f"[tuner] Best WNS={best.get('metrics', {}).get('wns_ns', 'N/A')} ns  config={best.get('config', {})}")


def route_after_tuner(state: PipelineState) -> str:
    return "runner"


def route_after_fmax_tuner(state: PipelineState) -> str:
    return "runner"


def _should_autotune(metrics: Dict[str, Any], state: PipelineState) -> bool:
    """Trigger failure tuner on negative WNS or failed run."""
    if not state.get("enable_autotuner", False):
        return False
    if state.get("tuner_iteration", 0) >= MAX_TUNER_ITERATIONS:
        return False
    wns        = metrics.get("wns_ns")
    run_passed = metrics.get("run_passed", False)
    return (not run_passed) or (wns is not None and wns < 0)


def _should_optimize_fmax(metrics: Dict[str, Any], state: PipelineState) -> bool:
    """Trigger Fmax optimization when run passed and there is meaningful positive slack."""
    if not state.get("optimize_fmax", False):
        return False
    if state.get("fmax_iteration", 0) >= MAX_FMAX_ITERATIONS:
        return False
    if not metrics.get("run_passed", False):
        return False
    wns = metrics.get("wns_ns")
    return wns is not None and FMAX_WNS_THRESHOLD_NS < wns < STA_NO_PATHS_NS


# ── 2f. Repair Node ─────────────────────────────────────────────────────────

def repair_node(state: PipelineState) -> PipelineState:
    """
    Agentic repair node — sits between runner and reporter.
    Triggered only on genuine flow failures (non-zero exit, no GDS).

    Claude reads the log tail, classifies the error into a known category,
    and applies a targeted fix to config.mk before the runner retries.

    Error classes and fixes:
      - unpacked_array_port  : switch to SYNTH_HDL_FRONTEND = slang
      - pdn_too_small        : reduce CORE_UTILIZATION, increase CORE_MARGIN
      - routing_congestion   : reduce PLACE_DENSITY
      - timing_too_tight     : relax CLOCK_PERIOD by 20%
      - unknown              : log and escalate (no fix applied)

    Max MAX_REPAIR_ITERATIONS attempts before passing through to reporter.
    """
    runner_result   = state.get("runner_result") or {}
    packager_report = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    packager_resolved = packaged_manifest.get("packager", {}).get("resolved", {})

    design_name = runner_result.get("design_name") or packager_resolved.get("design_name", "design")
    orfs_dir    = runner_result.get("orfs_dir")    or packager_resolved.get("orfs_dir", "")
    platform    = runner_result.get("platform")    or packager_resolved.get("platform", "sky130hd")
    log_path    = runner_result.get("log_path")
    exit_code   = runner_result.get("exit_code", -1)
    repair_iteration = state.get("repair_iteration", 0) + 1
    repair_history   = list(state.get("repair_history", []))

    config_mk_path = Path(orfs_dir) / "flow" / "designs" / platform / design_name / "config.mk"

    # Read log tail for Claude to analyze
    log_tail = ""
    if log_path and Path(log_path).exists():
        log_tail = Path(log_path).read_text(errors="ignore")[-6000:]

    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model   = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    system = (
        "You are an ASIC physical design repair agent. "
        "Given an OpenROAD flow failure log, classify the error and propose a fix. "
        "Respond ONLY with a JSON object — no preamble, no markdown fences — with these fields:\n"
        "  error_class: one of [unpacked_array_port, pdn_too_small, routing_congestion, "
        "timing_too_tight, synthesis_error, unknown]\n"
        "  fixable: true or false\n"
        "  fix_description: one sentence explaining what you will change\n"
        "  config_mk_changes: object mapping make variable names to new string values "
        "(empty {} if no changes needed or not fixable)"
    )

    user = f"""
Design: {design_name}
Exit code: {exit_code}
Repair iteration: {repair_iteration} of {MAX_REPAIR_ITERATIONS}

Previous repair attempts:
{json.dumps(repair_history, indent=2) if repair_history else "None"}

Log tail (last 6000 chars):
{log_tail}
""".strip()

    error_class  = "unknown"
    fixable      = False
    fix_desc     = "Could not classify error — escalating to human."
    mk_changes: Dict[str, str] = {}

    if api_key:
        try:
            raw = call_claude(api_key, model, system, user, max_tokens=500)
            raw = re.sub(r"```json|```", "", raw).strip()
            proposal = json.loads(raw)
            error_class = proposal.get("error_class", "unknown")
            fixable     = bool(proposal.get("fixable", False))
            fix_desc    = proposal.get("fix_description", "")
            mk_changes  = proposal.get("config_mk_changes", {})
        except Exception as e:
            print(f"[repair] Claude call failed ({e}) — using heuristic fallback.")
            error_class, fixable, fix_desc, mk_changes = _heuristic_repair(log_tail)
    else:
        error_class, fixable, fix_desc, mk_changes = _heuristic_repair(log_tail)

    msg = f"[repair] Iteration {repair_iteration}/{MAX_REPAIR_ITERATIONS}  error_class={error_class}  fixable={fixable}"
    print(msg)
    if fix_desc:
        print(f"[repair] Fix: {fix_desc}")

    # Apply config.mk changes if fixable
    if fixable and mk_changes and config_mk_path.exists():
        _apply_repair_to_config_mk(config_mk_path, mk_changes)
        print(f"[repair] Applied changes to config.mk: {mk_changes}")

    # Record this attempt
    repair_history.append({
        "iteration":    repair_iteration,
        "error_class":  error_class,
        "fixable":      fixable,
        "fix_applied":  mk_changes if fixable else {},
        "fix_desc":     fix_desc,
    })

    # Decide next step: retry runner if fixable and under iteration limit,
    # otherwise pass through to reporter with the failure
    if fixable and repair_iteration < MAX_REPAIR_ITERATIONS:
        next_status = "REPAIR_RETRY"
    else:
        if not fixable:
            print(f"[repair] Error not fixable — passing to reporter.")
        else:
            print(f"[repair] Max repair iterations reached — passing to reporter.")
        next_status = "RUNNING"  # reporter will handle final status

    return {
        **state,
        "repair_iteration": repair_iteration,
        "repair_history":   repair_history,
        "current_node":     "repair",
        "pipeline_status":  next_status,
        "messages":         [msg],
    }


def _heuristic_repair(log_tail: str) -> tuple:
    """Fallback heuristic repair when Claude is unavailable."""
    if re.search(r"syntax error.*unexpected '\['", log_tail, re.IGNORECASE):
        return (
            "unpacked_array_port", True,
            "Unpacked array port syntax detected — switching to slang frontend.",
            {"SYNTH_HDL_FRONTEND": "slang"},
        )
    if re.search(r"PDN-0185|Insufficient width", log_tail, re.IGNORECASE):
        return (
            "pdn_too_small", True,
            "PDN straps don't fit — reducing core utilization and increasing margin.",
            {"CORE_UTILIZATION": "15", "CORE_MARGIN": "15"},
        )
    if re.search(r"DRC violation|congestion", log_tail, re.IGNORECASE):
        return (
            "routing_congestion", True,
            "Routing congestion detected — reducing placement density.",
            {"PLACE_DENSITY": "0.50"},
        )
    return ("unknown", False, "Could not classify error — escalating to human.", {})


def _apply_repair_to_config_mk(config_mk_path: Path, changes: Dict[str, str]) -> None:
    """
    Apply repair changes to config.mk. For each variable:
    - If it already exists in the file, replace the line
    - If it doesn't exist, append it
    """
    if not config_mk_path.exists():
        return
    lines = config_mk_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    applied = set()
    new_lines = []
    for line in lines:
        replaced = False
        for var, val in changes.items():
            if re.match(rf"^\s*export\s+{re.escape(var)}\s*[=:]", line):
                new_lines.append(f"export {var} = {val}")
                applied.add(var)
                replaced = True
                break
        if not replaced:
            new_lines.append(line)
    # Append any variables that weren't already in the file
    for var, val in changes.items():
        if var not in applied:
            new_lines.append(f"export {var} = {val}")
    config_mk_path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")


def route_after_runner(state: PipelineState) -> str:
    """Route to repair if the run failed, otherwise straight to reporter."""
    exit_code = (state.get("runner_result") or {}).get("exit_code", -1)
    repair_iteration = state.get("repair_iteration", 0)
    if exit_code != 0 and repair_iteration < MAX_REPAIR_ITERATIONS:
        return "repair"
    return "reporter"


def route_after_repair(state: PipelineState) -> str:
    """Route back to runner for retry, or forward to reporter if giving up."""
    if state.get("pipeline_status") == "REPAIR_RETRY":
        return "runner"
    return "reporter"


# ── 2g. Power Tuner Node ─────────────────────────────────────────────────────

def power_tuner_node(state: PipelineState) -> PipelineState:
    """
    Uses Claude to minimize power consumption while preserving timing closure.
    Each iteration Claude is given the current power_mw, wns_ns (available
    slack budget), and history of previous attempts. It proposes config.mk
    changes that trade timing margin for lower power — e.g. lower drive
    strengths, reduced placement density, area-focused synthesis.

    Constraints Claude must respect:
      - WNS must remain positive after changes (timing closure preserved)
      - DRC and LVS must still pass (Claude cannot change these)
      - Max MAX_POWER_ITERATIONS iterations

    Triggers only with --optimize_power flag, after all other checks pass.
    """
    reporter_summary  = state.get("reporter_summary") or {}
    metrics           = reporter_summary.get("metrics", {})
    packager_report   = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    packager_resolved = packaged_manifest.get("packager", {}).get("resolved", {})

    power_iteration = state.get("power_iteration", 0) + 1
    power_history   = list(state.get("power_history", []))

    power_mw    = metrics.get("power_mw", 0.0) or 0.0
    wns_ns      = metrics.get("wns_ns", 0.0) or 0.0
    design_dir  = packager_resolved.get("orfs_design_dir")
    design_name = packager_resolved.get("design_name", "design")
    platform    = packager_resolved.get("platform", "sky130hd")

    # Record what this configuration actually produced, before proposing the next.
    # Every metric for an iteration comes from the same run: reporting power from
    # one iteration next to the area from another produced the mixed rows in the
    # 2026-09-24 tradeoff report.
    cfg_applied = dict(state.get("power_config_applied") or {})
    power_history.append({
        "iteration":       power_iteration - 1,
        "power_mw":        power_mw,
        "wns_ns":          wns_ns,
        "area_um2":        metrics.get("area_um2"),
        "utilization_pct": metrics.get("utilization_pct"),
        "cell_count":      metrics.get("cell_count"),
        "config":          cfg_applied,      # the cumulative config that produced this row
        "is_baseline":     power_iteration == 1,
    })

    # Has optimization actually helped? The tuner used to keep whichever iteration
    # ran last, so on 2026-09-24 cmd_gen shipped 0.753 mW against a 0.639 mW
    # baseline — 18% worse than doing nothing — and still reported PASS.
    best = _best_power_observation(power_history)
    baseline = power_history[0]
    regressed = (best is not None and power_mw > best["power_mw"] + 1e-9)

    if regressed:
        # Do not ask for another proposal. On 2026-09-24 the model was told power had
        # gone up, concluded its settings "weren't fully applied", and applied more of
        # them — spreading the design further, adding wire capacitance, and driving
        # power up again. Revert to the best configuration and stop.
        msg = (f"[power_tuner] Iteration {power_iteration}/{MAX_POWER_ITERATIONS}  "
               f"power={power_mw:.4f}mW is worse than the best seen "
               f"({best['power_mw']:.4f}mW at iteration {best['iteration']}) — "
               f"reverting to that configuration and stopping.")
        print(msg)
        if design_dir:
            config_mk = Path(design_dir) / "config.mk"
            if config_mk.exists() and best.get("config"):
                _apply_repair_to_config_mk(config_mk, best["config"])
                print(f"[power_tuner] Restored: {best['config']}")
        print(f"[power_tuner] NOTE: the layout on disk is from iteration "
              f"{power_history[-1]['iteration']}, not the best one. Re-run to rebuild it "
              f"from the restored config.")
        return {
            **state,
            "power_iteration":  MAX_POWER_ITERATIONS,     # stop optimizing
            "power_history":    power_history,
            "power_regressed":  True,
            "current_node":     "power_tuner",
            "pipeline_status":  "RUNNING",
            "messages":         [msg],
        }

    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model   = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    system = (
        "You are an ASIC power optimization agent. "
        "Given current power consumption and timing slack, propose OpenROAD flow "
        "config.mk variable changes that will reduce power while keeping timing closed. "
        "You may trade timing slack for power reduction but WNS must remain positive. "
        "Respond ONLY with a JSON object — no preamble, no markdown — with these fields:\n"
        "  changes: object mapping make variable names to new string values\n"
        "  rationale: one sentence explaining the tradeoff being made\n"
        "  expected_power_reduction: estimated % reduction (integer)\n\n"
        "Useful variables for power reduction:\n"
        "  PLACE_DENSITY: lower = more spacing = less wire cap = less dynamic power (min 0.20)\n"
        "  SYNTH_STRATEGY: 'AREA 0' or 'DELAY 0' — AREA uses smaller/lower-power cells\n"
        "  GPL_ROUTABILITY_DRIVEN: 0 to disable routability pressure (reduces congestion fixes)\n"
        "  REMOVE_CELLS_FOR_ESD: 1 to remove ESD cells if not needed\n"
        "Rules:\n"
        "  - Always preserve at least 0.1 ns of WNS margin\n"
        "  - Do not change CLOCK_PERIOD or SDC_FILE\n"
        "  - Do not change DESIGN_NAME, PLATFORM, or VERILOG_FILES\n"
        "  - If no further power reduction is possible without violating timing, "
        "return changes: {}"
    )

    user = f"""
Design: {design_name}
Current power: {power_mw:.4f} mW
Current WNS (slack budget): {wns_ns:.3f} ns
Power optimization iteration: {power_iteration} of {MAX_POWER_ITERATIONS}

Previous attempts:
{json.dumps(power_history[:-1], indent=2) if len(power_history) > 1 else "None — this is the first attempt."}

Propose config.mk changes to reduce power while keeping WNS > 0.1 ns.
If the slack budget is small, be conservative. If it is large, be aggressive.
""".strip()

    changes: Dict[str, str] = {}
    rationale = ""
    expected_reduction = 0

    if api_key:
        try:
            raw = call_claude(api_key, model, system, user, max_tokens=400)
            raw = re.sub(r"```json|```", "", raw).strip()
            proposal = json.loads(raw)
            changes            = proposal.get("changes", {})
            rationale          = proposal.get("rationale", "")
            expected_reduction = proposal.get("expected_power_reduction", 0)
        except Exception as e:
            print(f"[power_tuner] Claude call failed ({e}) — using heuristic.")
            changes, rationale = _heuristic_power_reduction(power_history, wns_ns)
    else:
        changes, rationale = _heuristic_power_reduction(power_history, wns_ns)

    msg = (
        f"[power_tuner] Iteration {power_iteration}/{MAX_POWER_ITERATIONS}  "
        f"power={power_mw:.4f}mW  wns={wns_ns:.3f}ns  "
        f"expected_reduction={expected_reduction}%"
    )
    print(msg)
    if rationale:
        print(f"[power_tuner] {rationale}")

    # Apply changes to config.mk
    if changes and design_dir:
        config_mk = Path(design_dir) / "config.mk"
        if config_mk.exists():
            _apply_repair_to_config_mk(config_mk, changes)
            print(f"[power_tuner] Applied: {changes}")
    elif not changes:
        print("[power_tuner] No further changes proposed — power optimization converged.")

    # Update power history with proposed changes
    power_history[-1]["changes"] = changes
    power_history[-1]["rationale"] = rationale

    # Carry the cumulative config forward so the next observation knows what produced it.
    cfg_next = dict(cfg_applied)
    cfg_next.update(changes or {})

    return {
        **state,
        "power_iteration": power_iteration,
        "power_history":   power_history,
        "power_config_applied": cfg_next,
        "current_node":    "power_tuner",
        "pipeline_status": "RUNNING",
        "messages":        [msg],
    }


def _with_final_observation(history: List[Dict[str, Any]], metrics: Dict[str, Any],
                            cfg: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Append the result of the last configuration tried.

    Each tuner records the metrics it was given, then proposes the next change. The
    run that follows the final proposal therefore has no row, so the best result can
    be one that was never recorded. This closes that off-by-one.
    """
    if not history:
        return history
    if any(h.get("final_observation") for h in history):
        return history                      # already closed out; do not append twice
    power = metrics.get("power_mw")
    if not isinstance(power, (int, float)):
        return history
    return history + [{
        "iteration":       history[-1]["iteration"] + 1,
        "final_observation": True,
        "power_mw":        power,
        "wns_ns":          metrics.get("wns_ns"),
        "area_um2":        metrics.get("area_um2"),
        "utilization_pct": metrics.get("utilization_pct"),
        "cell_count":      metrics.get("cell_count"),
        "config":          cfg,
        "changes":         {},
        "rationale":       "Final configuration — result recorded after the last proposal.",
    }]


def _best_power_observation(history: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    """Lowest-power observation that still closes timing.

    Only rows with a real power number and positive slack can win: a configuration
    that saves power by breaking timing has not optimized anything. The baseline
    row is a legitimate winner — if nothing beats doing nothing, doing nothing wins.
    """
    usable = [h for h in history
              if isinstance(h.get("power_mw"), (int, float)) and h["power_mw"] > 0
              and isinstance(h.get("wns_ns"), (int, float)) and h["wns_ns"] > 0]
    return min(usable, key=lambda h: h["power_mw"]) if usable else None


def _heuristic_power_reduction(
    history: List[Dict[str, Any]],
    wns_ns: float,
) -> tuple:
    """Fallback heuristic power reduction when Claude is unavailable."""
    iteration = len(history)
    if wns_ns > 1.0 and iteration == 1:
        return (
            {"PLACE_DENSITY": "0.35", "SYNTH_STRATEGY": "AREA 0"},
            "Good slack budget — reducing placement density and switching to area synthesis.",
        )
    if wns_ns > 0.5 and iteration <= 2:
        return (
            {"PLACE_DENSITY": "0.30"},
            "Moderate slack — further reducing placement density.",
        )
    return ({}, "Insufficient slack for further power reduction.")


def _should_optimize_power(metrics: Dict[str, Any], state: PipelineState) -> bool:
    """Trigger power optimization after a clean pass if --optimize_power is set."""
    if not state.get("optimize_power", False):
        return False
    if state.get("power_iteration", 0) >= MAX_POWER_ITERATIONS:
        return False
    if not metrics.get("run_passed", False):
        return False
    # Only optimize if there's meaningful slack to trade
    wns = metrics.get("wns_ns")
    if wns is None or wns <= 0.1:
        return False
    return True


def _write_power_summary(state: PipelineState, out_root: Path, design_name: str) -> None:
    """Write power_summary.json with optimization history."""
    history = state.get("power_history", [])
    if history:
        best = min(history, key=lambda h: h.get("power_mw", float("inf")))
    else:
        best = None

    summary = {
        "design_name":      design_name,
        "total_iterations": state.get("power_iteration", 0),
        "best_power_mw":    best.get("power_mw") if best else None,
        "history":          history,
    }
    out_path = out_root / "power" / design_name / "power_summary.json"
    write_json(out_path, summary)
    print(f"[power_tuner] Power summary -> {out_path}")
    if best:
        print(f"[power_tuner] Best power = {best.get('power_mw', 'N/A')} mW  (iter {best.get('iteration', '?')})")




# ── 2h. Tradeoff Transition Node ─────────────────────────────────────────────

def tradeoff_transition_node(state: PipelineState) -> PipelineState:
    """
    Fires when both --optimize_fmax and --optimize_power are set and Fmax
    optimization has completed. Saves the Fmax results, resets the clock
    period to the original default, and kicks off the power optimization phase.
    """
    packager_report   = state.get("packager_report") or {}
    packaged_manifest = packager_report.get("packaged_manifest") or {}
    packager_resolved = packaged_manifest.get("packager", {}).get("resolved", {})
    design_dir  = packager_resolved.get("orfs_design_dir")
    clock_port  = packager_resolved.get("clock_port") or "clk"
    platform    = packager_resolved.get("platform", "sky130hd")
    design_name = packager_resolved.get("design_name", "design")

    # Save Fmax phase results
    fmax_history = state.get("fmax_history", [])
    converged_entries = [h for h in fmax_history if h.get("wns_ns", -1) >= 0]
    if converged_entries:
        best_fmax = min(converged_entries, key=lambda h: h["clock_period_ns"])
    else:
        best_fmax = fmax_history[-1] if fmax_history else {}

    reporter_summary = state.get("reporter_summary") or {}
    metrics = reporter_summary.get("metrics", {})

    fmax_result = {
        "achieved_fmax_mhz":  best_fmax.get("fmax_mhz"),
        "best_period_ns":     best_fmax.get("clock_period_ns"),
        "best_wns_ns":        best_fmax.get("wns_ns"),
        "power_mw":           metrics.get("power_mw"),
        "utilization_pct":    metrics.get("utilization_pct"),
        "area_um2":           metrics.get("area_um2"),
        "iterations":         state.get("fmax_iteration", 0),
    }

    # Reset clock period to original default for power phase
    original_period = state.get("original_clock_period_ns") or \
                      packager_resolved.get("clock_period_ns") or 10.0

    print(f"[tradeoff] Fmax phase complete — achieved {best_fmax.get('fmax_mhz', 'N/A')} MHz")
    print(f"[tradeoff] Resetting clock period to {original_period} ns for power optimization phase.")

    if design_dir:
        _patch_clock_period(
            Path(design_dir), original_period, clock_port, platform, design_name
        )

    msg = f"[tradeoff] Transitioning from Fmax phase to power optimization phase."
    print(msg)

    return {
        **state,
        "tradeoff_fmax_result":   fmax_result,
        "current_clock_period_ns": original_period,
        # Reset fmax iteration so it doesn't re-trigger
        "fmax_iteration":          MAX_FMAX_ITERATIONS,
        # Reset power counters for fresh power phase
        "power_iteration":         0,
        "power_history":           [],
        "current_node":            "tradeoff_transition",
        "pipeline_status":         "RUNNING",
        "messages":                [msg],
    }


def _write_tradeoff_report(
    state: PipelineState,
    out_root: Path,
    design_name: str,
) -> None:
    """Write tradeoff_summary.json and a Claude-generated tradeoff_report.md."""
    fmax_result  = state.get("tradeoff_fmax_result") or {}
    power_result = state.get("tradeoff_power_result") or {}

    summary = {
        "design_name": design_name,
        "fmax_phase":  fmax_result,
        "power_phase": power_result,
    }

    out_dir = out_root / "tradeoff" / design_name
    out_dir.mkdir(parents=True, exist_ok=True)
    write_json(out_dir / "tradeoff_summary.json", summary)

    # Claude-generated tradeoff report
    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model   = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    if api_key:
        system = (
            "You are an ASIC design tradeoff analyst. "
            "Given results from two optimization runs of the same block — one maximizing "
            "Fmax and one minimizing power — produce a concise markdown report with a "
            "tradeoff table and a brief analysis of the design space. "
            "Be specific with numbers. Do not invent data not present."
        )
        user = f"""
Design: {design_name}

Fmax optimization results:
{json.dumps(fmax_result, indent=2)}

Power optimization results:
{json.dumps(power_result, indent=2)}

Produce a markdown report with:
1. A tradeoff table comparing the two runs across: Clock Period, Fmax, Power, WNS, Utilization, Area
2. A brief analysis (3-4 sentences) of the Fmax vs power tradeoff for this block
3. A recommendation for which operating point to use depending on the system requirement
""".strip()
        try:
            md = call_claude(api_key, model, system, user, max_tokens=800)
        except Exception as e:
            md = _build_fallback_tradeoff_report(design_name, fmax_result, power_result)
    else:
        md = _build_fallback_tradeoff_report(design_name, fmax_result, power_result)

    write_text(out_dir / "tradeoff_report.md", md)
    print(f"[tradeoff] Report written -> {out_dir / 'tradeoff_report.md'}")


def _build_fallback_tradeoff_report(
    design_name: str,
    fmax_result: Dict[str, Any],
    power_result: Dict[str, Any],
) -> str:
    lines = [
        f"# Tradeoff Report: {design_name}",
        "",
        "## Fmax vs Power Tradeoff",
        "",
        "| Metric | Max Fmax Run | Min Power Run |",
        "|--------|-------------|---------------|",
        f"| Clock Period | {fmax_result.get('best_period_ns', 'N/A')} ns | {power_result.get('clock_period_ns', 'N/A')} ns |",
        f"| Fmax | {fmax_result.get('achieved_fmax_mhz', 'N/A')} MHz | {power_result.get('fmax_mhz', 'N/A')} MHz |",
        f"| Power | {fmax_result.get('power_mw', 'N/A')} mW | {power_result.get('power_mw', 'N/A')} mW |",
        f"| WNS | {fmax_result.get('best_wns_ns', 'N/A')} ns | {power_result.get('wns_ns', 'N/A')} ns |",
        f"| Utilization | {fmax_result.get('utilization_pct', 'N/A')} % | {power_result.get('utilization_pct', 'N/A')} % |",
        f"| Area | {fmax_result.get('area_um2', 'N/A')} um2 | {power_result.get('area_um2', 'N/A')} um2 |",
    ]
    return "\n".join(lines) + "\n"





def route_after_power_tuner(state: PipelineState) -> str:
    return "runner"


def route_after_tradeoff_transition(state: PipelineState) -> str:
    return "runner"


def build_graph() -> Any:
    g = StateGraph(PipelineState)

    g.add_node("intake",               intake_node)
    g.add_node("packager",             packager_node)
    g.add_node("runner",               runner_node)
    g.add_node("repair",               repair_node)
    g.add_node("reporter",             reporter_node)
    g.add_node("validator",            validator_node)
    g.add_node("tuner",                tuner_node)
    g.add_node("fmax_tuner",           fmax_tuner_node)
    g.add_node("power_tuner",          power_tuner_node)
    g.add_node("tradeoff_transition",  tradeoff_transition_node)

    g.set_entry_point("intake")

    g.add_conditional_edges("intake",              route_after_intake,              {"packager":            "packager",           "end": END})
    g.add_conditional_edges("packager",            route_after_packager,            {"runner":              "runner",             "end": END})
    g.add_conditional_edges("runner",              route_after_runner,              {"repair":              "repair",             "reporter": "reporter"})
    g.add_conditional_edges("repair",              route_after_repair,              {"runner":              "runner",             "reporter": "reporter"})
    g.add_conditional_edges("reporter",            route_after_reporter,            {"validator":           "validator"})
    g.add_conditional_edges("validator",           route_after_validator,           {"tuner":               "tuner",
                                                                                     "fmax_tuner":          "fmax_tuner",
                                                                                     "power_tuner":         "power_tuner",
                                                                                     "tradeoff_transition": "tradeoff_transition",
                                                                                     "end":                 END})
    g.add_conditional_edges("tuner",               route_after_tuner,               {"runner":              "runner"})
    g.add_conditional_edges("fmax_tuner",          route_after_fmax_tuner,          {"runner":              "runner"})
    g.add_conditional_edges("power_tuner",         route_after_power_tuner,         {"runner":              "runner"})
    g.add_conditional_edges("tradeoff_transition", route_after_tradeoff_transition, {"runner":              "runner"})

    return g.compile()


# ═══════════════════════════════════════════════════════════════════════════════
# 5.  Main
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> int:
    ap = argparse.ArgumentParser(description="DDR3 Backend LangGraph Pipeline")
    ap.add_argument("--bundle_dir",       required=True,  type=Path)
    ap.add_argument("--out_root",         type=Path, default=Path("./pipeline_out"))
    ap.add_argument("--env_file",         type=Path, default=Path(".env"))
    ap.add_argument("--enable_autotuner", action="store_true", default=False)
    ap.add_argument("--optimize_fmax",    action="store_true", default=False,
                    help="After a clean PASS, tighten clock period to maximize Fmax (up to 3 iterations)")
    ap.add_argument("--optimize_power",   action="store_true", default=False,
                    help="After a clean PASS, use Claude to minimize power while preserving timing (up to 3 iterations)")
    ap.add_argument("--drop_id", default=None,
                    help="The frontend drop's content id (Validation's rtl_drop.py: "
                         "drop_id()). Passed by the orchestrator; findings are filed "
                         "under it so they can be tied to the RTL they ran on.")
    ap.add_argument("--spec_revision", default=None,
                    help="The spec revision this drop was generated from. The "
                         "orchestrator looks the findings outbox up by it.")
    ap.add_argument("--mode", choices=sorted(MODES), default=DEFAULT_MODE,
                    help="How far to take the run. "
                         + "; ".join(f"{k} ({v['cost']})" for k, v in MODES.items()))
    args = ap.parse_args()

    load_env_file(args.env_file)

    # `full` is `build` plus optimization, so it implies the tuner flags rather than
    # making a caller pass both. An explicit flag still wins.
    optimize = MODES[args.mode]["optimize"]

    initial_state: PipelineState = {
        "bundle_dir":       str(args.bundle_dir),
        "out_root":         str(args.out_root),
        "env_file":         str(args.env_file),
        "mode":             args.mode,
        "drop_id":          args.drop_id,
        "spec_revision":    args.spec_revision,
        "enable_autotuner":       args.enable_autotuner or optimize,
        "optimize_fmax":          args.optimize_fmax or optimize,
        "optimize_power":         args.optimize_power or optimize,
        "intake_report":          None,
        "packager_report":  None,
        "runner_result":    None,
        "reporter_summary": None,
        "validator_result": None,
        "tuner_config":     None,
        "tuner_history":          [],
        "best_result":            None,
        "fmax_iteration":         0,
        "fmax_history":           [],
        "current_clock_period_ns": None,
        "power_iteration":        0,
        "power_history":          [],
        "tradeoff_fmax_result":   None,
        "tradeoff_power_result":  None,
        "original_clock_period_ns": None,
        "repair_iteration":       0,
        "repair_history":         [],
        "current_node":     "start",
        "error_message":    None,
        "tuner_iteration":  0,
        "messages":         ["[pipeline] Starting DDR3 backend pipeline..."],
    }

    graph = build_graph()

    print("=" * 60)
    print("  DDR3 Backend Pipeline  (LangGraph)")
    print(f"  bundle_dir : {args.bundle_dir}")
    print(f"  out_root   : {args.out_root}")
    print(f"  autotuner  : {args.enable_autotuner}")
    print(f"  opt_fmax   : {args.optimize_fmax}")
    print("=" * 60)

    final_state = graph.invoke(initial_state)

    # ── Final summary ────────────────────────────────────────────────────────
    out_root = Path(args.out_root)
    validator = final_state.get("validator_result") or {}
    final_report = {
        "pipeline_status":   final_state["pipeline_status"],
        "error_message":     final_state.get("error_message"),
        "tuner_iterations":  final_state.get("tuner_iteration", 0),
        "intake_status":     (final_state.get("intake_report")    or {}).get("status"),
        "packager_status":   (final_state.get("packager_report")   or {}).get("status"),
        "runner_exit_code":  (final_state.get("runner_result")     or {}).get("exit_code"),
        "failed_stage":      (final_state.get("runner_result")     or {}).get("failed_stage"),
        "validator_failed_at": validator.get("failed_at"),
        "drc_violations":    (validator.get("checks", {}).get("drc") or {}).get("violation_count"),
        "lvs_status":        (validator.get("checks", {}).get("lvs") or {}).get("status"),
        "sta_wns_ns":        (validator.get("checks", {}).get("sta") or {}).get("wns_ns"),
        "sta_status":        (validator.get("checks", {}).get("sta") or {}).get("status"),
        "artifacts":         (final_state.get("runner_result")     or {}).get("artifacts", {}),
        "messages":          final_state.get("messages", []),
        # Which tier ran. A PASS from `contract` and a PASS from `build` mean very
        # different things; a consumer must be able to tell them apart.
        "mode":              final_state.get("mode", DEFAULT_MODE),
        "checks_applicable": sorted(k for k, v in {
            "intake": True, "packaging": True,
            "synthesis": mode_of(final_state)["runs_orfs"],
            "drc": mode_of(final_state)["signoff"],
            "lvs": mode_of(final_state)["signoff"],
            "sta": mode_of(final_state)["signoff"],
        }.items() if v),
    }

    # Optimization outcomes. Without these the batch summary had only the delivered
    # run's metrics, so a design that closed at 390 MHz during the Fmax phase was
    # summarised as 293 MHz — the speed implied by the power-optimised layout, which
    # was never asked to go fast. Two different quantities, one label.
    _fh = final_state.get("fmax_history") or []
    _closed = [h for h in _fh if isinstance(h.get("wns_ns"), (int, float)) and h["wns_ns"] >= 0]
    if _closed:
        _best = min(_closed, key=lambda h: h["clock_period_ns"])
        final_report["fmax_best_closed_mhz"] = round(1000.0 / _best["clock_period_ns"], 2)
        final_report["fmax_best_period_ns"]  = _best["clock_period_ns"]
        final_report["fmax_best_wns_ns"]     = _best["wns_ns"]

    _ph = final_state.get("power_history") or []
    if _ph:
        _bp = _best_power_observation(_ph)
        final_report["power_baseline_mw"]  = _ph[0].get("power_mw")
        final_report["power_best_mw"]      = _bp.get("power_mw") if _bp else None
        final_report["power_delivered_mw"] = _ph[-1].get("power_mw")
        final_report["power_delivered_is_best"] = bool(
            _bp and _bp.get("iteration") == _ph[-1].get("iteration"))

    design_name_final = (final_state.get("runner_result") or {}).get("design_name", Path(args.bundle_dir).name)
    final_report_path = out_root / f"pipeline_final_report_{design_name_final}.json"
    write_json(final_report_path, final_report)

    print("\n" + "=" * 60)
    print(f"  PIPELINE STATUS : {final_state['pipeline_status']}")
    if final_state.get("error_message"):
        print(f"  ERROR           : {final_state['error_message']}")
    reporter_s = final_state.get("reporter_summary") or {}
    if reporter_s:
        m = reporter_s.get("metrics", {})
        if m.get("wns_ns") is not None:
            print(f"  WNS             : {m['wns_ns']} ns")
        else:
            print(f"  WNS             : {'n/a (no timing paths)' if m.get('timing_paths') is False else 'unknown'}")
        print(f"  Utilization     : {m.get('utilization_pct', 'N/A')} %")
        print(f"  Area            : {m.get('area_um2', 'N/A')} µm²")
    if validator:
        checks = validator.get("checks", {})
        print(f"  DRC             : {(checks.get('drc') or {}).get('status', 'N/A')}  violations={(checks.get('drc') or {}).get('violation_count', 'N/A')}")
        print(f"  LVS             : {(checks.get('lvs') or {}).get('status', 'N/A')}")
        sta = checks.get("sta") or {}
        sta_wns = f"  WNS={sta['wns_ns']} ns" if sta.get("wns_ns") is not None else ""
        sta_why = {"N/A": "  (no timing paths)", "ERROR": "  (not verified: no timing data)"}.get(
            sta.get("status"), "")
        print(f"  STA sign-off    : {sta.get('status', 'N/A')}{sta_wns}{sta_why}")
        design_name_final = (final_state.get("runner_result") or {}).get("design_name", "design")
        print(f"  Validator report: {out_root / 'validator' / design_name_final / 'validator_report.md'}")
    if final_state.get("tuner_iteration", 0) > 0:
        iters = final_state["tuner_iteration"]
        best  = final_state.get("best_result")
        print(f"  Tuner iters     : {iters}/{MAX_TUNER_ITERATIONS}")
        if best:
            bm = best.get("metrics", {})
            print(f"  Best WNS        : {bm.get('wns_ns', 'N/A')} ns  (iter {best.get('iteration', '?')})")
    if final_state.get("fmax_iteration", 0) > 0:
        fmax_iters = final_state["fmax_iteration"]
        fmax_hist  = final_state.get("fmax_history", [])
        print(f"  Fmax iters      : {fmax_iters}/{MAX_FMAX_ITERATIONS}")
        passed = [h for h in fmax_hist if h.get("wns_ns", -1) >= 0]
        if passed:
            best_fmax = min(passed, key=lambda h: h["clock_period_ns"])
            print(f"  Achieved Fmax   : {round(1000.0/best_fmax['clock_period_ns'],1)} MHz  "
                  f"(period={best_fmax['clock_period_ns']} ns, WNS={best_fmax['wns_ns']:.3f} ns)")
        else:
            print(f"  Fmax opt        : Did not converge within {MAX_FMAX_ITERATIONS} iterations")
    print(f"  Full report     : {final_report_path}")
    print("=" * 60)

    return 0 if final_state["pipeline_status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
