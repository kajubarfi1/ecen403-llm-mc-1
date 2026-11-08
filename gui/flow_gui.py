#!/usr/bin/env python3
"""Live progress GUI for flow.py.

Watches a run directory (runs/<run_id>/) and serves a page that shows where
the flow is, with most of the detail on the backend (RTL -> GDSII), which is
the longest stage. Nothing here changes a run; it only reads:

  runs/<id>/RUN_STATE.json          stage outcomes (written by flow.py)
  runs/<id>/flow.log                live command output (backend markers)
  runs/<id>/backend/pipeline_final_report_*.json   backend result
  $ORFS_DIR/flow/logs/<platform>/<design>/base/*.log   ORFS per-step logs

The backend runs ORFS with its output captured, so nothing reaches flow.log
for the hour ORFS takes. The ORFS step logs are written to the host through
the Docker bind mount, though, and those say which step is running (and, for
placement and detailed routing, how far along it is).

Usage:
  python3 gui/flow_gui.py                    follow the newest run
  python3 gui/flow_gui.py --run runs/<id>    watch one run
  python3 gui/flow_gui.py --demo             fake a whole run (no ORFS needed)
  python3 flow.py --gui ...                  run the flow with this GUI attached

Opened on its own, the page also has a terminal panel that starts flow.py
and takes keyboard input (gui/flow_terminal.py; macOS/Linux). A run started
there keeps going with the tab closed and stops when this server stops.
--no-terminal makes the page watch-only.

ORFS_DIR comes from --orfs-dir, the environment, or backend/agents/.env.
"""

import argparse
import base64
import glob
import hmac
import json
import math
import os
import re
import secrets
import sys
import threading
import time
import webbrowser
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# --------------------------------------------------------------------------
# flow-level stages
# --------------------------------------------------------------------------

FLOW_STAGES = [
    ("spec_synthesis", "Spec synthesis"),
    ("spec_review", "Spec review"),
    ("rtl_generation", "RTL generation"),
    ("rtl_validation", "RTL validation"),
    ("formal", "Formal"),
    ("backend", "Backend"),
    ("final_validation", "Netlist validation"),
]
# loop stages show on the stage they feed back into
STAGE_ALIAS = {"frontend_regeneration": "rtl_generation",
               "backend_to_frontend": "rtl_generation"}

# which flow stage a subsystem command belongs to (flow.py logs "$ <cmd>")
CMD_STAGES = [
    (re.compile(r"microarch_cli\.py|^\$ \(interactive"), "spec_synthesis"),
    (re.compile(r"validate_spec_stage\.py"), "spec_review"),
    (re.compile(r"phase\d_pipeline\.py|generate_top\.py"), "rtl_generation"),
    (re.compile(r"validate_drop\.py"), "rtl_validation"),
    (re.compile(r"run_formal\.py"), "formal"),
    (re.compile(r"to_frontend_error_report\.py|phase\d_validation_agent\.py"), "frontend_regeneration"),
    (re.compile(r"backend/agents/pipeline\.py"), "backend"),
    (re.compile(r"run_path\.py"), "final_validation"),
]

STATUS_MAP = {"PASS": "pass", "FAIL": "fail", "HALT": "halt", "SKIPPED": "skip",
              "ROUTED": "loop"}

PHASE_MODULES = {1: ["init_fsm", "config_regs", "wb_port"],
                 2: ["addr_decoder", "bank_tracker", "refresh_ctrl", "calibration"],
                 3: ["cmd_queue", "scheduler", "cmd_gen"],
                 4: ["data_path"]}

# --------------------------------------------------------------------------
# Frontend (per-phase/module generation + its own fix-loop) and Validation
# (the system-level path suite) detail -- the two subsystems either side of
# `rtl_generation`/`rtl_validation` in the stage strip, broken out so a
# module failing, a fix attempt, and a validation round sending work back
# to the Frontend are all visible as they happen, not just as one dot.
# --------------------------------------------------------------------------

PHASE_START_LINE = re.compile(r"^-- phase (\d+):")
GEN_CHECK_HDR = re.compile(r"^\s*GENERATION CHECK\s*$")
LINT_GATE_HDR = re.compile(r"^\s*LINT GATE\b")
SIM_GATE_HDR = re.compile(r"^\s*SIM GATE\b")
MOD_STATUS_LINE = re.compile(r"^\s*(OK|FAIL|--)\s+(\w+)\s+(.*)$")
PHASE_PASS_LINE = re.compile(r"^\s*PHASE (\d+) PIPELINE -- ALL CHECKS PASSED")
PHASE_FAIL_LINE = re.compile(r"^\s*PHASE (\d+) PIPELINE FAILED AT (\S.*)$")
FAIL_MOD_LINE = re.compile(r"^\s*FAIL (\w+) -- (.*)$")
FIX_ATTEMPT_HDR = re.compile(r"^\s*#\s+(\w+): fix attempt (\d+)/(\d+)\s*$")
ROOT_CAUSE_LINE = re.compile(r"^\s*ROOT CAUSE \(([^)]*)\):")
FIX_OUTCOME_LINE = re.compile(
    r"^\s*(\w+): (FIXED|still failing after this patch|unresolved)")
FAILING_MODULES_LINE = re.compile(r"^\s*Failing module\(s\): (.+)$")
FIX_ERROR_LINE = re.compile(r"^\s*ERROR: response hit max_tokens")
VAL_FAIL_LINE = re.compile(
    r"^rtl_validation\s+FAIL\b.*?failed modules:\s*([^;]+).*?round_(\d+)")
SIMULATE_HDR_LINE = re.compile(r"^\s*\[4\] simulate (\d+) path")
PATH_LINE = re.compile(r"^\s*(path_\w+)\s+(PASS|FAIL|ERROR)\s*$")
PATH_SUMMARY_LINE = re.compile(r"^\s*pass=(\d+)\s+fail=(\d+)\s+error=(\d+)")

LINE = re.compile(r"^\[(\d\d):(\d\d):(\d\d)\] (.*)$")
RECORD = re.compile(r"^([a-z_]+)(?::(\S+))?\s+([A-Z_]+)\s*(.*)$")

# --------------------------------------------------------------------------
# backend steps (pipeline.py: intake -> packager -> runner/ORFS -> reporter
# -> validator -> tuners -> runner again ...)
# --------------------------------------------------------------------------

# key, label, weight (share of a typical full-chip build; sums to 100)
BACKEND_STEPS = [
    ("intake", "Intake check", 1),
    ("packager", "Package for ORFS", 1),
    ("synth", "Synthesis (Yosys)", 7),
    ("floorplan", "Floorplan + power grid", 4),
    ("place", "Placement", 16),
    ("cts", "Clock tree synthesis", 8),
    ("grt", "Global routing", 7),
    ("route", "Detailed routing", 36),
    ("finish", "Finish + GDSII", 6),
    ("signoff", "DRC + LVS sign-off", 12),
    ("sta", "Timing sign-off (STA)", 2),
]
ORFS_STEPS = ["synth", "floorplan", "place", "cts", "grt", "route", "finish"]
# ORFS log files each stage writes (newer and older ORFS name a few differently)
ORFS_EXPECTED_FILES = {"synth": 2, "floorplan": 4, "place": 5, "cts": 1, "grt": 1,
                       "route": 2, "finish": 2}
# a typical full-chip ORFS pass, used for time-based guesses until a pass has been seen
DEFAULT_ORFS_SECONDS = 3600.0

BK_MARKERS = [
    (re.compile(r"^\[intake\] Running"), "intake", "start"),
    (re.compile(r"^\[intake\] Status=(\w+)"), "intake", "status"),
    (re.compile(r"^\[packager\] Running"), "packager", "start"),
    (re.compile(r"^\[packager\] Status=(\w+)"), "packager", "status"),
    (re.compile(r"^\[runner\] Executing"), "orfs", "start"),
    (re.compile(r"^\[runner\] mode=.*skipping ORFS"), "orfs", "skip"),
    (re.compile(r"^\[runner\] exit_code=(-?\d+)"), "orfs", "end"),
    (re.compile(r"^\[validator\] Running sign-off"), "signoff", "start"),
    (re.compile(r"^\[validator\] Running STA"), "sta", "start"),
    (re.compile(r"^\[validator\] (DRC|LVS|STA) (HARD FAIL|NOT VERIFIED|MISMATCH|FAIL|soft fail)"),
     "validator", "fail"),
    (re.compile(r"^\[validator\] Runner did not complete"), "validator", "skip"),
    (re.compile(r"^\[(tuner|fmax_tuner|power_tuner|repair)\]\s*(.*)"), "tune", "note"),
]


def orfs_stage_of(fname):
    """ORFS log file name -> backend step key."""
    m = re.match(r"^(\d)_(\d)?", fname)
    if not m:
        return None
    major, minor = m.group(1), m.group(2)
    if major == "5":
        return "grt" if minor == "1" else "route"
    return {"1": "synth", "2": "floorplan", "3": "place", "4": "cts", "6": "finish"}.get(major)


def read_tail(path, nbytes=65536):
    try:
        with open(path, "rb") as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            f.seek(max(0, size - nbytes))
            return f.read().decode("utf-8", "replace")
    except OSError:
        return ""


def load_json(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def iso_to_epoch(s):
    try:
        return datetime.fromisoformat(s).timestamp()
    except (TypeError, ValueError):
        return None


def env_file_value(key):
    """One key from backend/agents/.env (only that key is read out)."""
    path = os.path.join(ROOT, "backend", "agents", ".env")
    try:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line.startswith(key + "="):
                    return line.split("=", 1)[1].strip().strip('"').strip("'")
    except OSError:
        pass
    return None


# --------------------------------------------------------------------------
# flow.log
# --------------------------------------------------------------------------

def parse_flow_log(path, created_epoch):
    """Lines of flow.log as (epoch, body). flow.log stamps HH:MM:SS local
    time only, so the date comes from the run's creation and rolls over when
    the clock goes backwards."""
    out = []
    try:
        with open(path, errors="replace") as f:
            lines = f.read().splitlines()
    except OSError:
        return out
    base = datetime.fromtimestamp(created_epoch or time.time())
    day = base.replace(hour=0, minute=0, second=0, microsecond=0)
    prev = None
    last_t = created_epoch or time.time()
    for raw in lines:
        m = LINE.match(raw)
        if not m:
            out.append((last_t, raw))
            continue
        sod = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3))
        if prev is not None and sod < prev - 3600:
            day += timedelta(days=1)
        prev = sod
        last_t = (day + timedelta(seconds=sod)).timestamp()
        out.append((last_t, m.group(4)))
    return out


def stage_of_cmd(body):
    for rx, stage in CMD_STAGES:
        if rx.search(body):
            return stage
    return None


# --------------------------------------------------------------------------
# ORFS step logs
# --------------------------------------------------------------------------

def orfs_log_root(orfs_dir, platform):
    if not orfs_dir:
        return None
    p = os.path.join(orfs_dir, "flow", "logs", platform)
    return p if os.path.isdir(p) else None


def find_orfs_design(log_root, since):
    """The design ORFS is writing logs for right now: the one whose base/
    has the newest log written since `since`."""
    best, best_t = None, 0
    for d in glob.glob(os.path.join(log_root, "*", "base")):
        for f in glob.glob(os.path.join(d, "*.log")):
            try:
                t = os.path.getmtime(f)
            except OSError:
                continue
            if t >= since - 5 and t > best_t:
                best, best_t = d, t
    return best


def parse_place(text):
    """Global placement: overflow falls from ~1.0 to the 0.1 target."""
    ovs = re.findall(r"overflow:\s*([0-9.]+)", text)
    if not ovs:   # newer OpenROAD prints a table: iter | overflow | HPWL ...
        ovs = [m.group(2) for m in re.finditer(r"^\s*(\d+)\s*\|\s*([0-9.]+)\s*\|", text, re.M)]
    if not ovs:
        return None, None
    ov = float(ovs[-1])
    return max(0.0, min(1.0, (1.0 - ov) / 0.9)), f"overflow {ov:.3f}"


def parse_route(text):
    """Detailed routing: iteration 0 does the bulk; later iterations clear
    violations."""
    iters = re.findall(r"Start (\d+)(?:st|nd|rd|th) optimization iteration", text)
    pct = re.findall(r"Completing (\d+)% with (\d+) violations", text)
    viol_end = re.findall(r"Number of violations = (\d+)", text)
    if not iters and not pct:
        return None, None, None
    it = int(iters[-1]) if iters else 0
    p = int(pct[-1][0]) / 100.0 if pct else 0.0
    v = int(viol_end[-1]) if viol_end else (int(pct[-1][1]) if pct else None)
    if it == 0:
        frac = 0.65 * p
    else:
        frac = min(0.97, 0.65 + 0.32 * (1 - math.exp(-(it - 1 + p) / 3.0)))
    detail = f"iteration {it}, {p * 100:.0f}%" + (f", {v} violations" if v is not None else "")
    return frac, detail, v


def synth_cells(orfs_dir, platform, design):
    if not (orfs_dir and design):
        return None
    for name in ("synth_stat.txt", "synth_stat.rpt"):
        txt = read_tail(os.path.join(orfs_dir, "flow", "reports", platform, design, "base", name), 400000)
        m = re.findall(r"Number of cells:?\s+(\d+)", txt) or re.findall(r"^\s*(\d+)\s+[0-9.E+-]+\s+cells\s*$", txt, re.M)
        if m:
            return int(m[-1])
    return None


def orfs_progress(log_dir, since, now, expected_total, running):
    """Per-step state for one ORFS pass from its step logs."""
    files = []
    for f in glob.glob(os.path.join(log_dir, "*.log")):
        try:
            t = os.path.getmtime(f)
        except OSError:
            continue
        if t < since - 5:
            continue
        name = os.path.basename(f)
        st = orfs_stage_of(name)
        if st:
            files.append((t, name, st, f))
    files.sort()
    steps = {k: {"state": "pending", "frac": 0.0, "detail": "", "started": None, "ended": None}
             for k in ORFS_STEPS}
    if not files:
        return steps, None, {}
    by_stage = {}
    for t, name, st, f in files:
        by_stage.setdefault(st, []).append((t, name, f))
    cur_t, cur_name, cur_stage, cur_file = files[-1]
    cur_idx = ORFS_STEPS.index(cur_stage)
    extra = {}
    for i, k in enumerate(ORFS_STEPS):
        lst = by_stage.get(k, [])
        s = steps[k]
        if lst:
            s["ended"] = lst[-1][0]
        if i < cur_idx:
            s["state"], s["frac"] = "done", 1.0
        elif i == cur_idx:
            s["state"] = "active" if running else "done"
            nexp = ORFS_EXPECTED_FILES[k]
            ndone = max(0, len(lst) - 1)
            inner, detail = None, ""
            txt = read_tail(cur_file)
            if k == "place" and "place_gp" in cur_name and "skip_io" not in cur_name:
                inner, detail = parse_place(txt)
            elif k == "route" and "route" in cur_name:
                inner, detail, v = parse_route(txt)
                if v is not None:
                    extra["violations"] = v
            if inner is None:   # time-based guess with a ceiling
                weight = dict((a, c) for a, _, c in BACKEND_STEPS)[k]
                tau = max(20.0, expected_total * weight / 80.0 / nexp)
                # the step started when the previous log stopped growing
                prev_t = files[-2][0] if len(files) > 1 else since
                inner = 0.9 * (1 - math.exp(-(now - prev_t) / tau))
            s["frac"] = min(0.99, (ndone + inner) / max(nexp, len(lst))) if running else 1.0
            s["detail"] = detail or cur_name.replace(".tmp", "").replace(".log", "")
    # the router's last violation count stays on show after routing ends
    if "violations" not in extra:
        for t, name, f in by_stage.get("route", []):
            if "route" in name:
                _, _, v = parse_route(read_tail(f))
                if v is not None:
                    extra["violations"] = v
    # start time of each step = end of the previous one's last log
    prev_end = since
    for k in ORFS_STEPS:
        s = steps[k]
        if s["state"] != "pending":
            s["started"] = prev_end
            prev_end = s["ended"] or prev_end
    return steps, cur_stage, extra


# --------------------------------------------------------------------------
# the status a page polls
# --------------------------------------------------------------------------

class Watcher:
    def __init__(self, runs_root, run=None, orfs_dir=None, platform=None):
        self.runs_root = runs_root
        self.fixed_run = run
        self.orfs_dir = orfs_dir or os.environ.get("ORFS_DIR") or env_file_value("ORFS_DIR")
        if self.orfs_dir and not os.path.isdir(self.orfs_dir):
            self.orfs_dir = None
        self.platform = platform or os.environ.get("PLATFORM") or env_file_value("PLATFORM") or "sky130hd"
        self.orfs_seconds = {}   # (run, round) -> measured seconds of a finished ORFS pass

    def list_runs(self):
        out = []
        for d in glob.glob(os.path.join(self.runs_root, "*", "RUN_STATE.json")):
            rd = os.path.dirname(d)
            st = load_json(d) or {}
            out.append({"id": os.path.basename(rd), "status": st.get("status"),
                        "updated": st.get("updated_utc") or st.get("created_utc"),
                        "mtime": max(os.path.getmtime(d),
                                     os.path.getmtime(os.path.join(rd, "flow.log"))
                                     if os.path.exists(os.path.join(rd, "flow.log")) else 0)})
        out.sort(key=lambda r: r["mtime"], reverse=True)
        return out

    def resolve_run(self, run_id):
        if run_id:
            p = os.path.join(self.runs_root, os.path.basename(run_id))
            if os.path.isdir(p):
                return p
        if self.fixed_run:
            return self.fixed_run
        runs = self.list_runs()
        return os.path.join(self.runs_root, runs[0]["id"]) if runs else None

    def block_cells(self):
        d = load_json(os.path.join(ROOT, "backend", "outputs", "NETLISTS.json")) or {}
        blocks = d.get("blocks", d) if isinstance(d, dict) else {}
        out = {}
        for k, v in blocks.items():
            if isinstance(v, dict) and isinstance(v.get("cell_count"), int):
                out[k] = v["cell_count"]
        return out or {m: 1000 for ms in PHASE_MODULES.values() for m in ms}

    def status(self, run_id=None):
        now = time.time()
        run_dir = self.resolve_run(run_id)
        res = {"now": now, "runs": self.list_runs()[:40], "block_cells": self.block_cells(),
               "phase_modules": PHASE_MODULES, "orfs_dir": self.orfs_dir, "platform": self.platform}
        if not run_dir:
            res["run"] = None
            return res
        state = load_json(os.path.join(run_dir, "RUN_STATE.json")) or {}
        created = iso_to_epoch(state.get("created_utc")) or os.path.getctime(run_dir)
        log = parse_flow_log(os.path.join(run_dir, "flow.log"), created)
        try:
            log_mtime = os.path.getmtime(os.path.join(run_dir, "flow.log"))
        except OSError:
            log_mtime = created

        run = {"id": os.path.basename(run_dir), "dir": os.path.relpath(run_dir, ROOT),
               "status": state.get("status", "unknown"), "created": created,
               "updated": iso_to_epoch(state.get("updated_utc")), "halt": state.get("halt"),
               "rounds": state.get("rounds", {}), "log_mtime": log_mtime}
        res["run"] = run
        res["stages"], cur = self._flow_stages(state, log, run["status"])
        res["current"] = cur
        res["rtl"] = self._rtl_state(state, log)
        res["frontend"] = self._frontend_state(state, log)
        res["validation"] = self._validation_state(state, log)
        res["backend"] = self._backend(run_dir, state, log, now, cur)
        tail = [(t, b) for t, b in log[-200:]]
        res["log_tail"] = [{"t": t, "line": b} for t, b in tail]
        # is anything still being written?
        last_write = max(log_mtime, res["backend"].get("last_write") or 0)
        run["quiet_s"] = now - last_write
        return res

    # -- flow stage strip -------------------------------------------------
    def _flow_stages(self, state, log, run_status):
        stages = {k: {"key": k, "label": lab, "state": "pending", "started": None,
                      "ended": None, "detail": "", "count": 0}
                  for k, lab in FLOW_STAGES}
        current = None
        for t, body in log:
            if body.startswith("$ "):
                st = stage_of_cmd(body)
                if st:
                    key = STAGE_ALIAS.get(st, st)
                    if current is None or current["stage"] != st:
                        current = {"stage": st, "key": key, "since": t, "cmd": body[2:][:200]}
                    s = stages[key]
                    if s["state"] != "active":
                        s["started"] = t
                    s["state"] = "active"
                continue
            m = RECORD.match(body)
            if m and m.group(1) in stages or (m and m.group(1) in STAGE_ALIAS):
                st, tag, status, detail = m.groups()
                key = STAGE_ALIAS.get(st, st)
                s = stages[key]
                mapped = STATUS_MAP.get(status, "info")
                if st in STAGE_ALIAS and mapped == "pass":
                    mapped = "active"   # a repair passed: generation continues
                if s["started"] is None:
                    s["started"] = t
                s["state"] = mapped
                s["ended"] = t if mapped != "active" else None
                s["detail"] = (f"{tag}: " if tag else "") + detail[:240]
                if st == key and status in ("PASS", "FAIL"):
                    s["count"] += 1
                if current and STAGE_ALIAS.get(current["stage"], current["stage"]) == key:
                    current = None
        # RUN_STATE is authoritative for outcomes (flow.log may be truncated)
        for rec in state.get("stages", []):
            key = STAGE_ALIAS.get(rec["stage"].split(":")[0], rec["stage"].split(":")[0])
            if key in stages and stages[key]["state"] == "pending":
                stages[key]["state"] = STATUS_MAP.get(rec["status"], "info")
                stages[key]["detail"] = rec.get("detail", "")[:240]
                stages[key]["ended"] = iso_to_epoch(rec.get("utc"))
        if run_status != "running":
            for s in stages.values():
                if s["state"] == "active":
                    s["state"] = "halt" if run_status == "halted" else "pass"
            current = None
        return [stages[k] for k, _ in FLOW_STAGES], current

    def _rtl_state(self, state, log):
        """Per-phase RTL status, for the floorplan's block outlines."""
        phases = {str(n): "pending" for n in PHASE_MODULES}
        phases["top"] = "pending"
        cur = None
        for t, body in log:
            m = re.match(r"^-- phase (\d):", body)
            if m:
                cur = m.group(1)
                phases[cur] = "active"
                continue
            if body.startswith("$ ") and "generate_top.py" in body:
                phases["top"] = "active"
            m = RECORD.match(body)
            if m and m.group(1) == "rtl_generation":
                d = m.group(4)
                pm = re.match(r"phase (\d)", d)
                if pm:
                    phases[pm.group(1)] = STATUS_MAP.get(m.group(3), "info")
                elif "top-level" in d:
                    phases["top"] = STATUS_MAP.get(m.group(3), "info")
        validated = any(s["stage"] == "rtl_validation" and s["status"] == "PASS"
                        for s in state.get("stages", []))
        return {"phases": phases, "validated": validated}

    def _frontend_state(self, state, log):
        """Per-phase, per-module generation/lint/sim status, plus the
        Frontend's own fix-loop (a module failing its own phase's sim gate,
        or Validation sending a module back) -- the detail behind the
        single `rtl_generation` dot in the stage strip."""
        phases = {n: {"n": n, "modules": {m: "pending" for m in mods},
                      "result": "pending", "failing_module": None,
                      "started": None, "ended": None}
                  for n, mods in PHASE_MODULES.items()}
        section = None
        cur_phase = None
        fixloop = []
        cur_fix = None
        last_trigger = None   # {"kind": "validation"|"own_sim_gate", "round": n, "modules": [...]}

        def find_open(mod):
            return next((f for f in reversed(fixloop)
                        if f["module"] == mod and f["outcome"] is None), None)

        for t, body in log:
            m = PHASE_START_LINE.match(body)
            if m:
                cur_phase = int(m.group(1))
                if cur_phase in phases:
                    phases[cur_phase]["started"] = phases[cur_phase]["started"] or t
                    phases[cur_phase]["result"] = "active"
                section = None
                continue
            if GEN_CHECK_HDR.match(body):
                section = "gen"
                continue
            if LINT_GATE_HDR.search(body):
                section = "lint"
                continue
            if SIM_GATE_HDR.search(body):
                section = "sim"
                continue
            m = MOD_STATUS_LINE.match(body)
            if m and cur_phase in phases and m.group(2) in phases[cur_phase]["modules"]:
                tag, mod = m.group(1), m.group(2)
                if tag in ("OK", "FAIL"):
                    phases[cur_phase]["modules"][mod] = "pass" if tag == "OK" else "fail"
                continue
            m = PHASE_PASS_LINE.match(body)
            if m:
                n = int(m.group(1))
                if n in phases:
                    phases[n]["result"] = "pass"
                    phases[n]["ended"] = t
                continue
            m = PHASE_FAIL_LINE.match(body)
            if m:
                n = int(m.group(1))
                if n in phases:
                    phases[n]["result"] = "fail"
                    phases[n]["ended"] = t
                continue
            m = FAIL_MOD_LINE.match(body)
            if m and cur_phase in phases:
                mod = m.group(1)
                phases[cur_phase]["failing_module"] = mod
                if mod in phases[cur_phase]["modules"]:
                    phases[cur_phase]["modules"][mod] = "fail"
                last_trigger = {"kind": "own_sim_gate", "round": None, "modules": [mod], "t": t}
                continue
            m = VAL_FAIL_LINE.match(body)
            if m:
                mods = [x.strip() for x in m.group(1).split(",")]
                last_trigger = {"kind": "validation", "round": int(m.group(2)), "modules": mods, "t": t}
                continue
            m = FAILING_MODULES_LINE.match(body)
            if m:
                mods = [x.strip() for x in m.group(1).split(",")]
                if last_trigger and set(last_trigger["modules"]) & set(mods):
                    last_trigger = {**last_trigger, "modules": mods, "t": t}
                else:
                    last_trigger = {"kind": "own_sim_gate", "round": None, "modules": mods, "t": t}
                continue
            m = FIX_ATTEMPT_HDR.match(body)
            if m:
                mod, att, mx = m.group(1), int(m.group(2)), int(m.group(3))
                trig = last_trigger if last_trigger and mod in last_trigger["modules"] else None
                cur_fix = {"module": mod, "attempt": att, "max_attempts": mx,
                           "phase": cur_phase, "started": t, "ended": None,
                           "confidence": None, "outcome": None, "trigger": trig}
                fixloop.append(cur_fix)
                continue
            m = ROOT_CAUSE_LINE.match(body)
            if m and cur_fix:
                cur_fix["confidence"] = m.group(1)
                continue
            if FIX_ERROR_LINE.match(body) and cur_fix:
                cur_fix["outcome"] = "error"
                cur_fix["ended"] = t
                cur_fix = None
                continue
            m = FIX_OUTCOME_LINE.match(body)
            if m:
                mod, outcome = m.group(1), m.group(2)
                if outcome == "unresolved":
                    # The loop's own final verdict, one line after the last
                    # attempt's "still failing" already closed it out --
                    # overwrite that attempt's outcome, not a fresh (absent)
                    # open one, so the loop's actual end isn't dropped.
                    target = next((f for f in reversed(fixloop) if f["module"] == mod), None)
                else:
                    target = cur_fix if cur_fix and cur_fix["module"] == mod else find_open(mod)
                if target:
                    target["outcome"] = ("fixed" if outcome == "FIXED" else
                                         "unresolved" if outcome == "unresolved" else
                                         "retry")
                    target["ended"] = t
                    if target is cur_fix:
                        cur_fix = None
                continue

        return {"phases": [phases[n] for n in sorted(phases)],
                "fixloop": fixloop[-25:], "active_fix": cur_fix,
                "round": state.get("rounds", {}).get("rtl", 0)}

    def _validation_state(self, state, log):
        """The system-level path suite (validate_drop.py's [4] simulate
        N path(s)) -- every path run this round, not just pass/fail/count,
        plus which modules a FAIL sends back to the Frontend."""
        paths, cur_paths = [], {}
        total = None
        summary = None
        failed_modules = []
        result = "pending"
        started = None

        for t, body in log:
            m = SIMULATE_HDR_LINE.match(body)
            if m:
                total = int(m.group(1))
                cur_paths = {}
                started = t
                result = "active"
                continue
            m = PATH_LINE.match(body)
            if m and total is not None:
                cur_paths[m.group(1)] = m.group(2).lower()
                continue
            m = PATH_SUMMARY_LINE.match(body)
            if m:
                summary = {"pass": int(m.group(1)), "fail": int(m.group(2)), "error": int(m.group(3))}
                paths = [{"name": k, "status": v} for k, v in cur_paths.items()]
                continue
            if body.startswith("rtl_validation"):
                mm = re.match(r"^rtl_validation\s+(\S+)\s+(.*)$", body)
                if mm:
                    status, detail = mm.groups()
                    result = STATUS_MAP.get(status, "info")
                    fm = re.search(r"failed modules:\s*([^;]+)", detail)
                    txt = fm.group(1).strip() if fm else ""
                    failed_modules = [x.strip() for x in txt.split(",")] if txt and txt != "none" else []
                continue

        # RUN_STATE's own round counter is authoritative and always current
        # (a PASS round's detail carries no "round_N" path to parse it from).
        return {"paths": paths, "total": total, "summary": summary,
                "failed_modules": failed_modules, "result": result,
                "round": state.get("rounds", {}).get("rtl", 0), "started": started}

    # -- backend ----------------------------------------------------------
    def _backend(self, run_dir, state, log, now, current):
        bk = {"active": False, "round": state.get("rounds", {}).get("backend", 0),
              "steps": [{"key": k, "label": lab, "weight": w, "state": "pending", "frac": 0.0,
                         "detail": "", "started": None, "ended": None}
                        for k, lab, w in BACKEND_STEPS],
              "progress": 0.0, "eta_s": None, "started": None, "elapsed": None,
              "current_step": None, "result_detail": None,
              "orfs": {"dir_found": bool(self.orfs_dir), "design": None, "pass": 0,
                       "estimated": False},
              "notes": [], "result": None, "report": None, "last_write": None}
        steps = {s["key"]: s for s in bk["steps"]}

        # the last backend invocation in flow.log
        start_i = None
        for i, (t, body) in enumerate(log):
            if body.startswith("$ ") and "backend/agents/pipeline.py" in body:
                start_i = i
        if start_i is None:
            rec = [s for s in state.get("stages", []) if s["stage"] == "backend"]
            if rec:
                bk["result"] = STATUS_MAP.get(rec[-1]["status"], "info")
            return bk
        seg_start = log[start_i][0]
        bk["started"] = seg_start
        seg, end_t, end_status = [], None, None
        for t, body in log[start_i + 1:]:
            m = RECORD.match(body)
            if m and m.group(1) in ("backend",):
                end_t, end_status = t, m.group(3)
                bk["result"] = STATUS_MAP.get(end_status, "info")
                bk["result_detail"] = m.group(4)[:300]
                break
            if m and m.group(1) in dict(FLOW_STAGES):
                break
            seg.append((t, body.strip()))
        running = end_t is None and state.get("status") == "running"
        bk["active"] = running
        bk["elapsed"] = (end_t or now) - seg_start

        # markers -> step timeline
        orfs_passes = []   # (start_t, end_t, skipped)
        def start(k, t):
            s = steps[k]
            if s["state"] == "pending" or s["state"] == "done" and k in ("signoff", "sta"):
                s["state"], s["started"], s["frac"], s["ended"] = "active", t, 0.0, None
        def finish(k, t, ok=True):
            s = steps[k]
            if s["state"] == "active":
                s["state"], s["frac"], s["ended"] = ("done" if ok else "fail"), 1.0, t

        for t, body in seg:
            for rx, k, what in BK_MARKERS:
                m = rx.search(body)
                if not m:
                    continue
                if k in ("intake", "packager"):
                    if what == "start":
                        if k == "packager":
                            finish("intake", t)
                        start(k, t)
                    else:
                        if steps[k]["state"] == "pending":
                            start(k, t)
                        finish(k, t, m.group(1).upper() == "PASS")
                elif k == "orfs":
                    if what == "start":
                        finish("packager", t)
                        orfs_passes.append([t, None, False])
                        for key in ORFS_STEPS + ["signoff", "sta"]:
                            steps[key].update(state="pending", frac=0.0, detail="", started=None, ended=None)
                    elif what == "skip":
                        finish("packager", t)
                        orfs_passes.append([t, t, True])
                    elif orfs_passes and orfs_passes[-1][1] is None:
                        orfs_passes[-1][1] = t
                        orfs_passes[-1].append(int(m.group(1)))
                elif k == "signoff":
                    start("signoff", t)
                elif k == "sta":
                    finish("signoff", t)
                    start("sta", t)
                elif k == "validator":
                    for key in ("sta", "signoff"):
                        if steps[key]["state"] == "active":
                            finish(key, t, False)
                elif k == "tune":
                    bk["notes"].append({"t": t, "text": f"[{m.group(1)}] {m.group(2)}"[:200]})
                break
        bk["notes"] = bk["notes"][-8:]
        bk["orfs"]["pass"] = len([p for p in orfs_passes if not p[2]])

        # ORFS steps for the newest pass
        if orfs_passes:
            p_start, p_end, skipped = orfs_passes[-1][:3]
            exit_code = orfs_passes[-1][3] if len(orfs_passes[-1]) > 3 else None
            if skipped:
                for k in ORFS_STEPS:
                    steps[k].update(state="skip", frac=1.0, detail="mode skips ORFS")
            else:
                orfs_running = p_end is None and running
                key = (os.path.basename(run_dir), len(orfs_passes) - 1)
                prev = [b - a for a, b, s, *_ in orfs_passes[:-1] if b and not s]
                expected = prev[-1] if prev else DEFAULT_ORFS_SECONDS
                log_root = orfs_log_root(self.orfs_dir, self.platform)
                design_dir = find_orfs_design(log_root, p_start) if log_root else None
                if design_dir:
                    design = os.path.basename(os.path.dirname(design_dir))
                    bk["orfs"]["design"] = design
                    osteps, cur, extra = orfs_progress(design_dir, p_start, now, expected, orfs_running)
                    for k, v in osteps.items():
                        steps[k].update(v)
                    bk["orfs"].update(extra)
                    cells = synth_cells(self.orfs_dir, self.platform, design)
                    if cells:
                        bk["orfs"]["cells"] = cells
                    try:
                        bk["last_write"] = max(os.path.getmtime(f) for f in glob.glob(os.path.join(design_dir, "*.log")))
                    except ValueError:
                        pass
                else:
                    # no step logs to read: a time-based estimate across ORFS steps
                    bk["orfs"]["estimated"] = True
                    el = (p_end or now) - p_start
                    total_w = sum(w for k, _, w in BACKEND_STEPS if k in ORFS_STEPS)
                    frac = 1.0 if p_end else min(0.97, el / expected)
                    acc = 0.0
                    for k, _, w in BACKEND_STEPS:
                        if k not in ORFS_STEPS:
                            continue
                        lo, hi = acc / total_w, (acc + w) / total_w
                        acc += w
                        if frac >= hi:
                            steps[k].update(state="done", frac=1.0)
                        elif frac > lo:
                            steps[k].update(state="active" if orfs_running else "done",
                                            frac=(frac - lo) / (hi - lo), detail="estimated from elapsed time")
                if p_end is not None:
                    for k in ORFS_STEPS:
                        if steps[k]["state"] in ("active", "pending"):
                            steps[k].update(state="done" if exit_code == 0 else "fail",
                                            frac=1.0 if exit_code == 0 else steps[k]["frac"])
                    if exit_code not in (0, None):
                        failed = next((k for k in ORFS_STEPS if steps[k]["state"] == "fail"), None)
                        for k in ORFS_STEPS:
                            if steps[k]["state"] == "fail" and k != failed:
                                steps[k]["state"] = "pending"

        # steps with no log of their own: a time-based guess, scaled to how long
        # this design's ORFS pass took (sign-off grows with the layout)
        orfs_dur = None
        if orfs_passes and orfs_passes[-1][1] and not orfs_passes[-1][2]:
            orfs_dur = orfs_passes[-1][1] - orfs_passes[-1][0]
        orfs_w = sum(w for k, _, w in BACKEND_STEPS if k in ORFS_STEPS)
        for s in bk["steps"]:
            if s["state"] == "active" and s["key"] not in ORFS_STEPS and s["started"]:
                tau = max(5.0, (orfs_dur or DEFAULT_ORFS_SECONDS) * s["weight"] / orfs_w)
                s["frac"] = 0.92 * (1 - math.exp(-(now - s["started"]) / tau))
                s["detail"] = s["detail"] or "estimated from elapsed time"

        # backend finished: the report has the numbers
        if end_t is not None:
            reps = sorted(glob.glob(os.path.join(run_dir, "backend", "pipeline_final_report_*.json")),
                          key=os.path.getmtime)
            rep = load_json(reps[-1]) if reps else None
            if rep:
                bk["report"] = {k: rep.get(k) for k in
                                ("pipeline_status", "failed_stage", "drc_violations", "lvs_status",
                                 "sta_wns_ns", "sta_status", "tuner_iterations", "error_message")}
            for s in bk["steps"]:
                if s["state"] == "active":
                    s["state"] = "done" if end_status == "PASS" else "fail"
                    s["ended"] = end_t
            if end_status == "PASS":
                for s in bk["steps"]:
                    if s["state"] in ("pending", "active"):
                        s["state"], s["frac"] = "done", 1.0
        elif not running:
            for s in bk["steps"]:
                if s["state"] == "active":
                    s["state"] = "halt"

        # progress across the steps of this pass
        total = sum(s["weight"] for s in bk["steps"])
        done = 0.0
        for s in bk["steps"]:
            if s["state"] in ("done", "skip"):
                s["frac"] = 1.0
            done += s["weight"] * (s["frac"] if s["state"] != "pending" else 0.0)
        bk["progress"] = 1.0 if (end_status == "PASS") else min(0.999, done / total)
        cur_step = next((s for s in bk["steps"] if s["state"] == "active"), None)
        bk["current_step"] = cur_step["key"] if cur_step else None
        if running and bk["progress"] > 0.03:
            pass_start = orfs_passes[-1][0] if orfs_passes and not orfs_passes[-1][2] else seg_start
            pre = sum(s["weight"] for s in bk["steps"] if s["key"] in ("intake", "packager")) / total
            pp = max(1e-3, bk["progress"] - (pre if orfs_passes else 0))
            el = now - pass_start
            bk["eta_s"] = max(0.0, el * (1 - bk["progress"]) / pp) if pp > 0.02 else None
        return bk


# --------------------------------------------------------------------------
# HTTP
# --------------------------------------------------------------------------

def make_handler(watcher, terminal=None, token="", off_reason=""):
    page_path = os.path.join(HERE, "index.html")

    class H(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *a):
            pass

        def _send(self, code, body, ctype):
            data = body.encode() if isinstance(body, str) else body
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def _json(self, code, obj):
            return self._send(code, json.dumps(obj, default=str), "application/json")

        def _host_ok(self):
            # only pages served from this machine (blocks DNS-rebinding sites)
            host = (self.headers.get("Host") or "").rsplit(":", 1)[0].strip("[]")
            return host in ("127.0.0.1", "localhost", "::1")

        def _token_ok(self, q=None):
            got = self.headers.get("X-Flow-Token") or ((q or {}).get("token") or [""])[0]
            return bool(token) and hmac.compare_digest(got, token)

        def do_GET(self):
            if not self._host_ok():
                return self._send(403, "forbidden", "text/plain")
            u = urlparse(self.path)
            q = parse_qs(u.query)
            if u.path in ("/", "/index.html"):
                with open(page_path, encoding="utf-8") as f:
                    page = f.read()
                page = page.replace("__FLOW_GUI_TOKEN__", token if terminal else "")
                return self._send(200, page, "text/html; charset=utf-8")
            if u.path == "/api/status":
                try:
                    st = watcher.status((q.get("run") or [None])[0])
                except Exception as e:   # a half-written file: say so, the page retries
                    return self._json(500, {"error": f"{type(e).__name__}: {e}"})
                st["terminal"] = terminal.state() if terminal else {"available": False, "reason": off_reason}
                return self._json(200, st)
            if u.path == "/api/term/stream":
                if not (terminal and self._token_ok(q)):
                    return self._send(403, "forbidden", "text/plain")
                return self._stream(q)
            return self._send(404, "not found", "text/plain")

        def do_POST(self):
            if not self._host_ok():
                return self._send(403, "forbidden", "text/plain")
            u = urlparse(self.path)
            n = int(self.headers.get("Content-Length") or 0)
            body = self.rfile.read(n) if n else b""
            if not (terminal and self._token_ok()):
                return self._json(403, {"error": "forbidden"})
            try:
                if u.path == "/api/term/input":
                    terminal.write(body)
                    return self._json(200, {"ok": True})
                req = json.loads(body or b"{}")
                if u.path == "/api/term/start":
                    return self._json(200, terminal.start(req.get("args", ""), req.get("cols"), req.get("rows")))
                if u.path == "/api/term/resize":
                    terminal.resize(req.get("cols", 120), req.get("rows", 36))
                    return self._json(200, {"ok": True})
                if u.path == "/api/term/interrupt":
                    terminal.interrupt()
                    return self._json(200, terminal.state())
            except (RuntimeError, ValueError, OSError) as e:
                return self._json(409, {"error": str(e)})
            return self._json(404, {"error": "not found"})

        def _stream(self, q):
            """Server-sent events: terminal output, base64, from an offset
            (the browser resends its last id when it reconnects)."""
            try:
                since = int(self.headers.get("Last-Event-ID") or (q.get("from") or ["0"])[0])
            except ValueError:
                since = 0
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            self.close_connection = True
            try:
                while True:
                    data, end, reset = terminal.read(since)
                    if reset:
                        self.wfile.write(b"event: reset\ndata: \n\n")
                    if data or reset:
                        payload = base64.b64encode(data).decode()
                        self.wfile.write(f"id: {end}\ndata: {payload}\n\n".encode())
                        self.wfile.flush()
                        since = end
                    elif not terminal.wait(since, 15):
                        self.wfile.write(b": ping\n\n")
                        self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, OSError):
                return

    return H


OFF_FROM_FLOW = ("this page was opened by flow.py --gui; type into the terminal you started "
                 "that run from")


def serve(watcher, port=8765, open_browser=True, host="127.0.0.1", terminal=None,
          off_reason=OFF_FROM_FLOW):
    """Start the server in a daemon thread; returns (server, url). With a
    FlowTerminal the page can start flow.py and type into it."""
    token = secrets.token_urlsafe(24)
    for p in range(port, port + 20):
        try:
            srv = ThreadingHTTPServer((host, p), make_handler(watcher, terminal, token, off_reason))
            break
        except OSError:
            continue
    else:
        raise OSError(f"no free port in {port}..{port + 19}")
    srv.daemon_threads = True
    url = f"http://{host}:{srv.server_address[1]}/"
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    if open_browser:
        threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    return srv, url


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", help="run directory to watch (default: newest under runs/)")
    ap.add_argument("--runs-root", default=os.path.join(ROOT, "runs"))
    ap.add_argument("--orfs-dir", help="OpenROAD-flow-scripts checkout (default: ORFS_DIR)")
    ap.add_argument("--platform", help="ORFS platform (default: PLATFORM or sky130hd)")
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--no-browser", action="store_true")
    ap.add_argument("--demo", action="store_true", help="simulate a whole run, no ORFS needed")
    ap.add_argument("--demo-minutes", type=float, default=4.0, help="length of the simulated run")
    ap.add_argument("--no-terminal", action="store_true",
                    help="watch only: no terminal panel that can start flow.py")
    args = ap.parse_args()
    sys.path.insert(0, HERE)
    import flow_terminal
    terminal = None

    if args.demo:
        sys.path.insert(0, HERE)
        import demo_run
        sim = demo_run.Demo(minutes=args.demo_minutes)
        threading.Thread(target=sim.run, daemon=True).start()
        watcher = Watcher(sim.runs_root, run=sim.run_dir, orfs_dir=sim.orfs_dir, platform="sky130hd")
        print(f"demo run in {sim.root}")
    else:
        run = os.path.abspath(args.run) if args.run else None
        watcher = Watcher(os.path.abspath(args.runs_root), run=run,
                          orfs_dir=args.orfs_dir, platform=args.platform)
        if not watcher.orfs_dir:
            print("note: ORFS_DIR not found; backend steps will be estimated from elapsed time")
        if not args.no_terminal:
            terminal = flow_terminal.FlowTerminal(ROOT)
    off = ("demo mode: the page only watches the simulated run" if args.demo else
           "started with --no-terminal" if args.no_terminal else flow_terminal.WHY_NOT or "")
    srv, url = serve(watcher, args.port, not args.no_browser, terminal=terminal, off_reason=off)
    print(f"flow GUI at {url}  (ctrl-c to stop"
          + (", which also stops a run started from the page)" if terminal else ")"))
    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        if terminal and terminal.running():
            print("stopping the run started from the page")
            terminal.close()
        srv.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())
