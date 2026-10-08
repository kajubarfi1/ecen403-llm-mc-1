#!/usr/bin/env python3
"""
flow.py — the LLM-MC design flow, one command
=============================================
Connects the three subsystems in the order the project runs them:

    request ──► FRONTEND spec synthesis
                     │
                     ▼
              VALIDATION spec review ──FAIL──► halt (review in the run dir)
                     │ PASS
                     ▼
              FRONTEND RTL generation (phases 1-4, top-level assembly)
                     │
                     ▼
              VALIDATION of the RTL drop ──FAIL──► FRONTEND regeneration ──┐
                     │ PASS                        (feedback agent; capped)│
                     ▼                                                     │
              BACKEND RTL → GDSII ──needs a frontend change──► FRONTEND ───┘
                     │ PASS                                      (then validation again)
                     ▼
              VALIDATION of the backend netlist on the same paths (final)

Every run lives in runs/<run_id>/ with a RUN_STATE.json that records each
stage's outcome, so a halted run resumes where it stopped once a person has
dealt with what stopped it (`--resume runs/<run_id>`). Each loop has a fixed
cap; on exhaustion the run halts with the last package in place rather than
spinning.

Subsystems are driven through their own entry points, non-interactively, and
nothing here re-implements any of them:

  Frontend2/scripts/Microarch/microarch_cli.py   spec from English / preset / choices
  Frontend2/scripts/Phase{1..4}/phase{N}_pipeline.py   RTL per phase (stdin: spec, out dir)
  Frontend2/scripts/generate_top.py              top-level assembly (TOPRTL/)
  Validation/spec/validate_spec_stage.py         spec review
  Validation/tools/validate_drop.py              RTL validation (findings -> outbox/current)
  backend/agents/pipeline.py                     RTL -> GDSII (Docker + ORFS)

Two edges are defined but wait for a counterpart that does not exist yet, and
say so instead of pretending:
  * validation -> frontend regeneration goes through the Frontend's phase
    validation agents (Phase{N}/phase{N}_validation_agent.py). They take our
    retry_instructions.json directly (--findings); an agent without that
    option gets our findings rendered as its phase error report. Phases that
    have no agent yet (3, 4) halt with the package.
  * backend -> frontend: the backend's findings (backend/findings/outbox, in
    Validation's envelope) become a retry package through the same adapter
    and go to the Frontend's phase agents; the regenerated drop is validated
    again before the backend runs again.
  * final validation runs the backend's per-block netlists through every
    path that instantiates the block (run_path --netlist, sky130 models
    installed on the simulator); a top-level netlist waits for a top-level path.

Usage:
    python3 flow.py "DDR3-1333 x16, one byte lane, balanced"       # English
    python3 flow.py --preset balanced
    python3 flow.py --choices my_choices.json
    python3 flow.py --spec Spec/llmmc_microarchitecturespec_filled.json   # skip synthesis
    python3 flow.py --resume runs/20261001-153000-ddr3_1333
    python3 flow.py --preset balanced --dry-run                     # print the plan only
Options: --max-spec-rounds 1 --max-rtl-rounds 4 --max-backend-rounds 2
         --validate-per-phase  --skip-backend  --run-dir DIR  --from STAGE
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.abspath(__file__))
PY = sys.executable
RUNS = os.path.join(ROOT, "runs")

FRONTEND = os.path.join(ROOT, "Frontend2", "scripts")
MICROARCH_CLI = os.path.join(FRONTEND, "Microarch", "microarch_cli.py")
GENERATE_TOP = os.path.join(FRONTEND, "generate_top.py")
# The Frontend's repair agents: one per phase, reading that phase's
# VALIDATIONREPORT/phase{N}_error_report.json (Validation writes ours in that
# shape, see Validation/findings/to_frontend_error_report.py). Phases without
# one halt the run with the package.
def phase_agent(n):
    return os.path.join(FRONTEND, f"Phase{n}", f"phase{n}_validation_agent.py")


TO_ERROR_REPORT = os.path.join(ROOT, "Validation", "findings", "to_frontend_error_report.py")


def agent_findings_flag(agent):
    """The option under which the agent takes retry_instructions.json itself
    (`--findings`, Frontend 2026-10-01; `--retry` was our name for it), or
    None when it only reads the phase error report."""
    try:
        r = subprocess.run([PY, agent, "--help"], capture_output=True, text=True, timeout=60)
        text = r.stdout + r.stderr
    except Exception:
        return None
    for flag in ("--findings", "--retry"):
        if flag in text:
            return flag
    return None


def agent_takes_yes(agent):
    try:
        r = subprocess.run([PY, agent, "--help"], capture_output=True, text=True, timeout=60)
        return "--yes" in (r.stdout + r.stderr)
    except Exception:
        return False
PHASES = [(1, "Phase1", "phase1_pipeline.py", "PHASE1RTL", ["init_fsm", "config_regs", "wb_port"]),
          (2, "Phase2", "phase2_pipeline.py", "PHASE2RTL", ["addr_decoder", "bank_tracker", "refresh_ctrl", "calibration"]),
          (3, "Phase3", "phase3_pipeline.py", "PHASE3RTL", ["cmd_queue", "scheduler", "cmd_gen"]),
          (4, "Phase4", "phase4_pipeline.py", "PHASE4RTL", ["data_path"])]
VALIDATION = os.path.join(ROOT, "Validation")
SPEC_STAGE = os.path.join(VALIDATION, "spec", "validate_spec_stage.py")
VALIDATE_DROP = os.path.join(VALIDATION, "tools", "validate_drop.py")
OUTBOX_CURRENT = os.path.join(VALIDATION, "findings", "outbox", "current")
BACKEND_AGENTS = os.path.join(ROOT, "backend", "agents")
BACKEND_PIPELINE = os.path.join(BACKEND_AGENTS, "pipeline.py")

QUIET = False          # tests: keep the run log out of stdout

STAGES = ["spec_synthesis", "spec_review", "rtl_generation", "rtl_validation",
          "frontend_regeneration", "backend", "backend_to_frontend",
          "final_validation"]


# --------------------------------------------------------------------------
# run state
# --------------------------------------------------------------------------

class Run:
    """runs/<run_id>/: everything a run produced, and RUN_STATE.json."""

    def __init__(self, run_dir, args=None):
        self.dir = run_dir
        self.state_path = os.path.join(run_dir, "RUN_STATE.json")
        self.log_path = os.path.join(run_dir, "flow.log")
        if os.path.exists(self.state_path):
            with open(self.state_path) as f:
                self.state = json.load(f)
        else:
            os.makedirs(run_dir, exist_ok=True)
            self.state = {"$schema": "llmmc-flow-run/1",
                          "run_id": os.path.basename(run_dir),
                          "created_utc": _now(),
                          "request": vars(args) if args else {},
                          "stages": [], "rounds": {"spec": 0, "rtl": 0, "backend": 0},
                          "status": "running", "halt": None,
                          "spec": None, "drop": None, "netlist": None}
            self.save()

    # paths inside the run
    @property
    def spec_dir(self): return os.path.join(self.dir, "spec")
    @property
    def drop(self): return os.path.join(self.dir, "drop")
    @property
    def val_dir(self): return os.path.join(self.dir, "validation")
    @property
    def backend_dir(self): return os.path.join(self.dir, "backend")

    def save(self):
        self.state["updated_utc"] = _now()
        with open(self.state_path, "w") as f:
            json.dump(self.state, f, indent=2)

    def log(self, msg):
        line = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
        if not QUIET:
            print(line)
        with open(self.log_path, "a") as f:
            f.write(line + "\n")

    def record(self, stage, status, detail="", **extra):
        self.state["stages"].append({"stage": stage, "status": status, "detail": detail,
                                     "utc": _now(), **extra})
        self.save()
        self.log(f"{stage:22} {status:8} {detail}")

    def halt(self, stage, why, **extra):
        self.state["status"] = "halted"
        self.state["halt"] = {"stage": stage, "why": why, "utc": _now(), **extra}
        self.record(stage, "HALT", why, **extra)
        self.log(f"HALTED at {stage}: {why}")
        self.log(f"resume with: python3 flow.py --resume {os.path.relpath(self.dir, ROOT)}")
        return 2

    def done(self, stage):
        return any(s["stage"] == stage and s["status"] == "PASS" for s in self.state["stages"])


def _now():
    return datetime.now(timezone.utc).isoformat()


def sh(cmd, cwd=None, stdin=None, env=None, log=None, timeout=None):
    """Run a subsystem command, streaming its output to the run log. Returns
    (rc, combined output)."""
    if log:
        log(f"$ {' '.join(os.path.relpath(c, ROOT) if os.path.isabs(c) else c for c in cmd)}"
            + (f"   (cwd {os.path.relpath(cwd, ROOT)})" if cwd else ""))
    p = subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.PIPE if stdin is not None else None,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         env=env or os.environ.copy())
    if stdin is not None:
        p.stdin.write(stdin)
        p.stdin.close()
    out = []
    try:
        for line in p.stdout:
            out.append(line)
            if log:
                log("    " + line.rstrip())
        p.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        p.kill()
        return 124, "".join(out) + "\n[flow] timed out\n"
    return p.returncode, "".join(out)


def load_env():
    """Subsystem credentials, from the files each subsystem keeps them in.
    Shell exports win; nothing is written back."""
    for f in (os.path.join(VALIDATION, "setup.env"), os.path.join(ROOT, ".env"),
              os.path.join(ROOT, "Frontend2", ".env"), os.path.join(BACKEND_AGENTS, ".env")):
        if not os.path.exists(f):
            continue
        with open(f) as fh:
            for line in fh:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, _, v = line.partition("=")
                k, v = k.strip(), v.strip().strip('"').strip("'")
                os.environ.setdefault(k, v)


# --------------------------------------------------------------------------
# stages
# --------------------------------------------------------------------------

def stage_spec_synthesis(run, args, feedback=""):
    """Frontend: a spec from English, a preset, a choices file -- or a spec
    the caller already has (then this stage only copies it into the run).
    `feedback` is the review's blocking list on a retry, appended to the
    English request (the microarch agent revises on the text it is given)."""
    os.makedirs(run.spec_dir, exist_ok=True)
    out = os.path.join(run.spec_dir, "generated_spec.json")
    if args.spec:
        shutil.copy(args.spec, out)
        run.state["spec"] = out
        run.record("spec_synthesis", "PASS", f"supplied: {os.path.relpath(args.spec, ROOT)}")
        return 0
    if not os.path.exists(MICROARCH_CLI):
        return run.halt("spec_synthesis", f"missing {os.path.relpath(MICROARCH_CLI, ROOT)}")
    cmd = [PY, MICROARCH_CLI]
    if args.request:
        cmd.append(args.request + feedback)
        if args.goal:
            cmd += ["--goal", args.goal]
    elif args.preset:
        cmd += ["--preset", args.preset]
    elif args.choices:
        cmd += ["--from-choices", os.path.abspath(args.choices)]
    cmd += ["--out", out]
    if args.request and not os.environ.get("ANTHROPIC_API_KEY"):
        return run.halt("spec_synthesis", "an English request needs ANTHROPIC_API_KEY for the "
                        "Frontend's microarch agent (a --preset or --choices run does not)")
    run.state["rounds"]["spec"] += 1
    rc, txt = sh(cmd, cwd=os.path.dirname(MICROARCH_CLI), log=run.log, timeout=1800)
    if rc == 3:
        return run.halt("spec_synthesis", "the microarch agent needs clarification; its "
                        "questions are in flow.log -- answer them in the request and rerun",
                        exit_code=rc)
    if rc != 0 or not os.path.exists(out):
        return run.halt("spec_synthesis", f"microarch_cli exited {rc}; no spec written", exit_code=rc)
    run.state["spec"] = out
    run.record("spec_synthesis", "PASS", os.path.relpath(out, ROOT)
               + (" (revised on review findings)" if feedback else ""))
    if feedback:
        return stage_spec_review(run, args)
    return 0


def stage_spec_review(run, args):
    """Validation: the spec is reviewed before any RTL exists. On FAIL the
    findings go back to the Frontend's microarch agent (through the request
    text -- the one input it revises on) for another round, capped; a
    preset / choices / supplied spec has no agent to revise it and halts."""
    review = os.path.join(run.spec_dir, f"SPEC_REVIEW_round{run.state['rounds']['spec']}.json")
    rc, txt = sh([PY, SPEC_STAGE, "--spec", run.state["spec"], "--json", review], log=run.log)
    gaps = sum(1 for l in txt.splitlines() if "[gap:" in l)
    if rc == 0:
        if os.path.exists(review):
            shutil.copy(review, os.path.join(run.spec_dir, "SPEC_REVIEW.json"))
        run.record("spec_review", "PASS", f"{gaps} open gap(s) carried as advisory; review: "
                                          f"{os.path.relpath(review, ROOT)}")
        return 0
    blocking = []
    if os.path.exists(review):
        with open(review) as f:
            blocking = json.load(f).get("blocking", [])
    run.record("spec_review", "FAIL", f"{len(blocking)} blocking; review: {os.path.relpath(review, ROOT)}")
    if not args.request:
        return run.halt("spec_review", "the spec fails its review (schema / JEDEC / register map) "
                        "and came from a preset, a choices file or a file, which the microarch "
                        "agent cannot revise. Fix the spec (or the compiler) and resume.",
                        review=review)
    if run.state["rounds"]["spec"] >= args.max_spec_rounds:
        return run.halt("spec_review", f"{run.state['rounds']['spec']} synthesis round(s) and "
                        f"the spec still fails its review (cap {args.max_spec_rounds}). The "
                        f"blocking findings are not something the agent's choices can change "
                        f"(see the review); fix the compiler or the schema and resume.",
                        review=review)
    feedback = ("\n\nThe previous spec you produced for this request FAILED validation review. "
                "Revise your choices so that none of these hold any more:\n"
                + "\n".join(f"  - {b}" for b in blocking[:12]))
    run.state["spec"] = None
    run.save()
    run.record("spec_review", "RETRY", f"findings returned to the microarch agent (round "
                                       f"{run.state['rounds']['spec'] + 1})")
    return stage_spec_synthesis(run, args, feedback=feedback)


def _phase_report(run, n):
    for kind in ("final", "error"):
        p = os.path.join(run.drop, "VALIDATIONREPORT", f"phase{n}_{kind}_report.json")
        if os.path.exists(p):
            with open(p) as f:
                return kind, json.load(f)
    return None, None


def _check_frontend_sim_env(run):
    if not os.environ.get("OLYMPUS_KEY"):
        return run.halt("rtl_generation",
                        "the Frontend phase pipelines prompt for an Olympus password unless "
                        "OLYMPUS_USER and OLYMPUS_KEY (path to a private key) are exported; a "
                        "non-interactive run cannot answer that prompt. Export them and resume.")
    return 0


def stage_rtl_generation(run, args, phases=None):
    """Frontend: phases 1-4 then the top-level assembly, into run/drop/. Each
    phase pipeline runs its own lint/sim retry loop (up to 4 attempts) and
    exits 0 only on pass."""
    rc = _check_frontend_sim_env(run)
    if rc:
        return rc
    os.makedirs(run.drop, exist_ok=True)
    spec = run.state["spec"]
    only = sorted(int(x) for x in str(args.phases).split(",")) if getattr(args, "phases", None) else None
    if phases is None and only:
        phases = only
    # the drop ships the spec it was generated from (validation reads it)
    shutil.copy(spec, os.path.join(run.drop, "generated_spec.json"))
    env = os.environ.copy()
    for n, sub, script, outdir, blocks in PHASES:
        if phases and n not in phases:
            continue
        script_path = os.path.join(FRONTEND, sub, script)
        if not os.path.exists(script_path):
            return run.halt("rtl_generation", f"missing {os.path.relpath(script_path, ROOT)}")
        run.log(f"-- phase {n}: {', '.join(blocks)}")
        rc, txt = sh([PY, script_path], cwd=os.path.dirname(script_path),
                     stdin=f"{spec}\n{run.drop}\n", env=env, log=run.log, timeout=4 * 3600)
        kind, rep = _phase_report(run, n)
        if rc != 0 or kind != "final":
            why = (f"phase {n} failed at {rep.get('failure_stage')} "
                   f"({', '.join(rep.get('failed_modules', []))})" if rep else
                   f"phase {n} exited {rc} with no report")
            run.record("rtl_generation", "FAIL", why, phase=n)
            return run.halt("rtl_generation", why + ". The Frontend's own fix agents need a "
                            "person at the keyboard (phaseN_validation_agent.py); run one, then "
                            "resume.", phase=n,
                            report=os.path.relpath(os.path.join(run.drop, "VALIDATIONREPORT",
                                                                f"phase{n}_error_report.json"), ROOT))
        # Frontend 2026-10-01: a gate that could not run fails the phase
        # unless ALLOW_SKIPPED_GATES=1, in which case the report says
        # PASS_UNVERIFIED with `skipped_gates`. Validation is the gate that
        # does run, so the flow continues and records it.
        skipped = list((rep or {}).get("skipped_gates") or []) or \
            [k for k in ("lint_status", "sim_status") if rep and rep.get(k) == "SKIPPED"]
        status = (rep or {}).get("status", "PASS")
        run.record("rtl_generation", "PASS", f"phase {n}" + (
            f" ({status}: {', '.join(skipped)} did not run on the Frontend side)" if skipped else ""),
            phase=n, frontend_status=status)
        if args.validate_per_phase and n < 4:
            rc = stage_rtl_validation(run, args, partial=True, tag=f"phase{n}")
            if rc:
                return rc
    # top-level assembly (not for a phase-limited run: the top needs all four)
    if only and set(only) != {1, 2, 3, 4}:
        run.state["drop"] = run.drop
        run.record("rtl_generation", "PASS", f"phase(s) {only} generated; top-level assembly "
                   f"skipped (--phases)")
        return 0
    if not os.path.exists(GENERATE_TOP):
        return run.halt("rtl_generation", f"missing {os.path.relpath(GENERATE_TOP, ROOT)}")
    rc, txt = sh([PY, GENERATE_TOP, "--output-dir", run.drop, "--spec", spec],
                 cwd=FRONTEND, env=env, log=run.log, timeout=3600)
    if rc != 0:
        return run.halt("rtl_generation", f"generate_top.py exited {rc} (top-level assembly or "
                        f"its lint failed); see flow.log")
    run.state["drop"] = run.drop
    run.record("rtl_generation", "PASS", "top-level assembled: drop/TOPRTL")
    return 0


def _copy_current(run, dest):
    os.makedirs(dest, exist_ok=True)
    for f in os.listdir(OUTBOX_CURRENT) if os.path.isdir(OUTBOX_CURRENT) else []:
        shutil.copy(os.path.join(OUTBOX_CURRENT, f), dest)


def stage_rtl_validation(run, args, partial=False, tag=None):
    """Validation: the drop in run/drop/ against the spec it ships. Results
    land in run/validation/round_<n>[_<tag>]/ (a copy of outbox/current)."""
    run.state["rounds"]["rtl"] += 0 if tag else 1
    rnd = run.state["rounds"]["rtl"]
    dest = os.path.join(run.val_dir, f"round_{rnd}" + (f"_{tag}" if tag else ""))
    env = os.environ.copy()
    env["VALIDATION_RTL_DROP_ROOTS"] = run.drop
    env["VALIDATION_SPEC"] = run.state["spec"]
    partial = partial or bool(getattr(args, "phases", None))
    cmd = [PY, VALIDATE_DROP] + (["--partial"] if partial else [])
    rc, txt = sh(cmd, cwd=ROOT, env=env, log=run.log, timeout=4 * 3600)
    _copy_current(run, dest)
    hand = os.path.join(dest, "HANDOFF.json")
    if not os.path.exists(hand):
        return run.halt("rtl_validation", f"validate_drop exited {rc} and produced no handoff; "
                        f"see flow.log", exit_code=rc)
    with open(hand) as f:
        h = json.load(f)
    # validate_drop names the drop it resolved before it judges anything; a
    # handoff for another drop is the previous round's, left in outbox/current
    # when a generator refused this one (an agent's patch that broke a
    # manifest, 2026-10-08). That is a stop before judging, never a verdict.
    m = re.search(r"declared drop \(git ([0-9a-f]+)\)", txt)
    if m and h.get("drop_id") != m.group(1):
        stop = [l.strip() for l in txt.splitlines() if "STOP" in l or "refused" in l][-2:]
        return run.halt("rtl_validation",
                        f"validation stopped before judging drop {m.group(1)} "
                        f"({' | '.join(stop) or f'validate_drop exited {rc}'}); the handoff in "
                        f"outbox/current is for drop {h.get('drop_id')}. See flow.log", exit_code=rc)
    ds = {}
    if os.path.exists(os.path.join(dest, "DROP_STATUS.json")):
        with open(os.path.join(dest, "DROP_STATUS.json")) as f:
            ds = json.load(f)
    blocked = len(ds.get("paths_blocked", {}))
    # a block this run generated must have been judged: absent (unresolved,
    # ambiguous copies) or foreign means the drop is not what the run thinks
    only = sorted(int(x) for x in str(args.phases).split(",")) if getattr(args, "phases", None) else [1, 2, 3, 4]
    mine = {b for n, _, _, _, blocks in PHASES if n in only for b in blocks}
    unjudged = sorted((mine & set(ds.get("blocks_absent", []))) | (mine & set(ds.get("foreign_spec_blocks", {}))))
    if unjudged:
        run.record("rtl_validation", "FAIL", f"generated block(s) not judged: {', '.join(unjudged)}; "
                   f"package: {os.path.relpath(dest, ROOT)}", package=dest)
        return run.halt("rtl_validation", f"block(s) this run generated could not be judged: "
                        f"{', '.join(unjudged)} (absent, ambiguous copies in the drop, or from "
                        f"another spec -- see DROP_STATUS.json and the resolver's report in flow.log)",
                        package=dest, unjudged=unjudged)
    detail = (f"{h['status']}; failed modules: {', '.join(h['failed_modules']) or 'none'}"
              + (f"; {blocked} path(s) blocked" if blocked else "")
              + f"; package: {os.path.relpath(dest, ROOT)}")
    stage = "rtl_validation" + (f":{tag}" if tag else "")
    run.state["drop_id"] = h["drop_id"]
    run.record(stage, h["status"], detail, drop_id=h["drop_id"], package=dest)
    if h["status"] == "PASS":
        if blocked and not partial:
            return run.halt("rtl_validation", f"every path that could run passed, but {blocked} "
                            f"path(s) were blocked (DROP_STATUS.json says why: absent blocks, "
                            f"a width mismatch, or blocks from another spec); the drop is not "
                            f"judged in full", package=dest)
        return 0
    return 1            # FAIL -> the caller decides (regeneration edge)


def stage_frontend_regeneration(run, args, package):
    """Frontend: repair the generators validation found wanting, through the
    Frontend's own phase validation agents. Our package is written as each
    phase's error report (the shape those agents read); the agent's
    apply/re-verify prompts are answered 'apply' for every proposal; then the
    affected phases and the top are regenerated."""
    rounds = run.state["rounds"]["rtl"]
    if rounds >= args.max_rtl_rounds:
        return run.halt("frontend_regeneration", f"{rounds} validation round(s) without a pass "
                        f"(cap {args.max_rtl_rounds}); last package: "
                        f"{os.path.relpath(package, ROOT)}", package=package)
    ri = os.path.join(package, "retry_instructions.json")
    phases_json = json.dumps({n: blocks for n, _, _, _, blocks in PHASES})
    pj = os.path.join(package, "phases.json")
    with open(pj, "w") as f:
        f.write(phases_json)
    rc, txt = sh([PY, TO_ERROR_REPORT, "--retry", ri, "--drop", run.drop, "--phases", pj], log=run.log)
    if rc != 0:
        return run.halt("frontend_regeneration", "could not write the Frontend error reports; see flow.log")
    written = {int(k): v for k, v in json.loads(txt.strip().splitlines()[-1]).items()}
    if not written:
        return run.halt("frontend_regeneration", "validation FAILED but names no module the "
                        "Frontend generates (see the package)", package=package)
    no_agent = [n for n in written if not os.path.exists(phase_agent(n))]
    if no_agent:
        return run.halt("frontend_regeneration",
                        f"validation FAILED in phase(s) {no_agent} and the Frontend has no "
                        f"validation agent for them yet ({', '.join(os.path.relpath(phase_agent(n), ROOT) for n in no_agent)}). "
                        f"The error report(s) are written in VALIDATIONREPORT/ and the package is "
                        f"at {os.path.relpath(package, ROOT)}; resume when the agent exists.",
                        package=package, phases=no_agent)
    if not os.environ.get("ANTHROPIC_API_KEY"):
        return run.halt("frontend_regeneration", "the Frontend's validation agents need ANTHROPIC_API_KEY")
    outcomes, reasons = {}, {}
    for n in sorted(written):
        agent = phase_agent(n)
        # An agent that takes our package directly (--retry, the ask in
        # HANDOFF_FRONTEND_2026-10-01.md) gets it; otherwise it reads the
        # phase error report the adapter just wrote in its own shape.
        flag = agent_findings_flag(agent)
        run.log(f"-- phase {n} validation agent on "
                f"{os.path.relpath(ri if flag else written[n], ROOT)}"
                + ("" if flag else "  (rendered as the phase error report)"))
        cmd = [PY, agent, "--output-dir", run.drop, "--spec", run.state["spec"]]
        if flag:
            cmd += [flag, ri]
            if agent_takes_yes(agent):
                cmd.append("--yes")
        # Unattended: every proposal is applied (the agent's prompts are
        # answered 'a'). The review of what it changed is the next validation
        # round, the rtl-round cap, and the agent's own re-verify/revert.
        rc, txt = sh(cmd, cwd=os.path.dirname(agent), stdin="a\n" * 40, log=run.log, timeout=3600)
        # The agent exits 0 only when every module ends 'fixed'. Its fix
        # report says which did; regenerating a generator the agent did not
        # change reproduces the same drop, so with nothing fixed the run
        # halts with the agent's reason instead of spinning to the cap.
        fixed = fixed_modules(run, n, newer_than=ri)
        outcomes[n] = fixed
        tail = [l for l in txt.strip().splitlines() if l.strip()][-3:]
        reasons[n] = f"exited {rc}: " + " | ".join(l.strip()[:120] for l in tail)
        run.record("frontend_regeneration", "PASS" if rc == 0 else "PARTIAL",
                   f"phase {n} agent exited {rc}; fixed: {', '.join(fixed) or 'none'}"
                   + ("" if fixed else ": " + " | ".join(l.strip()[:120] for l in tail)), phase=n)
    # One phase fixing something is progress worth a validation round, even
    # when another phase's agent gave up (its findings stay open in the next
    # package). Only when NO phase changed a generator would regeneration
    # reproduce the same drop, so only then does the run halt.
    if not any(outcomes.values()):
        why = "; ".join(f"phase {n} agent {reasons.get(n, 'ran')}" for n in sorted(outcomes))
        return run.halt("frontend_regeneration",
                        f"every phase agent fixed nothing ({why}). Package: {os.path.relpath(package, ROOT)}",
                        package=package)
    return stage_rtl_generation(run, args, phases=sorted(written))


def fixed_modules(run, n, newer_than=None):
    """Modules the phase agent's fix report marks fixed (phase{N}_fix_report.json).
    With `newer_than`, a report older than that file is ignored: it belongs to
    an earlier package."""
    p = os.path.join(run.drop, "VALIDATIONREPORT", f"phase{n}_fix_report.json")
    try:
        if newer_than and os.path.getmtime(p) < os.path.getmtime(newer_than):
            return []
        with open(p) as f:
            rep = json.load(f)
    except (OSError, ValueError):
        return []
    out = []
    for m in rep.get("modules", rep.get("results", [])) if isinstance(rep, dict) else []:
        if isinstance(m, dict) and m.get("final_status") == "fixed":
            out.append(m.get("module", "?"))
    if isinstance(rep, dict) and isinstance(rep.get("modules"), dict):
        out = [k for k, v in rep["modules"].items() if isinstance(v, dict) and v.get("final_status") == "fixed"]
    return out


def stage_backend(run, args):
    """Backend: RTL -> GDSII on the assembled top (drop/TOPRTL is a bundle)."""
    if args.skip_backend or getattr(args, "phases", None):
        run.record("backend", "SKIPPED", "--skip-backend" if args.skip_backend else "--phases run")
        return 0
    bundle = os.path.join(run.drop, "TOPRTL")
    if not os.path.isdir(bundle):
        return run.halt("backend", "drop/TOPRTL is missing; the backend takes the assembled top")
    if not os.path.exists(BACKEND_PIPELINE):
        return run.halt("backend", f"missing {os.path.relpath(BACKEND_PIPELINE, ROOT)}")
    if os.environ.get("USE_DOCKER") != "1":
        return run.halt("backend", "the backend runs ORFS in Docker and needs USE_DOCKER=1 "
                        "(and ORFS_DIR) in backend/agents/.env or the shell; export them and "
                        "resume, or rerun with --skip-backend")
    run.state["rounds"]["backend"] += 1
    env_file = os.path.join(BACKEND_AGENTS, ".env")
    with open(run.state["spec"]) as f:
        rev = json.load(f).get("revision") or ""
    # the backend names its outbox by the drop it ran on and the spec revision
    # it was given (Backend handoff 2026-10-08); it cannot compute either
    # without reaching into other subsystems, so the flow passes both
    cmd = [PY, BACKEND_PIPELINE, "--bundle_dir", bundle, "--out_root", run.backend_dir,
           "--drop_id", run.state.get("drop_id") or "", "--spec_revision", rev,
           "--mode", getattr(args, "backend_mode", None) or "build"]
    if os.path.exists(env_file):
        cmd += ["--env_file", env_file]
    t_start = time.time()
    rc, txt = sh(cmd, cwd=BACKEND_AGENTS, log=run.log, timeout=12 * 3600)
    # Only a report this invocation wrote counts (one from an earlier round
    # in the same out_root has the status key, and a stale PASS would be
    # taken over a nonzero exit: backend handoff 2026-10-08). Newest first.
    reports = sorted((os.path.join(run.backend_dir, f) for f in os.listdir(run.backend_dir)
                      if f.startswith("pipeline_final_report_")
                      and os.path.getmtime(os.path.join(run.backend_dir, f)) >= t_start - 1),
                     key=os.path.getmtime, reverse=True) if os.path.isdir(run.backend_dir) else []
    rep = {}
    if reports:
        with open(reports[0]) as f:
            rep = json.load(f)
    # the exit code decides first; a report can only confirm or detail it
    status = "FAIL" if rc else rep.get("pipeline_status", "PASS")
    if not rc and not reports:
        status = "FAIL"
        rep = {"failed_stage": "report", "error_message": "the backend exited 0 but wrote no "
               "pipeline_final_report_*.json this round"}
    netlist = next((a for a in (rep.get("artifacts") or []) if str(a).endswith("6_final.v")), None)
    run.state["netlist"] = netlist
    run.record("backend", status, f"exit {rc}; failed_stage={rep.get('failed_stage')}; "
               f"drc={rep.get('drc_violations')} lvs={rep.get('lvs_status')} "
               f"sta={rep.get('sta_status')}" + (f"; netlist {netlist}" if netlist else ""),
               report=reports[0] if reports else None)
    if status == "PASS":
        return 0
    if rep.get("failed_stage") == "synth" or "synth" in str(rep.get("error_message", "")).lower():
        return 1            # the RTL itself: backend -> frontend edge
    return run.halt("backend", f"backend FAILED at {rep.get('failed_stage') or 'unknown'} "
                    f"({rep.get('error_message', '')[:160]}); report: "
                    f"{os.path.relpath(reports[0], ROOT) if reports else 'none'}")


BACKEND_OUTBOX = os.path.join(ROOT, "backend", "findings", "outbox")


def backend_findings(spec_rev):
    """The backend's newest findings_v2.json for this spec revision (its
    emitter writes Validation's envelope: backend/findings/emit_findings.py)."""
    lp = os.path.join(BACKEND_OUTBOX, spec_rev or "", "latest")
    if not os.path.exists(lp):
        return None
    with open(lp) as f:
        head = f.read().strip()
    p = os.path.join(BACKEND_OUTBOX, spec_rev, head, "findings_v2.json")
    return p if os.path.exists(p) else None


def stage_backend_to_frontend(run, args, report):
    """Backend asked for an RTL change. Its findings (our envelope, written
    by backend/findings/emit_findings.py) become a retry package through
    the same adapter validation uses, and go to the Frontend's phase agents
    like a validation package; then the regenerated drop is validated again
    before the backend runs again."""
    rounds = run.state["rounds"]["backend"]
    if rounds >= args.max_backend_rounds:
        return run.halt("backend_to_frontend", f"{rounds} backend round(s) without a pass "
                        f"(cap {args.max_backend_rounds})")
    with open(run.state["spec"]) as f:
        rev = json.load(f).get("revision")
    src = backend_findings(rev)
    if not src:
        return run.halt("backend_to_frontend",
                        "the backend's failure names the RTL but it emitted no findings for "
                        f"spec revision {rev} (backend/findings/outbox/<rev>/latest). Backend "
                        f"report: {os.path.relpath(report, ROOT) if report else 'none'}.", report=report)
    sys.path.insert(0, os.path.join(VALIDATION, "findings"))
    import retry_adapter as RA
    with open(src) as f:
        doc = json.load(f)
    ri = RA.adapt(doc)
    ri["source"] = "backend/findings/emit_findings.py -> Validation/findings/retry_adapter.py"
    pkg = os.path.join(run.backend_dir, f"retry_round_{rounds}")
    os.makedirs(pkg, exist_ok=True)
    with open(os.path.join(pkg, "retry_instructions.json"), "w") as f:
        json.dump(ri, f, indent=2)
    shutil.copy(src, os.path.join(pkg, "findings_v2.json"))
    run.record("backend_to_frontend", "ROUTED", f"{len(ri['failed_modules'])} module(s) from the "
               f"backend's findings: {', '.join(ri['failed_modules'])}; package {os.path.relpath(pkg, ROOT)}")
    if not ri["failed_modules"]:
        return run.halt("backend_to_frontend", "the backend's findings name no module; "
                        f"see {os.path.relpath(src, ROOT)}")
    return stage_frontend_regeneration(run, args, pkg)


RUN_PATH = os.path.join(VALIDATION, "tools", "run_path.py")
PATH_DEFS = os.path.join(VALIDATION, "spec", "path_definitions.json")


def find_netlists(run):
    """{block: 6_final.v} the backend produced in this run: one per bundle
    directory under backend/runner/<design>/ (pipeline_batch names a design
    after its bundle, i.e. the block), plus the top-level bundle's netlist
    under its own name."""
    out = {}
    root = os.path.join(run.backend_dir, "runner")
    if not os.path.isdir(root):
        return out
    for d in sorted(os.listdir(root)):
        p = os.path.join(root, d, "6_final.v")
        if os.path.exists(p):
            out[d] = p
    return out


def stage_final_validation(run, args):
    """Validation of the backend's netlists on the same paths the RTL passed:
    every path whose blocks include a block with a netlist is run again with
    that netlist in the block's place (run_path --netlist; the sky130 cell
    models installed by tools/install_sky130_models.py). A top-level netlist
    (ddr3_controller) has no block path yet and is reported as such."""
    nets = find_netlists(run)
    blocks = {b: p for b, p in nets.items() if b != "TOPRTL" and b != "ddr3_controller"}
    if not blocks:
        return run.halt("final_validation",
                        "the backend produced no per-block netlist to run (only "
                        + (", ".join(nets) if nets else "nothing") +
                        "); per-block bundles (backend/agents/pipeline_batch.py on "
                        "backend/bundles/<block>) give runner/<block>/6_final.v, which "
                        "this stage runs through every path that instantiates the block. "
                        "A top-level netlist needs a top-level path, not built yet.",
                        netlists=nets)
    with open(PATH_DEFS) as f:
        pdefs = [p for p in json.load(f)["paths"] if not p.get("judged_in")]
    dest = os.path.join(run.val_dir, "gate")
    os.makedirs(dest, exist_ok=True)
    env = os.environ.copy()
    env["VALIDATION_RTL_DROP_ROOTS"] = run.drop
    env["VALIDATION_SPEC"] = run.state["spec"]
    verdicts = {}
    for p in pdefs:
        swap = [b for b in p["blocks"] if b in blocks]
        if not swap:
            continue
        cmd = [PY, RUN_PATH, "--path", p["id"], "--report-dir", dest, "--timeout", "1500"]
        for b in swap:
            cmd += ["--netlist", f"{b}={blocks[b]}"]
        rc, txt = sh(cmd, cwd=ROOT, env=env, log=run.log, timeout=3600)
        m = re.search(r"path verdict : (\w+)", txt)
        verdicts[p["id"]] = (m.group(1) if m else f"rc={rc}", swap)
    n_pass = sum(1 for v, _ in verdicts.values() if v == "PASS")
    n_fail = sum(1 for v, _ in verdicts.values() if v == "FAIL")
    detail = "; ".join(f"{pid}:{v} ({'+'.join(sw)} gate-level)" for pid, (v, sw) in verdicts.items())
    run.record("final_validation", "PASS" if n_fail == 0 and n_pass else "FAIL",
               f"{n_pass} pass / {n_fail} fail / {len(verdicts) - n_pass - n_fail} other over "
               f"{len(blocks)} netlist(s): {detail}", netlists=blocks, verdicts=verdicts)
    if n_fail or not n_pass:
        return run.halt("final_validation", f"gate-level: {n_fail} path(s) failed with the backend's "
                        f"netlist in place of the RTL the paths passed with; reports in "
                        f"{os.path.relpath(dest, ROOT)}")
    return 0


# --------------------------------------------------------------------------
# the flow
# --------------------------------------------------------------------------

def run_flow(run, args):
    """Advance the run from wherever it stands. Each stage returns 0 to
    continue, 1 for a loop edge, 2 for a halt."""
    st = run.state
    st["status"] = "running"
    st["halt"] = None
    if getattr(args, "revalidate", False):
        # the backend verdict (if any) was for the previous drop
        st["stages"] = [x for x in st["stages"] if x["stage"] not in ("backend", "final_validation")]
    run.save()

    if not st.get("spec"):
        rc = stage_spec_synthesis(run, args)
        if rc:
            return rc
    if not run.done("spec_review"):
        rc = stage_spec_review(run, args)
        if rc:
            return rc
    if not st.get("drop"):
        rc = stage_rtl_generation(run, args)
        if rc:
            return rc

    # validation <-> frontend loop
    revalidate = bool(getattr(args, "revalidate", False))
    while True:
        last = [s for s in st["stages"] if s["stage"] == "rtl_validation"]
        if (last and last[-1]["status"] == "PASS" and last[-1]["utc"] > _stage_utc(st, "rtl_generation")
                and not revalidate):
            break
        revalidate = False
        rc = stage_rtl_validation(run, args)
        if rc == 2:
            return rc
        if rc == 0:
            break
        package = [s for s in st["stages"] if s["stage"] == "rtl_validation"][-1]["package"]
        rc = stage_frontend_regeneration(run, args, package)
        if rc:
            return rc

    # backend <-> frontend loop
    while True:
        if run.done("backend") or any(s["stage"] == "backend" and s["status"] == "SKIPPED"
                                      for s in st["stages"]):
            break
        rc = stage_backend(run, args)
        if rc == 2:
            return rc
        if rc == 0:
            break
        report = [s for s in st["stages"] if s["stage"] == "backend"][-1].get("report")
        rc = stage_backend_to_frontend(run, args, report)     # routes, regenerates
        if rc:
            return rc
        rc = stage_rtl_validation(run, args)                   # the regenerated drop, before the backend again
        if rc:
            return rc if rc == 2 else run.halt("rtl_validation", "failed after a backend-requested change")

    if args.skip_backend or getattr(args, "phases", None):
        st["status"] = "complete"
        run.save()
        run.log("COMPLETE (backend skipped): the RTL drop passed validation"
                + (f" (phase(s) {args.phases} only)" if getattr(args, "phases", None) else "") + ".")
        return 0
    rc = stage_final_validation(run, args)
    if rc:
        return rc
    st["status"] = "complete"
    run.save()
    run.log("COMPLETE: spec, RTL, GDSII and netlist validated.")
    return 0


def _stage_utc(st, stage):
    xs = [s["utc"] for s in st["stages"] if s["stage"] == stage and s["status"] == "PASS"]
    return xs[-1] if xs else ""


def plan(args):
    print("flow plan (dry run):")
    src = (f"English request: {args.request!r}" if args.request else
           f"preset {args.preset}" if args.preset else
           f"choices {args.choices}" if args.choices else f"supplied spec {args.spec}")
    print(f"  1 spec_synthesis        Frontend  {src}" + ("" if args.spec else
          f"\n      {os.path.relpath(MICROARCH_CLI, ROOT)} ... --out <run>/spec/generated_spec.json"))
    print(f"  2 spec_review           Validation  {os.path.relpath(SPEC_STAGE, ROOT)}  (FAIL halts)")
    ph = getattr(args, "phases", None)
    print(f"  3 rtl_generation        Frontend  "
          + (f"phase {ph} pipeline(s) only (stdin: spec, <run>/drop); no top-level assembly, backend skipped"
             if ph else "phase1..4 pipelines (stdin: spec, <run>/drop) + generate_top.py")
          + ("  [validate --partial after each phase]" if args.validate_per_phase else ""))
    print(f"  4 rtl_validation        Validation  validate_drop.py on <run>/drop against the shipped spec"
          f"  -> <run>/validation/round_N/  (cap {args.max_rtl_rounds} rounds)")
    have = [n for n, *_ in PHASES if os.path.exists(phase_agent(n))]
    print(f"  5 frontend_regeneration Frontend  Phase{{N}}/phase{{N}}_validation_agent.py on our package "
          f"(agents present for phases {have}; others halt)")
    print(f"  6 backend               Backend   {'SKIPPED (--skip-backend)' if args.skip_backend else os.path.relpath(BACKEND_PIPELINE, ROOT) + ' --bundle_dir <run>/drop/TOPRTL --drop_id <id> --spec_revision <rev> --mode ' + (getattr(args, 'backend_mode', None) or 'build')}"
          + ("" if args.skip_backend else f"  (cap {args.max_backend_rounds} rounds; needs USE_DOCKER=1)"))
    print(f"  7 backend_to_frontend   edge      backend/findings/outbox -> retry package -> phase agents -> validate again")
    print(f"  8 final_validation      Validation  backend netlists through the paths (run_path --netlist, sky130 models)")
    print(f"  env: ANTHROPIC_API_KEY {'set' if os.environ.get('ANTHROPIC_API_KEY') else 'MISSING'}, "
          f"OLYMPUS_KEY {'set' if os.environ.get('OLYMPUS_KEY') else 'MISSING (phase pipelines would prompt)'}, "
          f"USE_DOCKER {os.environ.get('USE_DOCKER') or 'unset'}")


def main() -> int:
    ap = argparse.ArgumentParser(description="LLM-MC design flow: spec -> RTL -> validation -> GDSII")
    src = ap.add_mutually_exclusive_group()
    src.add_argument("request", nargs="?", help="English description of the controller wanted")
    src.add_argument("--preset", help="microarch preset (low-cost-embedded, balanced, default, "
                                      "high-performance, server-grade)")
    src.add_argument("--choices", help="JSON file of Tier-1/2/3 choices")
    src.add_argument("--spec", help="an existing spec: skip synthesis, start at the review")
    ap.add_argument("--goal", choices=["performance", "power", "cost", "balanced"], default=None)
    ap.add_argument("--resume", metavar="RUN_DIR", help="continue a halted run")
    ap.add_argument("--run-dir", help="where to put this run (default runs/<timestamp>-<slug>)")
    ap.add_argument("--max-spec-rounds", type=int, default=2)
    ap.add_argument("--max-rtl-rounds", type=int, default=4)
    ap.add_argument("--max-backend-rounds", type=int, default=2)
    ap.add_argument("--phases", default=None, metavar="N[,N]",
                    help="generate only these Frontend phases (e.g. 1 for a Phase-1 loop); "
                         "the drop is validated as partial and the top-level assembly and "
                         "backend are skipped")
    ap.add_argument("--validate-per-phase", action="store_true",
                    help="run a partial validation after each Frontend phase, not only at the end")
    ap.add_argument("--skip-backend", action="store_true")
    ap.add_argument("--backend-mode", choices=["contract", "synth", "build", "full"], default="build",
                    help="backend depth (passed through as its --mode): contract = seconds, no ORFS; "
                         "synth = minutes; build = sign-off (~1 h for 11 blocks); full = + optimisation")
    ap.add_argument("--revalidate", action="store_true",
                    help="with --resume: validate the drop again even though the last "
                         "validation passed (the drop changed under the run)")
    ap.add_argument("--dry-run", action="store_true", help="print the plan and exit")
    args = ap.parse_args()

    load_env()
    if args.dry_run:
        plan(args)
        return 0
    if args.resume:
        run_dir = os.path.abspath(args.resume)
        if not os.path.exists(os.path.join(run_dir, "RUN_STATE.json")):
            print(f"no RUN_STATE.json in {args.resume}")
            return 2
        run = Run(run_dir)
        saved = run.state.get("request", {})
        for k in ("request", "preset", "choices", "spec", "goal"):
            if getattr(args, k) is None and saved.get(k):
                setattr(args, k, saved[k])
        run.log(f"resuming {run.state['run_id']} (last: "
                f"{run.state['stages'][-1]['stage'] + ' ' + run.state['stages'][-1]['status'] if run.state['stages'] else 'nothing yet'})")
    else:
        if not (args.request or args.preset or args.choices or args.spec):
            ap.error("give an English request, --preset, --choices or --spec (or --resume)")
        slug = re.sub(r"[^a-z0-9]+", "_", (args.request or args.preset or
                      os.path.basename(args.choices or args.spec)).lower())[:24].strip("_")
        run_dir = os.path.abspath(args.run_dir or os.path.join(
            RUNS, f"{datetime.now().strftime('%Y%m%d-%H%M%S')}-{slug}"))
        run = Run(run_dir, args)
        run.log(f"run {run.state['run_id']} -> {os.path.relpath(run_dir, ROOT)}")
    rc = run_flow(run, args)
    run.log(f"state: {run.state['status']}  ({os.path.relpath(run.state_path, ROOT)})")
    return rc


if __name__ == "__main__":
    sys.exit(main())
