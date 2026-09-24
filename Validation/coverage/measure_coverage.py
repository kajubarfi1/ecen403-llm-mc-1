#!/usr/bin/env python3
"""
measure_coverage.py — one number, reproducibly: design code coverage
======================================================================
Merges every coverage database the path runs produced on Olympus, reports
it through imc, and reduces the report to what actually matters: coverage
of the DESIGN, per block, with testbench code excluded.

Two things this gets right that the first hand-run merge got wrong:

  * `-initial_model union_all`. The path runs instantiate different block
    sets (boot paths have init_fsm/calibration, command paths do not), so a
    plain merge picks the first run as the model and silently drops every
    instance it lacks — 120 items on the first attempt, all of init_fsm and
    calibration. union_all builds the model from every run.
  * Design-only accounting. The harness, driver, monitors and DRAM stub are
    testbench; their code coverage says nothing about the controller. They
    are excluded here (and, since this change, also excluded at collection
    time by cov_conf.ccf), so the headline is the design's number.

Usage:
    python3 Validation/coverage/measure_coverage.py
    python3 Validation/coverage/measure_coverage.py --runs '~/vmanager_session/*/cov_work/scope/*'
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))

from sim_runner import CadenceSSHAgent

OUT_JSON = os.path.join(ROOT, "Validation", "reports", "coverage_code.json")
DEFAULT_RUNS = ["/home/ugrads/j/jacobz/vmanager_session/*/cov_work/scope/*",
                "/home/ugrads/j/jacobz/cadence_agent_work/cov_work/scope/*",
                "/home/ugrads/j/jacobz/cadence_agent_work/runs/*/cov_work/scope/*"]

# Module-name patterns that are testbench, not design.
TB_PATTERNS = [r"^chain_harness$", r"_txn_harness$", r"^seq_driver$",
               r"^dram_stub$", r"_monitor$", r"_tb$", r"^\$unit$",
               r"_coverage$", r"_sva$", r"_fcov$"]


def password():
    for line in open(os.path.join(ROOT, "Validation", "setup.env")):
        if line.strip().startswith("OLYMPUS_PASSWORD"):
            return line.split("=", 1)[1].strip().strip('"').strip("'")
    return os.environ.get("OLYMPUS_PASSWORD")


def is_tb(module):
    return any(re.search(p, module) for p in TB_PATTERNS)


def base(title):
    return title.split("#")[0]


def nums(node):
    m = re.match(r"(\d+) / (\d+)", node.get("All Cov", "0 / 0"))
    return (int(m.group(1)), int(m.group(2))) if m else (0, 0)



def select_runs_since(agent, run_globs, since):
    """Expand the remote globs and keep only run directories whose coverage
    data was written at or after `since` (remote local time)."""
    cmd = ("for g in " + " ".join(run_globs) + "; do [ -d \"$g\" ] && "
           f"[ -n \"$(find \"$g\" -type f -newermt '{since}' -print -quit)\" ] && echo \"$g\"; "
           "done 2>/dev/null")
    r = agent._head_exec(cmd, timeout=120)      # plain SSH on the head node; no Slurm needed
    out = r["stdout"] if isinstance(r, dict) else (r[0] if isinstance(r, tuple) else str(r))
    return [l.strip() for l in out.splitlines() if l.strip().startswith("/")]

def merge_and_report(agent, run_globs, label):
    """imc: merge -> load -> report_metrics; returns local tree.json path."""
    remote_db = f"/home/ugrads/j/jacobz/cov_merged_{label}"
    remote_rep = f"/home/ugrads/j/jacobz/cov_report_{label}"
    tcl = (f"merge {' '.join(run_globs)} -out {remote_db} -overwrite "
           f"-initial_model union_all\n"
           f"load -run {remote_db}\n"
           f"report_metrics -detail -out {remote_rep} -overwrite\n"
           f"exit\n")
    agent.write_remote_file(f"cov_{label}.tcl", tcl)
    r = agent.srun(
        f"cp ~/cadence_agent_work/cov_{label}.tcl ~/cov_{label}.tcl && cd /tmp && "
        f"imc -exec ~/cov_{label}.tcl 2>&1 | grep -i 'MERGL1\\|RUNLD\\|\\*E\\|not merged' "
        f"| tail -8; "
        f"tar czf ~/cadence_agent_work/cov_{label}.tgz -C ~ cov_report_{label} "
        f"&& echo TARRED", timeout=600)
    print(r["stdout"].strip())
    if "TARRED" not in r["stdout"]:
        raise SystemExit("imc report did not complete — see output above")
    local = os.path.join(tempfile.gettempdir(), f"cov_{label}.tgz")
    agent.download_file(f"cov_{label}.tgz", local)
    xdir = os.path.join(tempfile.gettempdir(), f"cov_{label}_x")
    subprocess.run(["rm", "-rf", xdir], check=False)
    os.makedirs(xdir)
    with tarfile.open(local) as t:
        t.extractall(xdir)
    rep = os.path.join(xdir, f"cov_report_{label}")
    print(f"  imc report: {rep}   (feed to coverage_rollup.py --report)")
    return os.path.join(rep, "tree.json")


def summarise(tree_path):
    with open(tree_path) as f:
        tree = json.load(f)
    types = [c for n in tree for ch in n.get("children", [])
             if ch.get("title") == "Types" for c in ch.get("children", [])]
    design, tb = {}, {}
    for c in types:
        name = base(c["title"])
        h, t = nums(c)
        bucket = tb if is_tb(name) else design
        ph, pt = bucket.get(name, (0, 0))
        bucket[name] = (ph + h, pt + t)
    return design, tb


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", nargs="*", default=DEFAULT_RUNS,
                    help="remote globs of coverage run directories")
    ap.add_argument("--label", default="paths")
    ap.add_argument("--out", default=OUT_JSON)
    ap.add_argument("--rollup", action="store_true",
                    help="also roll the covergroups in the same report up "
                         "to the vplan (coverage_rollup.py)")
    ap.add_argument("--since", metavar="YYYY-MM-DDTHH:MM:SS",
                    help="merge only run directories modified at or after this "
                         "time (the drop run's start). Without it the globs "
                         "union every run ever kept on the cluster, including "
                         "runs of OLDER drops, and a rewritten block is counted "
                         "twice (old code + new code) with only the new half hit.")
    args = ap.parse_args()

    agent = CadenceSSHAgent()
    agent.connect(password=password())
    try:
        runs = args.runs
        if args.since:
            runs = select_runs_since(agent, args.runs, args.since)
            print(f"  {len(runs)} coverage run(s) modified since {args.since}")
            if not runs:
                raise SystemExit("no coverage runs newer than --since; nothing to merge")
        tree = merge_and_report(agent, runs, args.label)
    finally:
        agent.disconnect()

    design, tb = summarise(tree)
    dh = sum(h for h, _ in design.values())
    dt = sum(t for _, t in design.values())
    th = sum(h for h, _ in tb.values())
    tt = sum(t for _, t in tb.values())

    print(f"\n  {'DESIGN MODULE':22} {'COVERED':>14}   {'%':>6}")
    for name in sorted(design):
        h, t = design[name]
        print(f"  {name:22} {h:6}/{t:<7} {100*h/t if t else 0:6.1f}%")
    print(f"  {'-'*46}")
    print(f"  {'DESIGN TOTAL':22} {dh:6}/{dt:<7} {100*dh/dt if dt else 0:6.1f}%")
    if tt:
        print(f"  {'(testbench, excluded)':22} {th:6}/{tt:<7} "
              f"{100*th/tt:6.1f}%")

    payload = {
        "$schema": "validation-code-coverage/1",
        "generated_utc": datetime.utcnow().isoformat() + "Z",
        "runs": runs,
        "run_globs": args.runs,
        "since": args.since,
        "merge": "imc merge -initial_model union_all",
        "design_total": {"covered": dh, "total": dt,
                         "percent": round(100 * dh / dt, 2) if dt else None},
        "per_module": {n: {"covered": h, "total": t,
                           "percent": round(100 * h / t, 2) if t else None}
                       for n, (h, t) in sorted(design.items())},
        "testbench_excluded": sorted(tb),
        "imc_report_dir": os.path.dirname(tree),
    }
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(payload, f, indent=2)
    print(f"\n  wrote {os.path.relpath(args.out, ROOT)}")

    if args.rollup:
        # Functional coverage from the same merged report: covergroup bins
        # mapped back to vplan items. One measurement, both numbers.
        print("\n  === vplan rollup (functional coverage) ===")
        r = subprocess.run(
            ["python3", os.path.join(HERE, "coverage_rollup.py"),
             "--report", os.path.dirname(tree)],
            capture_output=True, text=True, cwd=ROOT)
        print("\n".join(l for l in (r.stdout + r.stderr).splitlines()
                        if "NotOpenSSL" not in l and "warnings.warn" not in l))
    return 0


if __name__ == "__main__":
    sys.exit(main())
