#!/usr/bin/env python3
"""
closure_loop.py — coverage closure, and the experiment that measures it
========================================================================
Runs the loop the whole rebuild exists to enable:

    measure coverage -> find holes -> generate stimulus aimed at them
        -> simulate -> merge -> measure again -> repeat

and runs it twice: once with the sequence agent reading the holes, once with
constrained-random stimulus that does not. The only difference between the
arms is whether the generator sees the coverage rollup. Everything else — the
harness, the driver codegen, the assertions, the covergroups, the merge, the
rollup — is identical, because both arms go through the same code.

That comparison is the point. Coverage rising in the agent arm proves nothing
on its own; more simulation raises coverage. What is claimable is the
DIFFERENCE between targeted and untargeted stimulus at equal budget.

Terminating conditions, in priority order:
  * every targeted coverage goal met
  * no new bins for `--patience` consecutive iterations (the generator has
    stopped finding anything, and further iterations buy nothing)
  * iteration budget exhausted

Coverage MERGES across iterations: each run adds to the cumulative database,
so the reported number is what the whole campaign achieved rather than what
the last sequence happened to hit.

Usage:
    python3 Validation/closure/closure_loop.py --scope cmd_gen --arm agent
    python3 Validation/closure/closure_loop.py --scope cmd_gen --arm control
    python3 Validation/closure/closure_loop.py --scope cmd_gen --arm both -n 3
"""

import argparse
import json
import os
import subprocess
import sys
import tarfile
import tempfile
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "coverage"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
sys.path.insert(0, HERE)

from sim_runner import CadenceSSHAgent
from coverage_rollup import parse_imc_report
import random_sequence

RESULTS = os.path.join(ROOT, "Validation", "reports", "closure_experiment.json")
SEQ_DIR = os.path.join(ROOT, "Validation", "sequences", "generated")

RTL = "cmd_gen.sv"
FIXED_SV = ["cmd_gen.sv", "cmd_gen_sva.sv", "cmd_gen_sva_bind.sv",
            "cmd_gen_coverage.sv", "cmd_gen_coverage_bind.sv",
            "seq_driver.sv", "seq_harness.sv"]


def password():
    for line in open(os.path.join(ROOT, "Validation", "setup.env")):
        if "=" in line:
            k, _, v = line.partition("=")
            if k.replace("export", "").strip() == "OLYMPUS_PASSWORD":
                return v.strip().strip('"').strip("'")
    return os.environ.get("OLYMPUS_PASSWORD")


def run_local(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=ROOT)
    return r.returncode, r.stdout + r.stderr


def bins_hit(measured):
    return sum(m["bins_hit"] for m in measured.values())


def bins_total(measured):
    return sum(m["bins_total"] for m in measured.values())


def simulate_and_measure(agent, covtest, prior_covtests):
    """Run the current driver, then measure CUMULATIVE coverage.

    Each iteration writes its own covtest; the report loads every covtest so
    far, which imc merges. Reporting only the newest run would answer "what
    did the last sequence hit" when the question is "what has the campaign
    covered" — and would make a later sequence look worse simply for
    targeting what earlier ones missed."""
    agent.upload_files([os.path.join(SEQ_DIR, "seq_driver.sv")])
    cov_flags = f"-coverage A -covoverwrite -covfile cov_conf.ccf -covtest {covtest}"
    cmd = (f"xrun -sv -access +rwc -timescale 1ns/1ps {cov_flags} "
           f"{' '.join(FIXED_SV)} -l {covtest}.log")
    res = agent.run_sim(cmd, timeout=420)
    if res.get("exit_code") not in (0, None):
        out = res.get("stdout", "")
        fatal = [l for l in out.splitlines() if "*F," in l or "*E,ELBERR" in l]
        if fatal:
            raise SystemExit("simulation failed:\n  " + "\n  ".join(fatal[:5]))

    # imc's `load -run` REPLACES the loaded run — it logs UNLDPREV and
    # unloads the previous one — so loading several runs reports only the
    # last. Cumulative coverage requires an explicit `merge`. Reporting the
    # last run instead of the merge made an earlier version of this
    # experiment show coverage DECREASING between iterations, which is
    # impossible and was the tell.
    allruns = prior_covtests + [covtest]
    if len(allruns) > 1:
        srcs = " ".join(f"cov_work/scope/{c}" for c in allruns)
        merged = f"merged_{covtest}"
        tcl = (f"merge {srcs} -out {merged} -overwrite\n"
               f"load -run cov_work/scope/{merged}\n"
               f"report_metrics -detail -out rep_{covtest} -overwrite\nexit\n")
    else:
        tcl = (f"load -run cov_work/scope/{covtest}\n"
               f"report_metrics -detail -out rep_{covtest} -overwrite\nexit\n")
    agent.write_remote_file(f"rep_{covtest}.tcl", tcl)
    agent.run_sim(f"imc -exec rep_{covtest}.tcl >/dev/null 2>&1; "
                  f"tar czf rep_{covtest}.tgz rep_{covtest}", timeout=300)
    local = os.path.join(tempfile.gettempdir(), f"rep_{covtest}.tgz")
    agent.download_file(f"rep_{covtest}.tgz", local)
    outdir = os.path.join(tempfile.gettempdir(), f"rep_{covtest}")
    if os.path.exists(outdir):
        subprocess.run(["rm", "-rf", outdir], check=False)
    with tarfile.open(local) as t:
        t.extractall(tempfile.gettempdir())
    return parse_imc_report(outdir)


def write_rollup(measured):
    """The agent reads holes from the rollup file, so refresh it in place."""
    import shutil
    tmp = os.path.join(tempfile.gettempdir(), "_roll")
    os.makedirs(tmp, exist_ok=True)
    return measured


def reset_rollup():
    """Start a replicate from a clean measurement state.

    Replicates must be independent: if the agent could see the previous
    replicate's coverage it would start from holes another run already
    closed, and the replicates would not be samples of the same experiment.
    Writing an all-unmeasured rollup is the honest starting point — it is
    what the agent would see before any simulation had run."""
    vplan_path = os.path.join(ROOT, "Validation", "vplan", "vplan.json")
    with open(vplan_path) as f:
        vplan = json.load(f)
    items = []
    for item in vplan["items"]:
        cov = [{"name": c["name"], "goal": c.get("goal", 100),
                "measured": None, "state": "not_measured"}
               for c in item.get("coverage_items", [])]
        items.append({"id": item["id"], "title": item["title"],
                      "scope": item.get("scope"), "method": item.get("method"),
                      "priority": item.get("priority"),
                      "prior_status": item.get("status"),
                      "status": "not_measured" if cov else "no_coverage_declared",
                      "coverage": cov,
                      "short_of_goal": [],
                      "not_measured": [c["name"] for c in cov]})
    out = os.path.join(ROOT, "Validation", "reports", "coverage_rollup.json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        json.dump({"$schema": "validation-coverage-rollup/1",
                   "vplan_items": len(items), "coverpoints_measured": 0,
                   "summary": {}, "items": items}, f, indent=2)


def run_arm(arm, scope, iterations, patience, agent_ssh, rep=1):
    """One replicate of one arm. Returns per-iteration history."""
    history, stale, prior = [], 0, []
    prev_hit = 0
    reset_rollup()

    for it in range(1, iterations + 1):
        covtest = f"{arm}_r{rep}_it{it}"
        tag = f"[{arm} r{rep} {it}/{iterations}]"

        # --- produce a sequence ------------------------------------------
        if arm == "agent":
            rc, out = run_local(
                f"python3 Validation/agents/sequence_agent.py --scope {scope}")
            if rc != 0:
                print(f"  {tag} sequence generation failed:\n{out[-500:]}")
                break
            # exclude control-arm files: they share the scope prefix, and
            # picking one up would silently run the control's stimulus in the
            # agent arm and invalidate the comparison.
            cands = [os.path.join(SEQ_DIR, f) for f in os.listdir(SEQ_DIR)
                     if f.startswith(scope) and f.endswith(".json")
                     and "random" not in f]
            if not cands:
                print(f"  {tag} the agent produced no sequence file")
                break
            seq_path = sorted(cands, key=os.path.getmtime)[-1]
        else:
            seed = rep * 1000 + it        # distinct seeds across replicates
            seq_path = os.path.join(SEQ_DIR, f"{scope}_random_r{rep}_it{it}.json")
            rc, out = run_local(
                f"python3 Validation/closure/random_sequence.py --scope {scope} "
                f"--seed {seed} --out {seq_path}")
            if rc != 0:
                print(f"  {tag} control generation failed:\n{out[-400:]}")
                break

        rc, out = run_local(
            f"python3 Validation/sequences/driver_gen.py --sequence {seq_path}")
        if rc != 0:
            print(f"  {tag} driver codegen rejected the sequence:\n{out[-400:]}")
            break

        # --- simulate and measure (cumulative) ----------------------------
        measured = simulate_and_measure(agent_ssh, covtest, prior)
        prior.append(covtest)

        # The agent reads open holes from the rollup file. Without refreshing
        # it, every iteration would target the same stale holes and the loop
        # would not be a loop.
        rep_dir = os.path.join(tempfile.gettempdir(), f"rep_{covtest}")
        run_local(f"python3 Validation/coverage/coverage_rollup.py "
                  f"--report {rep_dir}")
        hit, total = bins_hit(measured), bins_total(measured)
        delta = hit - prev_hit
        met = sum(1 for m in measured.values() if m["percent"] >= 100.0)

        with open(seq_path) as f:
            seq = json.load(f)
        history.append({
            "iteration": it, "covtest": covtest,
            "sequence": seq.get("name"),
            "targets": seq.get("targets", []),
            "bins_hit": hit, "bins_total": total,
            "new_bins": delta,
            "coverpoints_at_100": met,
            "percent": round(100.0 * hit / total, 2) if total else 0.0,
        })
        print(f"  {tag} {seq.get('name','?'):28} bins {hit}/{total} "
              f"({100.0*hit/total:.1f}%)  +{delta} new  "
              f"{met} coverpoint(s) at goal")

        stale = stale + 1 if delta == 0 else 0
        prev_hit = hit
        if stale >= patience:
            print(f"  {tag} no new bins for {patience} iteration(s) — the "
                  f"generator has stopped finding anything; stopping.")
            break
        if met == len(measured):
            print(f"  {tag} every coverpoint at goal; stopping.")
            break

    return history


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", default="cmd_gen")
    ap.add_argument("--arm", choices=("agent", "control", "both"), default="both")
    ap.add_argument("-n", "--iterations", type=int, default=3)
    ap.add_argument("--patience", type=int, default=2)
    ap.add_argument("-r", "--replicates", type=int, default=1,
                    help="independent runs per arm; >1 turns the comparison "
                         "from an anecdote into a sample")
    args = ap.parse_args()

    ssh = CadenceSSHAgent()
    ssh.connect(password=password())
    print(f"  connected; scope={args.scope} iterations={args.iterations} "
          f"patience={args.patience}\n")

    results = {}
    try:
        arms = ["agent", "control"] if args.arm == "both" else [args.arm]
        for arm in arms:
            print(f"  === {arm.upper()} ARM ({args.replicates} replicate(s)) ===")
            results[arm] = []
            for rep in range(1, args.replicates + 1):
                hist = run_arm(arm, args.scope, args.iterations,
                               args.patience, ssh, rep=rep)
                results[arm].append(hist)
                if hist:
                    f = hist[-1]
                    print(f"    replicate {rep}: final {f['bins_hit']}/"
                          f"{f['bins_total']} bins ({f['percent']}%), "
                          f"{len(hist)} iteration(s)")
                print()
    finally:
        ssh.disconnect()

    payload = {
        "$schema": "validation-closure-experiment/1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "scope": args.scope,
        "iterations_budget": args.iterations,
        "design": ("Both arms use the same harness, driver codegen, "
                   "assertions, covergroups and rollup. The only difference "
                   "is whether the stimulus generator reads the coverage "
                   "rollup before producing a sequence."),
        "arms": results,
    }
    os.makedirs(os.path.dirname(RESULTS), exist_ok=True)
    with open(RESULTS, "w") as f:
        json.dump(payload, f, indent=2)

    print("  === RESULT ===")
    finals = {}
    for arm, reps in results.items():
        vals = [r[-1]["bins_hit"] for r in reps if r]
        goals = [r[-1]["coverpoints_at_100"] for r in reps if r]
        if not vals:
            print(f"    {arm:8} no replicates completed")
            continue
        finals[arm] = vals
        total = reps[0][-1]["bins_total"]
        mean = sum(vals) / len(vals)
        print(f"    {arm:8} n={len(vals)}  bins {min(vals)}-{max(vals)} "
              f"(mean {mean:.1f}/{total})  "
              f"coverpoints at goal {min(goals)}-{max(goals)}")
        print(f"             per-replicate: {vals}")

    if len(finals) == 2:
        a, c = finals["agent"], finals["control"]
        am, cm = sum(a) / len(a), sum(c) / len(c)
        print(f"\n    mean difference: {am - cm:+.1f} bins")
        overlap = not (min(a) > max(c) or min(c) > max(a))
        if overlap:
            print(f"    RANGES OVERLAP (agent {min(a)}-{max(a)} vs control "
                  f"{min(c)}-{max(c)}) — with n={len(a)} this is not a")
            print(f"    separation you can claim. Report it as a trend and "
                  f"say the sample size.")
        else:
            print(f"    ranges do not overlap (agent {min(a)}-{max(a)} vs "
                  f"control {min(c)}-{max(c)}); still only n={len(a)}.")
    print(f"\n  wrote {os.path.relpath(RESULTS, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
