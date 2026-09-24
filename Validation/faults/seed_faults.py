#!/usr/bin/env python3
"""
seed_faults.py — does the whole validation stack catch a real design bug?
=========================================================================
mutate_predictor.py answers "would the gates notice a wrong MODEL". This
answers the question one level up: would monitors, harness, generated SVA,
coverage sampling, scoreboard and checkers — the whole stack, on a real
simulation — notice a wrong DESIGN, and blame the right block?

For each fault in fault_catalog.json:
  1. copy the canonical RTL drop into faults/work/<id>/ and apply the fault's
     text substitution (it must match exactly once, or this is an error);
  2. run the fault's paths through run_path.py with the resolver pointed at
     the mutated copy (VALIDATION_RTL_DROP_ROOTS), under its own --tag and
     --report-dir so baseline reports are untouched;
  3. build a DETECTOR SIGNATURE from the mutant's report and sim log, and
     compare it with the baseline signature of the same path.

The drop under test is already broken, so "the path failed" proves nothing.
A fault is KILLED only when the mutant run shows a detector the baseline did
not (a new violation id, assertion, illegal bin, stage failure, log marker),
or an expected detector's count grew, or an exact stage matched fewer
transactions. The report also says whether the expected detector was the one
that fired and whether the failing stage names the mutated block.

Usage:
    python3 Validation/faults/seed_faults.py                # all faults
    python3 Validation/faults/seed_faults.py --only M03 M09 # a subset
    python3 Validation/faults/seed_faults.py --prep-only    # apply + harness gen only
    python3 Validation/faults/seed_faults.py --score-only   # re-score existing runs
"""

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CATALOG = os.path.join(HERE, "fault_catalog.json")
WORK = os.path.join(HERE, "work")
REPORTS = os.path.join(ROOT, "Validation", "reports", "faults")
BASELINE = os.path.join(ROOT, "Validation", "reports", "paths")
MATRIX = os.path.join(REPORTS, "fault_matrix.json")


class FaultError(Exception):
    pass


# --------------------------------------------------------------------------
# building the mutant drop
# --------------------------------------------------------------------------

def build(fault, drop_root):
    src = os.path.join(ROOT, drop_root)
    dst_root = os.path.join(WORK, fault["id"])
    dst = os.path.join(dst_root, drop_root)
    if os.path.exists(dst_root):
        shutil.rmtree(dst_root)
    shutil.copytree(src, dst)
    target = os.path.join(dst, fault["file"])
    with open(target) as f:
        text = f.read()
    n = text.count(fault["from"])
    if n != 1:
        raise FaultError(f"{fault['id']}: substitution matches {n} time(s) in "
                         f"{fault['file']}; it must match exactly once. The "
                         f"drop has changed under the catalog — update the "
                         f"fault, do not skip it.")
    with open(target, "w") as f:
        f.write(text.replace(fault["from"], fault["to"]))
    return dst


# --------------------------------------------------------------------------
# running
# --------------------------------------------------------------------------

def run(fault, path, mutant_root, prep_only=False, timeout=1500,
        judge_only=False):
    rep = os.path.join(REPORTS, fault["id"])
    os.makedirs(rep, exist_ok=True)
    env = dict(os.environ, VALIDATION_RTL_DROP_ROOTS=mutant_root)
    cmd = ["python3", "Validation/tools/run_path.py", "--path", path,
           "--tag", f"faults/{fault['id']}", "--report-dir", rep,
           "--no-coverage", "--timeout", str(timeout)]
    if prep_only:
        cmd.append("--prep-only")
    if judge_only:
        cmd.append("--judge-only")
    r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    out = (r.stdout or "") + (r.stderr or "")
    with open(os.path.join(rep, f"{path}_run.txt"), "w") as f:
        f.write(out)
    return r.returncode, out


# --------------------------------------------------------------------------
# detector signatures
# --------------------------------------------------------------------------

# A violation line starts with its rule: a taxonomy id (SCHED_001), a
# checker rule name (request_not_serviced) or the scoreboard's own kinds
# (x_value). All of them are detectors; the first draft matched only the
# first shape and missed a fault the checker had in fact reported.
ID_RE = re.compile(r"^\s*([A-Za-z][\w]*)(?: \([^)]*\))?:")
MATCHED_RE = re.compile(r"matched=(\d+)/(\d+)")
VIOL_RE = re.compile(r"violations=(\d+)")
ASSERT_RE = re.compile(r"Assertion \S*\.(\w+) has failed")
ILLEGAL_RE = re.compile(r"EILLVU.*?coverpoint \(\S*\.(\w+)\)")
LOG_MARKERS = ("DRIVER_STALL", "HARNESS_TIMEOUT")


def signature(report_dir, path):
    """{detector: count} for one path run. Missing report -> None."""
    rp = os.path.join(report_dir, f"{path}_report.json")
    if not os.path.exists(rp):
        return None
    with open(rp) as f:
        r = json.load(f)
    sig = {}
    for st in r.get("stages", []):
        name = st["stage"]
        if st["verdict"] == "fail":
            sig[f"stage:{name}"] = 1
        m = MATCHED_RE.search(st.get("summary", ""))
        if m:
            sig[f"matched:{name}"] = int(m.group(1))
        mv = VIOL_RE.search(st.get("summary", ""))
        if mv:
            sig[f"violations:{name}"] = int(mv.group(1))
        for d in st.get("detail", []):
            mm = ID_RE.match(d)
            if mm and mm.group(1) not in ("scope",):
                k = f"id:{mm.group(1)}"
                sig[k] = sig.get(k, 0) + 1
    lp = os.path.join(report_dir, f"{path}_sim.log")
    if os.path.exists(lp):
        with open(lp, errors="replace") as f:
            log = f.read()
        for name in ASSERT_RE.findall(log):
            sig[f"assert:{name}"] = sig.get(f"assert:{name}", 0) + 1
        for cp in ILLEGAL_RE.findall(log):
            sig[f"illegal:{cp}"] = sig.get(f"illegal:{cp}", 0) + 1
        for mk in LOG_MARKERS:
            if mk in log:
                sig[f"log:{mk}"] = log.count(mk)
    sig["_verdict"] = r.get("verdict")
    return sig


def compare(base, mut, expect, block):
    """What the mutant run shows that the baseline did not."""
    new, grew, fewer = {}, {}, {}
    for k, v in mut.items():
        if k.startswith("_"):
            continue
        if k.startswith("matched:"):
            b = base.get(k)
            if b is not None and v < b:
                fewer[k] = (b, v)
            continue
        b = base.get(k, 0)
        if b == 0:
            new[k] = v
        elif v > b * 1.5 + 2:
            grew[k] = (b, v)
    detectors = set(new) | set(grew) | set(fewer)
    killed = bool(detectors)
    hit = [e for e in expect if e in detectors]
    # blame: a newly failing stage, or a stage with new ids, naming the block
    blamed = sorted({k.split(":", 1)[1] for k in new if k.startswith("stage:")}
                    | {k.split(":", 1)[1] for k in fewer})
    blame_ok = (not blamed) or any(block in s or s == "(path-level)"
                                   for s in blamed)
    return {"killed": killed, "expected_hit": hit,
            "expected_missed": [e for e in expect if e not in detectors],
            "new": new, "grew": grew, "fewer_matched": fewer,
            "blamed_stages": blamed, "blame_names_block": blame_ok,
            "baseline_verdict": base.get("_verdict"),
            "mutant_verdict": mut.get("_verdict")}


# --------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*", default=None,
                    help="fault ids (or id prefixes) to run")
    ap.add_argument("--prep-only", action="store_true")
    ap.add_argument("--score-only", action="store_true",
                    help="skip building/running; score existing reports")
    ap.add_argument("--judge-only", action="store_true",
                    help="rebuild the mutant drops and re-judge their existing "
                         "traces (after a checker regenerated); no simulation")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=1500)
    args = ap.parse_args()

    with open(CATALOG) as f:
        cat = json.load(f)
    faults = cat["faults"]
    if args.only:
        faults = [x for x in faults
                  if any(x["id"].startswith(p) for p in args.only)]
    if not faults:
        print("no faults selected")
        return 2

    # 1. build every mutant drop first: a bad substitution stops the run
    #    before any cluster time is spent.
    roots = {}
    if not args.score_only:
        for fl in faults:
            roots[fl["id"]] = build(fl, cat["drop_root"])
            print(f"  built {fl['id']:36} {fl['block']:13} {fl['description'][:60]}")

    # 2. run (fault, path) jobs in parallel
    jobs = [(fl, p) for fl in faults for p in fl["paths"]]
    if not args.score_only:
        print(f"\n  running {len(jobs)} job(s), {args.jobs} at a time"
              + (" [prep only]" if args.prep_only else "") + "\n")
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
            futs = {ex.submit(run, fl, p, roots[fl["id"]], args.prep_only,
                              args.timeout, args.judge_only): (fl, p)
                    for fl, p in jobs}
            for fut in concurrent.futures.as_completed(futs):
                fl, p = futs[fut]
                rc, out = fut.result()
                tail = next((l for l in reversed(out.splitlines())
                             if "verdict" in l or "failed" in l.lower()), "")
                print(f"  done  {fl['id']:36} {p:34} rc={rc}  {tail.strip()[:60]}")
        if args.prep_only:
            print("\n  prep-only: mutations applied and harnesses generated; "
                  "nothing simulated.")
            return 0

    # 3. score
    rows = []
    for fl, p in jobs:
        base = signature(BASELINE, p)
        mut = signature(os.path.join(REPORTS, fl["id"]), p)
        if base is None or mut is None:
            rows.append({"fault": fl["id"], "block": fl["block"], "path": p,
                         "killed": None,
                         "note": "missing " + ("baseline" if base is None else "mutant")
                         + " report"})
            continue
        res = compare(base, mut, fl["expect"], fl["block"])
        rows.append({"fault": fl["id"], "block": fl["block"], "path": p,
                     "description": fl["description"], "expect": fl["expect"],
                     "masked_by": fl.get("masked_by"), **res})

    killed = sum(1 for r in rows if r.get("killed"))
    scored = sum(1 for r in rows if r.get("killed") is not None)
    by_fault = {}
    for r in rows:
        by_fault.setdefault(r["fault"], []).append(r)
    faults_killed = sum(1 for fid, rs in by_fault.items()
                        if any(r.get("killed") for r in rs))
    # A fault masked by an OPEN defect of the same drop is not a missed
    # check: the baseline already shows the symptom. It is reported apart
    # and re-tested when that defect closes; it never counts as a kill.
    masked = sorted(fid for fid, rs in by_fault.items()
                    if not any(r.get("killed") for r in rs)
                    and any(r.get("masked_by") for r in rs))
    survived = sorted(fid for fid, rs in by_fault.items()
                      if not any(r.get("killed") for r in rs)
                      and fid not in masked)

    print("\n" + "=" * 78)
    print(f"  {'fault':36} {'path':30} killed  expected-hit  blame")
    for r in rows:
        k = {True: "YES ", False: "no  ", None: "?   "}[r.get("killed")]
        if not r.get("killed") and r.get("masked_by"):
            k = "mask"
        hit = f"{len(r.get('expected_hit', []))}/{len(r.get('expect', []))}"
        blame = ("ok" if r.get("blame_names_block") else "WRONG") if r.get("killed") else "-"
        print(f"  {r['fault']:36} {r['path']:30} {k}    {hit:12}  {blame}")
        for k2, v in list(r.get("new", {}).items())[:4]:
            print(f"      new      {k2} x{v}")
        for k2, v in list(r.get("grew", {}).items())[:3]:
            print(f"      grew     {k2} {v[0]} -> {v[1]}")
        for k2, v in r.get("fewer_matched", {}).items():
            print(f"      matched  {k2} {v[0]} -> {v[1]}")
        if r.get("expected_missed") and r.get("killed"):
            print(f"      (expected but silent: {r['expected_missed']})")
        if not r.get("killed") and r.get("masked_by"):
            print(f"      masked by {r['masked_by'][:110]}")
    print("=" * 78)
    print(f"  faults killed : {faults_killed}/{len(by_fault) - len(masked)} "
          f"detectable   masked by open defects: {len(masked)}   "
          f"survived: {len(survived) or 'none'}")

    os.makedirs(REPORTS, exist_ok=True)
    with open(MATRIX, "w") as f:
        json.dump({"$schema": "validation-fault-matrix/1",
                   "generated_utc": datetime.utcnow().isoformat() + "Z",
                   "drop_root": cat["drop_root"],
                   "faults_total": len(by_fault), "faults_killed": faults_killed,
                   "faults_masked": masked, "faults_survived": survived,
                   "rows": rows}, f, indent=2)
    print(f"  wrote {os.path.relpath(MATRIX, ROOT)}")
    return 0 if not survived else 1


if __name__ == "__main__":
    sys.exit(main())
