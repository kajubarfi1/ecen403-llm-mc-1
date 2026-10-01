#!/usr/bin/env python3
"""
repair_suite.py — the seeded-fault suite in reverse
====================================================
seed_faults.py asks "does the stack notice a bug we put in?". This asks the
other half: "when a reported bug is taken OUT, do the checks that were firing
go silent — and does anything else change?" It is the nearest thing to a
known-good design for our own block interfaces: the current drop, minus one
confirmed defect at a time, in a Validation-owned copy.

For each repair in repair_catalog.json:
  1. copy the drop to repairs/work/<id>/ and apply the edits (each must match
     its declared count, or this is an error);
  2. run the repair's paths twice with identical stimulus — once on the
     untouched drop (baseline), once on the repaired copy;
  3. compare detector signatures per path.

Per path the result is three lists:
  silenced    detectors that fired on the baseline and not on the repair
              (expected ones are evidence the check was right)
  new         detectors that fire only on the repair (a bad repair, or a
              defect the first one was hiding)
  remaining   detectors that fire on both: a different defect, or a false
              positive — each is something to read at source

Usage:
    python3 Validation/repairs/repair_suite.py
    python3 Validation/repairs/repair_suite.py --score-only
"""
import argparse, concurrent.futures, json, os, shutil, subprocess, sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "faults"))
from seed_faults import signature  # noqa: E402

CATALOG = os.path.join(HERE, "repair_catalog.json")
WORK = os.path.join(HERE, "work")
REPORTS = os.path.join(ROOT, "Validation", "reports", "repairs")
MATRIX = os.path.join(REPORTS, "repair_matrix.json")


class RepairError(Exception):
    pass


def build(rep, drop_root, catalog=None):
    dst_root = os.path.join(WORK, rep["id"])
    dst = os.path.join(dst_root, drop_root)
    if os.path.exists(dst_root):
        shutil.rmtree(dst_root)
    shutil.copytree(os.path.join(ROOT, drop_root), dst)
    by_id = {r["id"]: r for r in (catalog or {}).get("repairs", [])}
    for bid in rep.get("base", []):
        _apply(by_id[bid], dst)
    _apply(rep, dst)
    return dst


def _apply(rep, dst):
    target = os.path.join(dst, rep["file"])
    with open(target) as f:
        text = f.read()
    for e in rep["edits"]:
        want = e.get("count", 1)
        n = text.count(e["from"])
        if n != want:
            raise RepairError(f"{rep['id']}: edit matches {n} time(s), expected "
                              f"{want}: {e['from'][:70]!r}. The drop changed "
                              f"under the catalog — update the repair.")
        text = text.replace(e["from"], e["to"])
    with open(target, "w") as f:
        f.write(text)


def run(tag, path, root, timeout, judge_only=False):
    rep = os.path.join(REPORTS, tag)
    os.makedirs(rep, exist_ok=True)
    env = dict(os.environ)
    if root:
        env["VALIDATION_RTL_DROP_ROOTS"] = root
    cmd = ["python3", "Validation/tools/run_path.py", "--path", path,
           "--tag", f"repairs/{tag}", "--report-dir", rep, "--no-coverage",
           "--timeout", str(timeout)] + (["--judge-only"] if judge_only else [])
    for attempt in range(3):          # the login node drops connections under load
        r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
        if r.returncode != 2 or not any(k in (r.stderr or "") + (r.stdout or "") for k in ("SSHException", "Connection reset", "timed out")):
            break
    with open(os.path.join(rep, f"{path}_run.txt"), "w") as f:
        f.write((r.stdout or "") + (r.stderr or ""))
    return r.returncode


def detectors(sig):
    return {k: v for k, v in sig.items()
            if k.startswith(("id:", "assert:", "stage:", "log:"))
            and not k.startswith("id:scope")}


def score(rep, path):
    # scored against the stack beneath it: the last base repair, or the
    # untouched drop
    under = rep["base"][-1] if rep.get("base") else "baseline"
    b = signature(os.path.join(REPORTS, under), path)
    r = signature(os.path.join(REPORTS, rep["id"]), path)
    if b is None or r is None:
        return {"repair": rep["id"], "path": path, "error":
                "missing " + ("baseline" if b is None else "repair") + " report"}
    db, dr = detectors(b), detectors(r)
    silenced = {k: db[k] for k in db if k not in dr}
    new = {k: dr[k] for k in dr if k not in db}
    remaining = {k: (db[k], dr[k]) for k in db if k in dr}
    matched = {k: (b[k], r[k]) for k in b if k.startswith("matched:") and k in r
               and b[k] != r[k]}
    exp = set(rep["expect_gone"])
    return {"repair": rep["id"], "path": path,
            "verdict": (b.get("_verdict"), r.get("_verdict")),
            "silenced_expected": {k: v for k, v in silenced.items() if k in exp},
            "silenced_other": {k: v for k, v in silenced.items() if k not in exp},
            "expected_still_firing": {k: v for k, v in remaining.items() if k in exp},
            "new": new,
            "remaining": {k: v for k, v in remaining.items() if k not in exp},
            "matched_changed": matched}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--score-only", action="store_true")
    ap.add_argument("--judge-only", action="store_true")
    ap.add_argument("--skip-baseline", action="store_true",
                    help="reuse the existing baseline reports")
    ap.add_argument("--missing-only", action="store_true",
                    help="run only the jobs that have no report yet")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=1500)
    args = ap.parse_args()
    with open(CATALOG) as f:
        cat = json.load(f)
    reps = [r for r in cat["repairs"]
            if not args.only or any(r["id"].startswith(p) for p in args.only)]
    if not args.score_only:
        jobs, seen = [], set()
        for r in reps:
            root = build(r, cat, ) if False else build(r, cat["drop_root"], cat)
            print(f"  built {r['id']} ({len(r['edits'])} edit(s) in {r['file']})")
            for p in r["paths"]:
                if p not in seen and not args.skip_baseline:
                    seen.add(p)
                    jobs.append(("baseline", p, None))
                jobs.append((r["id"], p, root))
        if args.missing_only:
            jobs = [j for j in jobs if not os.path.exists(
                os.path.join(REPORTS, j[0], f"{j[1]}_report.json"))]
        print(f"  running {len(jobs)} job(s), {args.jobs} at a time")
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
            futs = {ex.submit(run, t, p, root, args.timeout, args.judge_only): (t, p)
                    for t, p, root in jobs}
            for fu in concurrent.futures.as_completed(futs):
                t, p = futs[fu]
                print(f"    done {t:30} {p:34} rc={fu.result()}")
    rows = [score(r, p) for r in reps for p in r["paths"]]
    print("\n" + "=" * 78)
    for row in rows:
        if row.get("error"):
            print(f"  {row['repair']} {row['path']}: {row['error']}")
            continue
        print(f"  {row['repair']}  {row['path']}  {row['verdict'][0]} -> {row['verdict'][1]}")
        for label, key in (("silenced", "silenced_expected"), ("silenced (not predicted)", "silenced_other"),
                           ("EXPECTED GONE, STILL FIRES", "expected_still_firing"),
                           ("NEW", "new"), ("remaining", "remaining"), ("matched", "matched_changed")):
            if row[key]:
                print(f"      {label:26} " + ", ".join(
                    f"{k}={v}" for k, v in list(row[key].items())[:8]))
    print("=" * 78)
    os.makedirs(REPORTS, exist_ok=True)
    with open(MATRIX, "w") as f:
        json.dump({"$schema": "validation-repair-matrix/1",
                   "generated_utc": datetime.utcnow().isoformat() + "Z",
                   "drop_root": cat["drop_root"], "rows": rows}, f, indent=2)
    print(f"  wrote {os.path.relpath(MATRIX, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
