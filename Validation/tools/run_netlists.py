#!/usr/bin/env python3
"""
run_netlists.py — the backend's per-block netlists through the paths
====================================================================
SIGNOFF.md §5c: a block's netlist is accepted when every path that
instantiates the block passes with the netlist in the RTL's place, judged by
the same models, rules and assertions as the RTL (sky130 functional cell
models, zero delay). One block at a time, every path that lists it, each run
under its own tag and report directory so the RTL reports are untouched.

Input: backend/outputs/NETLISTS.json (blocks -> netlist path) or --netlists.
Output: Validation/reports/netlists/<block>/<path>_report.json per run and
        Validation/reports/netlists/summary.json (per block: paths, verdicts,
        fired assertions, the netlist's drop and the drop judged against).

Usage:
    python3 Validation/tools/run_netlists.py                 # every block
    python3 Validation/tools/run_netlists.py --blocks wb_port refresh_ctrl
    python3 Validation/tools/run_netlists.py --judge-only    # re-judge existing traces
"""
import argparse
import concurrent.futures
import datetime
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
NETLISTS = os.path.join(ROOT, "backend", "outputs", "NETLISTS.json")
OUT = os.path.join(ROOT, "Validation", "reports", "netlists")
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))


def paths_for(block, pdefs, imap):
    """Every runnable path whose simulated harness contains the block: the
    path's declared blocks plus the support closure the integration map
    adds. The declared list alone let the pre-fix bank_tracker netlist pass
    its 3 declared paths while the RTL's TIMING_007 lived on the 8 paths
    where bank_tracker is support (2026-10-14)."""
    sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))
    import chain_harness_gen as CHG
    out = []
    for p in pdefs:
        if p.get("judged_in"):
            continue
        if block in CHG.block_closure(p["blocks"], imap, bool(p.get("standalone"))):
            out.append(p["id"])
    return out


def run_one(block, netlist, path, timeout, judge_only):
    rep_dir = os.path.join(OUT, block)
    os.makedirs(rep_dir, exist_ok=True)
    cmd = [sys.executable, "-W", "ignore", os.path.join(ROOT, "Validation", "tools", "run_path.py"),
           "--path", path, "--netlist", f"{block}={netlist}", "--tag", f"netlist_{block}",
           "--report-dir", rep_dir, "--timeout", str(timeout)]
    if judge_only:
        cmd.append("--judge-only")
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout + 300)
    out = r.stdout + r.stderr
    with open(os.path.join(rep_dir, f"{path}.log"), "w") as f:
        f.write(out)
    m = re.search(r"path verdict : (\w+)", out)
    verdict = m.group(1) if m else f"rc={r.returncode}"
    fired, first = {}, None
    rp = os.path.join(rep_dir, f"{path}_report.json")
    if os.path.exists(rp):
        with open(rp) as f:
            rep = json.load(f)
        for s in rep.get("stages", []):
            if s.get("verdict") == "fail" and first is None:
                first = f"{s.get('stage')}: {str(s.get('summary', ''))[:160]}"
            # the runner folds fired assertions into the stage summary:
            # "SVA fired: a_TIMING_004 x23, a_PROTO_002 x5"
            m2 = re.search(r"SVA fired: (.*)$", str(s.get("summary", "")))
            if m2:
                for name, n in re.findall(r"(a_[A-Z0-9_]+) x(\d+)", m2.group(1)):
                    fired[name] = fired.get(name, 0) + int(n)
    return {"path": path, "verdict": verdict, "first_failure": first, "fired": fired}


def main():
    global OUT
    ap = argparse.ArgumentParser()
    ap.add_argument("--netlists", default=NETLISTS)
    ap.add_argument("--blocks", nargs="*")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=1500)
    ap.add_argument("--judge-only", action="store_true")
    ap.add_argument("--out", default=OUT,
                    help="report directory (default reports/netlists); use another to judge "
                         "netlists against a different drop root without touching the record")
    ap.add_argument("--skip-done", action="store_true",
                    help="keep (block, path) results already in summary.json for this drop and "
                         "netlist set; run only the pairs it lacks")
    args = ap.parse_args()
    OUT = os.path.abspath(args.out)

    with open(args.netlists) as f:
        nl = json.load(f)
    with open(PATH_DEFS) as f:
        pdefs = json.load(f)["paths"]
    with open(os.path.join(ROOT, "Validation", "structural", "integration_map.json")) as f:
        imap = json.load(f)
    import rtl_drop as RD
    judged = {"drop_id": RD.drop_id(), "design_id": RD.design_id()}
    blocks = args.blocks or sorted(nl["blocks"])
    os.makedirs(OUT, exist_ok=True)
    summary = {"$schema": "validation-netlists/1",
               "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "netlists": os.path.relpath(args.netlists, ROOT),
               "netlists_built_from": {"drop_id": nl.get("drop_id"),
                                       "design_equivalent_drop": nl.get("design_equivalent_drop")},
               "judged_against": judged,
               "path_rule": "every runnable path whose harness closure contains the block",
               "blocks": {}}
    done = {}
    sp = os.path.join(OUT, "summary.json")
    if args.skip_done and os.path.exists(sp):
        with open(sp) as f:
            prev = json.load(f)
        if prev.get("judged_against") == judged and prev.get("netlists") == summary["netlists"]:
            for b, s in prev.get("blocks", {}).items():
                for r in s.get("paths", []):
                    if r["verdict"] in ("PASS", "FAIL"):
                        done[(b, r["path"])] = r
    jobs = [(b, os.path.join(ROOT, nl["blocks"][b]["netlist"]), p)
            for b in blocks for p in paths_for(b, pdefs, imap) if (b, p) not in done]
    print(f"{len(jobs)} netlist run(s) over {len(blocks)} block(s), {args.jobs} at a time"
          + (f"; {len(done)} already judged" if done else "")
          + f"; judging against drop {judged['drop_id']} (design {judged['design_id']})")
    results = {b: [r for (bb, _p), r in done.items() if bb == b] for b in blocks}
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        futs = {ex.submit(run_one, b, n, p, args.timeout, args.judge_only): (b, p) for b, n, p in jobs}
        for fut in concurrent.futures.as_completed(futs):
            b, p = futs[fut]
            try:
                res = fut.result()
            except Exception as e:
                res = {"path": p, "verdict": f"error: {type(e).__name__}", "first_failure": str(e)[:160], "fired": {}}
            results[b].append(res)
            print(f"  {b:13} {p:34} {res['verdict']:6} {res['first_failure'] or ''}"[:150])
    for b in blocks:
        rows = sorted(results[b], key=lambda r: r["path"])
        verdict = "PASS" if rows and all(r["verdict"] == "PASS" for r in rows) else "FAIL"
        summary["blocks"][b] = {"netlist": nl["blocks"][b]["netlist"], "verdict": verdict,
                                "paths": rows,
                                "backend": {k: nl["blocks"][b].get(k) for k in ("fmax_mhz", "wns_ns", "sta", "drc_violations", "lvs")}}
    with open(os.path.join(OUT, "summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print("\n  block         verdict  paths")
    for b in blocks:
        s = summary["blocks"][b]
        n_pass = sum(1 for r in s["paths"] if r["verdict"] == "PASS")
        print(f"  {b:13} {s['verdict']:7}  {n_pass}/{len(s['paths'])}")
    print(f"  wrote {os.path.relpath(os.path.join(OUT, 'summary.json'), ROOT)}")
    return 0 if all(s["verdict"] == "PASS" for s in summary["blocks"].values()) else 1


if __name__ == "__main__":
    sys.exit(main())
