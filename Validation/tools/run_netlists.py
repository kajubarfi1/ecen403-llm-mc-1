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
    return attribute({"path": path, "verdict": verdict, "first_failure": first, "fired": fired}, block)


RTL_REPORTS = os.path.join(ROOT, "Validation", "reports", "paths")


def attribute(res, block):
    """A pair that fails on a stage that is not the netlist's block, exactly
    as the RTL-only run of the same path fails, is the RTL's failure
    carried into the harness, not evidence about the netlist: every
    netlist "failed" path_03/18 on the data_path read-capture defect
    (2026-10-15). Such a pair is RTL-FAIL and does not count against the
    block; a failure on the block's own stage, or one the RTL run does not
    show, stays FAIL."""
    if res.get("verdict") != "FAIL" or not res.get("first_failure"):
        return res
    stage = res["first_failure"].split(":", 1)[0]
    stage_blocks = {b.strip().split(" ")[0] for b in stage.split("+")}
    if block in stage_blocks:
        return res
    rp = os.path.join(RTL_REPORTS, f"{res['path']}_report.json")
    if not os.path.exists(rp):
        return res
    with open(rp) as f:
        rtl = json.load(f)
    rtl_first = next((s.get("stage") for s in rtl.get("stages", []) if s.get("verdict") == "fail"), None)
    if str(rtl.get("verdict", "")).lower() == "fail" and rtl_first == stage:
        res["verdict"] = "RTL-FAIL"
        res["attribution"] = f"the RTL-only run of this path fails on the same stage ({stage}); not the netlist's"
    return res


def block_ids_at_rev(rev):
    """Per-block design ids of Frontend2/OutputFolders at a git revision,
    computed by rtl_drop itself on a scratch export of that tree (so the
    hashing is the one the drop id uses, not a reimplementation)."""
    import tempfile, tarfile, io
    d = tempfile.mkdtemp(prefix="drop_at_rev_")
    r = subprocess.run(["git", "archive", rev, "Frontend2/OutputFolders"], cwd=ROOT, capture_output=True)
    if r.returncode != 0:
        raise SystemExit(f"--built-from-rev {rev}: git archive failed: {r.stderr.decode(errors='replace')[:200]}")
    with tarfile.open(fileobj=io.BytesIO(r.stdout)) as t:
        t.extractall(d)
    env = dict(os.environ, VALIDATION_RTL_DROP_ROOTS=os.path.join(d, "Frontend2", "OutputFolders"))
    r = subprocess.run([sys.executable, os.path.join(ROOT, "Validation", "structural", "rtl_drop.py"),
                        "--block-design-ids"], cwd=ROOT, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"--built-from-rev {rev}: {r.stdout[-300:]}{r.stderr[-300:]}")
    return json.loads(r.stdout.strip().splitlines()[-1])


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
    ap.add_argument("--rescore", action="store_true",
                    help="no runs: rebuild summary.json from the per-path reports on disk")
    ap.add_argument("--built-from-rev", default=None, metavar="GIT_REV",
                    help="the git revision whose Frontend2/OutputFolders the netlists were cut "
                         "from; staleness is then decided PER BLOCK (a block whose RTL did not "
                         "change between that revision and the drop under judgement has a "
                         "current netlist). Per-block `design_id` entries in NETLISTS.json "
                         "do the same without git.")
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
    done, kept = {}, {}
    sp = os.path.join(OUT, "summary.json")
    if os.path.exists(sp):
        with open(sp) as f:
            prev = json.load(f)
        if prev.get("judged_against") == judged and prev.get("netlists") == summary["netlists"]:
            # blocks not in this run keep their record; a --blocks run must
            # never shrink the summary to the blocks it ran (it did, 10-15)
            kept = {b: s for b, s in prev.get("blocks", {}).items() if b not in blocks}
            if args.skip_done:
                for b, s in prev.get("blocks", {}).items():
                    for r in s.get("paths", []):
                        if r["verdict"] in ("PASS", "FAIL"):
                            done[(b, r["path"])] = r
    if args.rescore:
        # read the reports already on disk instead of running anything
        for b in blocks:
            for p in paths_for(b, pdefs, imap):
                rp = os.path.join(OUT, b, f"{p}_report.json")
                if os.path.exists(rp):
                    with open(rp) as f:
                        rep = json.load(f)
                    first = next((f"{s.get('stage')}: {str(s.get('summary', ''))[:160]}"
                                  for s in rep.get("stages", []) if s.get("verdict") == "fail"), None)
                    done[(b, p)] = attribute({"path": p, "verdict": str(rep.get("verdict", "?")).upper(),
                                              "first_failure": first, "fired": {}}, b)
    jobs = [(b, os.path.join(ROOT, nl["blocks"][b]["netlist"]), p)
            for b in blocks for p in paths_for(b, pdefs, imap) if (b, p) not in done]
    if jobs and not args.judge_only:
        # a rebuilt netlist may use a cell the mirrored library lacks; fetch
        # it and reinstall before any run, or every pair fails to elaborate
        import install_sky130_models as ISM
        fetched = ISM.fetch_missing([os.path.join(ROOT, nl["blocks"][b]["netlist"]) for b in blocks])
        if fetched:
            r = subprocess.run([sys.executable, os.path.join(ROOT, "Validation", "tools", "install_sky130_models.py"),
                                "--no-fetch", "--no-smoke"], cwd=ROOT, capture_output=True, text=True)
            print("  " + (r.stdout.strip().splitlines() or ["(install produced no output)"])[-1])
            if r.returncode != 0:
                raise SystemExit("cell model install failed:\n" + (r.stdout + r.stderr)[-800:])
    if args.rescore:
        jobs = []
    # Provenance: a netlist is evidence about the drop it was cut from. When
    # the netlist set names another drop and no design id says the design
    # is the same, every verdict below is about a stale netlist and is
    # marked so (the scheduler netlist of 2026-10-14 reproduced the pre-fix
    # RTL's defects; nothing in the record said it predated the fix).
    built = nl.get("drop_id")
    built_design = nl.get("design_id")
    stale = bool(built) and built != judged["drop_id"] and built_design != judged["design_id"]
    summary["provenance"] = ("same drop" if built == judged["drop_id"]
                             else "same design" if built_design == judged["design_id"]
                             else "STALE: built from another drop and no design id matches"
                             if built else "unknown: the netlist set names no drop")
    # Per-block provenance: a netlist is evidence about ITS block's RTL. When
    # the netlist set (or --built-from-rev) says what each block was cut
    # from, a block unchanged since then has a current netlist even though
    # the drop id moved (the 10-15 drop changed refresh_ctrl only; the
    # scheduler and bank_tracker netlists rebuilt that day stay current).
    current_ids = RD.block_design_ids()
    built_ids = {b: v.get("design_id") for b, v in nl["blocks"].items() if v.get("design_id")}
    if args.built_from_rev and not built_ids:
        built_ids = block_ids_at_rev(args.built_from_rev)
        summary["netlists_built_from"]["git_rev"] = args.built_from_rev
    stale_blocks = {}
    for b in blocks:
        if built_ids.get(b):
            stale_blocks[b] = built_ids[b] != current_ids.get(b)
        else:
            stale_blocks[b] = stale
    summary["block_provenance"] = {b: ("current" if not stale_blocks[b] else "STALE") for b in blocks}
    if stale and built_ids:
        n_cur = sum(1 for b in blocks if not stale_blocks[b])
        summary["provenance"] = (f"per block: {n_cur}/{len(blocks)} netlist(s) current for this drop"
                                 + (f"; STALE: {', '.join(b for b in blocks if stale_blocks[b])}"
                                    if n_cur < len(blocks) else ""))
    print(f"{len(jobs)} netlist run(s) over {len(blocks)} block(s), {args.jobs} at a time"
          + (f"; {len(done)} already judged" if done else "")
          + f"; judging against drop {judged['drop_id']} (design {judged['design_id']})")
    if stale and built_ids:
        cur = [b for b in blocks if not stale_blocks[b]]
        print(f"  netlist set built from drop {built}; per-block provenance says "
              f"{len(cur)}/{len(blocks)} netlist(s) are current for this drop"
              + (f"; STALE: {', '.join(b for b in blocks if stale_blocks[b])}" if any(stale_blocks.values()) else ""))
    elif stale:
        print(f"  STALE NETLISTS: built from drop {built}"
              + (f" (design {built_design})" if built_design else " (no design id recorded)")
              + f", the drop under judgement is {judged['drop_id']} (design {judged['design_id']}). "
              f"A pass below says the old design still passes; a fail may be the old design's. "
              f"Rebuild from the current drop.")
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
    summary["blocks"].update(kept)
    for b in blocks:
        rows = sorted(results[b], key=lambda r: r["path"])
        verdict = "PASS" if rows and all(r["verdict"] in ("PASS", "RTL-FAIL") for r in rows) else "FAIL"
        summary["blocks"][b] = {"netlist": nl["blocks"][b]["netlist"], "verdict": verdict,
                                "stale_netlist": stale_blocks[b], "paths": rows,
                                "backend": {k: nl["blocks"][b].get(k) for k in ("fmax_mhz", "wns_ns", "sta", "drc_violations", "lvs")}}
    with open(os.path.join(OUT, "summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print("\n  block         verdict  paths")
    for b in sorted(summary["blocks"]):
        s = summary["blocks"][b]
        n_pass = sum(1 for r in s["paths"] if r["verdict"] == "PASS")
        n_rtl = sum(1 for r in s["paths"] if r["verdict"] == "RTL-FAIL")
        print(f"  {b:13} {s['verdict']:7}  {n_pass}/{len(s['paths'])}"
              + (f"  (+{n_rtl} RTL-FAIL, the RTL's own)" if n_rtl else "")
              + ("   (STALE netlist)" if s.get("stale_netlist") else ""))
    print(f"  provenance: {summary['provenance']}")
    print(f"  wrote {os.path.relpath(os.path.join(OUT, 'summary.json'), ROOT)}")
    return 0 if all(s["verdict"] == "PASS" for s in summary["blocks"].values()) else 1


if __name__ == "__main__":
    sys.exit(main())
