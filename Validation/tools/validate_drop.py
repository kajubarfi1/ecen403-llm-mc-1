#!/usr/bin/env python3
"""
validate_drop.py — one command per RTL drop
============================================
Everything that has to happen when a new drop lands, in the order it has to
happen, with each step's exit criterion enforced before the next:

  1. resolve     every block resolves through the declared drop roots
  2. intake      the spec answers the questions the intake gate asks
                 (gaps are reported and filed; --strict-intake stops here)
  3. regenerate  integration map (from manifest `source` fields), schemas,
                 monitors, SVA, coverage models from the drop's manifests and
                 the spec (deterministic; a port change shows up here, not as
                 a silent miswire later)
  4. run         every runnable path on Olympus, N at a time; derived
                 reports for the single-hop paths fall out of their hosts
  5. rollup      merge coverage, write vplan statuses
  6. findings    emit findings v2 and the Frontend's retry_instructions.json
  7. compare     this drop against the previous snapshot: regressions, fixes
  8. snapshot    archive the reports under this drop's commit
  9. cockpit     regenerate the dashboard

Usage:
    python3 Validation/tools/validate_drop.py                 # the whole thing
    python3 Validation/tools/validate_drop.py --skip-sim      # re-judge existing traces
    python3 Validation/tools/validate_drop.py --paths path_01_write_cmd path_12_csr_timing_to_scheduling
    python3 Validation/tools/validate_drop.py --dry-run       # print the plan
"""

import argparse
import concurrent.futures
import glob
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))

PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
REPORTS = os.path.join(ROOT, "Validation", "reports", "paths")
DROPS = os.path.join(ROOT, "Validation", "reports", "drops")
LOGS = os.path.join(ROOT, "Validation", "reports", "validate_drop")


def sh(cmd, log=None, check=True, timeout=None):
    r = subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True,
                       text=True, timeout=timeout)
    out = (r.stdout or "") + (r.stderr or "")
    if log:
        with open(log, "a") as f:
            f.write(f"\n$ {cmd}\n{out}")
    if check and r.returncode != 0:
        raise RuntimeError(f"step failed ({r.returncode}): {cmd}\n{out[-1500:]}")
    return r.returncode, out


def banner(n, title):
    print(f"\n[{n}] {title}")
    print("    " + "-" * 68)


def runnable_paths(pdefs, only=None):
    ps = [p["id"] for p in pdefs if not p.get("judged_in")]
    if only:
        ps = [p for p in ps if p in set(only)]
    return ps


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--paths", nargs="*", default=None)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=1500, help="per path, seconds")
    ap.add_argument("--skip-sim", action="store_true",
                    help="re-judge existing traces instead of simulating")
    ap.add_argument("--skip-rollup", action="store_true")
    ap.add_argument("--skip-regenerate", action="store_true")
    ap.add_argument("--strict-intake", action="store_true",
                    help="stop when the spec has intake gaps")
    ap.add_argument("--partial", action="store_true",
                    help="phase-partial drop: run every path whose blocks the drop "
                         "provides, report the rest as blocked, never substitute")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    with open(PATH_DEFS) as f:
        pdefs = json.load(f)["paths"]
    paths = runnable_paths(pdefs, args.paths)
    os.makedirs(LOGS, exist_ok=True)
    t0 = time.time()
    import rtl_drop as RD
    head = RD.drop_id()
    log = os.path.join(LOGS, f"{head}.log")
    if os.path.exists(log):
        os.remove(log)

    if args.dry_run:
        print(f"drop {head}: {len(paths)} runnable path(s), {args.jobs} at a time")
        for p in paths:
            print("   ", p)
        return 0

    # 1. resolve ---------------------------------------------------------------
    banner(1, f"resolve blocks through the declared drop (git {head})")
    rc, out = sh("python3 Validation/structural/rtl_drop.py", log, check=False)
    print("    " + out.strip().splitlines()[-1])
    blocked, drop_status = {}, None
    if rc != 0 and not args.partial:
        print("    STOP: the drop does not provide every block "
              "(--partial runs what it does provide).")
        return 1
    all_blocks = sorted({b for p in pdefs for b in p["blocks"]})
    absent = set(RD.missing(all_blocks)) if rc != 0 else set()
    present = [b for b in all_blocks if b not in absent]

    # 1b. spec consistency --------------------------------------------------
    # Every block says which spec revision generated it. Validation judges
    # against ONE spec (VALIDATION_SPEC, default Validation/spec/...). A block
    # from another revision is foreign: nothing the spec-derived checkers say
    # about it is evidence, so every path that includes it is blocked and the
    # mismatch is filed. The drop's own shipped spec is named so the run can
    # be repeated against it.
    spec_path = os.environ.get("VALIDATION_SPEC", os.path.join(
        ROOT, "Validation", "spec", "llmmc_microarchitecturespec_filled.json"))
    with open(spec_path) as f:
        val_rev = json.load(f).get("revision")
    stamps = {b: RD.spec_stamp(b)[1] for b in present}
    foreign = {b: r for b, r in stamps.items() if r and r != val_rev}
    unstamped = [b for b, r in stamps.items() if not r]
    ship_path, ship_rev = RD.shipped_spec()
    print(f"    validation spec : rev {val_rev} ({os.path.relpath(spec_path, ROOT)})")
    if ship_path:
        print(f"    drop ships spec : rev {ship_rev} ({os.path.relpath(ship_path, ROOT)})"
              + ("" if ship_rev == val_rev else "   <-- NOT the spec being judged against"))
    if foreign:
        by_rev = {}
        for b, r in foreign.items():
            by_rev.setdefault(r, []).append(b)
        for r, bs in by_rev.items():
            print(f"    FOREIGN spec rev {r}: {', '.join(sorted(bs))}")
        if ship_path and ship_rev != val_rev:
            print(f"    to judge those blocks against their own spec: "
                  f"VALIDATION_SPEC={os.path.relpath(ship_path, ROOT)} python3 Validation/tools/validate_drop.py --partial")
    if unstamped:
        print(f"    unstamped (no spec_revision in manifest or RTL header): {', '.join(unstamped)}")
    spec_findings = []
    for b, r in sorted(foreign.items()):
        spec_findings.append({
            "source": "validation", "target": "frontend", "kind": "spec_mismatch",
            "scope": b, "severity": "critical", "spec_revision": val_rev,
            "title": f"{b} was generated from spec rev {r}; the drop is judged against rev {val_rev}",
            "detail": (f"The block's manifest says spec_revision = {r}. The other blocks of this drop"
                       f"{' and the spec validation loads' if val_rev else ''} are rev {val_rev}. A design "
                       f"assembled from two specs has no single contract: every path through {b} is blocked "
                       f"until the drop is regenerated from one spec"
                       + (f" (the drop ships {os.path.relpath(ship_path, ROOT)}, rev {ship_rev})." if ship_path else ".")),
            "evidence": {"block": b, "block_spec_revision": r, "validation_spec_revision": val_rev,
                         "shipped_spec": os.path.relpath(ship_path, ROOT) if ship_path else None,
                         "shipped_spec_revision": ship_rev},
            "spec_ref": "revision", "status": "open"})
    os.makedirs(os.path.join(ROOT, "Validation", "findings", "outbox"), exist_ok=True)
    with open(os.path.join(ROOT, "Validation", "findings", "outbox", "spec_revision_findings.json"), "w") as f:
        json.dump({"$schema": "validation-findings/1", "spec_revision": val_rev,
                   "validation_spec": os.path.relpath(spec_path, ROOT),
                   "shipped_spec": os.path.relpath(ship_path, ROOT) if ship_path else None,
                   "shipped_spec_revision": ship_rev, "block_revisions": stamps,
                   "finding_count": len(spec_findings), "findings": spec_findings}, f, indent=2)

    # 2. spec review -------------------------------------------------------------
    # The same stage the Frontend pipeline runs before Phase 1
    # (validate_spec_stage: schema, JESD79-3, register map, intake gaps).
    # A spec that fails it is not a contract: RTL judged against it proves
    # nothing, so the run stops. Gaps are advisory unless --strict-intake.
    banner(2, f"spec review (rev {val_rev})")
    rc, out = sh(f"python3 Validation/spec/validate_spec_stage.py --spec {spec_path}",
                 log, check=False)
    for l in out.splitlines():
        if l.strip().startswith(("status", "JEDEC", "BLOCK", "human")):
            print("    " + l.strip()[:140])
    if rc != 0:
        print("    STOP: the spec fails its own review; nothing generated from it can be judged.")
        return 1
    n_gaps = sum(1 for l in out.splitlines() if "[gap:" in l)
    if n_gaps and args.strict_intake:
        print(f"    STOP: --strict-intake and the spec has {n_gaps} gap(s).")
        return 1

    # 3. regenerate ------------------------------------------------------------
    if not args.skip_regenerate:
        banner(3, "regenerate integration map, schemas, monitors, SVA, coverage from the drop")
        for cmd in ("python3 Validation/structural/integration_map_gen.py --findings "
                    "Validation/findings/outbox/integration_map_findings.json",
                    "python3 Validation/structural/width_conformance.py --json "
                    "Validation/findings/outbox/width_findings.json",
                    "python3 Validation/txn/schema_gen.py"
                    + (" --allow-missing" if absent else ""),
                    "python3 Validation/txn/monitor_gen.py",
                    "python3 Validation/sva/sva_gen.py",
                    "python3 Validation/sva/coverage_gen.py",
                    "python3 Validation/sva/block_coverage_gen.py"):
            rc, out = sh(cmd, log, check=False)
            last = out.strip().splitlines()[-1] if out.strip() else ""
            if "width_conformance" in cmd:
                # its non-zero exit means "mismatches filed", a finding about
                # the drop (routed in step 6), never a refusal to validate it
                n = re.search(r"(\d+) mismatch", out)
                print(f"    {'ok  ' if rc == 0 else 'FIND'} {cmd.split('/')[-1]:24} "
                      f"{n.group(1) + ' width mismatch(es) filed' if n else last[:80]}")
                continue
            print(f"    {'ok  ' if rc == 0 else 'FAIL'} {cmd.split('/')[-1]:24} {last[:80]}")
            if rc != 0:
                print("    STOP: a generator refused the drop; its output is in the log.")
                print(f"    log: {os.path.relpath(log, ROOT)}")
                return 1
    else:
        banner(3, "regenerate: skipped")

    # 3b. what can run ----------------------------------------------------------
    # A path is blocked when its closure needs an absent block, or crosses an
    # edge whose two manifests disagree on width (filed as width_mismatch).
    # Every path is classified, derived ones included, so a finding whose
    # paths are all blocked is carried as untested rather than resolved.
    sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))
    import chain_harness_gen as CHG
    with open(os.path.join(ROOT, "Validation", "structural", "integration_map.json")) as f:
        imap_now = json.load(f)
    bad_edges = imap_now.get("inconsistent_connections", [])
    runnable = []
    for pdef in pdefs:
        pid = pdef["id"]
        need = set(CHG.block_closure(pdef["blocks"], imap_now, bool(pdef.get("standalone"))))
        if need & absent:
            blocked[pid] = sorted(need & absent)
        elif need & set(foreign):
            blocked[pid] = [f"spec mismatch {b} (rev {foreign[b]})" for b in sorted(need & set(foreign))]
        else:
            cross = [f"{e['from']}({e['from_width']})->{e['to']}({e['to_width']})" for e in bad_edges
                     if e["from"].partition(".")[0] in need and e["to"].partition(".")[0] in need]
            if cross:
                blocked[pid] = ["width mismatch " + c for c in cross]
            elif pid in paths:
                runnable.append(pid)
    if absent:
        print(f"    PARTIAL drop: present {present}")
        print(f"                  absent  {sorted(absent)}")
    if blocked:
        print(f"    {len(runnable)} path(s) runnable, {len(blocked)} blocked:")
        for pid, need in blocked.items():
            print(f"      blocked  {pid:34} needs {', '.join(need)}")
    paths = runnable
    if absent or blocked:
        drop_status = {"$schema": "validation-drop-status/1", "drop": head,
                       "partial": bool(absent), "blocks_present": present,
                       "blocks_absent": sorted(absent),
                       "inconsistent_edges": bad_edges,
                       "validation_spec_revision": val_rev,
                       "foreign_spec_blocks": foreign,
                       "paths_run": runnable, "paths_blocked": blocked,
                       "note": "A blocked path is not a failure and not a pass: it waits "
                               "for the drop that brings its blocks or fixes the edge it "
                               "crosses. Nothing was substituted."}
    nothing_runs = not runnable
    if nothing_runs:
        print("    nothing can run on this drop; the structural findings are still "
              "emitted and routed (steps 4, 5, 7, 8 skipped).")

    # 4. run -------------------------------------------------------------------
    banner(4, f"{'re-judge' if args.skip_sim else 'simulate'} {len(paths)} path(s), "
              f"{args.jobs} at a time")
    verdicts = {}
    if nothing_runs:
        print("    (no runnable path)")

    # anything blocked => the run is isolated like a partial one: its reports
    # live apart, so a blocked path's report from an earlier drop is never
    # judged, compared or snapshotted as if it were this drop's
    partial = bool(absent) or bool(blocked)
    report_dir = REPORTS if not partial else os.path.join(
        ROOT, "Validation", "reports", "partial", head)
    if partial:
        os.makedirs(report_dir, exist_ok=True)
        os.makedirs(report_dir, exist_ok=True)
        for f in glob.glob(os.path.join(report_dir, "*")):
            os.remove(f)
        print(f"    reports -> {os.path.relpath(report_dir, ROOT)} (kept apart from "
              f"full-drop reports so nothing stale is judged)")

    def run_one(p):
        cmd = (f"python3 Validation/tools/run_path.py --path {p} "
               f"--timeout {args.timeout}" + (" --judge-only" if args.skip_sim else "")
               + (f" --report-dir {report_dir}" if partial else ""))
        rc, out = sh(cmd, None, check=False, timeout=args.timeout + 300)
        with open(os.path.join(LOGS, f"{head}_{p}.txt"), "w") as f:
            f.write(out)
        m = re.search(r"path verdict : (\w+)", out)
        return p, (m.group(1) if m else f"rc={rc}"), rc

    with concurrent.futures.ThreadPoolExecutor(1 if args.skip_sim else max(1, args.jobs)) as ex:
        for p, v, rc in ex.map(run_one, paths):
            verdicts[p] = v
            print(f"    {p:34} {v}")
    n_pass = sum(1 for v in verdicts.values() if v == "PASS")
    n_fail = sum(1 for v in verdicts.values() if v == "FAIL")
    n_err = len(verdicts) - n_pass - n_fail
    print(f"    pass={n_pass} fail={n_fail} error={n_err}")

    # 5. rollup ----------------------------------------------------------------
    if not args.skip_rollup and not args.skip_sim and not nothing_runs:
        banner(5, "coverage rollup")
        since = time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(t0 - 60))
        rc, out = sh(f"python3 Validation/coverage/measure_coverage.py --rollup "
                     f"--since {since}", log, check=False, timeout=1800)
        m = re.search(r"imc report: (\S+)", out)
        tot = re.search(r"DESIGN TOTAL\s+(\S+)\s+([\d.]+%)", out)
        if m:
            sh(f"python3 Validation/coverage/coverage_rollup.py --report {m.group(1)} "
               f"--write-vplan", log, check=False)
        cov = [l.strip() for l in out.splitlines() if "vplan item(s) fully covered" in l]
        print(f"    design code coverage {tot.group(2) if tot else '?'}; "
              + (cov[0] if cov else "rollup output in the log"))
    else:
        banner(5, "coverage rollup: skipped")

    # 6. findings --------------------------------------------------------------
    banner(6, "findings v2 + retry instructions")
    ds_file = None
    if drop_status:
        ds_file = os.path.join(report_dir, "DROP_STATUS.json")
        with open(ds_file, "w") as f:
            json.dump(drop_status, f, indent=2)
    rc, out = sh("python3 Validation/findings/emit_findings.py"
                 + (f" --reports {report_dir} --drop-status {ds_file}" if drop_status else ""),
                 log, check=False, timeout=1200)
    print("    " + next((l.strip() for l in out.splitlines() if "finding(s)" in l), out[-120:]))
    rc, out = sh("python3 Validation/findings/retry_adapter.py", log, check=False)
    print("    " + next((l.strip() for l in out.splitlines() if l.strip().startswith(("FAIL", "PASS"))), ""))

    # 7. compare ---------------------------------------------------------------
    banner(7, "compare with the previous drop")
    if nothing_runs:
        print("    nothing ran; no comparison, no snapshot")
        prev = []
    # a partial run's snapshot is never the reference: compare against the
    # newest COMPLETE drop, whether this run is partial or not
    prev = [d for d in sorted(glob.glob(os.path.join(DROPS, "*")))
            if os.path.basename(d) != head and not os.path.basename(d).endswith("-partial")]
    if blocked:
        print(f"    only the {len(paths)} path(s) that ran are compared")
    if prev and not nothing_runs:
        prev_dir = max(prev, key=lambda d: os.path.getmtime(os.path.join(d, "SNAPSHOT.json"))
                       if os.path.exists(os.path.join(d, "SNAPSHOT.json")) else 0)
        rc, out = sh(f"python3 Validation/tools/compare_drops.py --a {prev_dir} "
                     f"--b {report_dir} --json Validation/reports/drop_comparison.json"
                     + (" --paths " + " ".join(paths) if blocked else ""),
                     log, check=False)
        for l in out.splitlines():
            if l.strip().startswith(("REG", "FIX", "STIM", "CHG")) or "regression=" in l \
                    or l.strip().startswith(("same=", "changed=", "fixed=")):
                print("    " + l.strip())
        print(f"    vs {os.path.basename(prev_dir)}: "
              + (out.strip().splitlines()[-2].strip() if out.strip() else ""))
    elif not nothing_runs:
        print("    no previous snapshot; this drop becomes the reference")

    # 8. snapshot --------------------------------------------------------------
    banner(8, "snapshot")
    if nothing_runs:
        print("    skipped")
        rc, out = 0, ""
    else:
        rc, out = sh("python3 Validation/tools/compare_drops.py --snapshot"
                 + (f" --b {report_dir} --tag partial" if partial else ""),
                 log, check=False)
        print("    " + out.strip())

    # 9. cockpit ---------------------------------------------------------------
    banner(9, "cockpit")
    rc, out = sh("python3 Validation/tools/dashboard_gen.py", log, check=False)
    print("    " + out.strip())

    print(f"\n  drop {head}{' (partial)' if partial else ''}: {n_pass} pass / "
          f"{n_fail} fail / {n_err} error"
          + (f" / {len(blocked)} blocked" if blocked else "")
          + f" in {(time.time() - t0) / 60:.1f} min; log {os.path.relpath(log, ROOT)}")
    return 0 if n_err == 0 and not nothing_runs else 1


if __name__ == "__main__":
    sys.exit(main())
