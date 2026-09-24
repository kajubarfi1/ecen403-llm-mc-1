#!/usr/bin/env python3
"""
validate_drop.py — one command per RTL drop
============================================
Everything that has to happen when a new drop lands, in the order it has to
happen, with each step's exit criterion enforced before the next:

  1. resolve     every block resolves through the declared drop roots
  2. intake      the spec answers the questions the intake gate asks
                 (gaps are reported and filed; --strict-intake stops here)
  3. regenerate  schemas, monitors, SVA, coverage models from the drop's
                 manifests and the spec (deterministic; a port change shows
                 up here, not as a silent miswire later)
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
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    with open(PATH_DEFS) as f:
        pdefs = json.load(f)["paths"]
    paths = runnable_paths(pdefs, args.paths)
    os.makedirs(LOGS, exist_ok=True)
    t0 = time.time()
    import rtl_drop as RD
    head = RD._git_head() or "unknown"
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
    if rc != 0:
        print("    STOP: the drop does not provide every block.")
        return 1

    # 2. intake ----------------------------------------------------------------
    banner(2, "spec intake gate")
    rc, out = sh("python3 Validation/spec/spec_completeness.py --findings "
                 "Validation/findings/outbox/intake_spec_gaps.json", log, check=False)
    tail = [l for l in out.splitlines() if "gap(s)" in l or "complete:" in l]
    print("    " + (tail[0].strip() if tail else out.strip()[-120:]))
    if rc != 0 and args.strict_intake:
        print("    STOP: --strict-intake and the spec has gaps.")
        return 1

    # 3. regenerate ------------------------------------------------------------
    if not args.skip_regenerate:
        banner(3, "regenerate schemas, monitors, SVA, coverage from the drop")
        for cmd in ("python3 Validation/txn/schema_gen.py",
                    "python3 Validation/txn/monitor_gen.py",
                    "python3 Validation/sva/sva_gen.py",
                    "python3 Validation/sva/coverage_gen.py",
                    "python3 Validation/sva/block_coverage_gen.py"):
            rc, out = sh(cmd, log, check=False)
            last = out.strip().splitlines()[-1] if out.strip() else ""
            print(f"    {'ok  ' if rc == 0 else 'FAIL'} {cmd.split('/')[-1]:24} {last[:80]}")
            if rc != 0:
                print("    STOP: a generator refused the drop; its output is in the log.")
                print(f"    log: {os.path.relpath(log, ROOT)}")
                return 1
    else:
        banner(3, "regenerate: skipped")

    # 4. run -------------------------------------------------------------------
    banner(4, f"{'re-judge' if args.skip_sim else 'simulate'} {len(paths)} path(s), "
              f"{args.jobs} at a time")
    verdicts = {}

    def run_one(p):
        cmd = (f"python3 Validation/tools/run_path.py --path {p} "
               f"--timeout {args.timeout}" + (" --judge-only" if args.skip_sim else ""))
        rc, out = sh(cmd, None, check=False, timeout=args.timeout + 300)
        with open(os.path.join(LOGS, f"{head}_{p}.txt"), "w") as f:
            f.write(out)
        m = re.search(r"path verdict : (\w+)", out)
        return p, (m.group(1) if m else f"rc={rc}"), rc

    with concurrent.futures.ThreadPoolExecutor(1 if args.skip_sim else args.jobs) as ex:
        for p, v, rc in ex.map(run_one, paths):
            verdicts[p] = v
            print(f"    {p:34} {v}")
    n_pass = sum(1 for v in verdicts.values() if v == "PASS")
    n_fail = sum(1 for v in verdicts.values() if v == "FAIL")
    n_err = len(verdicts) - n_pass - n_fail
    print(f"    pass={n_pass} fail={n_fail} error={n_err}")

    # 5. rollup ----------------------------------------------------------------
    if not args.skip_rollup and not args.skip_sim:
        banner(5, "coverage rollup")
        rc, out = sh("python3 Validation/coverage/measure_coverage.py --rollup",
                     log, check=False, timeout=1800)
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
    rc, out = sh("python3 Validation/findings/emit_findings.py", log, check=False,
                 timeout=1200)
    print("    " + next((l.strip() for l in out.splitlines() if "finding(s)" in l), out[-120:]))
    rc, out = sh("python3 Validation/findings/retry_adapter.py", log, check=False)
    print("    " + next((l.strip() for l in out.splitlines() if l.strip().startswith(("FAIL", "PASS"))), ""))

    # 7. compare ---------------------------------------------------------------
    banner(7, "compare with the previous drop")
    prev = [d for d in sorted(glob.glob(os.path.join(DROPS, "*")))
            if os.path.basename(d) != head]
    if prev:
        prev_dir = max(prev, key=lambda d: os.path.getmtime(os.path.join(d, "SNAPSHOT.json"))
                       if os.path.exists(os.path.join(d, "SNAPSHOT.json")) else 0)
        rc, out = sh(f"python3 Validation/tools/compare_drops.py --a {prev_dir} "
                     f"--b {REPORTS} --json Validation/reports/drop_comparison.json",
                     log, check=False)
        for l in out.splitlines():
            if l.strip().startswith(("REG", "FIX", "STIM", "CHG")) or "regression=" in l \
                    or l.strip().startswith(("same=", "changed=", "fixed=")):
                print("    " + l.strip())
        print(f"    vs {os.path.basename(prev_dir)}: "
              + (out.strip().splitlines()[-2].strip() if out.strip() else ""))
    else:
        print("    no previous snapshot; this drop becomes the reference")

    # 8. snapshot --------------------------------------------------------------
    banner(8, "snapshot")
    rc, out = sh("python3 Validation/tools/compare_drops.py --snapshot", log, check=False)
    print("    " + out.strip())

    # 9. cockpit ---------------------------------------------------------------
    banner(9, "cockpit")
    rc, out = sh("python3 Validation/tools/dashboard_gen.py", log, check=False)
    print("    " + out.strip())

    print(f"\n  drop {head}: {n_pass} pass / {n_fail} fail / {n_err} error in "
          f"{(time.time() - t0) / 60:.1f} min; log {os.path.relpath(log, ROOT)}")
    return 0 if n_err == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
