#!/usr/bin/env python3
"""
compare_drops.py — what changed between two sets of path reports?
==================================================================
Three questions, one tool:

  determinism   the same drop run twice must produce the same verdicts, the
                same violations and the same traces; any difference is a
                bug in the harness or the tools, not in the design
                    compare_drops.py --a reports/paths --b reports/paths_repeat --strict

  regression    a new drop against the previous one: which (path, stage,
                rule) started failing, which stopped
                    compare_drops.py --a reports/drops/<old> --b reports/paths

  history       keep a copy of the current reports under the drop's git
                commit, so the next comparison has something to diff
                    compare_drops.py --snapshot

The unit of comparison is the DETECTOR SIGNATURE of a path run — stage
verdicts, matched counts, violation counts, violation ids, assertion and
illegal-bin hits — the same signature the seeded-fault scorer uses. A
regression is a detector that appears (or grows past tolerance) in B; a fix
is one that disappears. Timestamps, file paths and run tags are ignored:
they differ between any two runs by construction.
"""

import argparse
import glob
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "faults"))
from seed_faults import signature  # noqa: E402

PATHS = os.path.join(ROOT, "Validation", "reports", "paths")
DROPS = os.path.join(ROOT, "Validation", "reports", "drops")


def paths_in(d):
    return sorted(os.path.basename(f)[:-len("_report.json")]
                  for f in glob.glob(os.path.join(d, "*_report.json")))


def drop_head(d):
    for f in glob.glob(os.path.join(d, "*_report.json")):
        with open(f) as fh:
            h = json.load(fh).get("rtl_drop", {}).get("git_head")
        if h:
            return h
    return None


def trace_diff(a_dir, b_dir, path):
    """Line-by-line trace comparison; None when either trace is missing."""
    fa = os.path.join(a_dir, f"{path}_observed.jsonl")
    fb = os.path.join(b_dir, f"{path}_observed.jsonl")
    if not (os.path.exists(fa) and os.path.exists(fb)):
        return None
    with open(fa) as f:
        la = f.read().splitlines()
    with open(fb) as f:
        lb = f.read().splitlines()
    if la == lb:
        return 0
    n = sum(1 for x, y in zip(la, lb) if x != y) + abs(len(la) - len(lb))
    return n


def classify(sa, sb, strict=False):
    """(kind, details). kinds: same | regression | fixed | changed."""
    keys = (set(sa) | set(sb)) - {"_verdict"}
    new, gone, grew, shrank, matched_down, matched_up = {}, {}, {}, {}, {}, {}
    for k in sorted(keys):
        a, b = sa.get(k), sb.get(k)
        if k.startswith("matched:"):
            if a is not None and b is not None and a != b:
                (matched_down if b < a else matched_up)[k] = (a, b)
            continue
        if a is None and b is not None:
            new[k] = b
        elif b is None and a is not None:
            gone[k] = a
        elif a != b:
            if strict or b > a * 1.5 + 2:
                grew[k] = (a, b)
            elif a > b * 1.5 + 2 or strict:
                shrank[k] = (a, b)
            elif b > a:
                grew.setdefault("~", None)   # marker: small growth, not a regression
            else:
                shrank.setdefault("~", None)
    grew.pop("~", None)
    shrank.pop("~", None)
    details = {"new": new, "gone": gone, "grew": grew, "shrank": shrank,
               "matched_down": matched_down, "matched_up": matched_up,
               "verdict": (sa.get("_verdict"), sb.get("_verdict"))}
    worse = bool(new or grew or matched_down) or (
        sa.get("_verdict") == "pass" and sb.get("_verdict") != "pass")
    better = bool(gone or shrank or matched_up) or (
        sa.get("_verdict") != "pass" and sb.get("_verdict") == "pass")
    if strict:
        kind = "same" if not (worse or better or
                              sa.get("_verdict") != sb.get("_verdict")) else "changed"
    elif worse and better:
        kind = "changed"
    elif worse:
        kind = "regression"
    elif better:
        kind = "fixed"
    else:
        kind = "same"
    return kind, details


def report(d, path):
    with open(os.path.join(d, f"{path}_report.json")) as f:
        return json.load(f)


def stimulus_steps(rep):
    """The drive steps of the sequence a report ran, or None."""
    seq = rep.get("sequence")
    if not seq:
        return None
    p = seq if os.path.isabs(seq) else os.path.join(ROOT, seq)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return [s for s in json.load(f).get("steps", [])]



def backfilled(d):
    """True when the snapshot in `d` records backfilled logs (SNAPSHOT.json)."""
    try:
        with open(os.path.join(d, "SNAPSHOT.json")) as f:
            return bool(json.load(f).get("backfilled"))
    except (OSError, ValueError):
        return False

def compare(a_dir, b_dir, strict=False):
    rows = []
    for p in sorted(set(paths_in(a_dir)) | set(paths_in(b_dir))):
        sa, sb = signature(a_dir, p), signature(b_dir, p)
        if sa is None or sb is None:
            rows.append({"path": p, "kind": "missing",
                         "side": "a" if sa is None else "b"})
            continue
        ra, rb = report(a_dir, p), report(b_dir, p)
        notes = []
        # Two runs are only comparable as the SAME experiment when they drove
        # the same stimulus and collected the same evidence. Differences in
        # either are reported as such, never as a design change.
        st_a, st_b = stimulus_steps(ra), stimulus_steps(rb)
        if st_a is not None and st_b is not None and st_a != st_b:
            notes.append("stimulus differs (the sequence generator or seed "
                         "changed between the runs)")
        # Assertion / illegal-bin / log-marker keys come from the sim log.
        # When only one side archived its log, those keys are evidence of
        # what was kept, not of what the design did: drop them on both sides.
        log_a = os.path.exists(os.path.join(a_dir, f"{p}_sim.log"))
        log_b = os.path.exists(os.path.join(b_dir, f"{p}_sim.log"))
        if log_a != log_b:
            notes.append("sim log archived on one side only; assertion, "
                         "illegal-bin and log-marker keys ignored")
            drop = ("assert:", "illegal:", "log:")
            sa = {k: v for k, v in sa.items() if not k.startswith(drop)}
            sb = {k: v for k, v in sb.items() if not k.startswith(drop)}
        # A backfilled snapshot took its logs from an earlier run of the same
        # drop, possibly under an older coverage model: illegal-bin keys then
        # reflect which bins existed, not what the design did.
        if backfilled(a_dir) != backfilled(b_dir):
            notes.append("one side's sim logs are backfilled from an earlier run "
                         "(coverage model may differ); illegal-bin keys ignored")
            sa = {k: v for k, v in sa.items() if not k.startswith("illegal:")}
            sb = {k: v for k, v in sb.items() if not k.startswith("illegal:")}
        cov_a = ra.get("coverage_collected", True)
        cov_b = rb.get("coverage_collected", True)
        if cov_a != cov_b:
            notes.append("coverage collected on one side only; illegal-bin "
                         "hits ignored")
            sa = {k: v for k, v in sa.items() if not k.startswith("illegal:")}
            sb = {k: v for k, v in sb.items() if not k.startswith("illegal:")}
        kind, det = classify(sa, sb, strict)
        td = trace_diff(a_dir, b_dir, p) if strict else None
        if strict and td:
            kind = "changed"
            det["trace_lines_differ"] = td
        if notes and kind != "same":
            det["notes"] = notes
        if any(n.startswith("stimulus") for n in notes):
            kind = "stimulus"
        rows.append({"path": p, "kind": kind, **det})
    return rows


def snapshot(src, dest_root):
    head = drop_head(src) or subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
        capture_output=True, text=True).stdout.strip() or "unknown"
    dest = os.path.join(dest_root, head)
    os.makedirs(dest, exist_ok=True)
    n = 0
    for f in glob.glob(os.path.join(src, "*_report.json")):
        shutil.copy(f, dest)
        n += 1
    # The evidence the signature reads lives beside the report: the sim log
    # (assertion / illegal-bin counts) and the observed trace (strict diff).
    # A snapshot without them compares asymmetrically against a live run —
    # every assertion looks "new" — so they are archived too.
    for pat in ("*_sim.log", "*_observed.jsonl"):
        for f in glob.glob(os.path.join(src, pat)):
            shutil.copy(f, dest)
    with open(os.path.join(dest, "SNAPSHOT.json"), "w") as f:
        json.dump({"drop_head": head, "taken_utc": datetime.utcnow().isoformat() + "Z",
                   "reports": n, "source": os.path.relpath(src, ROOT)}, f, indent=2)
    return dest, n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", help="older / reference report dir")
    ap.add_argument("--b", default=PATHS, help="newer report dir (default reports/paths)")
    ap.add_argument("--strict", action="store_true",
                    help="determinism mode: any difference, including traces, fails")
    ap.add_argument("--snapshot", action="store_true",
                    help="copy reports/paths into reports/drops/<git_head>/")
    ap.add_argument("--json", help="write the comparison here")
    args = ap.parse_args()

    if args.snapshot:
        dest, n = snapshot(args.b, DROPS)
        print(f"  snapshot: {n} report(s) -> {os.path.relpath(dest, ROOT)}")
        return 0
    if not args.a:
        ap.error("--a is required unless --snapshot")

    a_dir = args.a if os.path.isabs(args.a) else os.path.join(ROOT, args.a)
    b_dir = args.b if os.path.isabs(args.b) else os.path.join(ROOT, args.b)
    rows = compare(a_dir, b_dir, args.strict)
    ha, hb = drop_head(a_dir), drop_head(b_dir)

    print(f"  A: {os.path.relpath(a_dir, ROOT)}  (drop {ha})")
    print(f"  B: {os.path.relpath(b_dir, ROOT)}  (drop {hb})"
          + ("   [strict / determinism]" if args.strict else ""))
    print()
    tally = {}
    for r in rows:
        tally[r["kind"]] = tally.get(r["kind"], 0) + 1
        mark = {"same": "  =  ", "regression": " REG ", "fixed": " FIX ",
                "changed": " CHG ", "missing": " ??  ",
                "stimulus": " STIM"}[r["kind"]]
        va, vb = r.get("verdict", ("?", "?"))
        print(f"  {mark} {r['path']:34} {str(va):9}-> {str(vb):9}")
        if r["kind"] != "same":
            for k, v in list(r.get("new", {}).items())[:4]:
                print(f"           new   {k} x{v}")
            for k, v in list(r.get("gone", {}).items())[:4]:
                print(f"           gone  {k} x{v}")
            for k, (x, y) in list(r.get("grew", {}).items())[:3]:
                print(f"           grew  {k} {x} -> {y}")
            for k, (x, y) in list(r.get("shrank", {}).items())[:3]:
                print(f"           less  {k} {x} -> {y}")
            for k, (x, y) in r.get("matched_down", {}).items():
                print(f"           match {k} {x} -> {y}")
            for k, (x, y) in r.get("matched_up", {}).items():
                print(f"           match {k} {x} -> {y}")
            if r.get("trace_lines_differ"):
                print(f"           trace {r['trace_lines_differ']} line(s) differ")
            for n in r.get("notes", []):
                print(f"           note  {n}")
    print()
    print("  " + "  ".join(f"{k}={v}" for k, v in sorted(tally.items())))
    if args.strict:
        ok = tally.get("same", 0) == len(rows)
        print("  DETERMINISTIC" if ok else "  NOT DETERMINISTIC — investigate before trusting any comparison")
    if args.json:
        with open(args.json, "w") as f:
            json.dump({"$schema": "validation-drop-comparison/1",
                       "a": {"dir": os.path.relpath(a_dir, ROOT), "drop_head": ha},
                       "b": {"dir": os.path.relpath(b_dir, ROOT), "drop_head": hb},
                       "strict": args.strict, "generated_utc":
                       datetime.utcnow().isoformat() + "Z", "rows": rows}, f, indent=2)
        print(f"  wrote {os.path.relpath(args.json, ROOT)}")
    if args.strict:
        return 0 if tally.get("same", 0) == len(rows) else 1
    return 1 if tally.get("regression") else 0


if __name__ == "__main__":
    sys.exit(main())
