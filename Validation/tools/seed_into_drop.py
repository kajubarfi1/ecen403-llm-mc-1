#!/usr/bin/env python3
"""
seed_into_drop.py — plant one catalogued fault into a run's drop
================================================================
The feedback-loop experiment: a defect whose right fix is known in advance
is planted into the RTL copy of a flow run's drop (never into a generator),
the run is resumed with --revalidate, validation must FAIL on it, the
Frontend's phase agent must fix it, and re-validation must PASS with no
person involved. The fault comes from Validation/faults/fault_catalog.json so
the planted line and the expected detectors are on record.

Usage:
    python3 Validation/tools/seed_into_drop.py --run runs/<run_id> --fault M05
    python3 flow.py --resume runs/<run_id> --revalidate
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "faults"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", required=True)
    ap.add_argument("--fault", required=True, help="fault id or id prefix, e.g. M05")
    args = ap.parse_args()
    import seed_faults as S
    with open(S.CATALOG) as f:
        cat = json.load(f)
    faults = [x for x in cat["faults"] if x["id"].startswith(args.fault)]
    if len(faults) != 1:
        print(f"{args.fault}: {len(faults)} catalogue entries match; name one")
        return 2
    fl = faults[0]
    drop = os.path.join(ROOT, args.run, "drop")
    edits = fl.get("edits") or [{"file": fl["file"], "from": fl["from"], "to": fl["to"]}]
    for e in edits:
        p = os.path.join(drop, e.get("file") or fl["file"])
        with open(p) as f:
            text = f.read()
        src, dst = S.expand_spec_values(e["from"]), S.expand_spec_values(e["to"])
        n = text.count(src)
        if n != e.get("count", 1):
            print(f"{fl['id']}: substitution matches {n} time(s) in {os.path.relpath(p, ROOT)}; expected 1")
            return 1
        with open(p, "w") as f:
            f.write(text.replace(src, dst))
        print(f"planted {fl['id']} in {os.path.relpath(p, ROOT)}")
    rec = {"fault": fl["id"], "block": fl["block"], "description": fl["description"],
           "expect": fl.get("expect"), "paths": fl.get("paths")}
    with open(os.path.join(ROOT, args.run, "SEEDED_FAULT.json"), "w") as f:
        json.dump(rec, f, indent=2)
    print(f"  block {fl['block']}: {fl['description']}")
    print(f"  expected detectors: {fl.get('expect')}")
    print(f"  next: python3 flow.py --resume {args.run} --revalidate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
