#!/usr/bin/env python3
"""
retry_adapter.py — findings v2 in the shape the Frontend already reads
======================================================================
The Frontend's phase pipelines re-prompt a generator with

    retry_instructions[module] = {"module": m, "attempt": n,
                                  "failed_checks": [{id, name, pass, expected, actual}],
                                  "message": "..."}

and Frontend2's feedback agent wants the same plus an anchor. This writes
one retry_instructions.json per drop from findings_v2.json: one entry per
owner module, one failed check per finding, with `anchor`, `repro`,
`confidence` and `spec_ref` as extra keys the current pipelines ignore and
the feedback agent uses. `requires_human_review` mirrors the Frontend's own
flag: true when any finding routes to a human (spec gaps, waivers).

Usage:
    python3 Validation/findings/retry_adapter.py                # latest drop
    python3 Validation/findings/retry_adapter.py --findings <findings_v2.json>
"""

import argparse
import json
import os
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUTBOX = os.path.join(HERE, "outbox")


def latest_findings():
    for rev in sorted(os.listdir(OUTBOX)):
        lp = os.path.join(OUTBOX, rev, "latest")
        if os.path.exists(lp):
            with open(lp) as f:
                head = f.read().strip()
            p = os.path.join(OUTBOX, rev, head, "findings_v2.json")
            if os.path.exists(p):
                return p
    return None


def adapt(doc):
    modules = {}
    human = False
    for f in doc["findings"]:
        if f.get("status") not in (None, "open"):
            continue
        if f["kind"] in ("spec_gap",):
            human = True
        m = modules.setdefault(f["owner_module"], {
            "module": f["owner_module"], "attempt": None,
            "drop": doc["drop"], "failed_checks": [], "message": ""})
        m["failed_checks"].append({
            "id": f["check_id"],
            "name": (f.get("requirement") or f["title"])[:160],
            "pass": False,
            "expected": f["expected"],
            "actual": f["actual"],
            "severity": f["severity"],
            "confidence": f["confidence"],
            "spec_ref": f.get("spec_ref"),
            "anchor": f.get("anchor", [])[:3],
            "owner_candidates": f.get("owner_candidates", []),
            "occurrences": f["occurrences"],
            "paths": f["paths"],
            "repro": f["repro"],
            "introduced_in": f.get("introduced_in"),
            "finding_id": f["id"],
        })
    for m in modules.values():
        n = len(m["failed_checks"])
        conf = sum(1 for c in m["failed_checks"] if c["confidence"] == "confirmed")
        m["message"] = (f"{n} check(s) failed on drop {doc['drop']}; {conf} with "
                        f"model-free evidence. Fix the highest-severity check "
                        f"first; each carries the spec requirement, expected vs "
                        f"actual, source anchors and a reproduction command.")
    return {
        "$schema": "validation-retry-instructions/1",
        "status": "FAIL" if modules else "PASS",
        "pipeline": "validation",
        "drop": doc["drop"],
        "spec_revision": doc.get("spec_revision"),
        "generated_utc": datetime.utcnow().isoformat() + "Z",
        "failed_modules": sorted(modules),
        "retry_instructions": modules,
        "resolved_since_previous_drop": doc.get("resolved", []),
        "requires_human_review": human,
        "source": "Validation/findings/emit_findings.py -> retry_adapter.py",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--findings", default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    fp = args.findings or latest_findings()
    if not fp:
        print("no findings_v2.json found; run emit_findings.py first")
        return 2
    with open(fp) as f:
        doc = json.load(f)
    ri = adapt(doc)
    out = args.out or os.path.join(os.path.dirname(fp), "retry_instructions.json")
    with open(out, "w") as f:
        json.dump(ri, f, indent=2)
    print(f"  {ri['status']}: {len(ri['failed_modules'])} module(s) with failed checks: "
          f"{', '.join(ri['failed_modules'])}")
    for m, v in ri["retry_instructions"].items():
        print(f"    {m:13} {len(v['failed_checks'])} check(s): "
              + ", ".join(c["id"] for c in v["failed_checks"])[:110])
    print(f"  wrote {os.path.relpath(out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
