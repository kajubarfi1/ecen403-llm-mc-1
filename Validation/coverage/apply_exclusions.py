#!/usr/bin/env python3
"""
apply_exclusions.py — adjusted code coverage under the signoff's exclusion rules
=================================================================================
Reads coverage/exclusions.json (SIGNOFF §4: instance, signal bits, one of the
four codes, a reason, an approver) and the per-instance uncovered-items
reports that `measure_coverage.py --uncovered` wrote, matches each exclusion
against the uncovered toggle bits, and writes reports/coverage_exclusions.json:
per instance, how many uncovered items the approved exclusions remove and the
adjusted coverage (covered / (total - excluded)) beside the measured one.

Proposed exclusions (no approver yet) are matched and reported separately
and change no number: an exclusion counts only once a named person approved
it. Nothing here changes what the simulator measured.

Usage:
    python3 Validation/coverage/apply_exclusions.py
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
EXCL = os.path.join(HERE, "exclusions.json")
REPORTS = os.path.join(ROOT, "Validation", "reports")
CODES = {"E-RESET", "E-SPEC", "E-DEAD", "E-TOOL"}


def uncovered_toggle_bits(inst):
    """[(signal, [indices])] from the instance's uncovered report, toggle section."""
    p = os.path.join(REPORTS, f"coverage_uncovered_{inst}.txt")
    if not os.path.exists(p):
        return None
    txt = open(p, errors="replace").read()
    if "Uncovered Toggle Detail Report" not in txt:
        return []
    body = txt.split("Uncovered Toggle Detail Report", 1)[1]
    rows = []
    for ln in body.splitlines():
        m = re.match(r"\s*\d+\s+\d+\s+\d+\s+([A-Za-z_]\w*)((?:\[\d+\])*)\s*$", ln)
        if m:
            rows.append((m.group(1), [int(x) for x in re.findall(r"\[(\d+)\]", m.group(2))]))
    return rows


def matches(excl, inst, sig, idx):
    if excl["instance"] not in ("*", inst):
        return False
    if sig not in excl["signals"]:
        return False
    bits = excl.get("bits", "all")
    if bits == "all" or not idx:
        return True
    return idx[-1] in bits


def main() -> int:
    with open(EXCL) as f:
        doc = json.load(f)
    bad = [e["id"] for e in doc["exclusions"] if e.get("code") not in CODES or not e.get("reason")]
    if bad:
        print(f"exclusions without a valid code or a reason: {bad}")
        return 1
    code_cov = {}
    cc = os.path.join(REPORTS, "coverage_code.json")
    if os.path.exists(cc):
        code_cov = json.load(open(cc)).get("per_module", {})
    insts = sorted({e["instance"] for e in doc["exclusions"] if e["instance"] != "*"}
                   | {f"u_{m}" for m in code_cov})
    out = {"$schema": "validation-coverage-exclusions-report/1", "instances": {}, "exclusions": []}
    counts = {e["id"]: {"approved": 0, "proposed": 0} for e in doc["exclusions"]}
    for inst in insts:
        rows = uncovered_toggle_bits(inst)
        if rows is None:
            continue
        approved = proposed = 0
        for sig, idx in rows:
            for e in doc["exclusions"]:
                if matches(e, inst, sig, idx):
                    if e.get("approved_by"):
                        approved += 1
                        counts[e["id"]]["approved"] += 1
                    else:
                        proposed += 1
                        counts[e["id"]]["proposed"] += 1
                    break
        mod = inst[2:] if inst.startswith("u_") else inst
        m = code_cov.get(mod, {})
        cov, tot = m.get("covered"), m.get("total")
        entry = {"uncovered_toggle_bits": len(rows), "excluded_approved": approved,
                 "excluded_proposed": proposed}
        if cov is not None and tot:
            entry["measured_percent"] = round(100.0 * cov / tot, 1)
            entry["adjusted_percent"] = round(100.0 * cov / max(tot - approved, 1), 1)
            entry["adjusted_if_proposed_approved_percent"] = round(100.0 * cov / max(tot - approved - proposed, 1), 1)
        out["instances"][inst] = entry
    for e in doc["exclusions"]:
        out["exclusions"].append({"id": e["id"], "code": e["code"], "status": "approved" if e.get("approved_by") else "proposed",
                                  "approved_by": e.get("approved_by"), "matched_bits": counts[e["id"]]})
    with open(os.path.join(REPORTS, "coverage_exclusions.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"  {'instance':14} {'uncov':>6} {'appr':>5} {'prop':>5} {'measured':>9} {'adjusted':>9} {'if approved':>12}")
    for inst, e in out["instances"].items():
        print(f"  {inst:14} {e['uncovered_toggle_bits']:6} {e['excluded_approved']:5} {e['excluded_proposed']:5} "
              f"{str(e.get('measured_percent', '')):>9} {str(e.get('adjusted_percent', '')):>9} "
              f"{str(e.get('adjusted_if_proposed_approved_percent', '')):>12}")
    for x in out["exclusions"]:
        print(f"  {x['id']} {x['code']:8} {x['status']:9} matched {x['matched_bits']}")
    print(f"  wrote {os.path.relpath(os.path.join(REPORTS, 'coverage_exclusions.json'), ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
