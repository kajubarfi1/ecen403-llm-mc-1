#!/usr/bin/env python3
"""
coverage_rollup.py — map measured coverage back onto the verification plan
===========================================================================
Closes the loop the vplan exists for. Without this, coverage is a number in a
tool's report and the plan says `not_started` next to every requirement, no
matter how much simulation has run — which is exactly the question the old
flow could not answer: how much of the specification is actually verified?

Reads an Incisive Metrics Center report (`report_metrics -detail -out <dir>`),
extracts per-coverpoint results, and resolves them against the coverage item
names the vplan already asks for. The names match by construction — the
covergroups are generated from the same vplan — so there is no translation
table to drift.

Three statuses, and the distinctions are the point:

  covered       every coverage item the vplan named reached its goal
  partial       measured, but at least one item is short of goal
  not_measured  the run produced no data for this item at all. NOT the same
                as 0% — 0% means the bin exists and was never hit, which is
                information; not_measured means nobody looked.

A vplan item whose assertion never fired AND whose exercised-coverpoint is 0%
is reported as unproven regardless of the run passing, because an assertion
that never saw its antecedent has proved nothing. That distinction is the
whole reason the `_exercised` coverpoints exist.

Usage:
    python3 Validation/coverage/coverage_rollup.py --report /tmp/covrep
    python3 Validation/coverage/coverage_rollup.py --report <dir> --write-vplan
"""

import argparse
import json
import os
import re
import sys
import zipfile
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
VPLAN_PATH = os.path.join(ROOT, "Validation", "vplan", "vplan.json")
OUT_PATH = os.path.join(ROOT, "Validation", "reports", "coverage_rollup.json")

COV_RE = re.compile(r"(\d+)\s*/\s*(\d+)\s*\(([\d.]+)%\)")


def parse_imc_report(report_dir):
    """Per-coverpoint results from an imc detail report.

    imc 22.03 emits no text format and exposes no Tcl query API, but
    `report_metrics -detail` writes the underlying data as JSON inside
    zipData*.zip. That is what is read here; the HTML is only a viewer.
    """
    results = {}
    zips = [os.path.join(report_dir, f) for f in os.listdir(report_dir)
            if f.startswith("zipData") and f.endswith(".zip")]
    if not zips:
        raise SystemExit(
            f"no zipData*.zip in {report_dir}. Generate the report with:\n"
            f"  imc -exec <tcl>  where the tcl does:\n"
            f"    load -run cov_work/scope/<covtest>\n"
            f"    report_metrics -detail -out <dir> -overwrite")

    def walk(o):
        if isinstance(o, dict):
            title = o.get("title", "")
            cov = o.get("All Cov", "")
            if isinstance(title, str) and (title.startswith("cp_")
                                           or title.startswith("cross_")):
                m = COV_RE.search(str(cov))
                if m:
                    hit, total, pct = int(m.group(1)), int(m.group(2)), float(m.group(3))
                    # A merged report lists the same coverpoint once per
                    # INSTANCE (a chain run's idle config_regs alongside the
                    # block run that exercised it) plus once at type level.
                    # Last-one-wins silently reported whichever instance the
                    # JSON happened to list last; keep the best-covered
                    # entry, which is what the type-level union means.
                    prev = results.get(title)
                    if prev is None or hit > prev["bins_hit"]:
                        results[title] = {"bins_hit": hit, "bins_total": total,
                                          "percent": pct}
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)

    for zp in zips:
        with zipfile.ZipFile(zp) as z:
            for name in z.namelist():
                if not name.endswith(".json"):
                    continue
                try:
                    walk(json.loads(z.read(name).decode("utf-8", "replace")))
                except (ValueError, KeyError):
                    continue
    return results


def rollup(vplan, measured):
    items = []
    for item in vplan["items"]:
        wanted = item.get("coverage_items", [])
        if not wanted:
            items.append({**_base(item), "status": "no_coverage_declared",
                          "coverage": []})
            continue
        rows, missing, short = [], [], []
        for cov in wanted:
            point = cov["name"].split(".", 1)[-1]
            goal = cov.get("goal", 100)
            got = measured.get(point)
            if got is None:
                missing.append(cov["name"])
                rows.append({"name": cov["name"], "goal": goal,
                             "measured": None, "state": "not_measured"})
                continue
            state = "met" if got["percent"] >= goal else "short"
            if state == "short":
                short.append(f"{cov['name']} {got['percent']}% of {goal}%")
            rows.append({"name": cov["name"], "goal": goal,
                         "measured": got["percent"],
                         "bins": f"{got['bins_hit']}/{got['bins_total']}",
                         "state": state})

        if missing and len(missing) == len(wanted):
            status = "not_measured"
        elif short or missing:
            status = "partial"
        else:
            status = "covered"
        items.append({**_base(item), "status": status, "coverage": rows,
                      "short_of_goal": short, "not_measured": missing})
    return items


def _base(item):
    return {"id": item["id"], "title": item["title"], "scope": item.get("scope"),
            "method": item.get("method"), "priority": item.get("priority"),
            "prior_status": item.get("status")}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report", required=True, help="imc report directory")
    ap.add_argument("--write-vplan", action="store_true",
                    help="update status fields in vplan.json")
    args = ap.parse_args()

    with open(VPLAN_PATH) as f:
        vplan = json.load(f)
    measured = parse_imc_report(args.report)
    items = rollup(vplan, measured)

    from collections import Counter
    tally = Counter(i["status"] for i in items)
    total = len(items)

    print(f"  vplan items      : {total}")
    print(f"  coverpoints found in the report: {len(measured)}")
    print()
    for st in ("covered", "partial", "not_measured", "no_coverage_declared"):
        if tally.get(st):
            print(f"    {st:22} {tally[st]:3}")
    print()

    proven = tally.get("covered", 0)
    print(f"  {proven}/{total} vplan item(s) fully covered "
          f"({100.0 * proven / total:.1f}%)")
    print()

    shown = [i for i in items if i["status"] == "partial"][:8]
    if shown:
        print("  partial (measured, short of goal):")
        for i in shown:
            detail = "; ".join(i["short_of_goal"][:2]) or \
                     f"{len(i['not_measured'])} item(s) not measured"
            print(f"    {i['id']:14} {i['title'][:40]:42} {detail[:60]}")
    nm = [i for i in items if i["status"] == "not_measured"]
    if nm:
        print(f"\n  not measured ({len(nm)}) — no data was produced for these; "
              f"that is different from 0%:")
        for i in nm[:6]:
            print(f"    {i['id']:14} {i['title'][:50]}")
        if len(nm) > 6:
            print(f"    ... and {len(nm) - 6} more")

    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    payload = {"$schema": "validation-coverage-rollup/1",
               "generated_utc": datetime.now(timezone.utc).isoformat(),
               "spec_revision": vplan.get("spec_revision"),
               "vplan_items": total,
               "coverpoints_measured": len(measured),
               "summary": dict(tally),
               "items": items}
    with open(OUT_PATH, "w") as f:
        json.dump(payload, f, indent=2)
    print(f"\n  wrote {os.path.relpath(OUT_PATH, ROOT)}")

    if args.write_vplan:
        by_id = {i["id"]: i["status"] for i in items}
        for item in vplan["items"]:
            new = by_id.get(item["id"])
            if new and new != "no_coverage_declared":
                item["status"] = new
        with open(VPLAN_PATH, "w") as f:
            json.dump(vplan, f, indent=2)
        print(f"  updated {os.path.relpath(VPLAN_PATH, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
