#!/usr/bin/env python3
"""
width_conformance.py — do the RTL's port widths match what the spec declares?
==============================================================================
A structural check that needs no simulation, no model and no stimulus: the
spec states how wide things are, the manifests state how wide the design made
them, and the two must agree.

This exists because expanding validation to data_path surfaced one:

    spec  data_path_mapping.ddr_channel_width_bits = 16
          data_path_mapping.pack_mode              = pack_32_to_16
    RTL   ddr_dq_o is 32 bits, assigned straight from the host word

The design presents a 32-bit DDR data bus where the specification calls for a
16-bit channel fed by packing each host word into two beats. No amount of
transaction-level checking would have found that quickly, because a predictor
built from the spec and a design built to a different width cannot even agree
on what a transaction looks like — the mismatch would have surfaced as a
confusing stream of value mismatches instead of one structural fact.

Rules are DATA (width_rules.json): each names a spec path and the ports that
must match it. Adding a design means adding rules, never editing this file.
A rule whose spec path or port is absent reports as `unchecked`, never as a
pass — an absent check is not a satisfied one.

Usage:
    python3 Validation/structural/width_conformance.py
    python3 Validation/structural/width_conformance.py --json findings.json
"""

import argparse
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
RULES_PATH = os.path.join(HERE, "width_rules.json")


def spec_value(spec, path):
    """Resolve a dotted path like 'memory_geometry.row_bits'."""
    cur = spec
    for part in path.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return None
        cur = cur[part]
    return cur


def manifest_ports(block):
    """{port: width} for a block, from its newest manifest."""
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{block}_manifest.json"),
                             recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    if not paths:
        return None
    with open(paths[0]) as f:
        m = json.load(f)
    out = {}
    for group in m["ports"].values():
        for p in group:
            out[p["name"]] = p["width"]
    return out


def check(spec, rules):
    results = []
    for rule in rules["rules"]:
        block = rule["block"]
        ports = manifest_ports(block)
        expected = spec_value(spec, rule["spec_path"])
        if isinstance(expected, (int, float)) and "multiply_by" in rule:
            expected = int(expected) * rule["multiply_by"]

        if ports is None:
            results.append({**rule, "state": "unchecked", "actual": None,
                            "expected": expected,
                            "why": f"no manifest found for block {block!r}"})
            continue
        if expected is None:
            results.append({**rule, "state": "unchecked", "actual": None,
                            "expected": None,
                            "why": f"spec has no {rule['spec_path']!r}"})
            continue

        for port in rule["ports"]:
            if port not in ports:
                results.append({**rule, "port": port, "state": "unchecked",
                                "actual": None, "expected": expected,
                                "why": f"{block} has no port {port!r}"})
                continue
            actual = ports[port]
            if isinstance(actual, str):
                results.append({**rule, "port": port, "state": "unchecked",
                                "actual": actual, "expected": expected,
                                "why": "array-shaped port; width comparison "
                                       "does not apply"})
                continue
            state = "ok" if int(actual) == int(expected) else "mismatch"
            results.append({**rule, "port": port, "state": state,
                            "actual": int(actual), "expected": int(expected)})
    return results


def to_findings(results, spec):
    out = []
    for r in results:
        if r["state"] != "mismatch":
            continue
        out.append({
            "source": "validation", "target": "frontend", "kind": "rtl_bug",
            "scope": r["block"], "severity": r.get("severity", "major"),
            "spec_revision": spec.get("revision"),
            "title": f"{r['block']}.{r['port']} is {r['actual']} bits; the "
                     f"spec declares {r['expected']}",
            "detail": (f"{r['spec_path']} = {r['expected']}, so "
                       f"{r['block']}.{r['port']} must be {r['expected']} bits "
                       f"wide; the design makes it {r['actual']}. "
                       + r.get("requirement", "")),
            "evidence": {"spec_path": r["spec_path"],
                         "spec_value": r["expected"],
                         "port": r["port"], "rtl_width": r["actual"]},
            "status": "open",
        })
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="write findings here")
    args = ap.parse_args()

    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(RULES_PATH) as f:
        rules = json.load(f)

    results = check(spec, rules)
    ok = [r for r in results if r["state"] == "ok"]
    bad = [r for r in results if r["state"] == "mismatch"]
    unk = [r for r in results if r["state"] == "unchecked"]

    print(f"  {len(results)} width rule(s): {len(ok)} ok, {len(bad)} mismatch, "
          f"{len(unk)} unchecked\n")
    for r in bad:
        print(f"  MISMATCH  {r['block']}.{r['port']}")
        print(f"            spec {r['spec_path']} = {r['expected']}, "
              f"RTL width = {r['actual']}")
        if r.get("requirement"):
            print(f"            {r['requirement']}")
    if unk:
        print(f"\n  unchecked ({len(unk)}) — an absent check is not a pass:")
        for r in unk[:8]:
            print(f"    {r['block']}.{r.get('port','?'):16} {r['why']}")
    if not bad:
        print("  every checkable width agrees with the specification.")

    if args.json:
        findings = to_findings(results, spec)
        with open(args.json, "w") as f:
            json.dump({"$schema": "validation-findings/1",
                       "spec_revision": spec.get("revision"),
                       "finding_count": len(findings),
                       "findings": findings}, f, indent=2)
        print(f"\n  wrote {len(findings)} finding(s) -> {args.json}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
