#!/usr/bin/env python3
"""
spec_completeness.py — the intake gate: does this spec SAY enough to build on?
=================================================================================
Every spec gap this project has hit had the same shape: a section is present
but silent on a question that section always has to answer (what does an
unmapped read return; which way does the data mask go; which cycle's status
does a read see). Those are checkable before anything is generated from the
document — which is when they are cheap. Found at the scoreboard they cost a
cluster run, a model regeneration and an argument about whose reading was
right.

This runs first, on arrival of a spec, in three roles:

  gate       exit non-zero when a required answer is missing, so nothing
             downstream (Frontend generation, model generation, simulation)
             proceeds on an incomplete document without a deliberate override
  findings   each gap becomes a machine-readable spec_gap finding with a
             proposed patch — the exact JSON path, the allowed values, and the
             standard's answer where one exists — so the spec owner receives a
             diff to accept rather than a question to research
  checklist  --checklist renders the rules as prose for the spec GENERATOR's
             prompt, so a customised spec arrives complete instead of being
             patched after the fact

Rules live in completeness_rules.json, keyed to section types rather than to
this design, and each cites the incident that produced it. That file is a
ratchet: a gap found the hard way becomes a rule, and no later spec gets past
intake with the same silence.

Usage:
    python3 Validation/spec/spec_completeness.py
    python3 Validation/spec/spec_completeness.py --spec other_spec.json --findings out.json
    python3 Validation/spec/spec_completeness.py --checklist
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DEFAULT_SPEC = os.path.join(HERE, "llmmc_microarchitecturespec_filled.json")
RULES = os.path.join(HERE, "completeness_rules.json")
PATH_DEFS = os.path.join(HERE, "path_definitions.json")


def get(spec, dotted):
    cur = spec
    for part in dotted.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return None, False
        cur = cur[part]
    return cur, True


def taxonomy_ids(node):
    """Every 'id' string anywhere under the taxonomy, whatever its nesting —
    specs group ids by category, by scope, or not at all."""
    if isinstance(node, dict):
        found = [node["id"]] if isinstance(node.get("id"), str) else []
        for v in node.values():
            found += taxonomy_ids(v)
        return found
    if isinstance(node, list):
        return [i for x in node for i in taxonomy_ids(x)]
    return []


def check_rule(rule, spec, pdefs):
    """Returns (status, detail) with status in ok / gap / not_applicable /
    invalid_value."""
    kind = rule["kind"]
    if "when_present" in rule:
        _, present = get(spec, rule["when_present"])
        if not present:
            return "not_applicable", f"{rule['when_present']} absent"

    if kind == "required_field":
        val, present = get(spec, rule["require"])
        if not present:
            return "gap", f"{rule['require']} is not stated"
        if "options" in rule and val not in rule["options"]:
            return "invalid_value", (f"{rule['require']} = {val!r} is not one "
                                     f"of {rule['options']}")
        return "ok", f"{rule['require']} = {val!r}"

    if kind == "taxonomy_family":
        ids = taxonomy_ids(spec.get("failure_taxonomy", {}))
        hits = [i for i in ids if i.startswith(rule["require_prefix"])]
        if not hits:
            return "gap", (f"no failure_taxonomy id starts with "
                           f"{rule['require_prefix']!r}; needed for: "
                           f"{', '.join(rule['minimum'])}")
        return "ok", f"{len(hits)} id(s): {hits}"

    if kind == "taxonomy_names_params":
        # Every timing parameter the spec states must be nameable as a
        # failure: an assertion bounded by it needs an id to report under.
        section, _ = get(spec, rule["params_from"])
        params = [k for k in (section or {})
                  if k.startswith(rule["param_prefix"]) and not k.startswith("$")
                  and k not in rule.get("exclude", [])]
        text = json.dumps(spec.get("failure_taxonomy", {})).lower()
        import re
        missing = [p for p in params
                   if not re.search(r"\b" + re.escape(p.lower()) + r"\b", text)]
        if missing:
            return "gap", (f"failure_taxonomy names no failure for "
                           f"{missing}; every stated timing parameter needs "
                           f"a violation id")
        return "ok", f"all {len(params)} timing parameter(s) named"

    if kind == "path_interfaces":
        section, present = get(spec, rule["require"])
        pairs = set()
        for p in pdefs:
            blocks = p.get("blocks", [])
            for a, b in zip(blocks, blocks[1:]):
                pairs.add((a, b))
        if not present:
            return "gap", (f"spec has no {rule['require']!r} section; "
                           f"{len(pairs)} block-to-block hops are declared by "
                           f"path_definitions and none has an interface "
                           f"contract")
        missing = [f"{a}->{b}" for a, b in sorted(pairs)
                   if not any(c.get("from") == a and c.get("to") == b
                              for c in section)]
        if missing:
            return "gap", f"hops without a contract: {missing}"
        return "ok", f"all {len(pairs)} hops have contracts"

    return "invalid_value", f"unknown rule kind {kind!r}"


def proposed_patch(rule, spec):
    """The smallest change that closes the gap, as a JSON fragment."""
    if rule["kind"] == "required_field":
        std = rule.get("standard")
        value = std["value"] if std else f"<one of {rule.get('options', [])}>"
        path = rule["require"].split(".")
        frag = value
        for part in reversed(path):
            frag = {part: frag}
        return frag
    if rule["kind"] == "taxonomy_family":
        return {"failure_taxonomy": {"scheduling": [
            {"id": f"{rule['require_prefix']}{i + 1:03d}", "description": d}
            for i, d in enumerate(rule["minimum"])]}}
    if rule["kind"] == "taxonomy_names_params":
        return {"failure_taxonomy": {"categories": [
            {"id": "<FAMILY>_<nnn>", "name": "<param> violation",
             "description": "<what issuing outside <param> looks like>"}]}}
    if rule["kind"] == "path_interfaces":
        return {"block_interfaces": [
            {"from": "<block>", "to": "<block>",
             "signals": [{"name": "<port>", "width": 0, "direction": "from->to"}],
             "handshake": "<valid/ready | pulse | level>"}]}
    return {}


def findings_for(gaps, spec):
    rev = spec.get("revision")
    out = []
    for rule, status, detail in gaps:
        std = rule.get("standard")
        out.append({
            "source": "validation", "target": "spec", "kind": "spec_gap",
            "scope": rule.get("require", rule["id"]).split(".")[0],
            "severity": "major" if rule["disposition"] != "vocabulary" else "minor",
            "spec_revision": rev,
            "title": f"[intake] {rule['question']}",
            "detail": (f"{detail}. {rule['consequence']} "
                       + (f"The applicable standard ({std['name']}) answers "
                          f"this: {std['value']} — {std.get('note', '')} "
                          f"Validation adopts that value and keeps checking; "
                          f"please state it in the spec. " if std else
                          f"Disposition: {rule['disposition']} — comparisons "
                          f"that depend on this are UNDETERMINED until the "
                          f"spec states it. ")
                       + f"First encountered as: {rule['discovered_by']}."),
            "evidence": {"rule": rule["id"], "status": status,
                         "proposed_patch": proposed_patch(rule, spec),
                         "options": rule.get("options")},
            "status": "open",
        })
    return out


def checklist(rules):
    lines = ["# Specification completeness checklist",
             "",
             "A generated specification must answer every applicable question "
             "below explicitly. Silence is a defect: downstream validation "
             "cannot distinguish a design that does the wrong thing from a "
             "specification that never said what the right thing was.",
             ""]
    for r in rules:
        cond = f" (when `{r['when_present']}` is present)" if "when_present" in r else ""
        lines.append(f"## {r['id']}{cond}")
        lines.append(f"**Question.** {r['question']}")
        if r["kind"] == "required_field":
            lines.append(f"**State it at** `{r['require']}`"
                         + (f", one of {r['options']}." if "options" in r else "."))
        elif r["kind"] == "taxonomy_family":
            lines.append(f"**State it as** failure_taxonomy ids prefixed "
                         f"`{r['require_prefix']}` covering: {', '.join(r['minimum'])}.")
        elif r["kind"] == "taxonomy_names_params":
            lines.append(f"**State it as** one failure_taxonomy id per "
                         f"`{r['params_from']}` parameter, naming the parameter.")
        elif r["kind"] == "path_interfaces":
            lines.append(f"**State it as** a `{r['require']}` section with one "
                         f"contract per connected block pair (signals, widths, "
                         f"directions, handshake).")
        if r.get("standard"):
            s = r["standard"]
            lines.append(f"**Standard default.** {s['name']}: `{s['value']}` — {s.get('note', '')}")
        lines.append(f"**Why it matters.** {r['consequence']}")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", default=DEFAULT_SPEC)
    ap.add_argument("--rules", default=RULES)
    ap.add_argument("--path-defs", default=PATH_DEFS)
    ap.add_argument("--findings", help="write spec_gap findings JSON here")
    ap.add_argument("--checklist", action="store_true",
                    help="print the rules as a checklist for the spec generator")
    args = ap.parse_args()

    with open(args.rules) as f:
        rules = json.load(f)["rules"]
    if args.checklist:
        print(checklist(rules))
        return 0

    with open(args.spec) as f:
        spec = json.load(f)
    pdefs = []
    if os.path.exists(args.path_defs):
        with open(args.path_defs) as f:
            pdefs = json.load(f)["paths"]

    print(f"  spec {spec.get('revision', '?')} — {len(rules)} completeness rule(s)\n")
    gaps = []
    for r in rules:
        status, detail = check_rule(r, spec, pdefs)
        mark = {"ok": "ok  ", "gap": "GAP ", "invalid_value": "BAD ",
                "not_applicable": "n/a "}[status]
        print(f"  {mark} {r['id']:30} {detail[:90]}")
        if status in ("gap", "invalid_value"):
            gaps.append((r, status, detail))

    print()
    if not gaps:
        print("  complete: every applicable question is answered.")
        return 0

    by = {}
    for r, _, _ in gaps:
        by.setdefault(r["disposition"], []).append(r["id"])
    print(f"  {len(gaps)} gap(s):")
    for d, ids in by.items():
        print(f"    {d:11} {ids}")
    std = [r for r, _, _ in gaps if r.get("standard")]
    if std:
        print("  standard-determined (adopt the standard, request the sentence):")
        for r in std:
            print(f"    {r['id']}: {r['require']} = {r['standard']['value']}  "
                  f"[{r['standard']['name']}]")

    if args.findings:
        with open(args.findings, "w") as f:
            json.dump({"$schema": "validation-findings/1",
                       "spec_revision": spec.get("revision"),
                       "finding_count": len(gaps),
                       "findings": findings_for(gaps, spec)}, f, indent=2)
        print(f"\n  wrote {len(gaps)} finding(s) -> {os.path.relpath(args.findings, ROOT)}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
