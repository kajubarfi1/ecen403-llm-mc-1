#!/usr/bin/env python3
"""
vplan_gen.py — derive the verification plan from the microarchitecture spec
===========================================================================
The vplan is generated DETERMINISTICALLY from llmmc_microarchitecturespec_filled.json.
No LLM is involved: every item here is traceable to a spec field, so the plan cannot
drift from the spec and cannot invent requirements.

Three derivation sources:
  1. failure_taxonomy   -> one assertion item per failure category (20 items)
  2. csr_register_map   -> access-semantics items per field access class (46 fields)
  3. timing_model       -> timing coverage items bound to the TIMING_* assertions

An LLM pass may later ADD scenario items (corner cases a human would think of), but it
may never modify or delete a generated item. Generated items carry "derived": true.

Usage:
    python3 vplan/vplan_gen.py --spec spec/llmmc_microarchitecturespec_filled.json \
                               --out  vplan/vplan.json
"""

import argparse
import json
import os
from collections import OrderedDict


def _cov(kind, name, goal=100):
    return {"type": kind, "name": name, "goal": goal}


def derive_failure_items(spec):
    """One assertion item per failure_taxonomy category.

    These are the 20 documented ways this controller can fail. Each becomes an SVA
    property whose name encodes the failure ID, so a firing assertion names its own
    taxonomy entry in the log.
    """
    items = []
    for i, cat in enumerate(spec["failure_taxonomy"]["categories"], start=1):
        fid = cat["id"]
        scope = cat["scope"]
        items.append(OrderedDict([
            ("id", f"VP_FAIL_{i:03d}"),
            ("title", cat["name"]),
            ("scope", scope),
            ("requirement",
             f"The design shall never exhibit: {cat['description']}"),
            ("spec_ref", f"failure_taxonomy.categories[{fid}]"),
            ("failure_ref", fid),
            ("method", "assertion"),
            ("coverage_items", [
                # Did the assertion ever get a chance to fire? An assertion that is
                # never exercised is not evidence of correctness.
                _cov("functional", f"cg_{scope}.cp_{fid.lower()}_exercised"),
            ]),
            ("priority", cat["severity"]),
            ("status", "not_started"),
            ("derived", True),
            ("tests", []),
        ]))
    return items


def derive_csr_items(spec):
    """Access-semantics items for the CSR block, grouped by access class.

    Grouping by access class rather than emitting 46 near-identical items keeps the
    plan readable: the interesting requirement is "RW1C clears on write-1", not
    "field foo is RW1C". Per-field granularity lives in the coverage model instead.
    """
    csr = spec["csr_register_map"]
    by_access = OrderedDict()
    for reg in csr["registers"]:
        for f in reg.get("fields", []):
            by_access.setdefault(f["access"], []).append((reg, f))

    semantics = {
        "RO":   "shall ignore bus writes entirely and read back only hardware-driven state",
        "RW":   "shall store a written value and read it back unchanged",
        "RW1C": "shall clear a bit when 1 is written to it, and leave it unchanged when 0 is written",
        "WO":   "shall accept the write side-effect and thereafter always read back 0",
    }

    items = []
    for i, (access, pairs) in enumerate(sorted(by_access.items()), start=1):
        coverage = [
            _cov("functional", f"cg_csr_access.cp_{access.lower()}_fields"),
            _cov("functional", f"cg_csr_access.cross_{access.lower()}_x_wdata_pattern"),
        ]
        nregs = len({r["name"] for r, _ in pairs})
        items.append(OrderedDict([
            ("id", f"VP_CSR_{i:03d}"),
            ("title", f"{access} field access semantics"),
            ("scope", "config_regs"),
            ("requirement",
             f"Every {access} field {semantics.get(access, 'shall behave per spec')}. "
             f"Applies to {len(pairs)} field{'s' if len(pairs) != 1 else ''} across "
             f"{nregs} register{'s' if nregs != 1 else ''}."),
            ("spec_ref", f"csr_register_map.registers[*].fields[access={access}]"),
            ("failure_ref", "CSR_001"),
            ("method", "random"),
            ("coverage_items", coverage),
            ("priority", "major"),
            ("status", "not_started"),
            ("derived", True),
            ("fields", [f"{r['name']}.{f['name']}" for r, f in pairs]),
            ("tests", []),
        ]))

    # Reset values are a distinct requirement from access semantics.
    n = len(items) + 1
    all_fields = [(r, f) for r in csr["registers"] for f in r.get("fields", [])]
    items.append(OrderedDict([
        ("id", f"VP_CSR_{n:03d}"),
        ("title", "Reset values"),
        ("scope", "config_regs"),
        ("requirement",
         f"After reset deassertion, all {len(all_fields)} fields shall read back the "
         f"reset_value defined in the spec."),
        ("spec_ref", "csr_register_map.registers[*].fields[*].reset_value"),
        ("failure_ref", None),
        ("method", "directed"),
        ("coverage_items", [_cov("functional", "cg_csr_access.cp_reset_checked")]),
        ("priority", "critical"),
        ("status", "not_started"),
        ("derived", True),
        ("tests", []),
    ]))

    # Unmapped address behavior — flagged, because the current refmodel prompt asserts
    # 0xDEADBEEF as RTL behavior while the spec does not define it. See audit V-06.
    n += 1
    items.append(OrderedDict([
        ("id", f"VP_CSR_{n:03d}"),
        ("title", "Unmapped address response"),
        ("scope", "config_regs"),
        ("requirement",
         "Reads and writes to addresses outside the register map shall behave as the "
         "spec defines."),
        ("spec_ref", "csr_register_map (UNDEFINED — see open_question)"),
        ("failure_ref", "CSR_001"),
        ("method", "directed"),
        ("coverage_items", [_cov("functional", "cg_csr_access.cp_unmapped_addr")]),
        ("priority", "major"),
        ("status", "blocked"),
        ("open_question",
         "The spec does not define unmapped-address behavior, but the reference model "
         "prompt hardcodes 0xDEADBEEF as 'what the RTL returns'. Either promote this to "
         "a spec field so both RTL and refmodel derive it, or treat any RTL/refmodel "
         "agreement here as untested. Do not verify against the implementation."),
        ("derived", True),
        ("tests", []),
    ]))
    return items


def derive_timing_items(spec):
    """Timing coverage items bound to the TIMING_* assertions.

    The assertion proves the constraint is never violated; these coverage items prove
    the constraint was actually approached. A tRCD assertion that never sees a
    back-to-back ACT->RD is passing vacuously.
    """
    tm = spec["timing_model"]
    derived = tm.get("$derived_cycles", {})
    items = []
    idx = 1
    for key, cycles in sorted(derived.items()):
        if not key.endswith("_nCK"):
            continue
        param = key[:-4]                    # tRCD_nCK -> tRCD
        fail_id = None
        for cat in spec["failure_taxonomy"]["categories"]:
            if cat["name"].lower().startswith(param.lower() + " "):
                fail_id = cat["id"]
                break
        items.append(OrderedDict([
            ("id", f"VP_TIME_{idx:03d}"),
            ("title", f"{param} boundary exercised"),
            ("scope", "timing"),
            ("requirement",
             f"Stimulus shall drive the {param} constraint to its boundary "
             f"({cycles} cycles at tCK={tm['tCK_ns']}ns), including the exact-minimum "
             f"legal spacing, so the corresponding assertion is non-vacuous."),
            ("spec_ref", f"timing_model.$derived_cycles.{key}"),
            ("failure_ref", fail_id),
            ("method", "random"),
            ("coverage_items", [
                _cov("functional", f"cg_timing.cp_{param.lower()}_spacing"),
            ]),
            ("priority", "critical" if fail_id else "major"),
            ("status", "not_started"),
            ("derived", True),
            ("target_cycles", cycles),
            ("tests", []),
        ]))
        idx += 1
    return items


def build(spec):
    items = (derive_failure_items(spec)
             + derive_csr_items(spec)
             + derive_timing_items(spec))
    return OrderedDict([
        ("$comment", "GENERATED by vplan_gen.py from the microarchitecture spec. "
                     "Items with derived=true must not be hand-edited — change the "
                     "spec and regenerate. Hand-authored scenario items may be added "
                     "with derived=false."),
        ("schema_version", "1.0"),
        ("spec_source", spec.get("design_id", "unknown")),
        ("spec_revision", spec.get("revision", "unknown")),
        ("item_count", len(items)),
        ("items", items),
    ])


def summarize(vplan):
    from collections import Counter
    items = vplan["items"]
    print(f"vplan items: {len(items)}")
    for label, key in (("method", "method"), ("priority", "priority"),
                       ("scope", "scope"), ("status", "status")):
        c = Counter(i[key] for i in items)
        print(f"  by {label:9}", dict(c))
    cov = sum(len(i["coverage_items"]) for i in items)
    print(f"  coverage items: {cov}")
    blocked = [i for i in items if i["status"] == "blocked"]
    if blocked:
        print(f"\n  BLOCKED ({len(blocked)}):")
        for b in blocked:
            print(f"    {b['id']}  {b['title']}")


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(here)
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", default=os.path.join(root, "spec",
                                                   "llmmc_microarchitecturespec_filled.json"))
    ap.add_argument("--out", default=os.path.join(here, "vplan.json"))
    args = ap.parse_args()

    with open(args.spec) as f:
        spec = json.load(f)

    vplan = build(spec)
    with open(args.out, "w") as f:
        json.dump(vplan, f, indent=2)

    summarize(vplan)
    print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
