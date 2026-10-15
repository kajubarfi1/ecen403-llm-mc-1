#!/usr/bin/env python3
"""
refresh_stress.py — drive the refresh subsystem to its postpone limit
======================================================================
The refresh vplan items (REF_001 starvation, tREFI boundary) had never been
exercised: at the spec's tREFI a random 19-write sequence ends thousands of
cycles before the first refresh is even due, so the antecedent of every
refresh rule was vacuous. This sequence creates the situation deliberately:

  1. over the register bus, shrink the refresh interval to a few tRFC and cut
     the postpone budget, so refreshes come due quickly and starvation is
     reachable within a simulation;
  2. then keep the scheduler busy with a sustained stream of writes long
     enough for several intervals to elapse, so the arbiter has to choose
     between traffic and refresh — postponing until the urgent threshold.

The register, its field bit positions, the interval floor (tRFC) and the
postpone budget are all read from the spec; the field is found by matching
the spec's own parameter names against the register map, so a spec that
names things differently either resolves or fails loudly — nothing is
hardcoded to this design.

Usage:
    python3 Validation/sequences/refresh_stress.py --seed 1 --out seq.json
"""

import argparse
import json
import math
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

from register_walk import SPEC, SCHEMAS, CATALOG, register_iface, to_int  # noqa: E402

TREFI_MULT_OF_TRFC = 4        # stressed interval: a few refresh cycles long
# The budget stays the spec's: refresh_ctrl drops a tick that arrives while
# saturated at the programmed budget and raises ref_starve_flag, so a budget
# of 2 with a tREFI of a few tRFC starves by configuration whatever the
# scheduler does (52 starve events on the clean drop, 2026-10-15). With the
# spec budget, starvation needs the scheduler to lag max_postpone_count
# ticks, which is the defect this path exists to catch.
STRESS_POSTPONE = 8


def field_bits(f):
    b = str(f.get("bits", f.get("bit_range")))
    hi, _, lo = b.partition(":")
    hi = int(hi)
    lo = int(lo) if lo else hi
    return hi, lo


def find_field(spec, *needles):
    """(register, field) whose names contain every needle (case-insensitive).
    The needles are spec parameter names, so the match is spec-to-spec."""
    hits = []
    for reg in spec["csr_register_map"]["registers"]:
        for f in reg.get("fields", []):
            name = f["name"].lower()
            if all(n.lower() in name for n in needles):
                hits.append((reg, f))
    if len(hits) != 1:
        raise SystemExit(f"register map has {len(hits)} field(s) matching "
                         f"{needles}; need exactly one to program it")
    return hits[0]


def word_with(reg, field, value):
    """The register's reset word with one field replaced."""
    word = to_int(reg.get("reset_value", 0))
    hi, lo = field_bits(field)
    mask = ((1 << (hi - lo + 1)) - 1) << lo
    if value << lo & ~mask:
        raise SystemExit(f"{reg['name']}.{field['name']}: {value} does not "
                         f"fit bits {hi}:{lo}")
    return (word & ~mask) | (value << lo)


def generate(spec, schemas, catalog, seed=1, drives=600, csr_block="config_regs",
             host_block="wb_port"):
    rng = random.Random(seed)
    csr = register_iface(catalog, schemas, csr_block)
    host = next(i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == host_block
                and "write" in schemas[i]["kinds"])
    wk = schemas[host]["kinds"]["write"]

    tm = spec["timing_model"]
    tck = float(tm["tCK_ns"])
    trfc_nck = math.ceil(float(tm["tRFC"]) / tck)
    trefi_nck = math.ceil(float(tm["tREFI"]) / tck)
    budget = spec["controller_architecture"]["refresh_policy"]["max_postpone_count"]

    # The spec may declare that the design's timing counters tick in
    # controller cycles while loading nCK values (counter_clock.window_scale):
    # then the ENFORCED tRFC is window_scale x tRFC_nCK, and a tREFI shorter
    # than that lets the scheduler issue at most one REFRESH per tick, so the
    # postponed count can never drain and ticks are dropped by configuration
    # (42 starve events on the clean drop, 2026-10-15). Stress against the
    # enforced window, not the nominal one.
    window_scale = int((tm.get("counter_clock") or spec.get("counter_clock") or {}).get("window_scale", 1))
    stress_trefi = TREFI_MULT_OF_TRFC * window_scale * trfc_nck
    stress_postpone = min(STRESS_POSTPONE, budget)

    r_refi, f_refi = find_field(spec, "tREFI")
    r_post, f_post = find_field(spec, "max_postpone")
    # The urgency threshold must not exceed the budget it escalates within:
    # the reset value (spec 6) left beside a budget of 2 means urgency can
    # never assert, the scheduler never preempts, and the controller starves
    # by configuration rather than by any scheduling fault (REF_001 on the
    # clean drop, 2026-10-15). Urgent when the budget is reached; starvation
    # then needs a further tick the scheduler failed to serve.
    r_urg, f_urg = find_field(spec, "urgent_threshold")
    assert r_urg["name"] == r_post["name"], "max_postpone and urgent_threshold share a register"
    spec_urgent = int(spec["controller_architecture"]["refresh_policy"].get("urgent_threshold", stress_postpone))
    config_word = word_with(r_post, f_post, stress_postpone)
    hi, lo = field_bits(f_urg)
    config_word = (config_word & ~(((1 << (hi - lo + 1)) - 1) << lo)) | (min(spec_urgent, stress_postpone) << lo)

    steps = [{"op": "reset"}]

    def drive(iface, kind, **fields):
        steps.append({"op": "drive", "iface": iface, "kind": kind,
                      "fields": fields})

    drive(csr, "write", addr=to_int(r_refi["offset"]),
          data=word_with(r_refi, f_refi, stress_trefi))
    drive(csr, "write", addr=to_int(r_post["offset"]), data=config_word)
    steps.append({"op": "idle", "cycles": 4})

    for _ in range(drives):
        vals = {}
        for fname, info in wk.items():
            w = info["width"]
            if fname == "sel":
                vals[fname] = (1 << w) - 1
            else:
                vals[fname] = rng.randrange(0, 1 << w)
        drive(host, "write", **vals)
        if rng.random() < 0.25:
            steps.append({"op": "idle", "cycles": rng.randint(1, 3)})

    return {
        "name": f"refresh_stress_seed{seed}",
        "targets": ["VP_FAIL_012", "VP_TIME_006"],
        "rationale": (f"Programs {r_refi['name']}.{f_refi['name']} = "
                      f"{stress_trefi} nCK ({TREFI_MULT_OF_TRFC} x tRFC; spec "
                      f"tREFI = {trefi_nck} nCK) and {r_post['name']}."
                      f"{f_post['name']} = {stress_postpone} (spec budget "
                      f"{budget}), then {drives} back-to-back host writes so "
                      f"refresh must contend with traffic through several "
                      f"intervals: the REF_001 starvation antecedent and the "
                      f"postponed-refresh bins of cp_trefi_spacing."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "refresh_stress.py",
                        "seed": seed, "spec_revision": spec.get("revision"),
                        "reads_coverage": False},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--drives", type=int, default=600)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]

    seq = generate(spec, schemas, catalog, args.seed, args.drives)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    n = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {len(seq['steps'])} steps, {n} drives "
          f"-> {os.path.relpath(args.out, ROOT)}")
    print(f"    {seq['rationale']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
