#!/usr/bin/env python3
"""
ack_collision.py — land a write beat the cycle before a read's data returns
================================================================================
HOST_001 (formal counterexample, 2026-10-28): the port's write acknowledge
(registered one cycle after the beat) and its read response share one
`wb_ack_o`; when both are due in the same cycle the host sees one ack for
two beats. This sequence reproduces it in simulation so the finding has a
waveform and the fix has a test: one warm-up read opens the row, then for
each gap d in a window around the steady-state read latency, a pipelined
run of {read A, gap d, write B} -- the gap is an idle inside the run (cyc
held, stb low), so the write beat is accepted exactly d+1 cycles after the
read beat; one value of d puts it the cycle before the read data returns.

The latency window comes from the spec (CL in controller cycles plus the
scheduler's pipeline) widened on both sides, not from a measured trace, so
it holds for any spec; a sweep costs a few hundred cycles per gap.

Usage:
    python3 Validation/sequences/ack_collision.py --seed 1 --out seq.json
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

from register_walk import SPEC, SCHEMAS, CATALOG, VPLAN  # noqa: E402


def latency_window(spec):
    """(lo, hi) gaps in controller cycles to sweep: the read latency from
    the spec (CL in nCK over the clock ratio, the scheduler's own pipeline,
    the data path's capture beats; tRCD is zero for the row the warm-up
    left open) with a margin of 9 cycles below and 32 above: the measured
    hit latency on the golden drop is 26 cycles and a miss 41, well past the
    spec arithmetic, because every hop (port, queue, scheduler, command
    generator, capture, response FIFO) adds a register stage."""
    ratio = int(spec.get("clocking_model", {}).get("clock_ratio", 4) or 4)
    cl = int(spec.get("timing_model", {}).get("CL_nCK", 11) or 11)
    lat = spec.get("latency_model", {}) or {}
    pipe = int(lat.get("pipeline_latency", 2) or 2)
    dpm = spec.get("data_path_mapping", {})
    beats = int(dpm.get("host_width_bits", 32)) // int(dpm.get("ddr_channel_width_bits", 16))
    core = -(-cl // ratio) + pipe + beats + 4      # ceil(CL/ratio) + pipeline + capture + queue/port hops
    return max(2, core - 9), core + 32


def generate(spec, schemas, catalog, seed=1, host_block="wb_port"):
    host = next(i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == host_block
                and "write" in schemas[i]["kinds"] and "read" in schemas[i]["kinds"])
    if not catalog[host].get("drive", {}).get("pipelined"):
        raise SystemExit(f"{host}: the catalog drive block is not pipelined; the gap needs a pipelined run")
    kinds = schemas[host]["kinds"]
    word = int(spec["host_interface"].get("data_width_bits", 32)) // 8
    addr_w = kinds["read"]["addr"]["width"]
    a_read = (0x100 * word) & ((1 << addr_w) - 1)                         # one row, read every time
    a_write = ((1 << (addr_w - 2)) + 0x40 * word) & ((1 << addr_w) - 1)  # far away: another bank/row

    def f(kind, addr, data=0):
        vals = {}
        for fname, info in kinds[kind].items():
            w = info["width"]
            if fname == "addr":
                vals[fname] = addr & ~(word - 1)
            elif fname in ("cti", "bte"):
                vals[fname] = 0
            elif fname == "sel":
                vals[fname] = (1 << w) - 1
            elif fname == "data":
                vals[fname] = data & ((1 << w) - 1)
            else:
                vals[fname] = 0
        return vals

    lo, hi = latency_window(spec)
    steps = [{"op": "reset"},
             {"op": "drive", "iface": host, "kind": "read", "fields": f("read", a_read)},   # warm-up: opens the row
             {"op": "idle", "cycles": 300}]
    for d in range(lo, hi + 1):
        steps.append({"op": "drive", "iface": host, "kind": "read", "fields": f("read", a_read)})
        steps.append({"op": "idle", "cycles": d, "within_run": True})
        steps.append({"op": "drive", "iface": host, "kind": "write",
                      "fields": f("write", a_write, 0xA5A50000 | d)})
        steps.append({"op": "idle", "cycles": 120})
    with open(VPLAN) as f_:
        vplan = json.load(f_)
    # the plan has no host-port scope yet (HOST_001 is a proposed taxonomy
    # extension); the items this witness bears on are the host request ones
    targets = sorted({it["id"] for it in vplan["items"]
                      if it.get("scope") == "wb_port"
                      or "host" in (it.get("requirement") or "").lower()
                      and it.get("scope") in ("cmd_queue", "scheduling", "data_path")})
    return {
        "name": f"ack_collision_{host_block}_seed{seed}",
        "scope": host_block,
        "targets": targets,
        "rationale": (f"HOST_001 witness: a read to one open row, then a write beat d+1 cycles later for every "
                      f"d in [{lo}, {hi}] (spec read latency with margin), so one write acknowledge falls in the "
                      f"same cycle as the read response on the port's single ack line."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "ack_collision.py",
                        "seed": seed, "spec_revision": spec.get("revision"),
                        "reads_coverage": False, "gap_window": [lo, hi]},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    seq = generate(spec, schemas, catalog, args.seed)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    lo, hi = seq["_provenance"]["gap_window"]
    print(f"  {seq['name']}: gaps {lo}..{hi}, {len(seq['steps'])} step(s) -> {os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
