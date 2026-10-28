#!/usr/bin/env python3
"""
wb_burst.py — Wishbone linear bursts, and reads piled up until the port stalls
================================================================================
The host port's burst tracker and read-tag FIFO had never run: every
sequence drove classic single cycles (cti = 0) and waited for each ack, so
cti/bte never toggled, the burst states were dead and the tag FIFO never
held more than a few entries (coverage report 2026-10-28). This sequence
drives what the spec's host_interface declares and nothing had used:

  1. linear bursts (burst_type = linear, up to max_burst_length beats):
     cti = INCREMENTING on every beat but the last, END on the last,
     bte = linear, addresses stepping by one data word, one direction per
     burst, writes and reads mixed across bursts;
  2. a pile of pipelined single reads deeper than the read buffer
     (host_interface.read_buffer_depth), so the tag FIFO fills and the port
     stalls the host for the first time.

Consecutive drives of the interface are one pipelined run (catalog `drive`
block), so the beats are back to back. Field names, widths, the burst and
buffer parameters come from the spec, the catalog and the schemas.

Usage:
    python3 Validation/sequences/wb_burst.py --seed 1 --out seq.json
"""

import argparse
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

from register_walk import SPEC, SCHEMAS, CATALOG, VPLAN  # noqa: E402

CTI_INCREMENTING = 0b010
CTI_END = 0b111
BTE_LINEAR = 0b00


def generate(spec, schemas, catalog, seed=1, bursts=10, host_block="wb_port"):
    rng = random.Random(seed)
    host = next(i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == host_block
                and "write" in schemas[i]["kinds"] and "read" in schemas[i]["kinds"])
    kinds = schemas[host]["kinds"]
    for k in ("write", "read"):
        if "cti" not in kinds[k] or "bte" not in kinds[k]:
            raise SystemExit(f"{host}.{k} declares no cti/bte fields; bursts need them in the catalog")
    hi = spec["host_interface"]
    max_len = int(hi.get("max_burst_length", 8))
    word = int(hi.get("data_width_bits", 32)) // 8
    depth = int(hi.get("read_buffer_depth", 16))
    addr_w = kinds["write"]["addr"]["width"]

    def fields(kind, addr, cti):
        vals = {}
        for fname, info in kinds[kind].items():
            w = info["width"]
            if fname == "addr":
                vals[fname] = addr & ((1 << w) - 1)
            elif fname == "cti":
                vals[fname] = cti
            elif fname == "bte":
                vals[fname] = BTE_LINEAR
            elif fname == "sel":
                vals[fname] = (1 << w) - 1
            else:
                vals[fname] = rng.randrange(0, 1 << w)
        return vals

    steps = [{"op": "reset"}]
    for _ in range(bursts):
        n = rng.randint(2, max_len)
        kind = rng.choice(["write", "read"])
        base = rng.randrange(0, 1 << addr_w) & ~(word - 1)
        base = min(base, (1 << addr_w) - n * word)
        for b in range(n):
            steps.append({"op": "drive", "iface": host, "kind": kind,
                          "fields": fields(kind, base + b * word, CTI_END if b == n - 1 else CTI_INCREMENTING)})
        steps.append({"op": "idle", "cycles": rng.randint(2, 6)})
    # the pile: more pipelined single reads than the read buffer holds
    for _ in range(depth + depth // 2):
        steps.append({"op": "drive", "iface": host, "kind": "read",
                      "fields": fields("read", rng.randrange(0, 1 << addr_w) & ~(word - 1), 0)})

    with open(VPLAN) as f:
        vplan = json.load(f)
    # the plan has no host-port item of its own: a stalled host is back-pressure's
    # host-side face, and piled reads are the data path's read return
    targets = sorted({it["id"] for it in vplan["items"]
                      if it.get("scope") in ("cmd_queue", "data_path")})
    return {
        "name": f"wb_burst_{host_block}_seed{seed}",
        "targets": targets,
        "rationale": (f"{bursts} Wishbone linear bursts of 2..{max_len} beats (cti INCREMENTING then END, "
                      f"bte linear, addresses stepping {word} bytes, one direction per burst) and a pile of "
                      f"{depth + depth // 2} pipelined reads against a {depth}-deep read buffer: the burst "
                      f"tracker, the tag FIFO at full depth and the read-side stall, none of which classic "
                      f"single cycles ever reached."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "wb_burst.py",
                        "seed": seed, "spec_revision": spec.get("revision"),
                        "reads_coverage": False},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--bursts", type=int, default=10)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    seq = generate(spec, schemas, catalog, args.seed, args.bursts)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    n = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {n} beats in {args.bursts} bursts + read pile -> {os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
