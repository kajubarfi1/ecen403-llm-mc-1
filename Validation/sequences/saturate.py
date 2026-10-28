#!/usr/bin/env python3
"""
saturate.py — keep the command queue full of unlike requests for a long time
=============================================================================
The queue's and the scheduler's per-entry storage (row, column, bank, aux,
we for every slot) toggled in only the first few slots: traffic arrived in
short bursts, drained, and the upper slots rarely held anything, let alone
anything different from what they held before (coverage report
2026-10-28). This drives a long pipelined stream of mixed reads and writes
with high-entropy addresses and no idle, so every slot is occupied and
rewritten many times with unlike values while the scheduler works at its
limit. Depth and widths come from the spec and the schemas.

Usage:
    python3 Validation/sequences/saturate.py --seed 1 --drives 240 --out seq.json
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


def generate(spec, schemas, catalog, seed=1, drives=240, host_block="wb_port"):
    rng = random.Random(seed)
    host = next(i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == host_block
                and "write" in schemas[i]["kinds"])
    kinds = schemas[host]["kinds"]
    word = int(spec["host_interface"].get("data_width_bits", 32)) // 8
    depth = spec["controller_architecture"].get("command_queue_depth", 16)
    steps = [{"op": "reset"}]
    for _ in range(drives):
        kind = rng.choice(sorted(kinds))
        vals = {}
        for fname, info in kinds[kind].items():
            w = info["width"]
            if fname == "addr":
                vals[fname] = rng.randrange(0, 1 << w) & ~(word - 1)
            elif fname in ("cti", "bte"):
                vals[fname] = 0
            elif fname == "sel":
                vals[fname] = (1 << w) - 1 if rng.random() < 0.5 else rng.randrange(1, 1 << w)
            else:
                vals[fname] = rng.randrange(0, 1 << w)
        steps.append({"op": "drive", "iface": host, "kind": kind, "fields": vals})
    with open(VPLAN) as f:
        vplan = json.load(f)
    targets = sorted({it["id"] for it in vplan["items"] if it.get("scope") in ("cmd_queue", "scheduler")})
    return {
        "name": f"saturate_{host_block}_seed{seed}",
        "targets": targets,
        "rationale": (f"{drives} pipelined mixed reads and writes with no idle against a {depth}-deep "
                      f"command queue: every slot occupied and rewritten with unlike row, column, bank, "
                      f"aux and direction while the scheduler drains at its limit."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "saturate.py",
                        "seed": seed, "spec_revision": spec.get("revision"),
                        "reads_coverage": False},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--drives", type=int, default=240)
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
    print(f"  {seq['name']}: {args.drives} back-to-back drives -> {os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
