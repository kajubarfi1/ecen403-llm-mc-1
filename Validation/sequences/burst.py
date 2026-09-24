#!/usr/bin/env python3
"""
burst.py — overrun the command queue so back-pressure actually happens
=======================================================================
A queue's back-pressure is only tested in the cycles when the queue is full
and a request is still being presented. A random sequence with idle cycles
between requests never gets there, which is how a "backpressure" path can
pass while testing nothing. This drives 2 x command_queue_depth writes with
no idle cycles at all, spread across banks and rows so the scheduler cannot
drain them faster than they arrive, then lets everything settle.

Depth, address widths and the host stream come from the spec, the catalog
and the schemas; nothing here names a port.

Usage:
    python3 Validation/sequences/burst.py --seed 1 --out seq.json
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

MULTIPLE = 2       # burst length as a multiple of the queue depth


def generate(spec, schemas, catalog, seed=1, host_block="wb_port"):
    rng = random.Random(seed)
    depth = spec["controller_architecture"].get("command_queue_depth")
    if not depth:
        raise SystemExit("spec declares no controller_architecture."
                         "command_queue_depth; there is no bound to drive to")
    host = next(i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == host_block
                and "write" in schemas[i]["kinds"])
    wk = schemas[host]["kinds"]["write"]

    steps = [{"op": "reset"}]
    for _ in range(MULTIPLE * depth):
        vals = {}
        for fname, info in wk.items():
            w = info["width"]
            vals[fname] = (1 << w) - 1 if fname == "sel" else rng.randrange(0, 1 << w)
        steps.append({"op": "drive", "iface": host, "kind": "write",
                      "fields": vals})
        # no idle: the point is to arrive faster than the queue drains

    with open(VPLAN) as f:
        vplan = json.load(f)
    targets = [it["id"] for it in vplan["items"]
               if it.get("scope") == "cmd_queue"
               or "backpressure" in json.dumps(it).lower()]
    if not targets:
        raise SystemExit("no vplan item covers queue back-pressure; regenerate "
                         "the vplan (vplan_gen.py derives VP_FLOW_001 from "
                         "command_queue_depth)")
    return {
        "name": f"burst_{host_block}_seed{seed}",
        "targets": sorted(set(targets)),
        "rationale": (f"{MULTIPLE * depth} back-to-back host writes with no idle "
                      f"cycles against a {depth}-deep command queue "
                      f"(controller_architecture.command_queue_depth): the "
                      f"queue must fill and the host must be stalled, and "
                      f"no accepted request may be lost."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "burst.py",
                        "seed": seed, "spec_revision": spec.get("revision"),
                        "reads_coverage": False},
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
    n = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {n} back-to-back writes -> "
          f"{os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
