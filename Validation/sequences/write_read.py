#!/usr/bin/env python3
"""
write_read.py — read back what was just written, with no gap
=============================================================
tWTR (write-to-read turnaround) had never been measured: the random mixed
sequence on path_18 chooses addresses independently, so a READ landing on a
bank that was WRITTEN moments before — the only situation in which the
turnaround is enforced — happened 0 times in 19 drives (cp_twtr_spacing
0%, 2026-10-15). This sequence creates it on purpose: pairs of a host write
and a host read of the SAME address, back to back across random addresses.
Same address means same bank and row, so the scheduler sees WR then a
row-hit RD and must hold the read for tWTR; and the read returns the data
just written, which the data_path predictor checks.

The host stream, its field widths and the address width all come from the
catalog and the schemas; nothing here names a port or an address bit.

Usage:
    python3 Validation/sequences/write_read.py --seed 1 --pairs 12 --out seq.json
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


def generate(spec, schemas, catalog, seed=1, pairs=12, host_block="wb_port"):
    rng = random.Random(seed)
    host = next(i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == host_block
                and "write" in schemas[i]["kinds"] and "read" in schemas[i]["kinds"])
    wk = schemas[host]["kinds"]["write"]
    rk = schemas[host]["kinds"]["read"]
    if "addr" not in wk or "addr" not in rk:
        raise SystemExit(f"{host}: write and read kinds must both carry 'addr' "
                         f"for a read-back of the same location")

    steps = [{"op": "reset"}]
    for _ in range(pairs):
        vals = {}
        for fname, info in wk.items():
            w = info["width"]
            vals[fname] = (1 << w) - 1 if fname == "sel" else rng.randrange(0, 1 << w)
        steps.append({"op": "drive", "iface": host, "kind": "write", "fields": vals})
        rd = {fname: vals[fname] if fname in vals else rng.randrange(0, 1 << info["width"])
              for fname, info in rk.items()}
        steps.append({"op": "drive", "iface": host, "kind": "read", "fields": rd})
        # no idle: the turnaround must come from the controller, not the host

    with open(VPLAN) as f:
        vplan = json.load(f)
    targets = sorted({it["id"] for it in vplan["items"]
                      if any("twtr" in c["name"].lower() for c in it.get("coverage_items", []))
                      or it.get("scope") == "data_path"})
    return {
        "name": f"write_read_{host_block}_seed{seed}",
        "targets": targets,
        "rationale": (f"{pairs} write/read pairs to the same address with no idle "
                      f"cycles: each read is a row hit on a bank written moments "
                      f"before, so the write-to-read turnaround (tWTR) is enforced "
                      f"and measured, and each read returns the data just written."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "write_read.py",
                        "seed": seed, "spec_revision": spec.get("revision"),
                        "reads_coverage": False},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pairs", type=int, default=12)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    seq = generate(spec, schemas, catalog, args.seed, args.pairs)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    print(f"  {seq['name']}: {args.pairs} write/read pairs -> "
          f"{os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
