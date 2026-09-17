#!/usr/bin/env python3
"""
register_walk.py — directed CSR stimulus derived from the spec's register map
==============================================================================
Random 8-bit CSR addresses mostly miss the handful of implemented registers,
which is why config_regs sat at 15.7% code coverage after the first sweep.
This walks every register the spec declares, in the same step format the
agent's sequences use, so the identical driver codegen and harness run it.

Per register, driven by its declared access type:

  RW    read (reset value) -> write each pattern -> read back after each
  RW1C  read -> write each pattern (each a partial clear) -> read back
  RO    read -> write each pattern (must be ignored) -> read back

Every class sees every pattern so the vplan's register x write-pattern
crosses can reach 100%.

then a few deliberately unmapped addresses, which exercise the error path
(the read data there is spec-silent and waiver-tracked as VP_CSR_006; the
error flag itself is compared).

Patterns are chosen for TOGGLE coverage, not plausibility: all-ones, zero,
and the two alternating patterns flip every writable bit both ways.

Nothing here is design-specific: register offsets, widths, access types and
patterns come from the spec and the schemas.

Usage:
    python3 Validation/sequences/register_walk.py --out seq.json
    python3 Validation/tools/rerun_scope.py --scope config_regs --sequence seq.json
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

SPEC = os.path.join(ROOT, "Validation", "spec",
                    "llmmc_microarchitecturespec_filled.json")
SCHEMAS = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
VPLAN = os.path.join(ROOT, "Validation", "vplan", "vplan.json")

PATTERNS = [0xFFFFFFFF, 0x00000000, 0xA5A5A5A5, 0x5A5A5A5A]


def to_int(v):
    return int(v, 16) if isinstance(v, str) else int(v)


def register_iface(catalog, schemas, block):
    """The block's request stream that carries an address and data — the
    register bus. Picked by shape, not by name."""
    for name, d in catalog.items():
        if d.get("block") != block or d.get("role") != "request":
            continue
        kinds = schemas[name]["kinds"]
        if "write" in kinds and "read" in kinds \
                and {"addr", "data"} <= set(kinds["write"]):
            return name
    raise SystemExit(f"no register-bus stream declared for block {block!r}")


def generate(spec, schemas, catalog, block="config_regs", idle=2):
    iface = register_iface(catalog, schemas, block)
    kinds = schemas[iface]["kinds"]
    addr_w = kinds["write"]["addr"]["width"]
    data_w = kinds["write"]["data"]["width"]
    data_mask = (1 << data_w) - 1
    addr_mask = (1 << addr_w) - 1

    rmap = spec["csr_register_map"]
    regs = sorted(rmap["registers"], key=lambda r: to_int(r["offset"]))

    steps = [{"op": "reset"}]

    def drive(kind, **fields):
        steps.append({"op": "drive", "iface": iface, "kind": kind,
                      "fields": fields})
        steps.append({"op": "idle", "cycles": idle})

    for reg in regs:
        off = to_int(reg["offset"]) & addr_mask
        acc = reg["access"].upper()
        drive("read", addr=off)                     # reset value
        if acc == "RW":
            for pat in PATTERNS:
                drive("write", addr=off, data=pat & data_mask)
                drive("read", addr=off)
        else:
            # RW1C: each pattern is a (partial) clear, read back after each.
            # RO: each pattern must be ignored, read back proves it. Every
            # class sees every pattern so the register x pattern crosses in
            # the vplan can actually reach 100%.
            for pat in PATTERNS:
                drive("write", addr=off, data=pat & data_mask)
                drive("read", addr=off)

    # A few unmapped addresses: just past the last register, one mid-gap
    # (if any), and the top of the address space.
    used = {to_int(r["offset"]) & addr_mask for r in regs}
    stride = 4 if rmap.get("data_width_bits", 32) == 32 else 1
    probes = [max(used) + stride, addr_mask & ~(stride - 1)]
    gaps = [a for a in range(0, max(used), stride) if a not in used]
    if gaps:
        probes.insert(1, gaps[len(gaps) // 2])
    for a in probes:
        if a not in used and 0 <= a <= addr_mask:
            drive("read", addr=a)
            drive("write", addr=a, data=PATTERNS[3] & data_mask)

    with open(VPLAN) as f:
        vplan = json.load(f)
    targets = [it["id"] for it in vplan["items"] if it.get("scope") == block]

    n_drive = sum(1 for s in steps if s["op"] == "drive")
    return {
        "name": f"register_walk_{block}",
        "targets": targets,
        "rationale": (f"Directed walk of all {len(regs)} registers in "
                      f"csr_register_map on {iface}: reset-value read, then "
                      f"access-type-appropriate writes with toggle patterns "
                      f"and read-back, plus {len(probes)} unmapped probes. "
                      f"{n_drive} drives."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "register_walk.py",
                        "spec_revision": spec.get("revision"),
                        "reads_coverage": False},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--block", default="config_regs")
    ap.add_argument("--idle", type=int, default=2)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]

    seq = generate(spec, schemas, catalog, args.block, args.idle)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    n = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {len(seq['steps'])} steps, {n} drives "
          f"-> {os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
