#!/usr/bin/env python3
"""
random_v2.py — constrained-random stimulus that knows the address map
=====================================================================
The v1 control (`random_sequence.py`) draws every field uniformly. Uniform
29-bit addresses almost never revisit a bank, so a "random" run never makes
the scheduler resolve a row conflict, never precharges under pressure, and
never issues two CAS commands to one row back to back — exactly the corners
the timing-boundary bins (VP_TIME_*) and the scheduler/cmd_queue code sit in.

v2 is still seeded, still legal, still reads no coverage. What it adds is
STRUCTURE derived from the spec:

  * address locality — each request is a row HIT (same bank, same row, next
    column), a CONFLICT (same bank, different row), a BANK SWITCH (another
    bank), or a fresh random address, with weights from a seed-chosen
    profile; the row/bank/column split comes from memory_geometry;
  * back-pressure bursts — runs of 2 x command_queue_depth requests with no
    idle cycles, so the queue fills and the host is stalled;
  * pacing phases — idle gaps drawn from {0..3} so consecutive commands land
    at or near the minimum legal spacing, and occasional drains so the next
    burst starts against empty banks;
  * read/write shaping — write-then-read and read-then-write to the same
    address (tWTR, read-to-write turnaround), same-row read pairs (tCCD),
    write-then-conflict (tWR before precharge).

Same step format and validation as every other sequence, so the identical
driver, harness, assertions and rollup run it.

Usage:
    python3 Validation/closure/random_v2.py --scope wb_port --seed 3 --drives 400 --out seq.json
"""
import argparse
import json
import math
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))

SPEC = os.path.join(ROOT, "Validation", "spec", "llmmc_microarchitecturespec_filled.json")
SCHEMAS = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")

# Locality profiles: weights for (hit, conflict, bank_switch, random).
PROFILES = {
    "hit_heavy":      (0.60, 0.15, 0.15, 0.10),
    "conflict_heavy": (0.20, 0.55, 0.15, 0.10),
    "bank_spread":    (0.20, 0.15, 0.55, 0.10),
    "mixed":          (0.35, 0.30, 0.25, 0.10),
}
TARGETS = ["VP_TIME_001", "VP_TIME_002", "VP_TIME_003", "VP_TIME_004", "VP_TIME_005",
           "VP_TIME_007", "VP_TIME_008", "VP_TIME_009", "VP_TIME_010", "VP_TIME_011",
           "VP_TIME_012", "VP_FLOW_001"]


class AddressMap:
    """Byte address <-> (row, bank, column) exactly as addr_decoder_predictor
    reads the spec: row-bank-column above the burst and byte-offset bits."""

    def __init__(self, spec):
        g = spec["memory_geometry"]
        self.row_bits = int(g["row_bits"])
        self.bank_bits = int(g["bank_bits"])
        self.col_bits = int(g["column_bits"])
        bl = int(g.get("burst_length", 8))
        chan_bytes = int(spec["data_path_mapping"]["ddr_channel_width_bits"]) // 8
        self.byte_off = int(math.log2(chan_bytes))
        self.burst_off = int(math.log2(bl))
        self.col_upper = self.col_bits - self.burst_off
        self.addr_bits = int(spec["host_interface"]["address_width_bits"])

    def compose(self, row, bank, colu, burst_off=0, byte_off=0):
        a = row
        a = (a << self.bank_bits) | bank
        a = (a << self.col_upper) | colu
        a = (a << self.burst_off) | burst_off
        a = (a << self.byte_off) | byte_off
        return a & ((1 << self.addr_bits) - 1)


def generate(spec, schemas, catalog, scope, seed=1, drives=400, only_kinds=None,
             profile=None):
    rng = random.Random(seed)
    amap = AddressMap(spec)
    depth = int(spec["controller_architecture"].get("command_queue_depth", 16))
    drivable = [i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == scope]
    if not drivable:
        raise SystemExit(f"no stimulus interface for scope {scope!r}")
    iface = drivable[0]
    kinds = schemas[iface]["kinds"]
    if only_kinds:
        kinds = {k: v for k, v in kinds.items() if k in only_kinds}
    kind_names = sorted(kinds)
    if not kind_names:
        raise SystemExit(f"{iface!r} has none of the requested kinds")
    prof = profile or sorted(PROFILES)[seed % len(PROFILES)]
    w_hit, w_conf, w_bank, w_rand = PROFILES[prof]

    # working set: what we believe the controller has open, per bank
    open_row = {}
    last = None                     # (row, bank, colu) of the previous request

    def next_addr():
        nonlocal last
        r = rng.random()
        if last and r < w_hit:
            row, bank, colu = last[0], last[1], (last[2] + 1) % (1 << amap.col_upper)
        elif last and r < w_hit + w_conf:
            row = (last[0] + rng.randrange(1, 1 << amap.row_bits)) % (1 << amap.row_bits)
            bank, colu = last[1], rng.randrange(1 << amap.col_upper)
        elif r < w_hit + w_conf + w_bank:
            bank = rng.randrange(1 << amap.bank_bits)
            row = open_row.get(bank, rng.randrange(1 << amap.row_bits))
            colu = rng.randrange(1 << amap.col_upper)
        else:
            row = rng.randrange(1 << amap.row_bits)
            bank = rng.randrange(1 << amap.bank_bits)
            colu = rng.randrange(1 << amap.col_upper)
        open_row[bank] = row
        last = (row, bank, colu)
        # mostly burst-aligned; a few unaligned so byte enables / offsets vary
        boff = 0 if rng.random() < 0.85 else rng.randrange(1 << amap.burst_off)
        return amap.compose(row, bank, colu, boff, 0)

    def fields_for(kind, addr):
        vals = {}
        for fname, info in kinds[kind].items():
            w = info["width"]
            if fname in ("addr", "address"):
                vals[fname] = addr
            elif fname == "sel" or fname == "mask":
                vals[fname] = (1 << w) - 1 if rng.random() < 0.7 else rng.randrange(1, 1 << w)
            elif fname == "we":
                vals[fname] = 1 if kind == "write" else 0
            elif isinstance(w, int):
                vals[fname] = rng.randrange(0, 1 << w)
            else:
                vals[fname] = 0
        return vals

    steps = [{"op": "reset"}]
    n = 0
    phases = []
    while n < drives:
        phase = rng.choice(["burst", "paced", "paced", "rw_pairs", "drain"])
        phases.append(phase)
        if phase == "burst":
            for _ in range(min(2 * depth, drives - n)):
                kind = rng.choice(kind_names)
                steps.append({"op": "drive", "iface": iface, "kind": kind,
                              "fields": fields_for(kind, next_addr())})
                n += 1
        elif phase == "paced":
            for _ in range(min(rng.randint(8, 24), drives - n)):
                kind = rng.choice(kind_names)
                steps.append({"op": "drive", "iface": iface, "kind": kind,
                              "fields": fields_for(kind, next_addr())})
                n += 1
                gap = rng.randint(0, 3)
                if gap:
                    steps.append({"op": "idle", "cycles": gap})
        elif phase == "rw_pairs" and "read" in kinds and "write" in kinds:
            for _ in range(min(rng.randint(3, 8), (drives - n) // 2)):
                a = next_addr()
                first, second = (("write", "read") if rng.random() < 0.5 else ("read", "write"))
                steps.append({"op": "drive", "iface": iface, "kind": first, "fields": fields_for(first, a)})
                gap = rng.randint(0, 2)
                if gap:
                    steps.append({"op": "idle", "cycles": gap})
                steps.append({"op": "drive", "iface": iface, "kind": second, "fields": fields_for(second, a)})
                n += 2
        else:   # drain: let the queue empty and banks close on their own
            steps.append({"op": "idle", "cycles": rng.randint(20, 60)})
    steps.append({"op": "idle", "cycles": 32})

    return {
        "name": f"crv2_{prof}_seed{seed}",
        "targets": TARGETS,
        "rationale": (f"Constrained-random v2, profile {prof} (hit/conflict/bank-switch/random = "
                      f"{w_hit}/{w_conf}/{w_bank}/{w_rand}), seed {seed}: {n} host requests over "
                      f"{len(phases)} phases (bursts of {2 * depth} with no idle against a "
                      f"{depth}-deep queue, paced runs at 0-3 idle cycles, read/write pairs to one "
                      f"address, drains). Address locality derived from memory_geometry "
                      f"({amap.row_bits} row / {amap.bank_bits} bank / {amap.col_upper}+{amap.burst_off} column bits). "
                      f"Generated without reading coverage."),
        "steps": steps,
        "_provenance": {"arm": "constrained_v2", "generator": "random_v2.py", "seed": seed,
                        "profile": prof, "spec_revision": spec.get("revision"),
                        "reads_coverage": False, "phases": phases},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", default="wb_port")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--drives", type=int, default=400)
    ap.add_argument("--kinds", help="comma-separated kinds to restrict to")
    ap.add_argument("--profile", choices=sorted(PROFILES))
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    seq = generate(spec, schemas, catalog, args.scope, args.seed, args.drives,
                   only_kinds=set(args.kinds.split(",")) if args.kinds else None,
                   profile=args.profile)
    import sequence_contract as SC
    errs = SC.validate(seq, schemas, {s["iface"] for s in seq["steps"] if s["op"] == "drive"})
    if errs:
        print("sequence rejected by the contract:\n  " + "\n  ".join(errs[:5]), file=sys.stderr)
        return 1
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    n_drive = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {len(seq['steps'])} steps, {n_drive} drives, "
          f"phases={len(seq['_provenance']['phases'])} -> {os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
