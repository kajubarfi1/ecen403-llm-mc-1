#!/usr/bin/env python3
"""
status_poll.py — directed CSR reads of the hardware-reported status registers
==============================================================================
The status paths (init → CSR, calibration → CSR, refresh → CSR) used to be
"observed": the blocks ran on their own and nothing asked the register
interface what it was reporting. This is the missing stimulus. It reads every
register that carries hardware-driven fields (RO levels, RW1C event flags) at
a fixed interval across the whole observation window, so the exact predictor
for the register block can be judged on what the bus actually returned while
initialisation, calibration and refresh were happening underneath it.

Nothing here is design-specific: which registers report hardware state, their
offsets, and the window are read from the spec, the schemas, and the path
definition.

Usage:
    python3 Validation/sequences/status_poll.py --window 160000 --out seq.json
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

from register_walk import (SPEC, SCHEMAS, CATALOG, VPLAN, register_iface,  # noqa: E402
                           to_int)

HW_ACCESS = {"RO", "RW1C"}      # fields the hardware writes and the bus reads


def status_registers(spec):
    """Registers with at least one hardware-reported field that is not a
    reserved filler."""
    out = []
    for reg in spec["csr_register_map"]["registers"]:
        hw = [f for f in reg.get("fields", [])
              if f["access"].upper() in HW_ACCESS
              and "reserved" not in f["name"].lower()]
        if hw:
            out.append((reg, [f["name"] for f in hw]))
    return out


def generate(spec, schemas, catalog, block="config_regs", window=150_000,
             interval=2000):
    iface = register_iface(catalog, schemas, block)
    addr_w = schemas[iface]["kinds"]["read"]["addr"]["width"]
    regs = status_registers(spec)
    if not regs:
        raise SystemExit("the register map declares no hardware-reported "
                         "(RO / RW1C) fields; there is no status to poll")

    steps = [{"op": "reset"}]
    polls = max(1, window // interval)
    for _ in range(polls):
        for reg, _fields in regs:
            steps.append({"op": "drive", "iface": iface, "kind": "read",
                          "fields": {"addr": to_int(reg["offset"])
                                     & ((1 << addr_w) - 1)}})
        steps.append({"op": "idle", "cycles": interval})

    # The vplan items whose fields are the ones being polled: the sequence is
    # credited against those, nothing else.
    polled = {f"{reg['name']}.{fname}" for reg, names in regs for fname in names}
    with open(VPLAN) as f:
        vplan = json.load(f)
    targets = [it["id"] for it in vplan["items"]
               if polled & set(it.get("fields", []))]
    if not targets:
        raise SystemExit("no vplan item names any of the polled status fields; "
                         "an untargeted sequence cannot be credited")

    return {
        "name": f"status_poll_{block}",
        "targets": targets,
        "rationale": (f"Polls {len(regs)} status register(s) "
                      f"({', '.join(r['name'] for r, _ in regs)}) every "
                      f"{interval} cycles across a {window}-cycle window: "
                      f"{polls} poll(s), {polls * len(regs)} reads. The block "
                      f"underneath runs autonomously; the reads are what "
                      f"lets its reported state be judged."),
        "steps": steps,
        "_provenance": {"arm": "directed", "generator": "status_poll.py",
                        "spec_revision": spec.get("revision"),
                        "window_cycles": window, "interval": interval,
                        "reads_coverage": False},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--block", default="config_regs")
    ap.add_argument("--window", type=int, default=150_000)
    ap.add_argument("--interval", type=int, default=2000)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    with open(SPEC) as f:
        spec = json.load(f)
    with open(SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]

    seq = generate(spec, schemas, catalog, args.block, args.window,
                   args.interval)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    n = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {len(seq['steps'])} steps, {n} reads over "
          f"{args.window} cycles -> {os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
