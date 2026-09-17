#!/usr/bin/env python3
"""
harness_gen.py — generate the testbench top that runs one scope's DUT
======================================================================
The missing deterministic piece between driver_gen.py and a simulator: a
module that instantiates the DUT and the generated seq_driver, wires them,
generates the clock, ties off every DUT input the driver does not drive, and
finishes when the driver reports done.

Everything is derived from data:

  * DUT ports come from the block's newest Frontend manifest — names, widths
    and directions are the design's own declaration, so a port rename shows
    up as a compile error, not a silently unconnected net.
  * The driver's port list is re-derived from the sequence with the same rule
    driver_gen.py uses (every field port of every driven interface, plus its
    qualifier), so the two generators cannot disagree.
  * The clock period comes from the spec's clocking_model, not a literal.
    The controller clock is the only clock a block-level harness generates.
  * Clock/reset port names come from the interface catalog entries of the
    scope's own streams.

The old per-scope testbenches drove hex vectors and compared expected values
cycle-by-cycle inside the TB. This harness checks NOTHING on purpose: the
monitors observe, the trace extractor and scoreboard judge, offline. A
testbench that both drives and grades is how the 176 phantom failures
happened.

Usage:
    python3 Validation/sequences/harness_gen.py --scope config_regs \
        --sequence Validation/sequences/generated/foo.json
"""

import argparse
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated",
                           "schemas.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn",
                            "interface_catalog.json")
DEFAULT_OUT = os.path.join(HERE, "generated")

# Cycles the harness waits after `done` before $finish, so in-flight
# responses and change-qualified level monitors get their final samples.
SETTLE_CYCLES = 16
# Absolute watchdog: a wedged DUT must end the job, not the Slurm timeout.
WATCHDOG_NS = 2_000_000


class HarnessError(Exception):
    pass


def manifest_ports(scope):
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{scope}_manifest.json"),
                             recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    if not paths:
        raise HarnessError(f"no manifest found for block {scope!r} under "
                           f"Frontend/ — the harness cannot know its ports.")
    with open(paths[0]) as f:
        m = json.load(f)
    ports = []
    for group in m["ports"].values():
        for p in group:
            ports.append((p["name"], p["width"], p["dir"]))
    return ports, paths[0]


def driver_ports(seq, schemas, catalog):
    """Delegates to the SAME derivation driver_gen.py uses
    (sequence_contract.stimulus_ports), so the harness and the driver agree
    by construction. Returns (driver_outputs, driver_inputs) as port-name
    sets; the driver's inputs (handshake completion signals) are DUT outputs
    the harness routes back, never tie-offs."""
    sys.path.insert(0, HERE)
    import sequence_contract as SC
    ifaces = sorted({s["iface"] for s in seq["steps"] if s.get("op") == "drive"})
    if not ifaces:
        raise HarnessError("sequence drives nothing")
    outs, ins = set(), set()
    for iface in ifaces:
        try:
            sp = SC.stimulus_ports(iface, catalog, schemas)
        except SC.SequenceError as e:
            raise HarnessError(str(e))
        outs |= set(sp["outputs"])
        ins |= set(sp["inputs"])
    return outs, ins


def clock_reset_names(scope, catalog):
    names = {(d.get("clock"), d.get("reset")) for d in catalog.values()
             if d.get("block") == scope}
    names.discard((None, None))
    if len(names) != 1:
        raise HarnessError(
            f"scope {scope!r} interfaces declare {len(names)} distinct "
            f"clock/reset pairs ({sorted(names)}); a single-clock harness "
            f"cannot serve it.")
    return names.pop()


def generate(scope, seq):
    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]

    period = spec["clocking_model"]["controller_clock_period_ns"]
    half = period / 2.0
    clk, rst = clock_reset_names(scope, catalog)

    ports, manifest = manifest_ports(scope)
    driven, sampled = driver_ports(seq, schemas, catalog)

    decls, dut_conn, drv_conn, tieoffs = [], [], [], []
    for name, width, direction in ports:
        if name in (clk,):
            dut_conn.append(f".{name}({name})")
            continue
        if not isinstance(width, int):
            raise HarnessError(
                f"{scope}.{name} has non-scalar width {width!r}; a port the "
                f"manifest cannot describe as a vector cannot be harnessed.")
        dim = "" if width == 1 else f"[{width-1}:0] "
        decls.append(f"  logic {dim}{name};")
        dut_conn.append(f".{name}({name})")
        if name == rst:
            continue                      # the driver owns reset
        if name in driven:
            if direction != "input":
                raise HarnessError(
                    f"the driver would drive {scope}.{name}, but the design "
                    f"declares it an {direction} — the catalog's drive/"
                    f"qualifier declaration and the manifest disagree.")
            drv_conn.append(f".{name}({name})")
        elif name in sampled:
            # A handshake completion signal: the DUT drives it, the driver
            # waits on it.
            drv_conn.append(f".{name}({name})")
        elif direction == "input":
            # An input nobody drives floats as X and poisons the run; tie it
            # off explicitly so absence is a visible choice, not an accident.
            tieoffs.append(f"  assign {name} = '0;   // undriven input")

    for p in sorted(driven | sampled):
        if p not in {n for n, _, _ in ports}:
            raise HarnessError(
                f"the sequence drives or samples port {p!r} but block "
                f"{scope!r} has no such port — sequence and design disagree.")

    return f"""`timescale 1ns/1ps
// GENERATED by Validation/sequences/harness_gen.py — DO NOT EDIT BY HAND.
//
// Scope    : {scope}
// Manifest : {os.path.relpath(manifest, ROOT)}
// Sequence : {seq.get('name', '?')}
//
// This harness drives and observes; it never checks. Checking happens
// offline: monitors emit TXN lines, trace_extract.py parses them, and the
// scoreboard compares against the gate-accepted predictor.

module {scope}_txn_harness;

  logic {clk} = 1'b0;
  always #{half} {clk} = ~{clk};   // {period} ns from spec clocking_model

  logic done;

{chr(10).join(decls)}

{chr(10).join(tieoffs) if tieoffs else "  // every input is driver-driven"}

  seq_driver u_driver (
    .clk({clk}),
    .rst_n_i({rst}),
    .rst_n({rst}),
    .done(done),
    {("," + chr(10) + "    ").join(sorted(drv_conn))}
  );

  {scope} dut (
    {("," + chr(10) + "    ").join(dut_conn)}
  );

  initial begin
    wait (done);
    repeat ({SETTLE_CYCLES}) @(posedge {clk});
    $display("HARNESS_DONE");
    $finish;
  end

  initial begin
    #{WATCHDOG_NS};
    $display("HARNESS_TIMEOUT after {WATCHDOG_NS} ns — DUT or driver wedged");
    $finish;
  end

endmodule
"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--sequence", required=True)
    ap.add_argument("--outdir", default=DEFAULT_OUT)
    args = ap.parse_args()

    with open(args.sequence) as f:
        seq = json.load(f)
    try:
        sv = generate(args.scope, seq)
    except HarnessError as e:
        print(f"  {e}", file=sys.stderr)
        return 2

    os.makedirs(args.outdir, exist_ok=True)
    dest = os.path.join(args.outdir, f"{args.scope}_txn_harness.sv")
    with open(dest, "w") as f:
        f.write(sv)
    print(f"  wrote {os.path.relpath(dest, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
