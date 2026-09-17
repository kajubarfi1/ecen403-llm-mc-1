#!/usr/bin/env python3
"""
driver_gen.py — turn a generated sequence into a SystemVerilog stimulus driver
===============================================================================
The deterministic half of stimulus generation. The agent decides WHAT to try,
at transaction level; this decides HOW to drive it, and the agent never sees
SystemVerilog.

That split exists for the same reason the monitors are generated rather than
prompted: driving discipline has to be right every time. Stimulus applied on
the wrong clock edge, or held for the wrong number of cycles, produces a
design that appears to misbehave — and the resulting mismatch gets blamed on
the RTL. Every driver emitted here applies stimulus on the NEGATIVE edge so
inputs are stable well before the design samples them on the positive edge,
and deasserts the valid qualifier the cycle after.

The generated module is a testbench component, not a monitor: it drives. It is
instantiated by a harness rather than bound, because binding something that
drives into a DUT would be a very good way to create a bug nobody can find.

Usage:
    python3 Validation/sequences/driver_gen.py --sequence <seq.json>
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

import sequence_contract as SC

SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
DEFAULT_OUT = os.path.join(HERE, "generated")


def _kind_signal(cat, kind):
    """(signal, value) selecting this kind, from kind_select — reversed:
    the monitor maps signal value -> kind, the driver maps kind -> value."""
    ks = cat.get("kind_select")
    if not ks:
        return None
    rev = {v: k for k, v in ks["map"].items()}
    if kind not in rev:
        raise SC.SequenceError(
            f"kind {kind!r} is not in {ks['expr']}'s kind_select map "
            f"({sorted(rev)}); the driver cannot select it.")
    return ks["expr"], rev[kind]


def generate(seq, schemas, catalog):
    """Emit a SystemVerilog driver module for one sequence.

    Two driving styles, decided by catalog data (see
    sequence_contract.stimulus_ports):

      * valid-style — the qualifier is a DUT input the driver asserts. A
        drive consumes EXACTLY ONE cycle, because that is the model the
        agent is given ("a drive occupies one cycle; use idle of N-1 to
        place commands N cycles apart"). An earlier version deasserted the
        qualifier on a second negedge, so every spacing came out one too
        large and every at_minimum bin was unreachable. The qualifier is
        held across consecutive drives and dropped only when the next step
        is not a drive.

      * handshake — the catalog declares a `drive` block. The driver asserts
        the request signals, waits (bounded) for the completion signal the
        DUT owns, then deasserts. A handshake drive takes as many cycles as
        the DUT takes to accept, so spacing-sensitive scopes should use
        valid-style streams; the harness watchdog bounds a DUT that never
        answers, and DRIVER_STALL in the log names the interface that hung.
    """
    ifaces = sorted({s["iface"] for s in seq["steps"] if s.get("op") == "drive"})
    if not ifaces:
        raise SC.SequenceError("sequence drives nothing")

    outs, ins = {}, {}
    for iface in ifaces:
        sp = SC.stimulus_ports(iface, catalog, schemas)
        outs.update(sp["outputs"])
        ins.update(sp["inputs"])

    decls = ([f"    input  logic {p}" for p in sorted(ins)]
             + [f"    output logic {'' if w == 1 else f'[{w-1}:0] '}{p}"
                for p, w in sorted(outs.items())])

    # One bounded-wait task per handshake interface that declares completion.
    waits = []
    for iface in ifaces:
        drv = catalog[iface].get("drive")
        if drv and drv.get("complete"):
            c = drv["complete"]
            waits.append(f"""  task automatic wait_{iface}();
    int w_;
    w_ = 0;
    do begin @(negedge clk); w_++; end while (!{c} && w_ < 256);
    if (!{c})
      $display("DRIVER_STALL: {iface} — {c} never asserted within 256 cycles");
  endtask
""")

    steps = seq["steps"]
    body, name = [], seq["name"]
    for i, st in enumerate(steps):
        op = st["op"]
        nxt = steps[i + 1] if i + 1 < len(steps) else None
        if op == "reset":
            body.append("      do_reset();")
            continue
        if op == "idle":
            body.append(f"      idle({st['cycles']});")
            continue

        iface, kind = st["iface"], st["kind"]
        cat = catalog[iface]
        fields = schemas[iface]["kinds"][kind]
        assigns = [f"{fields[f]['port']} = {fields[f]['width']}'d{v}"
                   for f, v in sorted(st["fields"].items())]
        ksig = _kind_signal(cat, kind)
        if ksig:
            assigns.append(f"{ksig[0]} = 1'b{ksig[1]}")

        drv = cat.get("drive")
        if drv:
            req = list(drv.get("assert", [])) + \
                list(drv.get("assert_by_kind", {}).get(kind, []))
            if not req:
                raise SC.SequenceError(
                    f"{iface!r}'s drive block asserts nothing for kind "
                    f"{kind!r} — add it to assert or assert_by_kind.")
            for sig, val in drv.get("hold", {}).items():
                assigns.append(f"{sig} = {val}")
            for sig in req:
                if not (ksig and sig == ksig[0]):
                    assigns.append(f"{sig} = 1'b1")
            line = (f"      // {iface}.{kind} (handshake)\n"
                    f"      @(negedge clk); {'; '.join(assigns)};")
            if drv.get("complete"):
                line += f"\n      wait_{iface}();"
            else:
                line += "\n      @(negedge clk);"
            drop = sorted(set(req)
                          | set(drv.get("hold", {}))
                          | ({ksig[0]} if ksig else set()))
            line += ("\n      " + "; ".join(f"{s} = '0" for s in drop) + ";")
            body.append(line)
        else:
            q = cat["qualifier"]
            drop = (nxt is None or nxt.get("op") != "drive"
                    or nxt.get("iface") != iface)
            line = (f"      // {iface}.{kind}\n"
                    f"      @(negedge clk); {'; '.join(assigns)}; "
                    f"{q} = 1'b1;")
            if drop:
                line += f"\n      @(negedge clk); {q} = 1'b0;"
            body.append(line)

    zero = "\n".join(f"    {p} = '0;" for p in sorted(outs))

    return f"""`timescale 1ns/1ps
// GENERATED by Validation/sequences/driver_gen.py — DO NOT EDIT BY HAND.
//
// Sequence : {name}
// Targets  : {', '.join(seq.get('targets', []))}
// Steps    : {len(seq['steps'])}
//
// The sequence was chosen by an agent at transaction level; the driving
// discipline below is generated. Stimulus is applied on the NEGATIVE edge so
// inputs are stable before the design samples them on the positive edge —
// driving on the same edge the DUT samples is a race, and the mismatches it
// produces get blamed on the design.

module seq_driver (
    input  logic clk,
    input  logic rst_n_i,
    output logic rst_n,
{",".join(chr(10) + d for d in decls)},
    output logic done
);

  task automatic idle(input int n);
    begin
      repeat (n) @(negedge clk);
    end
  endtask

  task automatic do_reset();
    begin
      rst_n = 1'b0;
      repeat (4) @(negedge clk);
      rst_n = 1'b1;
      repeat (2) @(negedge clk);
    end
  endtask

{chr(10).join(waits)}
  initial begin
    done  = 1'b0;
    rst_n = 1'b0;
{zero}
    @(negedge clk);

{chr(10).join(body)}

    repeat (16) @(negedge clk);
    done = 1'b1;
  end

endmodule
"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", required=True)
    ap.add_argument("--outdir", default=DEFAULT_OUT)
    args = ap.parse_args()

    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]
    seq = SC.load(args.sequence)

    drivable = {i for i, d in catalog.items() if d.get("role") == "request"}
    # A sequence may declare itself an untargeted control. Everything else
    # about it is validated identically — same schema, same field widths, same
    # legality — because both experiment arms must go through this code.
    is_control = seq.get("_provenance", {}).get("arm") == "control"
    errs = SC.validate(seq, schemas, drivable, require_targets=not is_control)
    if errs:
        print("sequence rejected:", file=sys.stderr)
        for e in errs:
            print(f"  {e}", file=sys.stderr)
        return 1

    src = generate(seq, schemas, catalog)
    os.makedirs(args.outdir, exist_ok=True)
    dest = os.path.join(args.outdir, "seq_driver.sv")
    with open(dest, "w") as f:
        f.write(src)
    print(f"  {SC.summarize(seq)}")
    print(f"  wrote {os.path.relpath(dest, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
