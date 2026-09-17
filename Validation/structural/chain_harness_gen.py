#!/usr/bin/env python3
"""
chain_harness_gen.py — generate the multi-block integration harness
====================================================================
The Frontend drop contains eleven blocks and no top level, so composed-path
simulation needs an integration harness nobody wrote. This generates it from
integration_map.json: instantiate the path's blocks (plus the support
closure the map declares), wire every declared connection, tie off what
remains, drive the entry stream with the generated seq_driver, and bind the
passive monitors of every instantiated module.

Wiring is CHECKED, not assumed: every connection's ports must exist in the
manifests and the widths must agree, or generation fails loudly with the
mismatch named. A regenerated RTL drop that renames or resizes a port breaks
here first, at zero simulation cost. Run with --check to run only that
conformance pass.

Like the single-block harness, this checks nothing at runtime: monitors
observe, and judgment happens offline per stage (exact stages against their
predictors, nondeterministic stages against their invariant checkers).

Usage:
    python3 Validation/structural/chain_harness_gen.py --path path_01_write_cmd \
        --sequence Validation/sequences/generated/seq.json
    python3 Validation/structural/chain_harness_gen.py --check
"""

import argparse
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))

MAP_PATH = os.path.join(HERE, "integration_map.json")
SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated",
                           "schemas.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn",
                            "interface_catalog.json")
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
DEFAULT_OUT = os.path.join(ROOT, "Validation", "sequences", "generated")

DEFAULT_SETTLE = 64         # refresh/queue drain after the driver finishes
WATCHDOG_NS = 4_000_000


class WiringError(Exception):
    pass


def manifest_ports(block):
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{block}_manifest.json"),
                             recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    if not paths:
        raise WiringError(f"no manifest for block {block!r}")
    with open(paths[0]) as f:
        m = json.load(f)
    return {p["name"]: (p["width"], p["dir"])
            for g in m["ports"].values() for p in g}


def rtl_file(block):
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{block}.sv"), recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    if not paths:
        raise WiringError(f"no {block}.sv under Frontend/")
    return paths[0]


def net_decl(name, width):
    """SystemVerilog net declaration matching a manifest width. 'DxW' means
    an unpacked array (depth D of W-bit words), the form the RTL uses."""
    if isinstance(width, str) and "x" in width:
        d, w = width.split("x")
        return f"  logic [{int(w)-1}:0] {name} [{int(d)}];"
    w = int(width)
    dim = "" if w == 1 else f"[{w-1}:0] "
    return f"  logic {dim}{name};"


def block_closure(blocks, imap):
    req = imap.get("requires", {})
    out = set(blocks)
    frontier = list(blocks)
    while frontier:
        b = frontier.pop()
        for dep in req.get(b, []):
            if dep not in out:
                out.add(dep)
                frontier.append(dep)
    return sorted(out)


def check_wiring(imap, blocks):
    """Every connection among these blocks must name real, width-matched
    ports with the right directions."""
    ports = {b: manifest_ports(b) for b in blocks}
    errs = []

    def endpoint(ref):
        blk, _, port = ref.partition(".")
        return blk, port

    def width_of(ref):
        blk, port = endpoint(ref)
        if blk not in ports:
            return None
        if port not in ports[blk]:
            errs.append(f"{ref}: block {blk!r} has no port {port!r}")
            return None
        return ports[blk][port]

    conns = list(imap["connections"])
    for g in imap.get("glue", []):
        for to in g["to"]:
            conns.append({"from": g["from"], "to": to})

    for c in conns:
        fb, _ = endpoint(c["from"])
        tb, _ = endpoint(c["to"])
        if fb not in ports or tb not in ports:
            continue                      # spans a block outside this set
        fw = width_of(c["from"])
        tw = width_of(c["to"])
        if fw is None or tw is None:
            continue
        if fw[1] != "output":
            errs.append(f"{c['from']} is an {fw[1]}, but is wired as a source")
        if tw[1] != "input":
            errs.append(f"{c['to']} is an {tw[1]}, but is wired as a sink")
        if str(fw[0]) != str(tw[0]):
            errs.append(f"{c['from']} ({fw[0]}) -> {c['to']} ({tw[0]}): "
                        f"width mismatch")
    return errs


def generate(path_id, seq, imap, settle=DEFAULT_SETTLE):
    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]
    with open(PATH_DEFS) as f:
        pdefs = {p["id"]: p for p in json.load(f)["paths"]}
    if path_id not in pdefs:
        raise WiringError(f"unknown path {path_id!r}; known: {sorted(pdefs)}")

    blocks = block_closure(pdefs[path_id]["blocks"], imap)
    errs = check_wiring(imap, blocks)
    if errs:
        raise WiringError("wiring conformance failed:\n  " + "\n  ".join(errs))

    period = spec["clocking_model"]["controller_clock_period_ns"]
    ports = {b: manifest_ports(b) for b in blocks}

    # Driver ports for the entry stream(s) the sequence drives. seq may be
    # None: the observe paths (init, calibration, boot) are autonomous —
    # they run from reset with no stimulus, and the harness generates its
    # own reset instead of instantiating a driver.
    import sequence_contract as SC
    seq_ifaces = sorted({s["iface"] for s in (seq or {}).get("steps", [])
                         if s.get("op") == "drive"})
    drv_out, drv_in = set(), set()
    for iface in seq_ifaces:
        sp = SC.stimulus_ports(iface, catalog, schemas)
        drv_out |= set(sp["outputs"])
        drv_in |= set(sp["inputs"])
    drv_blocks = {catalog[i]["block"] for i in seq_ifaces}
    missing_blk = drv_blocks - set(blocks)
    if missing_blk:
        raise WiringError(f"the sequence drives {sorted(missing_blk)}, which "
                          f"the path (with support closure) does not include")

    # Net for every source port; sinks connect to their source's net.
    sink_of = {}
    for c in imap["connections"]:
        sink_of[c["to"]] = c["from"]
    for g in imap.get("glue", []):
        for to in g["to"]:
            sink_of[to] = ("__delayed__" + g["from"], g["from"],
                           g.get("delay_cycles", 1))
    # Expression glue: an input computed from several source ports, where no
    # single design port carries the event (e.g. a write-accept strobe).
    expr_of = {e["to"]: e["expr"] for e in imap.get("expr_glue", [])}
    # Stub outputs feed block inputs exactly like connections do.
    active_stubs = [s for s in imap.get("stubs", [])
                    if s.get("when_block") in blocks]
    for s in active_stubs:
        for sport, target in s["outputs"].items():
            sink_of[target] = ("__stub__", s["instance"], sport)

    decls, insts, tieoffs, glue_ff = [], [], [], []
    declared = set()

    def net_for_source(blk, port):
        n = f"{blk}__{port}"
        if n not in declared:
            declared.add(n)
            decls.append(net_decl(n, ports[blk][port][0]))
        return n

    ties = {k: v for k, v in imap.get("ties", {}).items()
            if not k.startswith("$")}

    for b in blocks:
        conns = []
        for pname, (width, pdir) in ports[b].items():
            ref = f"{b}.{pname}"
            if pname == "clk":
                conns.append(f".{pname}(clk)")
                continue
            if pname == "rst_n":
                conns.append(f".{pname}(rst_n)")
                continue
            if pdir == "output":
                conns.append(f".{pname}({net_for_source(b, pname)})")
                continue
            # input port resolution: a real connection whose source block is
            # instantiated wins; then a declared tie (refresh_ctrl.init_done
            # comes from init_fsm when it is in the harness, and falls back
            # to its tie in command-path harnesses that omit it); then
            # expression glue; then the driver; then a zero tie-off.
            def source_present(src):
                if isinstance(src, tuple) and src[0] == "__stub__":
                    return True                      # stubs are pre-filtered
                if isinstance(src, tuple):
                    return src[1].partition(".")[0] in ports
                return src.partition(".")[0] in ports

            if ref in sink_of and source_present(sink_of[ref]):
                src = sink_of[ref]
                if isinstance(src, tuple) and src[0] == "__stub__":
                    _, inst, sport = src
                    n = f"stub__{inst}__{sport}"
                    if n not in declared:
                        declared.add(n)
                        decls.append(net_decl(n, width))
                    conns.append(f".{pname}({n})")
                elif isinstance(src, tuple):
                    _, src_ref, delay = src
                    sb, _, sp = src_ref.partition(".")
                    src_net = net_for_source(sb, sp)
                    dnet = f"dly__{sb}__{sp}"
                    if dnet not in declared:
                        declared.add(dnet)
                        decls.append(net_decl(dnet, ports[sb][sp][0]))
                        glue_ff.append(
                            f"  always_ff @(posedge clk) {dnet} <= {src_net};"
                            f"   // glue: aligns with registered fb pulses")
                    conns.append(f".{pname}({dnet})")
                else:
                    sb, _, sp = src.partition(".")
                    conns.append(f".{pname}({net_for_source(sb, sp)})")
            elif ref in ties:
                n = f"tie__{b}__{pname}"
                if n not in declared:
                    declared.add(n)
                    decls.append(net_decl(n, width))
                    tieoffs.append(f"  assign {n} = {ties[ref]};")
                conns.append(f".{pname}({n})")
            elif ref in expr_of:
                n = f"xg__{b}__{pname}"
                if n not in declared:
                    declared.add(n)
                    decls.append(net_decl(n, width))
                    import re as _re
                    body = _re.sub(
                        r"\b([A-Za-z_]\w*)\.([A-Za-z_]\w*)\b",
                        lambda m: net_for_source(m.group(1), m.group(2)),
                        expr_of[ref])
                    tieoffs.append(f"  assign {n} = {body};   // expr glue")
                conns.append(f".{pname}({n})")
            elif pname in drv_out or pname in drv_in:
                n = f"drv__{pname}"
                if n not in declared:
                    declared.add(n)
                    decls.append(net_decl(n, width))
                conns.append(f".{pname}({n})")
            else:
                n = f"tie__{b}__{pname}"
                if n not in declared:
                    declared.add(n)
                    decls.append(net_decl(n, width))
                    if isinstance(width, str):
                        tieoffs.append(f"  initial {n} = '{{default: '0}};")
                    else:
                        tieoffs.append(f"  assign {n} = '0;")
                conns.append(f".{pname}({n})")
        insts.append(f"  {b} u_{b} (\n    " + ",\n    ".join(conns) + "\n  );")

    for s in active_stubs:
        sconns = []
        for sport, src in s["inputs"].items():
            if src == "@clk":
                sconns.append(f".{sport}(clk)")
            elif src == "@rst_n":
                sconns.append(f".{sport}(rst_n)")
            else:
                sb, _, sp = src.partition(".")
                sconns.append(f".{sport}({net_for_source(sb, sp)})")
        for sport in s["outputs"]:
            n = f"stub__{s['instance']}__{sport}"
            # declared already iff some block input consumes it
            sconns.append(f".{sport}({n})" if n in declared
                          else f".{sport}()")
        insts.append(f"  {s['module']} {s['instance']} (\n    "
                     + ",\n    ".join(sconns) + "\n  );")

    # driver instance: outputs drive drv__ nets; inputs (handshake completes)
    # come from the DUT port that produces them — the sink map's source net.
    if seq is not None:
        drv_conns = [".clk(clk)", ".rst_n_i(rst_n)", ".rst_n(rst_n)",
                     ".done(done)"]
        for p in sorted(drv_out):
            drv_conns.append(f".{p}(drv__{p})")
        for p in sorted(drv_in):
            owners = [b for b in blocks if p in ports[b]
                      and ports[b][p][1] == "output"]
            if not owners:
                raise WiringError(f"driver waits on {p!r}, but no "
                                  f"instantiated block produces it")
            drv_conns.append(f".{p}({net_for_source(owners[0], p)})")
        driver_block = ("  seq_driver u_driver (\n    "
                        + ",\n    ".join(drv_conns) + "\n  );")
        end_block = f"""  initial begin
    wait (done);
    repeat ({settle}) @(posedge clk);
    $display("HARNESS_DONE");
    $finish;
  end"""
    else:
        # Autonomous run: the harness owns reset; `settle` is the whole
        # observation window, counted from reset release.
        driver_block = """  initial begin
    done  = 1'b0;
    rst_n = 1'b0;
    repeat (4) @(negedge clk);
    rst_n = 1'b1;
  end"""
        end_block = f"""  initial begin
    wait (rst_n);
    repeat ({settle}) @(posedge clk);
    $display("HARNESS_DONE");
    $finish;
  end"""
    return f"""`timescale 1ns/1ps
// GENERATED by Validation/structural/chain_harness_gen.py — DO NOT EDIT.
//
// Path     : {path_id}
// Blocks   : {', '.join(blocks)}
// Sequence : {seq.get('name', '?') if seq else '(none — autonomous run from reset)'}
//
// Integration harness generated from integration_map.json. No top level
// exists in the RTL drop; this wiring is validation's, checked against the
// manifests. It checks nothing at runtime — monitors observe, the
// scoreboard and stage checkers judge offline.

module chain_harness;

  logic clk = 1'b0;
  always #{period / 2.0} clk = ~clk;   // {period} ns from spec clocking_model
  logic rst_n;
  logic done;

{chr(10).join(decls)}

{chr(10).join(tieoffs)}

{chr(10).join(glue_ff)}

{driver_block}

{chr(10).join(insts)}

{end_block}

  initial begin
    #{WATCHDOG_NS};
    $display("HARNESS_TIMEOUT after {WATCHDOG_NS} ns — chain wedged");
    $finish;
  end

endmodule
""", blocks


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", help="path id from path_definitions.json")
    ap.add_argument("--sequence", help="stimulus sequence .json")
    ap.add_argument("--check", action="store_true",
                    help="run only the wiring conformance check, all blocks")
    ap.add_argument("--outdir", default=DEFAULT_OUT)
    ap.add_argument("--settle", type=int, default=DEFAULT_SETTLE,
                    help="cycles to keep simulating after the driver is done "
                         "(refresh paths need to outlive tREFI)")
    args = ap.parse_args()

    with open(MAP_PATH) as f:
        imap = json.load(f)

    if args.check:
        blocks = sorted({r.partition(".")[0]
                         for c in imap["connections"]
                         for r in (c["from"], c["to"])})
        errs = check_wiring(imap, blocks)
        if errs:
            print("wiring conformance FAILED:")
            for e in errs:
                print(f"  {e}")
            return 1
        n = len(imap["connections"]) + sum(len(g["to"])
                                           for g in imap.get("glue", []))
        print(f"  {n} connection(s) across {len(blocks)} block(s): every "
              f"port exists, every width and direction agrees.")
        return 0

    if not args.path:
        print("--path is required (or use --check)", file=sys.stderr)
        return 2
    seq = None
    if args.sequence:
        with open(args.sequence) as f:
            seq = json.load(f)
    try:
        sv, blocks = generate(args.path, seq, imap, settle=args.settle)
    except WiringError as e:
        print(f"  {e}", file=sys.stderr)
        return 1
    os.makedirs(args.outdir, exist_ok=True)
    dest = os.path.join(args.outdir, "chain_harness.sv")
    with open(dest, "w") as f:
        f.write(sv)
    print(f"  wrote {os.path.relpath(dest, ROOT)}  "
          f"({len(blocks)} block(s): {', '.join(blocks)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
