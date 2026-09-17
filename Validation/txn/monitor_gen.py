#!/usr/bin/env python3
"""
monitor_gen.py — generate passive SystemVerilog monitors from the schemas
==========================================================================
The fuel line for the transaction architecture. Monitors watch a DUT interface
and print one line per completed transaction; those lines become the observed
trace the scoreboard consumes. Without them nothing can run except hex vectors.

Deterministic codegen, deliberately — not an LLM job. Two reasons, both
learned the hard way on this project:

  * Sampling discipline must be right EVERY time. The old generated testbench
    sampled in the active region at the clock edge, read pre-NBA values, and
    manufactured 176 failures against RTL that was provably correct. A
    template gets the sampling right once; a prompt gets it right on average.
  * A monitor that is subtly wrong is worse than no monitor, because it
    produces confident garbage that looks like evidence.

Monitors are PASSIVE. They declare only inputs, drive nothing, and attach with
`bind`, so neither the DUT nor an existing testbench is modified. That is what
lets them run alongside the current vector-driven testbenches during migration,
and what makes autonomous FSMs observable at all.

Emitted line format (one per completed transaction):

    TXN <iface> <kind> t=<sim_time> <field>=<hex> <field>=<hex> ...

Usage:
    python3 Validation/txn/monitor_gen.py                 # all interfaces
    python3 Validation/txn/monitor_gen.py --iface csr
    python3 Validation/txn/monitor_gen.py --outdir <dir>
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CATALOG = os.path.join(HERE, "interface_catalog.json")
SCHEMAS = os.path.join(HERE, "generated", "schemas.json")
DEFAULT_OUT = os.path.join(HERE, "generated", "monitors")

# The delay after the clock edge at which a monitor samples. Sampling at the
# edge itself reads pre-NBA values — the exact defect that fabricated 176
# failures in config_regs. #1 places the read after non-blocking assignments
# have committed, which the diagnostic probe proved correct on this design.
SAMPLE_DELAY = 1


EDGE_LABEL = {None: "", "rising": " (rising edge only)",
              "change": " (emit only when the observed state changes)"}


class MonitorGenError(Exception):
    """Raised when a monitor cannot be generated. Never emit a wrong one."""


def _all_ports(iface_schema):
    """Every distinct DUT port this interface's transactions reference,
    as {port: (width, dir)}."""
    ports = {}
    for kind, fields in iface_schema["kinds"].items():
        for fname, info in fields.items():
            ports[info["port"]] = (info["width"], info["dir"])
    return ports


# SystemVerilog sized literals (4'b0111, 8'hFF) must be stripped before
# hunting for identifiers, or their base/digits parse as signal names.
_SV_LITERAL = re.compile(r"\d*'[bdhoBDHO][0-9a-fA-FxzXZ_]+")
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_SV_KEYWORDS = {"and", "or", "not", "if", "else", "begin", "end", "posedge",
                "negedge", "logic", "wire", "reg", "inside", "signed", "unsigned"}


def expression_ports(expr, manifest_ports, iface, what):
    """Identifiers in a catalog expression that are real DUT ports.

    Every identifier must resolve against the block's manifest. An expression
    naming a port that does not exist is a hard error, never a monitor that
    silently fails to compile later or, worse, binds to the wrong net."""
    stripped = _SV_LITERAL.sub(" ", expr)
    found, missing = [], []
    for tok in _IDENT.findall(stripped):
        if tok in _SV_KEYWORDS:
            continue
        if tok in manifest_ports:
            if tok not in found:
                found.append(tok)
        else:
            missing.append(tok)
    if missing:
        raise MonitorGenError(
            f"{iface}: {what} expression {expr!r} names {sorted(set(missing))}, "
            f"which is not a port of {iface}'s block. The design changed or the "
            f"catalog is stale — update interface_catalog.json.")
    return found


def load_manifest_ports(manifest_rel):
    """{port_name: width} for a block, from its frontend manifest."""
    path = os.path.join(ROOT, manifest_rel)
    with open(path) as f:
        m = json.load(f)
    out = {}
    for grp, plist in m["ports"].items():
        for port in plist:
            w = port["width"]
            # Array widths arrive as "NxM" strings. Keep them as-is: a port
            # can legitimately appear in a qualifier expression without being
            # a transaction field, and _decl() raises a useful error if one is
            # actually used as a field.
            try:
                out[port["name"]] = int(w)
            except (TypeError, ValueError):
                out[port["name"]] = w
    return out


def _decl(name, width):
    """One monitor port declaration.

    Manifests express an array port as "NxM" (e.g. bank_open_row is "8x15":
    eight 15-bit rows). Those are DUT *state*, not transaction fields — a
    single $display cannot flatten one, and packing 120 bits into a
    transaction field would be inventing a transaction the interface does not
    have. Refuse rather than emit something that will not compile."""
    if isinstance(width, str):
        raise MonitorGenError(
            f"port {name!r} has array width {width!r}. Array-shaped ports carry "
            f"continuous state, not transactions — they cannot be a transaction "
            f"field. Either drop {name!r} from the interface's kinds, or give "
            f"this scope a check_strategy of 'invariant'/'observe', where state "
            f"is checked by assertions rather than compared as a stream.")
    rng = "" if width == 1 else f"[{width - 1}:0] "
    return f"    input  logic {rng}{name}"


def generate_monitor(iface, cat_entry, schema_entry):
    """Return (module_name, systemverilog_source) for one interface."""
    for required in ("qualifier", "clock", "reset"):
        if required not in cat_entry:
            raise MonitorGenError(
                f"{iface}: interface_catalog.json has no {required!r}. A monitor "
                f"cannot know when a transaction completes without a qualifier, "
                f"nor when to sample without a clock. Add it to the catalog.")

    clk, rst = cat_entry["clock"], cat_entry["reset"]
    active_low = cat_entry.get("reset_active_low", True)
    qual = cat_entry["qualifier"]
    kinds = schema_entry["kinds"]
    ksel = cat_entry.get("kind_select")

    if len(kinds) > 1 and not ksel:
        raise MonitorGenError(
            f"{iface}: {len(kinds)} transaction kinds ({sorted(kinds)}) but no "
            f"'kind_select' in the catalog. The monitor cannot tell which kind "
            f"occurred. Add kind_select with an expression and a value map.")
    if ksel:
        unknown = set(ksel["map"].values()) - set(kinds)
        if unknown:
            raise MonitorGenError(
                f"{iface}: kind_select maps to unknown kind(s) {sorted(unknown)}; "
                f"schema defines {sorted(kinds)}.")

    ports = {p: w for p, (w, d) in _all_ports(schema_entry).items()}
    mod = f"{iface}_monitor"

    # The qualifier and kind_select expressions reference DUT ports too — they
    # are how the monitor knows a transaction happened and which kind it was.
    # Those ports must be declared or the module will not compile.
    manifest_ports = load_manifest_ports(schema_entry["manifest"])
    for expr, what in [(qual, "qualifier")] + (
            [(ksel["expr"], "kind_select")] if ksel else []):
        for port in expression_ports(expr, manifest_ports, iface, what):
            ports.setdefault(port, manifest_ports[port])

    # --- port list: clock, reset, then every referenced signal --------------
    decls = [_decl(clk, 1), _decl(rst, 1)]
    for p in sorted(ports):
        if p in (clk, rst):
            continue
        decls.append(_decl(p, ports[p]))

    # --- one $display per kind ---------------------------------------------
    def display_for(kind):
        fields = kinds[kind]
        names = sorted(fields)
        fmt = " ".join(f"{n}=%0h" for n in names)
        args = ", ".join(fields[n]["port"] for n in names)
        return (f'$display("TXN {iface} {kind} t=%0t {fmt}", $time, {args});'
                if args else
                f'$display("TXN {iface} {kind} t=%0t", $time);')

    if ksel:
        branches = []
        for value, kind in sorted(ksel["map"].items(), key=lambda kv: kv[0], reverse=True):
            cond = f"({ksel['expr']}) == {value}"
            branches.append((cond, kind))
        body_lines = []
        for i, (cond, kind) in enumerate(branches):
            kw = "if" if i == 0 else "else if"
            body_lines.append(f"        {kw} ({cond})")
            body_lines.append(f"          {display_for(kind)}")
        body = "\n".join(body_lines)
    else:
        only = next(iter(kinds))
        body = f"        {display_for(only)}"

    rst_cond = f"{rst}" if active_low else f"!{rst}"

    # Some interfaces are qualified by a LEVEL that stays high (init_done,
    # cal_done, ref_required). Emitting every cycle it is high would flood the
    # trace with duplicates of one event. `qualifier_edge: rising` emits once,
    # on the 0->1 transition, using a monitor-local register. The register is
    # internal state — the monitor still drives nothing in the DUT.
    edge = cat_entry.get("qualifier_edge")
    if edge not in (None, "rising", "change"):
        raise MonitorGenError(
            f"{iface}: qualifier_edge {edge!r} is not supported (use 'rising', "
            f"'change', or omit for a level qualifier).")

    if edge == "change":
        # A LEVEL input stream: the fields carry continuously-valid state
        # rather than pulses. Emitting every cycle would flood the trace;
        # emitting only when the value changes gives a predictor exactly the
        # updates it needs to track the state. Tracked expression is the
        # concatenation of this kind's field ports.
        if len(kinds) != 1:
            raise MonitorGenError(
                f"{iface}: qualifier_edge 'change' needs exactly one kind "
                f"(found {sorted(kinds)}); a level stream has one shape.")
        only_kind = next(iter(kinds))
        fports = [kinds[only_kind][f]["port"] for f in sorted(kinds[only_kind])]
        fwidths = [kinds[only_kind][f]["width"] for f in sorted(kinds[only_kind])]
        if any(isinstance(w, str) for w in fwidths):
            raise MonitorGenError(
                f"{iface}: change-detection cannot concatenate array-shaped "
                f"ports; those carry state checked by assertions instead.")
        total = sum(int(w) for w in fwidths)
        concat = "{" + ", ".join(fports) + "}"
        edge_decl = f"  logic [{total - 1}:0] {iface}_prev;\n\n"
        fire_cond = f"({qual}) && ({concat} !== {iface}_prev)"
        edge_track = (f"\n    {iface}_prev <= {rst_cond} ? {concat} : "
                      f"{total}'b0;")
    elif edge == "rising":
        edge_decl = f"  logic {iface}_qual_prev;\n\n"
        fire_cond = f"({qual}) && !{iface}_qual_prev"
        edge_track = f"\n    {iface}_qual_prev <= {rst_cond} ? ({qual}) : 1'b0;"
    elif edge is None:
        edge_decl, fire_cond, edge_track = "", f"({qual})", ""
    port_block = ",\n".join(decls)     # joined here: an f-string expression
                                        # may not contain a backslash pre-3.12

    src = f"""// GENERATED by Validation/txn/monitor_gen.py — DO NOT EDIT BY HAND.
// Regenerate after any change to interface_catalog.json or the frontend
// manifests. Source of truth: generated/schemas.json.
//
// Interface : {iface}   ({schema_entry.get('description', '')})
// Block     : {schema_entry['block']}
// Manifest  : {schema_entry.get('manifest', '?')}
// Emits     : one TXN line per completed transaction, consumed by
//             Validation/txn/trace_extract.py -> observed.jsonl -> scoreboard.
//
// PASSIVE: declares only inputs and drives nothing. Attach with the bind
// statement in the generated bind file; the DUT and any existing testbench
// are left untouched.

module {mod} #(
    // Sampling offset after the clock edge. Reading AT the edge returns
    // pre-NBA values — the defect that fabricated 176 failures in config_regs.
    parameter int SAMPLE_DELAY = {SAMPLE_DELAY}
) (
{port_block}
);

  // A reset is a real event a stateful predictor must see. Without it the
  // model keeps state the DUT has just cleared and diverges permanently —
  // silently, and for the rest of the run.
  always @(negedge {rst}) begin
    $display("TXN {iface} reset t=%0t", $time);
  end

{edge_decl}  // Transaction detected when: {qual}{EDGE_LABEL[edge]}
  always @(posedge {clk}) begin
    #SAMPLE_DELAY;                 // sample after non-blocking assignments commit
    if ({rst_cond} && {fire_cond}) begin
{body}
    end{edge_track}
  end

endmodule
"""
    return mod, src


def generate_bind(entries):
    """One bind file attaching every generated monitor to its block."""
    lines = [
        "// GENERATED by Validation/txn/monitor_gen.py — DO NOT EDIT BY HAND.",
        "//",
        "// Compile this alongside the DUT and the monitor modules. `bind`",
        "// attaches each monitor inside its target module without modifying",
        "// the DUT or the testbench, so monitors can run alongside the",
        "// existing vector-driven testbenches during migration.",
        "//",
        "// .* connects each monitor port to the same-named net in the bound",
        "// scope; monitor ports are named exactly after the DUT ports, so the",
        "// match is total. A rename in the RTL becomes a compile error here",
        "// rather than a silently unconnected monitor.",
        "",
    ]
    for iface, block, mod in entries:
        lines.append(f"bind {block} {mod} u_{iface}_mon (.*);")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", default=CATALOG)
    ap.add_argument("--schemas", default=SCHEMAS)
    ap.add_argument("--outdir", default=DEFAULT_OUT)
    ap.add_argument("--iface", help="generate only this interface")
    args = ap.parse_args()

    with open(args.catalog) as f:
        catalog = json.load(f)["interfaces"]
    with open(args.schemas) as f:
        schemas = json.load(f)["interfaces"]

    names = [args.iface] if args.iface else sorted(schemas)
    os.makedirs(args.outdir, exist_ok=True)

    written, entries, errors = [], [], []
    for iface in names:
        if iface not in schemas:
            errors.append(f"{iface}: not in generated schemas. Run schema_gen.py.")
            continue
        try:
            mod, src = generate_monitor(iface, catalog[iface], schemas[iface])
        except MonitorGenError as e:
            errors.append(str(e))
            continue
        path = os.path.join(args.outdir, f"{mod}.sv")
        with open(path, "w") as f:
            f.write(src)
        written.append(path)
        entries.append((iface, schemas[iface]["block"], mod))

    if errors:
        print("monitor generation FAILED:")
        for e in errors:
            print(f"  {e}")
        return 1

    bind_path = os.path.join(args.outdir, "monitors_bind.sv")
    with open(bind_path, "w") as f:
        f.write(generate_bind(entries))

    print(f"wrote {len(written)} monitor(s) -> {os.path.relpath(args.outdir, ROOT)}")
    for iface, block, mod in entries:
        print(f"  {mod:20} bind into {block}")
    print(f"  {os.path.basename(bind_path):20} {len(entries)} bind statement(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
