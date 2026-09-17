#!/usr/bin/env python3
"""
sva_gen.py — generate independent timing and protocol assertions from the spec
===============================================================================
The "when" oracle. The scoreboard checks WHAT happened and in what order and
is deliberately blind to timing; these assertions supply the rest. Without
them a design could violate every DDR3 timing constraint and the flow would
report a clean pass — which is the state the project is in today, since the
generated testbenches contain no assertions at all.

Deterministic codegen, for the same reason the monitors are: the numbers are
already in the spec. `timing_model.tRCD` is 13.75ns and the controller clock
is 5.0ns, so the separation is ceil(13.75/5) = 3 cycles. There is no judgement
for a model to contribute, and a subtly wrong assertion is worse than none —
it fires on correct behaviour and trains people to ignore it.

INDEPENDENCE IS THE POINT. The design's own bank_tracker already asserts

    cmd_rd_valid |-> (ctr_rcd[cmd_rd_bank] == '0)

which checks the design against its own counter: load that counter with the
wrong value and the assertion agrees with the bug. Every assertion generated
here instead counts elapsed cycles from the OBSERVED command stream and
compares against a bound recomputed from the spec. It never references a DUT
counter, permission signal, or state register.

A note on units. The spec's $derived_cycles are in nCK (DDR clocks, 1.25ns)
while commands are issued on the controller clock (5.0ns). Deriving the bounds
from the spec's NANOSECOND values sidesteps that mismatch and states the
physical requirement JESD79-3 actually imposes.

Usage:
    python3 Validation/sva/sva_gen.py
    python3 Validation/sva/sva_gen.py --outdir <dir>
"""

import argparse
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
RULES_PATH = os.path.join(HERE, "sva_rules.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
DEFAULT_OUT = os.path.join(HERE, "generated")


class SvaGenError(Exception):
    """Never emit an assertion that cannot be justified from the spec."""


def spec_value(spec, path):
    """A value from the spec by dotted path; bare names are timing_model
    parameters (the common case), so 'tRCD' and
    'initialization_sequence.tZQinit_ns' both resolve."""
    parts = path.split(".") if "." in path else ["timing_model", path]
    cur = spec
    for p in parts:
        if not isinstance(cur, dict) or p not in cur:
            where = ".".join(parts[:-1])
            have = cur if isinstance(cur, dict) else {}
            raise SvaGenError(
                f"spec has no {path!r}; an assertion bounded by it cannot be "
                f"generated. Available under {where!r}: "
                f"{sorted(k for k in have if not k.startswith('$'))}")
        cur = cur[p]
    return cur


def cycles_for(spec, param):
    """Separation in controller cycles required by a spec timing value (ns)."""
    ns = spec_value(spec, param)
    period = spec.get("clocking_model", {}).get("controller_clock_period_ns")
    if not period:
        raise SvaGenError("clocking_model.controller_clock_period_ns is required "
                          "to convert a timing parameter into cycles.")
    return math.ceil(float(ns) / float(period)), float(ns), float(period)


def interval_bound(spec, rule):
    """(cycles, ns, period, multiplier, bound) for a max-interval rule: the
    parameter in cycles times how many occurrences the spec lets the design
    postpone, plus one."""
    n, ns, period = cycles_for(spec, rule["param"])
    mult = 1
    m = rule.get("multiplier")
    if m:
        mult = int(spec_value(spec, m["spec_path"])) + int(m.get("plus", 0))
    return n, ns, period, mult, n * mult


def cmd_match(enc, names, sig):
    """SystemVerilog expression: the command signal is one of these."""
    missing = [n for n in names if n not in enc]
    if missing:
        raise SvaGenError(f"command encoding has no entry for {missing}; "
                          f"known: {sorted(k for k in enc if not k.startswith('$'))}")
    if len(names) == 1:
        return f"({sig} == {enc[names[0]]})"
    return "(" + " || ".join(f"{sig} == {enc[n]}" for n in names) + ")"


def gen_separation(rule, spec, enc, sig, bank):  # noqa: C901
    n, ns, period = cycles_for(spec, rule["param"])
    free = n - 1
    rid, param = rule["id"], rule["param"]
    frm = cmd_match(enc, rule["from"], sig)
    to = cmd_match(enc, rule["to"], sig)
    same = rule.get("same_bank")

    if free <= 0:
        return (f"  // {rid} ({param} = {ns}ns = {n} cycle(s) at {period}ns): "
                f"no separation required beyond the issue cycle itself, so no\n"
                f"  // assertion is generated. Generating `[*0]` would be a "
                f"property that is always true —\n"
                f"  // an assertion that cannot fail is worse than none, "
                f"because it looks like coverage.\n")

    if same is True:
        cond = f"{to} && ({bank} == b)"
        decl = "    logic [BANK_W-1:0] b;\n"
        trig = f"({frm}, b = {bank})"
        rel = "to the same bank"
    elif same is False:
        cond = f"{to} && ({bank} != b)"
        decl = "    logic [BANK_W-1:0] b;\n"
        trig = f"({frm}, b = {bank})"
        rel = "to a different bank"
    else:
        cond = to
        decl = ""
        trig = frm
        rel = "on any bank"

    return f"""  // ---- {rid} -------------------------------------------------------
  // {rule['requirement']}
  // Bound: {param} = {ns}ns; at a {period}ns controller clock that is
  // ceil({ns}/{period}) = {n} cycle(s) of separation, so {free} cycle(s)
  // between the two commands must be free of the second command {rel}.
  // Counted from the observed command stream — no DUT counter is consulted.
  property p_{rid};
{decl}    @(posedge clk) disable iff (!rst_n)
    {trig} |=> !({cond})[*{free}];
  endproperty
  a_{rid}: assert property (p_{rid})
    else $error("[{rid}] {param} violation: {rule['requirement']}");
  c_{rid}: cover property (p_{rid});

"""


def gen_window(rule, spec, enc, sig):
    n, ns, period = cycles_for(spec, rule["param"])
    rid, mx = rule["id"], rule["max_in_window"]
    act = cmd_match(enc, [rule["command"]], sig)
    return f"""  // ---- {rid} -------------------------------------------------------
  // {rule['requirement']}
  // Bound: {rule['param']} = {ns}ns = {n} cycle(s) at {period}ns. At most
  // {mx} {rule['command']} commands may fall in any window of that length.
  // A sliding count, not a pairwise separation: kept as a shift register
  // over the window so the check is over the whole window, not one pair.
  logic [{n - 1}:0] {rid.lower()}_hist;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) {rid.lower()}_hist <= '0;
    else        {rid.lower()}_hist <= {{{rid.lower()}_hist[{n - 2}:0], {act}}};
  end

  property p_{rid};
    @(posedge clk) disable iff (!rst_n)
    {act} |-> ($countones({rid.lower()}_hist) < {mx});
  endproperty
  a_{rid}: assert property (p_{rid})
    else $error("[{rid}] {rule['param']} violation: more than {mx} {rule['command']} in the window");
  c_{rid}: cover property (p_{rid});

"""


def gen_max_interval(rule, spec, enc, sig):
    """A MAXIMUM interval between occurrences of one command (tREFI): the
    design must issue the next one within the bound. Armed by the first
    occurrence, because the window before it (initialisation) has its own
    length; one error per missed interval, on the cycle the gap first
    exceeds the bound."""
    n, ns, period, mult, bound = interval_bound(spec, rule)
    rid, cmd_name, param = rule["id"], rule["command"], rule["param"]
    cmd = cmd_match(enc, [cmd_name], sig)
    lo = rid.lower()
    m = rule.get("multiplier", {})
    return f"""  // ---- {rid} -------------------------------------------------------
  // {rule['requirement']}
  // Bound: {param} = {ns}ns = {n} cycle(s) at {period}ns; the spec allows
  // {mult - 1} occurrence(s) to be postponed ({m.get('spec_path', 'none')}), so
  // consecutive {cmd_name} commands may be at most {mult} x {n} = {bound}
  // cycles apart. Counted from the observed command stream; armed by the
  // first {cmd_name} seen after reset.
  logic [31:0] {lo}_since;
  logic        {lo}_armed;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      {lo}_since <= '0;
      {lo}_armed <= 1'b0;
    end else if ({cmd}) begin
      {lo}_since <= '0;
      {lo}_armed <= 1'b1;
    end else if ({lo}_since != 32'hFFFF_FFFF) begin
      {lo}_since <= {lo}_since + 1;
    end
  end

  property p_{rid};
    @(posedge clk) disable iff (!rst_n)
    !({lo}_armed && {lo}_since == {bound + 1});
  endproperty
  a_{rid}: assert property (p_{rid})
    else $error("[{rid}] {param} violation: {rule['requirement']}");
  // The interesting event: a {cmd_name} that was postponed past {param}.
  c_{rid}: cover property (@(posedge clk) disable iff (!rst_n)
    {cmd} && {lo}_armed && {lo}_since > {n});

"""


def gen_state(rule, spec, enc, sig, bank, nbanks):
    rid = rule["id"]
    act = cmd_match(enc, ["ACT"], sig)
    cas = cmd_match(enc, ["RD", "WR"], sig)

    if rule["kind"] == "cas_requires_open_row":
        body = f"""  property p_{rid};
    @(posedge clk) disable iff (!rst_n)
    {cas} |-> row_open[{bank}];
  endproperty"""
        msg = "READ/WRITE to a bank with no active row"
    elif rule["kind"] == "no_double_activate":
        body = f"""  property p_{rid};
    @(posedge clk) disable iff (!rst_n)
    {act} |-> !row_open[{bank}];
  endproperty"""
        msg = "ACTIVATE to a bank that already has an open row"
    else:
        raise SvaGenError(f"{rid}: unknown state rule kind {rule['kind']!r}")

    return f"""  // ---- {rid} -------------------------------------------------------
  // {rule['requirement']}
  // Row-open state is tracked below from the OBSERVED ACT/PRE stream, never
  // read from the design's own bank state — a wrong state machine must not
  // be able to excuse itself.
{body}
  a_{rid}: assert property (p_{rid})
    else $error("[{rid}] {msg}");
  c_{rid}: cover property (p_{rid});

"""


GROUP_KEYS = ("min_separation_rules", "window_rules", "state_rules",
              "max_interval_rules")


def command_groups(rules):
    """The primary command stream (top-level keys) plus any extra command
    groups (e.g. the init FSM's own command stream), each a dict with
    command_signals and the four rule lists."""
    primary = {"name": "primary", "command_signals": rules["command_signals"]}
    for k in GROUP_KEYS:
        primary[k] = rules.get(k, [])
    groups = [primary]
    for g in rules.get("command_groups", []):
        grp = {"name": g["name"], "command_signals": g["command_signals"]}
        for k in GROUP_KEYS:
            grp[k] = g.get(k, [])
        groups.append(grp)
    return groups


def generate(spec, rules, catalog, schemas):
    iface = rules["command_signals"]["interface"]
    if iface not in schemas:
        raise SvaGenError(f"interface {iface!r} is not in the generated schemas; "
                          f"run schema_gen.py first.")
    enc = catalog[iface].get("command_encoding")
    if not enc:
        raise SvaGenError(
            f"interface_catalog.json has no command_encoding for {iface!r}. "
            f"Assertions cannot recognise a command without knowing how this "
            f"design encodes one.")

    kind = next(iter(schemas[iface]["kinds"]))
    fields = schemas[iface]["kinds"][kind]
    sig = fields[rules["command_signals"]["cmd_field"]]["port"]
    bank = fields[rules["command_signals"]["bank_field"]]["port"]
    bank_w = fields[rules["command_signals"]["bank_field"]]["width"]
    nbanks = 1 << int(spec["memory_geometry"]["bank_bits"])
    block = schemas[iface]["block"]

    act = cmd_match(enc, ["ACT"], sig)
    pre = cmd_match(enc, ["PRE"], sig)
    addr_f = rules["command_signals"].get("addr_field")
    pa_bit = rules["command_signals"].get("precharge_all_bit")
    if rules["state_rules"] and (addr_f is None or pa_bit is None):
        raise SvaGenError(
            "state rules need command_signals.addr_field and "
            "precharge_all_bit to model precharge-all; without them the "
            "bank-state tracker is wrong and the assertions false-fire.")
    addr = fields[addr_f]["port"] if addr_f else None

    body = ""
    for r in rules["min_separation_rules"]:
        body += gen_separation(r, spec, enc, sig, bank)
    for r in rules["window_rules"]:
        body += gen_window(r, spec, enc, sig)
    for r in rules["max_interval_rules"]:
        body += gen_max_interval(r, spec, enc, sig)
    if rules["state_rules"]:
        body += f"""  // ---- observed bank state, for the protocol rules below ----------
  // Reconstructed from the command stream. The design's own bank_open_row is
  // deliberately NOT used: an assertion that reads the state it is checking
  // proves only that the design is self-consistent.
  // A PRECHARGE with A{pa_bit} high closes EVERY bank (JESD79-3), not just the
  // addressed one. Tracking only the addressed bank would leave banks marked
  // open after they were closed, and the protocol assertions below would then
  // fire on correct behaviour.
  logic [{nbanks - 1}:0] row_open;
  wire pre_all = {pre} && {addr}[{pa_bit}];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)        row_open <= '0;
    else if (pre_all)  row_open <= '0;
    else if ({act})    row_open[{bank}] <= 1'b1;
    else if ({pre})    row_open[{bank}] <= 1'b0;
  end

"""
    for r in rules["state_rules"]:
        body += gen_state(r, spec, enc, sig, bank, nbanks)

    ids = ([r["id"] for r in rules["min_separation_rules"]]
           + [r["id"] for r in rules["window_rules"]]
           + [r["id"] for r in rules["max_interval_rules"]]
           + [r["id"] for r in rules["state_rules"]])
    addr_port = (f",\n    input logic [{fields[addr_f]['width'] - 1}:0] {addr}"
                 if addr_f else "")

    header = f"""`timescale 1ns/1ps
// GENERATED by Validation/sva/sva_gen.py — DO NOT EDIT BY HAND.
// Regenerate after any change to the spec or Validation/sva/sva_rules.json.
//
// Spec revision : {spec.get('revision')}
// Bound to      : {block} (via the bind statement in {block}_sva_bind.sv)
// Covers        : {', '.join(ids)}
//
// Every bound below is recomputed from the spec's nanosecond timing values
// and the controller clock period, not copied from a table. These assertions
// consult NO signal of the design except the command stream itself.

module {block}_sva #(
    parameter int BANK_W = {bank_w}
) (
    input logic clk,
    input logic rst_n,
    input logic [{fields[rules['command_signals']['cmd_field']]['width'] - 1}:0] {sig},
    input logic [{bank_w - 1}:0] {bank}{addr_port}
);

"""
    return f"{block}_sva", header + body + "endmodule\n", block, ids


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", default=DEFAULT_OUT)
    args = ap.parse_args()

    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(RULES_PATH) as f:
        rules = json.load(f)
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]

    os.makedirs(args.outdir, exist_ok=True)
    for grp in command_groups(rules):
        try:
            mod, src, block, ids = generate(spec, grp, catalog, schemas)
        except SvaGenError as e:
            print(f"SVA generation failed ({grp['name']} group): {e}",
                  file=sys.stderr)
            return 1

        path = os.path.join(args.outdir, f"{mod}.sv")
        with open(path, "w") as f:
            f.write(src)
        bind = os.path.join(args.outdir, f"{block}_sva_bind.sv")
        with open(bind, "w") as f:
            f.write(f"""// GENERATED by Validation/sva/sva_gen.py — DO NOT EDIT BY HAND.
// Attaches the generated assertions inside {block} without modifying it.
bind {block} {mod} u_{block}_sva (.*);
""")

        n_assert = src.count("assert property")
        n_cover = src.count("cover property")
        print(f"  wrote {os.path.relpath(path, ROOT)}  [{grp['name']} group, "
              f"{grp['command_signals']['interface']}]")
        print(f"    {n_assert} assertion(s), {n_cover} cover point(s)")
        print(f"    taxonomy IDs: {', '.join(ids)}")
        print(f"  wrote {os.path.relpath(bind, ROOT)}")
        skipped = [r["id"] for r in grp["min_separation_rules"]
                   if cycles_for(spec, r["param"])[0] - 1 <= 0]
        if skipped:
            print(f"    not generated (no separation required at this clock): "
                  f"{', '.join(skipped)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
