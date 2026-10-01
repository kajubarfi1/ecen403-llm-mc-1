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
import re
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SPEC_PATH = os.environ.get("VALIDATION_SPEC", SPEC_PATH)   # the spec the drop was generated from, when it is not the default
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


# Which clock the assertions are sampled on. "controller": the command stream
# is observed at the controller clock (this design's cmd_gen output).
# "ddr": the stream is observed at the DRAM pins, one command per tCK (a PHY
# that serialises several controller-cycle slots, or a known-good reference
# design watched at its DDR3 pins).
CLOCK_DOMAIN = "controller"
MODULE_SUFFIX = ""
CLOCK_KEY = {"controller": "controller_clock_period_ns", "ddr": "ddr_clock_period_ns"}


def cycles_for(spec, param):
    """Separation in cycles of the selected clock required by a spec timing
    value (ns)."""
    ns = spec_value(spec, param)
    key = CLOCK_KEY[CLOCK_DOMAIN]
    period = spec.get("clocking_model", {}).get(key)
    if not period:
        raise SvaGenError(f"clocking_model.{key} is required "
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
  // Bound: {param} = {ns}ns; at a {period}ns {CLOCK_DOMAIN} clock that is
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
  // Initialised at declaration as well as on reset: a testbench whose reset
  // is X or still high for the first cycles must not see X here and fail
  // (an X in the checked expression is a failure, not a don't-care).
  logic [31:0] {lo}_since = '0;
  logic        {lo}_armed = 1'b0;
  always @(posedge clk or negedge rst_n) begin   // plain always: initialiser + always_ff would be two drivers
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


def gen_event(rule, spec, enc, sig):
    """A level or pulse (not a command) that must not rise until a timing
    parameter has elapsed after a command: init_done after ZQCL (tZQinit).
    Command-to-command spacing cannot see this — the event is not on the
    command pins — so without it a controller that declares initialisation
    complete a few cycles after ZQCL passes every command rule."""
    n, ns, period = cycles_for(spec, rule["param"])
    rid, ev = rule["id"], rule["event"]
    cmd = cmd_match(enc, [rule["after"]], sig)
    return f"""  // ---- {rid} ({ev} after {rule['after']}) --------------------------------
  // {rule['requirement']}
  // Bound: {rule['param']} = {ns}ns = {n} cycle(s) at {period}ns: {ev} must
  // not rise within that many cycles of the {rule['after']} that starts it.
  property p_{rid}_{ev};
    @(posedge clk) disable iff (!rst_n)
    {cmd} |-> !{ev} ##1 (!{ev})[*{n - 1}];
  endproperty
  a_{rid}_{ev}: assert property (p_{rid}_{ev})
    else $error("[{rid}] {rule['param']} violation: {ev} raised within {n} cycles of {rule['after']}");
  c_{rid}_{ev}: cover property (@(posedge clk) disable iff (!rst_n) {cmd} ##[{n}:$] $rose({ev}));

"""


def gen_sequence(rule, spec, enc, sig, bank):
    """An ordered sequence the spec states in prose (the init sequence:
    MR2, MR3, MR1, MR0, then ZQCL, then the completion event). The order is
    parsed from the spec's own sentence, so a spec with a different order
    regenerates different assertions. Properties:
      <id>        the k-th <ordered_command> carries the k-th value of
                  <order_field>, and <then> is not issued before all of them
      <event_id>  <event> does not rise before <then> was issued"""
    text = spec_value(spec, rule["order_from_spec"])
    order = [int(m) for m in re.findall(rule.get("token_regex", r"MR(\d)"), str(text))]
    if not order:
        raise SvaGenError(f"{rule['id']}: {rule['order_from_spec']} names no "
                          f"{rule['ordered_command']} steps to order")
    rid, ev, lo = rule["id"], rule.get("event"), rule["id"].lower()
    ocmd = cmd_match(enc, [rule["ordered_command"]], sig)
    then = cmd_match(enc, [rule["then"]], sig)
    n = len(order)
    table = ", ".join(str(b) for b in order)
    body = f"""  // ---- {rid} ({rule['ordered_command']} order from {rule['order_from_spec']}) ----
  // {rule['requirement']}
  // Parsed order of {rule['order_field']} values: {table}; then {rule['then']}.
  logic [7:0] {lo}_step;
  logic       {lo}_then_seen;
  localparam logic [BANK_W-1:0] {lo}_order [{n}] = '{{{table}}};
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      {lo}_step <= '0;
      {lo}_then_seen <= 1'b0;
    end else begin
      if ({ocmd}) {lo}_step <= {lo}_step + 1;
      if ({then}) {lo}_then_seen <= 1'b1;
    end
  end
  property p_{rid};
    @(posedge clk) disable iff (!rst_n)
    {ocmd} |-> ({lo}_step < {n}) && ({bank} == {lo}_order[{lo}_step]);
  endproperty
  a_{rid}: assert property (p_{rid})
    else $error("[{rid}] {rule['ordered_command']} out of the spec's order");
  property p_{rid}_then;
    @(posedge clk) disable iff (!rst_n)
    {then} |-> ({lo}_step == {n});
  endproperty
  a_{rid}_then: assert property (p_{rid}_then)
    else $error("[{rid}] {rule['then']} issued before every {rule['ordered_command']} step");
  c_{rid}: cover property (@(posedge clk) disable iff (!rst_n) {then} && {lo}_step == {n});

"""
    if ev:
        did = rule.get("event_id", rid)
        body += f"""  // ---- {did} ({ev} before the sequence finished) --------------------------
  property p_{did}_{ev};
    @(posedge clk) disable iff (!rst_n)
    $rose({ev}) |-> {lo}_then_seen;
  endproperty
  a_{did}_{ev}: assert property (p_{did}_{ev})
    else $error("[{did}] {ev} raised before {rule['then']} was issued");

"""
    return body


def gen_state(rule, spec, enc, sig, bank, nbanks):
    rid = rule["id"]
    act = cmd_match(enc, ["ACT"], sig)
    cas = cmd_match(enc, ["RD", "WR"], sig)

    if rule["kind"] == "cas_requires_open_row":
        rd = cmd_match(enc, ["RD"], sig)
        body = f"""  property p_{rid};
    @(posedge clk) disable iff (!rst_n)
    {cas} |-> (row_open[{bank}] || (mpr_en && {rd}));
  endproperty"""
        msg = "READ/WRITE to a bank with no active row (and not an MPR read)"
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
              "max_interval_rules", "event_rules", "sequence_rules")


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
    mrs = cmd_match(enc, ["MRS"], sig)
    addr_f = rules["command_signals"].get("addr_field")
    pa_bit = rules["command_signals"].get("precharge_all_bit")
    # JESD79-3: MRS selects the mode register with the bank address pins;
    # MR3 is BA=3 and its A2 enables Multi-Purpose Register reads.
    mr3_sel = rules["command_signals"].get("mr3_bank_select", 3)
    mpr_bit = rules["command_signals"].get("mpr_enable_bit", 2)
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
    for r in rules["event_rules"]:
        body += gen_event(r, spec, enc, sig)
    for r in rules["sequence_rules"]:
        body += gen_sequence(r, spec, enc, sig, bank)
    if rules["state_rules"]:
        body += f"""  // ---- observed bank state, for the protocol rules below ----------
  // Reconstructed from the command stream. The design's own bank_open_row is
  // deliberately NOT used: an assertion that reads the state it is checking
  // proves only that the design is self-consistent.
  // A PRECHARGE with A{pa_bit} high closes EVERY bank (JESD79-3), not just the
  // addressed one. Tracking only the addressed bank would leave banks marked
  // open after they were closed, and the protocol assertions below would then
  // fire on correct behaviour.
  logic [{nbanks - 1}:0] row_open = '0;
  wire pre_all = {pre} && {addr}[{pa_bit}];
  always @(posedge clk or negedge rst_n) begin   // plain always: initialiser + always_ff would be two drivers
    if (!rst_n)        row_open <= '0;
    else if (pre_all)  row_open <= '0;
    else if ({act})    row_open[{bank}] <= 1'b1;
    else if ({pre})    row_open[{bank}] <= 1'b0;
  end
  // Multi-Purpose Register mode (JESD79-3 MR3 A2): while enabled, READs return
  // the MPR pattern and need no open row — this is how a controller calibrates
  // its read path during initialisation. Tracked from the observed MRS stream
  // (MRS to MR3 = bank address 3), so a design that forgets to leave MPR mode
  // is still caught by the data path, and one that reads a closed bank outside
  // MPR mode is still caught here.
  logic mpr_en = 1'b0;
  always @(posedge clk or negedge rst_n) begin   // plain always: initialiser + always_ff would be two drivers
    if (!rst_n)                                  mpr_en <= 1'b0;
    else if ({mrs} && {bank} == {mr3_sel})   mpr_en <= {addr}[{mpr_bit}];
  end

"""
    for r in rules["state_rules"]:
        body += gen_state(r, spec, enc, sig, bank, nbanks)

    ids = ([r["id"] for r in rules["min_separation_rules"]]
           + [r["id"] for r in rules["window_rules"]]
           + [r["id"] for r in rules["max_interval_rules"]]
           + [r["id"] for r in rules["event_rules"]]
           + [x for r in rules["sequence_rules"]
              for x in ([r["id"]] + ([r["event_id"]] if r.get("event_id") else []))]
           + [r["id"] for r in rules["state_rules"]])
    addr_port = (f",\n    input logic [ADDR_W-1:0] {addr}" if addr_f else "")
    for ev in sorted({r["event"] for r in rules["event_rules"]}
                     | {r["event"] for r in rules["sequence_rules"] if r.get("event")}):
        addr_port += f",\n    input logic {ev}"
    addr_param = (f",\n    parameter int ADDR_W = {fields[addr_f]['width']}"
                  if addr_f else "")
    clock_note = ("the controller clock period" if CLOCK_DOMAIN == "controller"
                  else "the DDR clock period (tCK): one command per tCK at the pins")

    header = f"""`timescale 1ns/1ps
// GENERATED by Validation/sva/sva_gen.py — DO NOT EDIT BY HAND.
// Regenerate after any change to the spec or Validation/sva/sva_rules.json.
//
// Spec revision : {spec.get('revision')}
// Bound to      : {block} (via the bind statement in {block}_sva_bind.sv)
// Covers        : {', '.join(ids)}
//
// Every bound below is recomputed from the spec's nanosecond timing values
// and {clock_note}, not copied from a table. These assertions
// consult NO signal of the design except the command stream itself.

module {block}_sva{MODULE_SUFFIX} #(
    parameter int BANK_W = {bank_w}{addr_param}
) (
    input logic clk,
    input logic rst_n,
    input logic [{fields[rules['command_signals']['cmd_field']]['width'] - 1}:0] {sig},
    input logic [{bank_w - 1}:0] {bank}{addr_port}
);

"""
    return f"{block}_sva{MODULE_SUFFIX}", header + body + "endmodule\n", block, ids


def generate_signal_group(spec, grp):
    """Assertions for a block that has no command stream: ordering between
    its own signals (calibration: cal_done needs init_done first; a ZQCS
    request needs cal_done first). Ports are the signals named."""
    block = grp["block"]
    body, ids, sigs = "", [], set()
    for r in grp.get("event_order_rules", []):
        ev, req = r["event"], r["requires"]
        sigs |= {ev, req}
        ids.append(r["id"])
        body += f"""  // ---- {r['id']} -------------------------------------------------------
  // {r['requirement']}
  property p_{r['id']};
    @(posedge clk) disable iff (!rst_n)
    $rose({ev}) |-> {req};
  endproperty
  a_{r['id']}: assert property (p_{r['id']})
    else $error("[{r['id']}] {ev} raised while {req} is low");
  c_{r['id']}: cover property (@(posedge clk) disable iff (!rst_n) $rose({ev}) && {req});

"""
    ports = "".join(f",\n    input logic {x}" for x in sorted(sigs))
    mod = f"{block}_order_sva{MODULE_SUFFIX}"
    src = f"""`timescale 1ns/1ps
// GENERATED by Validation/sva/sva_gen.py — DO NOT EDIT BY HAND.
// Ordering assertions for {block}, from Validation/sva/sva_rules.json
// signal_groups. Spec revision: {spec.get('revision')}. Covers: {', '.join(ids)}.

module {mod} (
    input logic clk,
    input logic rst_n{ports}
);

{body}endmodule
"""
    return mod, src, block, ids


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", default=DEFAULT_OUT)
    ap.add_argument("--spec", default=SPEC_PATH,
                    help="spec to derive bounds from (default: the declared spec)")
    ap.add_argument("--clock", choices=sorted(CLOCK_KEY), default="controller",
                    help="clock the command stream is sampled on: controller "
                         "(cmd_gen output, default) or ddr (DRAM pins, one command per tCK)")
    ap.add_argument("--suffix", default="",
                    help="module-name suffix, so a second variant (e.g. _pins) "
                         "can coexist with the default modules")
    args = ap.parse_args()
    global CLOCK_DOMAIN, MODULE_SUFFIX
    CLOCK_DOMAIN, MODULE_SUFFIX = args.clock, args.suffix

    with open(args.spec) as f:
        spec = json.load(f)
    with open(RULES_PATH) as f:
        rules = json.load(f)
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]
    with open(SCHEMA_PATH) as f:
        sdoc = json.load(f)
    schemas = sdoc["interfaces"]
    # streams schema_gen left out because their block is absent from a
    # phase-partial drop: their assertion group waits for that block
    absent_streams = {x.split(" ")[0] for x in sdoc.get("streams_without_block", [])}

    os.makedirs(args.outdir, exist_ok=True)
    for grp in command_groups(rules):
        iface = grp["command_signals"]["interface"]
        if iface not in schemas and iface in absent_streams:
            print(f"  deferred: {grp['name']} group on {iface} (its block is not in the drop)")
            continue
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
    for grp in rules.get("signal_groups", []):
        mod, src, block, ids = generate_signal_group(spec, grp)
        path = os.path.join(args.outdir, f"{mod}.sv")
        with open(path, "w") as f:
            f.write(src)
        with open(os.path.join(args.outdir, f"{block}_order_sva_bind.sv"), "w") as f:
            f.write(f"""// GENERATED by Validation/sva/sva_gen.py — DO NOT EDIT BY HAND.
bind {block} {mod} u_{block}_order_sva (.*);
""")
        print(f"  wrote {os.path.relpath(path, ROOT)}  [signal group {grp['name']}]")
        print(f"    {src.count('assert property')} assertion(s); taxonomy IDs: {', '.join(ids)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
