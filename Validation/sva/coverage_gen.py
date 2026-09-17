#!/usr/bin/env python3
"""
coverage_gen.py — generate the covergroups the vplan asks to be measured
=========================================================================
The vplan names 42 coverage items. Nothing produced them, so 37 of 38 vplan
items still read `not_started` even though the design has been simulated and
assertions have run. This closes that: it emits covergroups whose coverpoint
names are exactly the ones the vplan already asks for, so measured coverage
maps back to requirements without a translation table.

Two families, both derived from the same spec and rule catalog the assertions
come from:

  cp_<failure_id>_exercised
      Did stimulus ever create the situation this failure mode describes?
      An assertion that never sees its antecedent has proved nothing — it
      passed vacuously. This coverpoint is what distinguishes "the design
      never violated tRCD" from "we never issued an ACT followed by a CAS".

  cp_<param>_spacing
      Was the constraint driven to its BOUNDARY? A suite that always leaves
      ten idle cycles between commands satisfies every timing rule and
      demonstrates nothing. The `at_minimum` bin is the one that matters;
      `below_minimum` is an illegal bin, because reaching it means the
      assertion should already have fired.

Spacing is measured HERE from the observed command stream, with counters
belonging to this module. As with the assertions, no DUT counter is consulted
— coverage collected from the design's own notion of elapsed time would
inherit any error in it.

Usage:
    python3 Validation/sva/coverage_gen.py
"""

import argparse
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

from sva_gen import cycles_for, cmd_match, interval_bound, SvaGenError

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
RULES_PATH = os.path.join(HERE, "sva_rules.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
VPLAN_PATH = os.path.join(ROOT, "Validation", "vplan", "vplan.json")
DEFAULT_OUT = os.path.join(HERE, "generated")

MAX_SPACING = 255          # counter saturation; wide enough for tRFC (32)


def vplan_expects(vplan_path):
    """Every coverage item name the vplan asks for, by covergroup."""
    with open(vplan_path) as f:
        v = json.load(f)
    want = {}
    for item in v["items"]:
        for cov in item.get("coverage_items", []):
            grp, _, pt = cov["name"].partition(".")
            want.setdefault(grp, {})[pt] = item["id"]
    return want


def generate(spec, rules, catalog, schemas, want):
    iface = rules["command_signals"]["interface"]
    enc = catalog[iface]["command_encoding"]
    kind = next(iter(schemas[iface]["kinds"]))
    fields = schemas[iface]["kinds"][kind]
    sig = fields[rules["command_signals"]["cmd_field"]]["port"]
    bank = fields[rules["command_signals"]["bank_field"]]["port"]
    bank_w = fields[rules["command_signals"]["bank_field"]]["width"]
    nbanks = 1 << int(spec["memory_geometry"]["bank_bits"])
    block = schemas[iface]["block"]

    seps = rules["min_separation_rules"]
    win = rules["window_rules"]
    timing_want = want.get("cg_timing", {})

    # --- spacing counters: cycles since each "from" command, per bank -------
    # One counter set per distinct source command, so several rules measuring
    # from the same command share it.
    sources = sorted({tuple(r["from"]) for r in seps} | {(w["command"],) for w in win})
    counters, ctr_decl, ctr_upd = {}, [], []
    for src in sources:
        name = "since_" + "_".join(c.lower() for c in src)
        counters[src] = name
        match = cmd_match(enc, list(src), sig)
        ctr_decl.append(
            f"  // cycles since the last {'/'.join(src)}, per bank; saturating\n"
            f"  int unsigned {name} [{nbanks}];")
        ctr_upd.append(f"""    for (int b = 0; b < {nbanks}; b++)
      if ({name}[b] < {MAX_SPACING}) {name}[b] <= {name}[b] + 1;
    if ({match}) {name}[{bank}] <= 0;""")

    # --- coverpoints --------------------------------------------------------
    points, generated, skipped = [], [], []

    for r in seps + win:
        rid = r["id"]
        pt = f"cp_{rid.lower()}_exercised"
        if pt not in timing_want:
            continue
        if "command" in r:                       # window rule
            trig = cmd_match(enc, [r["command"]], sig)
        else:
            trig = cmd_match(enc, r["to"], sig)
        points.append(f"""    // {rid}: did stimulus ever create this situation? An assertion whose
    // antecedent never occurred has proved nothing.
    {pt}: coverpoint ({trig}) iff (rst_n) {{
      bins occurred = {{1'b1}};
    }}""")
        generated.append((f"cg_timing.{pt}", timing_want[pt]))

    for r in seps + win:
        param = r["param"]
        pt = f"cp_{param.lower()}_spacing"
        if pt not in timing_want or any(p[0].endswith(pt) for p in generated):
            continue
        try:
            n, ns, period = cycles_for(spec, param)
        except SvaGenError:
            skipped.append((f"cg_timing.{pt}", "spec has no such timing parameter"))
            continue
        src = tuple(r["from"]) if "from" in r else (r["command"],)
        ctr = counters[src]
        if "command" in r:
            trig = cmd_match(enc, [r["command"]], sig)
        else:
            trig = cmd_match(enc, r["to"], sig)
        below = f"bins below_minimum = {{[0:{n - 1}]}};" if n >= 1 else ""
        points.append(f"""    // {param} = {ns}ns = {n} cycle(s) at {period}ns. The at_minimum bin is
    // the one that matters: a suite that always leaves slack satisfies the
    // constraint without ever testing it.
    {pt}: coverpoint {ctr}[{bank}] iff (rst_n && {trig}) {{
      bins at_minimum   = {{{n}}};
      bins above_minimum = {{[{n + 1}:{MAX_SPACING - 1}]}};
      // Saturation means the source command never occurred, so this is an
      // artefact of counter initialisation rather than something stimulus
      // should aim at. Counting it would make 100% unreachable for any
      // coverpoint that was actually exercised — a goal nobody can hit is
      // indistinguishable from a goal nobody tried to hit.
      ignore_bins never_seen = {{{MAX_SPACING}}};
      illegal_bins below_minimum = {{[0:{n - 1}]}};
    }}""")
        generated.append((f"cg_timing.{pt}", timing_want[pt]))

    # --- maximum-interval parameters (tREFI): the boundary is the other way
    # round. A refresh issued at or before the interval is normal; one
    # issued later is a POSTPONED refresh (legal up to the spec's budget);
    # beyond (budget + 1) x interval the assertion has already fired. The
    # counter is bankless — a REFRESH is an all-bank command.
    extra_reset = []
    for r in rules.get("max_interval_rules", []):
        param = r["param"]
        pt = f"cp_{param.lower()}_spacing"
        if pt not in timing_want or any(p[0].endswith(pt) for p in generated):
            continue
        try:
            n, ns, period, mult, bound = interval_bound(spec, r)
        except SvaGenError as e:
            skipped.append((f"cg_timing.{pt}", str(e)))
            continue
        trig = cmd_match(enc, [r["command"]], sig)
        name = f"since_{r['command'].lower()}_any"
        ctr_decl.append(
            f"  // cycles since the last {r['command']} (any bank); armed by the"
            f" first one\n  int unsigned {name};\n  logic {name}_armed;")
        extra_reset.append(f"      {name} <= 0; {name}_armed <= 1'b0;")
        ctr_upd.append(f"""    if ({trig}) begin {name} <= 0; {name}_armed <= 1'b1; end
    else if ({name} < 32'h7FFF_FFFF) {name} <= {name} + 1;""")
        points.append(f"""    // {param} = {ns}ns = {n} cycle(s) at {period}ns; up to {mult - 1} may be
    // postponed, so the legal gap is at most {bound}. within_interval is the
    // ordinary case; postponed is the boundary the vplan asks to see driven.
    {pt}: coverpoint {name} iff (rst_n && {trig} && {name}_armed) {{
      bins within_interval = {{[1:{n}]}};
      bins postponed       = {{[{n + 1}:{bound}]}};
      illegal_bins beyond_maximum = {{[{bound + 1}:$]}};
    }}""")
        generated.append((f"cg_timing.{pt}", timing_want[pt]))

    for pt, vid in sorted(timing_want.items()):
        if not any(g[0].endswith("." + pt) for g in generated):
            skipped.append((f"cg_timing.{pt}", "no rule in sva_rules.json yields it"))

    src = f"""`timescale 1ns/1ps
// GENERATED by Validation/sva/coverage_gen.py — DO NOT EDIT BY HAND.
// Regenerate after any change to the spec, sva_rules.json, or the vplan.
//
// Spec revision : {spec.get('revision')}
// Bound to      : {block}
// Coverpoint names are exactly those the vplan asks for, so measured
// coverage maps to vplan items with no translation table.
//
// Spacing is measured by counters declared HERE, from the observed command
// stream. The design's own timing counters are deliberately not used:
// coverage taken from the design's notion of elapsed time would inherit any
// error in it, and would then report the design as well-exercised precisely
// where it is wrong.

module {block}_coverage (
    input logic clk,
    input logic rst_n,
    input logic [{fields[rules['command_signals']['cmd_field']]['width'] - 1}:0] {sig},
    input logic [{bank_w - 1}:0] {bank}
);

{chr(10).join(ctr_decl)}

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
{chr(10).join(f"      for (int b = 0; b < {nbanks}; b++) {c} [b] <= {MAX_SPACING};" for c in counters.values())}
{chr(10).join(extra_reset)}
    end else begin
{chr(10).join(ctr_upd)}
    end
  end

  covergroup cg_timing @(posedge clk);
    option.per_instance = 1;

{(chr(10) + chr(10)).join(points)}

  endgroup

  cg_timing cg_timing_inst = new();

endmodule
"""
    bind = f"""// GENERATED by Validation/sva/coverage_gen.py — DO NOT EDIT BY HAND.
bind {block} {block}_coverage u_{block}_cov (.*);
"""
    return f"{block}_coverage", src, bind, generated, skipped


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
    want = vplan_expects(VPLAN_PATH)

    try:
        mod, src, bind, generated, skipped = generate(
            spec, rules, catalog, schemas, want)
    except SvaGenError as e:
        print(f"coverage generation failed: {e}", file=sys.stderr)
        return 1

    os.makedirs(args.outdir, exist_ok=True)
    with open(os.path.join(args.outdir, f"{mod}.sv"), "w") as f:
        f.write(src)
    with open(os.path.join(args.outdir, f"{mod}_bind.sv"), "w") as f:
        f.write(bind)

    total_want = sum(len(v) for v in want.values())
    print(f"  wrote {os.path.relpath(os.path.join(args.outdir, mod + '.sv'), ROOT)}")
    print(f"    {len(generated)} coverpoint(s) generated, matching vplan names")
    for name, vid in sorted(generated):
        print(f"      {name:44} -> {vid}")
    if skipped:
        print(f"\n    NOT generated ({len(skipped)}):")
        for name, why in sorted(skipped):
            print(f"      {name:44} {why}")
    print(f"\n  vplan asks for {total_want} coverage item(s) across "
          f"{len(want)} covergroup(s); this generator covers cg_timing only.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
