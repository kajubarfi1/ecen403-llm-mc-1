#!/usr/bin/env python3
"""
block_coverage_gen.py — covergroups for the vplan's non-timing coverpoints
===========================================================================
coverage_gen.py produces the timing family (cg_timing) from sva_rules.json.
This produces everything else the vplan asks for — register-access, reset
checks, unmapped-address probes, and the "was this failure mode's situation
ever created" points for refresh, init, scheduler and data path — from
coverage_rules.json.

Same discipline as the timing generator:

  * coverpoint names are exactly the vplan's, so measured coverage maps to
    requirements with no translation table;
  * everything a recipe references (ports, registers, encodings) is resolved
    from the spec, the catalog, the schemas and the block's manifest, and a
    reference that does not resolve is a generation FAILURE — an absent bin
    would be indistinguishable from an unreached one;
  * a coverpoint the spec cannot support (e.g. "write-only registers" in a
    map that declares none) is reported as skipped with the reason, never
    emitted as a bin nobody could hit.

One module per block, `<block>_fcov`, bound with (.*). Its own code coverage
is excluded by cov_conf.ccf; only its covergroups count.

Usage:
    python3 Validation/sva/block_coverage_gen.py
"""

import argparse
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
RULES_PATH = os.path.join(HERE, "coverage_rules.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
VPLAN_PATH = os.path.join(ROOT, "Validation", "vplan", "vplan.json")
DEFAULT_OUT = os.path.join(HERE, "generated")

SV_KEYWORDS = {"if", "else", "case", "default", "inside", "and", "or", "not"}
IDENT = re.compile(r"\b[A-Za-z_]\w*\b")
SIZED_LIT = re.compile(r"\d*'[bhdoBHDO][0-9a-fA-F_xXzZ?]+")


class CovGenError(Exception):
    pass


# ---------------------------------------------------------------------------
# inputs
# ---------------------------------------------------------------------------

def manifest_ports(block):
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{block}_manifest.json"),
                             recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    if not paths:
        raise CovGenError(f"no manifest for block {block!r}")
    with open(paths[0]) as f:
        m = json.load(f)
    return {p["name"]: p["width"] for g in m["ports"].values() for p in g}


def numeric(sv):
    txt = str(sv)
    if "'" in txt:
        body = txt.split("'")[1]
        return int(body[1:].replace("_", ""),
                   {"b": 2, "h": 16, "d": 10, "o": 8}[body[0].lower()])
    return int(txt)


def to_int(v):
    return int(v, 16) if isinstance(v, str) else int(v)


def lit(width, value):
    return f"{width}'h{value & ((1 << width) - 1):X}"


def rep_pattern(byte, width):
    v = 0
    while v.bit_length() < width:
        v = (v << 8) | byte
    return v & ((1 << width) - 1)


# ---------------------------------------------------------------------------
# generation
# ---------------------------------------------------------------------------

class BlockModule:
    """Accumulates what one block's _fcov module needs."""

    def __init__(self, block, ports):
        self.block = block
        self.ports = ports                 # manifest {name: width}
        self.used = set()                  # ports referenced
        self.helpers = []                  # module-level SV (wires, always)
        self.groups = {}                   # cg name -> [coverpoint SV]
        self.generated = []                # (cg.cp, vplan id or None)
        self.skipped = []                  # (cg.cp, why)
        self.pattern_cps = set()           # cgs that already have cp_wdata_pattern
        self.post_sample = []              # statements run after .sample()

    def use(self, *names):
        for n in names:
            if n not in self.ports:
                raise CovGenError(f"{self.block}: port {n!r} not in manifest")
            self.used.add(n)

    def check_expr(self, expr):
        stripped = SIZED_LIT.sub(" ", expr)
        for ident in IDENT.findall(stripped):
            if ident in SV_KEYWORDS or ident.isdigit():
                continue
            self.use(ident)
        return expr


def bus_conditions(bm, catalog, schemas, bus):
    """(write_cond, read_cond, addr_port, addr_w, data_port, data_w)."""
    iface = bus["iface"]
    cat, sch = catalog[iface], schemas[iface]
    qual = bm.check_expr(cat["qualifier"])
    ks = cat.get("kind_select")
    if not ks:
        raise CovGenError(f"{iface}: register bus needs kind_select to tell "
                          f"writes from reads")
    bm.use(ks["expr"])
    by_kind = {v: k for k, v in ks["map"].items()}
    wk, rk = bus["write_kind"], bus["read_kind"]
    wcond = f"(({qual}) && ({ks['expr']} == 1'b{by_kind[wk]}))"
    rcond = f"(({qual}) && ({ks['expr']} == 1'b{by_kind[rk]}))"
    a = sch["kinds"][wk]["addr"]
    d = sch["kinds"][wk]["data"]
    bm.use(a["port"], d["port"])
    return wcond, rcond, a["port"], a["width"], d["port"], d["width"]


def registers(spec, section):
    rmap = spec[section]
    regs = []
    for r in rmap["registers"]:
        regs.append({"name": r["name"], "offset": to_int(r["offset"]),
                     "access": r["access"].upper(),
                     "field_access": {f["access"].upper()
                                      for f in r.get("fields", [])}})
    return sorted(regs, key=lambda r: r["offset"])


def gen_block(block, cps, spec, catalog, schemas, rules, vplan_ids):
    bm = BlockModule(block, manifest_ports(block))
    bm.use("clk", "rst_n")

    for cg_name, cp_name, cp in cps:
        cg = rules["covergroups"][cg_name]
        key = f"{cg_name}.{cp_name}"
        vid = vplan_ids.get(key)
        recipe = cp["recipe"]
        group = bm.groups.setdefault(cg_name, [])
        why = cp.get("why", "")

        # ---- occurred ---------------------------------------------------
        if recipe == "occurred":
            if "expr" in cp:
                expr = bm.check_expr(cp["expr"])
            else:
                iface = cp["iface"]
                cat = catalog[iface]
                expr = "(" + bm.check_expr(cat["qualifier"]) + ")"
                if "kind" in cp:
                    ks = cat["kind_select"]
                    bm.use(ks["expr"])
                    val = {v: k for k, v in ks["map"].items()}[cp["kind"]]
                    expr += f" && ({ks['expr']} == 1'b{val})"
                if "command" in cp:
                    enc = {k: v for k, v in cat["command_encoding"].items()
                           if not k.startswith("$")}
                    kind = next(iter(schemas[iface]["kinds"]))
                    fields = schemas[iface]["kinds"][kind]
                    cf = cp.get("command_field",
                                "cmd" if "cmd" in fields else "type")
                    port = fields[cf]["port"]
                    bm.use(port)
                    expr += (f" && ({port} == "
                             f"{lit(fields[cf]['width'], numeric(enc[cp['command']]))})")
            group.append(f"""    // {key}{(' — ' + why) if why else ''}
    {cp_name}: coverpoint ({expr}) iff (rst_n) {{
      bins occurred = {{1'b1}};
    }}""")
            bm.generated.append((key, vid))
            continue

        # ---- everything below needs the register bus ---------------------
        wcond, rcond, A, AW, D, DW = bus_conditions(bm, catalog, schemas,
                                                    cg["bus"])
        regs = registers(spec, cg["register_map"])

        if recipe == "register_access":
            want = {a.upper() for a in cp["access"]}
            if cp.get("field_level"):
                hits = [r for r in regs if r["field_access"] & want]
            else:
                hits = [r for r in regs if r["access"] in want]
            if not hits:
                bm.skipped.append((key, f"spec declares no {sorted(want)} "
                                        f"registers"))
                continue
            cond = wcond if cp["on"] == "write" else rcond
            bins = "\n".join(f"      bins {r['name']} = {{{lit(AW, r['offset'])}}};"
                             for r in hits)
            group.append(f"""    // {key}: every {sorted(want)} register {cp['on']}-accessed at least once
    {cp_name}: coverpoint {A} iff (rst_n && {cond}) {{
{bins}
    }}""")
            bm.generated.append((key, vid))

        elif recipe == "cross_pattern":
            with_cp = cp["with"]
            if not any(g[0] == f"{cg_name}.{with_cp}" for g in bm.generated):
                bm.skipped.append((key, f"{with_cp} was not generated"))
                continue
            if cg_name not in bm.pattern_cps:
                bm.pattern_cps.add(cg_name)
                group.append(f"""    // write-data pattern: toggles every writable bit both ways
    cp_wdata_pattern: coverpoint {D} iff (rst_n && {wcond}) {{
      bins zeros  = {{{lit(DW, 0)}}};
      bins ones   = {{{lit(DW, (1 << DW) - 1)}}};
      bins alt_a5 = {{{lit(DW, rep_pattern(0xA5, DW))}}};
      bins alt_5a = {{{lit(DW, rep_pattern(0x5A, DW))}}};
      bins other  = default;
    }}""")
            group.append(f"""    // {key}: each register of that class written with each pattern
    {cp_name}: cross {with_cp}, cp_wdata_pattern;""")
            bm.generated.append((key, vid))

        elif recipe == "first_read_after_reset":
            n = len(regs)
            cases_w = "\n".join(
                f"          {lit(AW, r['offset'])}: written_q[{i}] = 1'b1;"
                for i, r in enumerate(regs))
            cases_r = "\n".join(
                f"        {lit(AW, r['offset'])}: first_read = !written_q[{i}];"
                for i, r in enumerate(regs))
            bm.post_sample.append(f"""      if (!rst_n) written_q = '0;
      else if ({wcond}) begin
        case ({A})
{cases_w}
          default: ;
        endcase
      end""")
            bm.helpers.append(f"""  // one flag per register: has it been written since reset? Updated in
  // the post-NBA sampling block below, AFTER the covergroups sample, so a
  // read in the same cycle as the flag-setting write is not misjudged.
  logic [{n - 1}:0] written_q = '0;
  logic first_read;
  always_comb begin
    first_read = 1'b0;
    if ({rcond}) begin
      case ({A})
{cases_r}
        default: first_read = 1'b0;
      endcase
    end
  end""")
            bins = "\n".join(f"      bins {r['name']} = {{{lit(AW, r['offset'])}}};"
                             for r in regs)
            group.append(f"""    // {key}: a read of each register BEFORE any write to it — the reset value was actually checked
    {cp_name}: coverpoint {A} iff (rst_n && first_read) {{
{bins}
    }}""")
            bm.generated.append((key, vid))

        elif recipe == "unmapped_access":
            offs = ", ".join(lit(AW, r["offset"]) for r in regs)
            bm.helpers.append(f"""  logic mapped_addr;
  assign mapped_addr = ({A} inside {{{offs}}});""")
            qual = bm.check_expr(catalog[cg["bus"]["iface"]]["qualifier"])
            group.append(f"""    // {key}: an access to an offset the register map does not declare
    {cp_name}: coverpoint (({qual}) && !mapped_addr) iff (rst_n) {{
      bins occurred = {{1'b1}};
    }}""")
            bm.generated.append((key, vid))

        elif recipe == "access_violation_attempt":
            ro = [r for r in regs if r["access"] == "RO"]
            wo = [r for r in regs if r["access"] == "WO"
                  or (r["field_access"] and r["field_access"] <= {"WO"})]
            terms = []
            if ro:
                terms.append(f"({wcond} && ({A} inside {{"
                             + ", ".join(lit(AW, r["offset"]) for r in ro)
                             + "}))")
            if wo:
                terms.append(f"({rcond} && ({A} inside {{"
                             + ", ".join(lit(AW, r["offset"]) for r in wo)
                             + "}))")
            if not terms:
                bm.skipped.append((key, "spec declares no RO or write-only "
                                        "registers to violate"))
                continue
            group.append(f"""    // {key}: a write to a read-only register or a read of a write-only one — CSR_001's antecedent
    {cp_name}: coverpoint ({' || '.join(terms)}) iff (rst_n) {{
      bins occurred = {{1'b1}};
    }}""")
            bm.generated.append((key, vid))

        else:
            raise CovGenError(f"{key}: unknown recipe {recipe!r}")

    return bm


def render(bm, spec):
    ports = []
    for name in sorted(bm.used):
        w = bm.ports[name]
        if not isinstance(w, int):
            raise CovGenError(f"{bm.block}.{name}: array port {w!r} cannot be "
                              f"a covergroup input")
        dim = "" if w == 1 else f"[{w - 1}:0] "
        ports.append(f"    input logic {dim}{name}")
    groups = []
    for cg, pts in bm.groups.items():
        if not pts:
            continue
        groups.append(f"""  covergroup {cg};
    option.per_instance = 1;

{(chr(10) + chr(10)).join(pts)}

  endgroup

  {cg} {cg}_inst = new();""")
    src = f"""`timescale 1ns/1ps
// GENERATED by Validation/sva/block_coverage_gen.py — DO NOT EDIT BY HAND.
// Regenerate after any change to the spec, coverage_rules.json, or the vplan.
//
// Spec revision : {spec.get('revision')}
// Bound to      : {bm.block}
// Coverpoint names are exactly those the vplan asks for.

module {bm.block}_fcov (
{("," + chr(10)).join(ports)}
);

{(chr(10) + chr(10)).join(bm.helpers)}

{(chr(10) + chr(10)).join(groups)}

  // Sampling discipline, identical to the generated monitors: sample AFTER
  // the NBA region of the clock edge. A covergroup clocked directly on
  // @(posedge clk) samples pre-NBA, so a registered handshake output (the
  // CSR ack) is seen one edge late — after the driver has already dropped
  // its request — and every write-conditioned bin stays at zero while the
  // same accesses are miscounted as reads. That was the first result.
  localparam SAMPLE_DELAY = 1;
  always @(posedge clk) begin
    #SAMPLE_DELAY;
{chr(10).join(f"    {cg}_inst.sample();" for cg in bm.groups if bm.groups[cg])}
{chr(10).join(bm.post_sample)}
  end

endmodule
"""
    bind = (f"// GENERATED by Validation/sva/block_coverage_gen.py — DO NOT EDIT BY HAND.\n"
            f"bind {bm.block} {bm.block}_fcov u_{bm.block}_fcov (.*);\n")
    return src, bind


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
    with open(VPLAN_PATH) as f:
        vplan = json.load(f)
    vplan_ids = {c["name"]: it["id"] for it in vplan["items"]
                 for c in it.get("coverage_items", [])}

    # group coverpoints by the block they observe
    by_block = {}
    for cg_name, cg in rules["covergroups"].items():
        for cp_name, cp in cg["coverpoints"].items():
            blk = cp.get("block", cg["block"])
            by_block.setdefault(blk, []).append((cg_name, cp_name, cp))

    os.makedirs(args.outdir, exist_ok=True)
    total_gen, total_skip = [], []
    for block, cps in sorted(by_block.items()):
        try:
            bm = gen_block(block, cps, spec, catalog, schemas, rules, vplan_ids)
            src, bind = render(bm, spec)
        except CovGenError as e:
            print(f"  {block}: GENERATION FAILED — {e}", file=sys.stderr)
            return 1
        with open(os.path.join(args.outdir, f"{block}_fcov.sv"), "w") as f:
            f.write(src)
        with open(os.path.join(args.outdir, f"{block}_fcov_bind.sv"), "w") as f:
            f.write(bind)
        print(f"  {block}_fcov.sv: {len(bm.generated)} coverpoint(s)"
              + (f", {len(bm.skipped)} skipped" if bm.skipped else ""))
        for k, v in bm.generated:
            print(f"      {k:44} -> {v or '(not in vplan)'}")
        for k, why in bm.skipped:
            print(f"      {k:44} SKIPPED: {why}")
        total_gen += bm.generated
        total_skip += bm.skipped

    # vplan points nobody produces
    covered = {k for k, _ in total_gen}
    timing = {n for n in vplan_ids if n.startswith("cg_timing.")}
    missing = sorted(set(vplan_ids) - covered - timing
                     - {k for k, _ in total_skip})
    if missing:
        print(f"\n  vplan coverpoints with no recipe: {missing}")
    print(f"\n  {len(total_gen)} generated, {len(total_skip)} skipped, "
          f"{len(timing)} timing points via coverage_gen.py")
    return 0


if __name__ == "__main__":
    sys.exit(main())
