#!/usr/bin/env python3
"""
generate_top.py -- build the flat ddr3_controller top level (deterministic,
no LLM), per backend/Frontend2/TOP_LEVEL_SPEC_2026-09-24.md.

Backend's own scaffold (backend/integration/generate_top.py) wires ONLY the
connections a block manifest declares via `source`. Frontend2's manifests
only carry `source` on a fraction of ports today, so running that algorithm
unmodified here would reproduce the same "structurally valid, not
functionally a memory controller" scaffold already sitting in
backend/integration/ddr3_controller/ -- no better than what exists.

This version additionally draws on Validation's own connectivity map
(Validation/structural/integration_map.json / integration_overrides.json,
built and real-verified by Jacob's team from the SAME Frontend2 drop this
script reads), which independently identified the 12 real block-to-block
connections Frontend2's manifests don't yet declare, plus two places where
a straight wire is functionally *wrong* and the design needs one cycle of
registering (glue) or a small combinational expression (expr_glue) instead.
That knowledge is captured below as data (SUPPLEMENTAL_CONNECTIONS / GLUE /
EXPR_GLUE), not re-derived at runtime, so this script has no import-time
dependency on Validation/ internals -- but every one of those hardcoded
edges is a no-op the moment the named block backfills a real `source` field
for it (this script detects and reports that automatically, same hygiene
Validation's own integration_map_gen.py performs on its overrides file).

What this deliberately does NOT wire (documented as known gaps instead of
silently papered over -- see TOP_LEVEL_SPEC_2026-09-24.md section 6-7):
  - calibration.zqcs_req / calibration.zqcs_ack: nothing in the 11 blocks
    consumes a ZQCS request yet (no scheduler/cmd_gen arbitration path
    exists). Left as external pins.
  - Everything else with no declared or known producer (e.g.
    bank_tracker.cmd_pre_all) -- same treatment, promoted to a top pin.

Usage:
    python3 generate_top.py --output-dir Frontend2/OutputFolders \
                             --spec Spec/llmmc_microarchitecturespec_filled.json \
                             [--no-lint]
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from manifest_stamp import stamp  # noqa: E402
from gate_policy import gate_passes  # noqa: E402

TOP = "ddr3_controller"
CLK, RST = "clk", "rst_n"

BLOCK_ORDER = [
    "addr_decoder", "bank_tracker", "calibration", "cmd_gen", "cmd_queue",
    "config_regs", "data_path", "init_fsm", "refresh_ctrl", "scheduler", "wb_port",
]

PHASE_DIR = {
    "init_fsm": "PHASE1RTL", "config_regs": "PHASE1RTL", "wb_port": "PHASE1RTL",
    "addr_decoder": "PHASE2RTL", "bank_tracker": "PHASE2RTL",
    "calibration": "PHASE2RTL", "refresh_ctrl": "PHASE2RTL",
    "cmd_queue": "PHASE3RTL", "scheduler": "PHASE3RTL", "cmd_gen": "PHASE3RTL",
    "data_path": "PHASE4RTL",
}

# Real block-to-block connections that, as of drop b4d6f45, Frontend2's
# manifests did not yet declare a `source` for (matched Validation's
# integration_overrides.json). All 12 have since been backfilled directly
# into the relevant generators' generate_manifest() (cmd_queue_gen.py,
# refresh_ctrl_gen.py) -- kept here, empty, as the no-op detector: any
# edge that reappears unsourced (a manifest regression) is caught and
# reported by build_edges() rather than silently promoted to a pin.
SUPPLEMENTAL_CONNECTIONS = []

# Ports whose manifest-declared `source` is functionally wrong (the RTL
# needs glue/expr_glue instead of a straight wire) -- the manifest's claim
# is ignored for these targets.
OVERRIDDEN_BY_GLUE = {"data_path.wr_data_valid"}

# Registered (1-cycle) glue: NONE needed as of this drop. cmd_gen.sv
# already carries real, correctly-registered fb_pre_bank/fb_rd_bank/
# fb_wr_bank/fb_pre_all and cmd_out_aux ports (aligned with fb_pre_valid/
# fb_rd_valid/fb_wr_valid in the same always_ff branches) -- confirmed by
# reading cmd_gen.sv directly after a combined Verilator lint of an
# earlier draft of this script's output flagged %Warning-PINMISSING on
# exactly these ports, meaning cmd_gen.sv declares them but neither its
# manifest nor bank_tracker's/data_path's manifests knew about them yet.
# Fixed at the source (cmd_gen_gen.py now declares them; bank_tracker_gen.py
# and data_path_gen.py now point `source` at the real cmd_gen ports) rather
# than reconstructed here via a top-level register. Left as a hook in case
# a future block regresses back to needing it.
GLUE = []

# Combinational glue: data_path must only latch a write word on the cycle
# wb_port's write request is actually ACCEPTED (valid && we && ready) --
# not on every req_valid pulse (which also fires on reads and on
# stalled/unaccepted writes).
EXPR_GLUE = [
    {"target": "data_path.wr_data_valid",
     "terms": ["wb_port.req_valid", "wb_port.req_we", "cmd_queue.enq_ready"]},
]

KNOWN_GAPS = [
    "calibration.zqcs_req / calibration.zqcs_ack: no block issues or "
    "arbitrates ZQCS requests yet, so nothing can drive zqcs_ack from "
    "inside the design. Left as external pins rather than auto-acking "
    "(auto-ack would silently hide a real missing consumer).",
]


class GenError(Exception):
    pass


def load_manifests(base_dir: Path) -> dict:
    manifests = {}
    for block in BLOCK_ORDER:
        mpath = base_dir / PHASE_DIR[block] / f"{block}_manifest.json"
        svpath = base_dir / PHASE_DIR[block] / f"{block}.sv"
        if not mpath.is_file():
            raise GenError(f"missing manifest: {mpath}")
        if not svpath.is_file():
            raise GenError(f"missing RTL: {svpath}")
        m = json.loads(mpath.read_text())
        ports = {}
        for group, plist in m.get("ports", {}).items():
            for p in plist:
                ports[p["name"]] = {
                    "dir": p["dir"], "width": p["width"], "group": group,
                    "source": p.get("source"),
                }
        manifests[block] = {"manifest": m, "ports": ports, "sv_path": svpath}
    return manifests


def port_info(manifests: dict, block: str, name: str) -> dict:
    try:
        return manifests[block]["ports"][name]
    except KeyError:
        raise GenError(f"{block}.{name} is not a port in {block}'s manifest")


def build_edges(manifests: dict):
    """Returns (edges: [(src_ref, dst_ref)], redundant_supplemental: [...])."""
    edges = []
    seen_targets = set()

    def add_edge(src, dst):
        if dst in seen_targets:
            raise GenError(f"conflicting driver for {dst}: already wired")
        edges.append((src, dst))
        seen_targets.add(dst)

    # 1. manifest-declared `source` fields (skip the two glue supersedes).
    for block in BLOCK_ORDER:
        for name, p in manifests[block]["ports"].items():
            dst = f"{block}.{name}"
            if p["dir"] != "input" or not p["source"]:
                continue
            if dst in OVERRIDDEN_BY_GLUE:
                continue
            add_edge(p["source"], dst)

    # 2. supplemental connections -- skip (and report) any already covered.
    redundant = []
    for src, dst in SUPPLEMENTAL_CONNECTIONS:
        if dst in seen_targets:
            redundant.append((src, dst))
            continue
        add_edge(src, dst)

    return edges, redundant


def validate_edges(manifests: dict, edges: list):
    for src, dst in edges:
        sb, sp = src.split(".")
        db, dp = dst.split(".")
        sinfo = port_info(manifests, sb, sp)
        dinfo = port_info(manifests, db, dp)
        if sinfo["dir"] != "output":
            raise GenError(f"{src} is not an output (edge {src} -> {dst})")
        if dinfo["dir"] != "input":
            raise GenError(f"{dst} is not an input (edge {src} -> {dst})")
        if str(sinfo["width"]) != str(dinfo["width"]):
            raise GenError(
                f"width mismatch: {src} is {sinfo['width']} wide, "
                f"{dst} is {dinfo['width']} wide")


def net_name(block: str, port: str) -> str:
    return f"w_{block}__{port}"


def sv_decl(width) -> tuple[str, str]:
    """(packed, unpacked) SV declaration fragments for a manifest width."""
    if isinstance(width, int):
        return (f"[{width - 1}:0]" if width > 1 else "", "")
    if isinstance(width, str) and "x" in width.lower():
        n_str, _, b_str = width.lower().partition("x")
        n, b = int(n_str), int(b_str)
        return (f"[{b - 1}:0]" if b > 1 else "", f"[{n}]")
    raise GenError(f"unrecognized width spec: {width!r}")


def build_wiring(manifests: dict, edges: list):
    """Returns (input_net, output_consumed, produced_nets, glue_regs, expr_wires)."""
    input_net = {}          # "block.port" (input) -> net/wire name
    output_consumed = set()  # "block.port" (output) already wired somewhere
    produced_nets = {}       # net_name -> (block, port) for declarations

    for src, dst in edges:
        sb, sp = src.split(".")
        n = net_name(sb, sp)
        input_net[dst] = n
        output_consumed.add(src)
        produced_nets[n] = (sb, sp)

    glue_regs = []  # (src_net, reg_net, width_spec)
    for g in GLUE:
        sb, sp = g["source"].split(".")
        src_ref = g["source"]
        if src_ref not in output_consumed:
            raise GenError(f"glue source {src_ref} has no produced net "
                            f"(expected it to already be wired to something)")
        src_net = net_name(sb, sp)
        reg_net = f"w_glue_{sb}_{sp}_r"
        width = port_info(manifests, sb, sp)["width"]
        glue_regs.append((src_net, reg_net, width))
        for t in g["targets"]:
            input_net[t] = reg_net

    expr_wires = []  # (wire_name, [term_nets], target_width)
    for eg in EXPR_GLUE:
        tb, tp = eg["target"].split(".")
        term_nets = []
        for term in eg["terms"]:
            b, p = term.split(".")
            if term not in output_consumed:
                raise GenError(f"expr_glue term {term} has no produced net")
            term_nets.append(net_name(b, p))
        wire = f"w_expr__{tb}_{tp}"
        width = port_info(manifests, tb, tp)["width"]
        expr_wires.append((wire, term_nets, width))
        input_net[eg["target"]] = wire

    return input_net, output_consumed, produced_nets, glue_regs, expr_wires


def promote_top_ports(manifests: dict, input_net: dict, output_consumed: set):
    top_in, top_out = [], []
    for block in BLOCK_ORDER:
        for name, p in manifests[block]["ports"].items():
            if name in (CLK, RST):
                continue
            ref = f"{block}.{name}"
            if p["dir"] == "input":
                if ref not in input_net:
                    top_in.append((block, name, p))
            else:
                if ref not in output_consumed:
                    top_out.append((block, name, p))
    top_in.sort()
    top_out.sort()
    return top_in, top_out


def emit_sv(manifests, edges, input_net, output_consumed, produced_nets,
            glue_regs, expr_wires, top_in, top_out, header_lines) -> str:
    L = []
    L += header_lines
    L.append(f"module {TOP} (")
    decls = [f"    input  logic {CLK},", f"    input  logic {RST},"]
    for b, n, p in top_in:
        packed, unpacked = sv_decl(p["width"])
        decls.append(f"    input  logic {packed:<12} {b}_{n}{unpacked},")
    for b, n, p in top_out:
        packed, unpacked = sv_decl(p["width"])
        decls.append(f"    output logic {packed:<12} {b}_{n}{unpacked},")
    decls[-1] = decls[-1].rstrip(",")
    L += decls
    L.append(");")
    L.append("")

    L.append("    // -- internal nets: direct block-to-block connections --")
    for n in sorted(produced_nets):
        b, p = produced_nets[n]
        packed, unpacked = sv_decl(port_info(manifests, b, p)["width"])
        L.append(f"    logic {packed:<12} {n}{unpacked};")
    L.append("")

    if glue_regs:
        L.append("    // -- registered glue (see GLUE in this script's header) --")
        for src_net, reg_net, width in glue_regs:
            packed, unpacked = sv_decl(width)
            L.append(f"    logic {packed:<12} {reg_net}{unpacked};")
        L.append("    always_ff @(posedge clk or negedge rst_n) begin")
        L.append("        if (!rst_n) begin")
        for _src_net, reg_net, width in glue_regs:
            L.append(f"            {reg_net} <= '0;")
        L.append("        end else begin")
        for src_net, reg_net, _width in glue_regs:
            L.append(f"            {reg_net} <= {src_net};")
        L.append("        end")
        L.append("    end")
        L.append("")

    if expr_wires:
        L.append("    // -- combinational glue (see EXPR_GLUE in this script's header) --")
        for wire, term_nets, width in expr_wires:
            packed, unpacked = sv_decl(width)
            L.append(f"    logic {packed:<12} {wire}{unpacked};")
            L.append(f"    assign {wire} = {' && '.join(term_nets)};")
        L.append("")

    def conn_value(block, name, p):
        ref = f"{block}.{name}"
        if p["dir"] == "input":
            return input_net.get(ref, f"{block}_{name}")
        return net_name(block, name) if ref in output_consumed else f"{block}_{name}"

    for block in BLOCK_ORDER:
        info = manifests[block]
        conns = []
        if CLK in info["ports"]:
            conns.append(f".{CLK}({CLK})")
            if RST in info["ports"]:
                conns.append(f".{RST}({RST})")
        for name, p in info["ports"].items():
            if name in (CLK, RST):
                continue
            conns.append(f".{name}({conn_value(block, name, p)})")
        L.append(f"    {block} u_{block} (")
        L += [f"        {c}," for c in conns[:-1]] + [f"        {conns[-1]}"]
        L.append("    );")
        L.append("")
    L.append("endmodule")
    return "\n".join(L) + "\n"


def build_manifest(manifests, top_in, top_out, spec: dict, redundant, sv_files) -> dict:
    def entry(block, name, p, direction):
        return {"name": f"{block}_{name}", "width": p["width"], "dir": direction}

    m = {
        "module_name": TOP,
        "kind": "top",
        "file": [f"{TOP}.sv"] + sv_files,
        "generated_by": "Frontend2/scripts/generate_top.py",
        "dependencies": list(BLOCK_ORDER),
        "parameters": {},
        # Yosys FSM extraction does not terminate on the flattened 11-block
        # design (see TOP_LEVEL_SPEC_2026-09-24.md section 7).
        "orfs_config": {"SYNTH_ARGS": "-nofsm"},
        "ports": {
            "clock_reset": [
                {"name": CLK, "width": 1, "dir": "input"},
                {"name": RST, "width": 1, "dir": "input"},
            ],
            "external_in": [entry(b, n, p, "input") for b, n, p in top_in],
            "external_out": [entry(b, n, p, "output") for b, n, p in top_out],
        },
        "known_gaps": KNOWN_GAPS,
        "supplemental_connections_used": [
            {"from": s, "to": d} for s, d in SUPPLEMENTAL_CONNECTIONS
            if (s, d) not in redundant
        ],
        "supplemental_connections_now_redundant": [
            {"from": s, "to": d} for s, d in redundant
        ],
    }
    m.update(stamp(spec))
    return m


def run_lint(out_dir: Path, sv_names: list) -> dict:
    sys.path.insert(0, str(HERE))
    from simulator import XceliumSimulator, SSH_CONFIG
    from verilator_lint import _strip_sim_only_blocks

    cfg = dict(SSH_CONFIG)
    cfg["username"] = os.environ.get("OLYMPUS_USER", cfg["username"])
    cfg["key_path"] = os.environ.get("OLYMPUS_KEY", cfg["key_path"])

    sim = XceliumSimulator(ssh_config=cfg)
    try:
        sim.connect()
    except Exception as e:
        return {"status": "SKIPPED", "reason": f"SSH failed: {e}"}

    tmp_dir = tempfile.mkdtemp()
    try:
        local_paths = []
        for name in sv_names:
            stripped = _strip_sim_only_blocks((out_dir / name).read_text())
            tmp_path = os.path.join(tmp_dir, name)
            Path(tmp_path).write_text(stripped)
            local_paths.append(tmp_path)
        sim.upload_files(local_paths)
        file_args = " ".join(sv_names)
        cmd = f"cd {sim.work_dir} && verilator --lint-only -Wall -sv {file_args} 2>&1"
        result = sim.srun(cmd, timeout=120)
        stdout = result["stdout"]
        errors = [l.strip() for l in stdout.splitlines()
                  if l.strip().startswith("%Error")
                  and "Exiting due to" not in l]
        warnings = [l.strip() for l in stdout.splitlines()
                    if l.strip().startswith("%Warning")]
        return {
            "status": "PASS" if not errors else "FAIL",
            "errors": errors, "warnings": warnings, "raw_output": stdout,
        }
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        sim.disconnect()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-dir", required=True, type=Path,
                     help="pipeline output dir containing PHASE1RTL..PHASE4RTL")
    ap.add_argument("--spec", required=True, type=Path,
                     help="spec JSON used for this drop (for clock_period_ns / revision)")
    ap.add_argument("--out-subdir", default="TOPRTL")
    ap.add_argument("--no-lint", action="store_true",
                     help="skip the real Verilator lint check on Olympus")
    args = ap.parse_args()

    if not args.spec.is_file():
        print(f"ERROR: spec not found: {args.spec}", file=sys.stderr)
        return 1
    spec = json.loads(args.spec.read_text())

    from drop import revision_mismatches  # noqa: E402
    mixed = revision_mismatches(args.output_dir, args.spec)
    if mixed:
        print(f"ERROR: blocks were generated from a different spec than {args.spec.name} "
              f"(revision {spec.get('revision')}): one drop must come from one spec.", file=sys.stderr)
        for b, r in sorted(mixed.items()):
            print(f"  {b}: {r}", file=sys.stderr)
        print("Regenerate those phases from this spec, then re-run.", file=sys.stderr)
        return 1

    try:
        manifests = load_manifests(args.output_dir)
        edges, redundant = build_edges(manifests)
        validate_edges(manifests, edges)
        input_net, output_consumed, produced_nets, glue_regs, expr_wires = \
            build_wiring(manifests, edges)
        top_in, top_out = promote_top_ports(manifests, input_net, output_consumed)
    except GenError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    header = [
        f"// {TOP} -- generated by Frontend2/scripts/generate_top.py",
        f"// Follows backend/Frontend2/TOP_LEVEL_SPEC_2026-09-24.md.",
        f"// {len(edges)} direct connections, {len(glue_regs)} registered glue group(s), "
        f"{len(expr_wires)} combinational glue expression(s).",
    ]
    if redundant:
        header.append(
            f"// {len(redundant)} hardcoded supplemental connection(s) in this script are "
            f"now redundant (the consumer manifest declares its own `source`) -- safe to "
            f"delete from SUPPLEMENTAL_CONNECTIONS: " +
            ", ".join(f"{s}->{d}" for s, d in redundant))
    for gap in KNOWN_GAPS:
        header.append(f"// KNOWN GAP: {gap}")
    header.append("")

    sv_text = emit_sv(manifests, edges, input_net, output_consumed, produced_nets,
                       glue_regs, expr_wires, top_in, top_out, header)

    out_dir = args.output_dir / args.out_subdir
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / f"{TOP}.sv").write_text(sv_text)

    sv_files = []
    for block in BLOCK_ORDER:
        dst = out_dir / f"{block}.sv"
        shutil.copyfile(manifests[block]["sv_path"], dst)
        sv_files.append(f"{block}.sv")

    manifest = build_manifest(manifests, top_in, top_out, spec, redundant, sv_files)
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    print(f"wrote {out_dir / (TOP + '.sv')} and manifest.json")
    print(f"  blocks instantiated       : {len(BLOCK_ORDER)}")
    print(f"  direct connections        : {len(edges)}")
    print(f"  registered glue groups    : {len(glue_regs)}")
    print(f"  combinational glue exprs  : {len(expr_wires)}")
    print(f"  top-level ports           : {len(top_in)} in + {len(top_out)} out + clk/rst_n")
    print(f"  known gaps                : {len(KNOWN_GAPS)}")
    if redundant:
        print(f"  supplemental now redundant: {len(redundant)} "
              f"(see header comment / manifest.supplemental_connections_now_redundant)")

    if not args.no_lint:
        print("\nrunning combined Verilator lint on Olympus...")
        lint = run_lint(out_dir, [f"{TOP}.sv"] + sv_files)
        (out_dir / "top_lint_report.json").write_text(json.dumps(lint, indent=2) + "\n")
        if lint["status"] == "SKIPPED":
            print(f"  SKIPPED: {lint.get('reason')}")
            if not gate_passes("SKIPPED"):
                print("  A skipped lint is not a pass. Export OLYMPUS_USER / OLYMPUS_KEY, or set")
                print("  ALLOW_SKIPPED_GATES=1 to accept the bundle unverified.")
                return 1
        elif lint["status"] == "PASS":
            print(f"  PASS -- 0 errors, {len(lint.get('warnings', []))} warning(s)")
        else:
            print(f"  FAIL -- {len(lint['errors'])} error(s):")
            for e in lint["errors"][:20]:
                print(f"    {e}")
            return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
