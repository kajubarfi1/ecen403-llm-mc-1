"""
Event-Mode Testbench Codegen (Stage 4)
========================================
Deterministic SystemVerilog testbench generator for event-mode integration paths.
No LLM involvement — the testbench shape is fully determined by:

  1. The path's event_spec.json (signals, start expression, vector_format)
  2. The existing wiring template (instance names + port connections)
  3. The event-mode task library from path_scope_generator.py

Produces a single self-contained file: <path_id>_tb.sv, ready for simulation.

Called from path_scope_generator.py when a path has mode='event', OR as a
standalone CLI for regenerating testbenches after spec edits:

    python3 event_tb_codegen.py \\
        --event-spec scopes/path_08_init_to_cal/generated/event_spec.json \\
        --wiring     scopes/path_08_init_to_cal/generated/wiring_template.sv \\
        --output-dir scopes/path_08_init_to_cal/generated

Author: Validation Subsystem — Event TB Codegen (Stage 4)
"""

import argparse
import json
import os
import re
import sys
from typing import Dict, List, Optional, Tuple

# Import the library generator from the patched path_scope_generator
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    from path_scope_generator import generate_event_task_library_sv
except ImportError:
    # Standalone mode — look in the same directory
    generate_event_task_library_sv = None


# =============================================================================
# sample_signal() Body Generation
# =============================================================================

def build_sample_signal_cases(signals: List[dict]) -> str:
    """Emit the case body for sample_signal(id).

    For each signal, produce a case arm that returns a 32-bit value:
      - raw: width-aware zero extension of the port read
      - predicate: (expression) ? 32'h1 : 32'h0
    """
    lines = []
    for sig in signals:
        sid = sig["id"]
        kind = sig["kind"]
        name = sig.get("name", f"sig_{sid}")
        lines.append(f"            // sig {sid}: {name}")

        if kind == "raw":
            path = sig["path"]
            width = int(sig["width"])
            if width == 32:
                lines.append(f"            {sid}: sample_signal = {path};")
            elif width == 1:
                lines.append(f"            {sid}: sample_signal = {{31'b0, {path}}};")
            else:
                pad = 32 - width
                lines.append(f"            {sid}: sample_signal = {{{pad}'b0, {path}}};")

        elif kind == "predicate":
            expr = sig["expression"]
            lines.append(f"            {sid}: sample_signal = ({expr}) ? 32'h1 : 32'h0;")

        else:
            raise ValueError(f"Unknown signal kind: {kind!r} for sig {sid}")

    return "\n".join(lines)


def build_event_start_body(start: dict, tb_input_names: Optional[set] = None) -> str:
    """Emit the body for event_start() before sim_cycle = 0.

    If tb_input_names is provided, any `u_<block>.<port> = ...` reference
    where `<port>` is a testbench-driven input gets rewritten to just `<port>`.
    That's required because DUT input ports are wires from the TB's
    perspective and can't be driven procedurally; they must be driven via
    the testbench-declared reg/logic that the wiring passes into the instance.
    """
    kind = start.get("kind", "none")
    if kind == "none":
        return "        // No autonomous start for this path (kind=none)"
    elif kind == "pulse":
        expr = start["expression"].rstrip(";").strip()
        expr = _rewrite_tb_input_refs(expr, tb_input_names or set())
        return f"        {expr};"
    elif kind == "sequence":
        lines = []
        for stmt in start.get("statements", []):
            s = stmt.rstrip(";").strip()
            s = _rewrite_tb_input_refs(s, tb_input_names or set())
            lines.append(f"        {s};")
        return "\n".join(lines) if lines else "        // empty sequence"
    else:
        raise ValueError(f"Unknown start.kind: {kind!r}")


def _rewrite_tb_input_refs(expr: str, tb_input_names: set) -> str:
    """Replace u_<block>.<port> with <port> when <port> is a tb-driven input."""
    def repl(m):
        port = m.group(2)
        if port in tb_input_names:
            return port
        return m.group(0)
    return re.sub(r"\b(u_[a-zA-Z_][a-zA-Z0-9_]*)\.([a-zA-Z_][a-zA-Z0-9_]*)\b", repl, expr)


# =============================================================================
# Config Signal Defaults (from llmmc_microarchitecturespec_filled.json)
# =============================================================================
# When an event-mode path excludes config_regs but includes a block that needs
# cfg_* inputs (e.g. path_09 includes refresh_ctrl but not config_regs, so
# cfg_tREFI_nCK has nothing driving it), the generated testbench must tie
# those inputs to their spec-mandated defaults. Otherwise the DUT's internal
# counters are X or 0, producing no autonomous activity.
#
# These values are the DDR3-1600K golden config from the microarchitecture spec.
# Keep in sync with timing_model.$derived_cycles and
# controller_architecture.refresh_policy.
CFG_DEFAULTS = {
    # Timing parameters (timing_model.$derived_cycles)
    "cfg_tRCD_nCK":         11,
    "cfg_tRP_nCK":          11,
    "cfg_tRAS_nCK":         28,
    "cfg_tRC_nCK":          39,
    "cfg_tRRD_nCK":         6,
    "cfg_tFAW_nCK":         32,
    "cfg_tWTR_nCK":         6,
    "cfg_tWR_nCK":          12,
    "cfg_tRTP_nCK":         6,
    "cfg_tCCD_nCK":         4,
    "cfg_tRFC_nCK":         128,
    "cfg_tREFI_nCK":        6240,
    "cfg_CL_nCK":           11,
    "cfg_CWL_nCK":          8,
    # Refresh policy (controller_architecture.refresh_policy)
    "cfg_max_postpone":     8,
    "cfg_urgent_threshold": 6,
    "cfg_ref_priority":     1,   # 1 = urgent_preempt per spec
    "cfg_force_refresh":    0,   # pulse input, stays low
    # Scheduler policies (config_regs defaults)
    "cfg_sched_policy":     0,   # 0 = in_order
    "cfg_row_policy":       0,   # 0 = open_page
    "cfg_self_refresh":     0,
    "cfg_bist_start":       0,
    "cfg_bist_pattern":     0,
}

# Non-cfg inputs that need tie-offs when a block is isolated from the rest of
# the design (e.g. ref_ack from scheduler, zqcs_ack from scheduler). These
# would otherwise float and hang the DUT.
HANDSHAKE_TIEOFFS = {
    "ref_ack":  0,    # scheduler never acks — refresh_ctrl accumulates postpone
    "zqcs_ack": 0,    # scheduler never acks — calibration's ZQCS stays pending
}

# Upstream completion signals: when a downstream block is tested in isolation,
# the "I'm done, you can start" signal from its upstream block normally needs
# a default so downstream triggers fire. In practice the event_spec_agent's
# start.expression handles this procedurally (e.g. path_15 uses
# "u_calibration.init_done = 1'b1;" which rewrites to init_done = 1'b1 inside
# event_start). A continuous-assign tie-off would conflict with that procedural
# drive under Xcelium. Leave this empty — the start.expression is authoritative.
UPSTREAM_COMPLETION_TIEOFFS = {}


def _emit_cfg_tieoffs(wiring_sv: str) -> Tuple[List[str], List[str]]:
    """Inspect the wiring template and emit assign statements for cfg_*
    inputs + known handshake acks that aren't driven by another block.

    Returns (tieoff_lines, warnings).
    - tieoff_lines: SV assign statements ready to paste into the TB
    - warnings: a list of human-readable warnings for cfg_* signals with
      no default in CFG_DEFAULTS (still emits a tie-off to 0, but logs it)
    """
    tb_inputs = _parse_tb_input_declarations(wiring_sv)
    tieoff_lines = []
    warnings = []

    if not tb_inputs:
        return tieoff_lines, warnings

    tieoff_lines.append("    // ---- Config & handshake tie-offs (Stage 4) ----")
    tieoff_lines.append("    // These inputs would otherwise float because the path does not")
    tieoff_lines.append("    // include the block that normally drives them. Defaults come from")
    tieoff_lines.append("    // llmmc_microarchitecturespec_filled.json (DDR3-1600K golden config).")

    any_emitted = False
    for name, width in tb_inputs:
        default = None
        if name in CFG_DEFAULTS:
            default = CFG_DEFAULTS[name]
        elif name in HANDSHAKE_TIEOFFS:
            default = HANDSHAKE_TIEOFFS[name]
        elif name in UPSTREAM_COMPLETION_TIEOFFS:
            default = UPSTREAM_COMPLETION_TIEOFFS[name]
        elif name.startswith("cfg_"):
            default = 0
            warnings.append(
                f"cfg signal {name!r} has no default in CFG_DEFAULTS — "
                f"tying to 0 (may cause DUT hang if DUT expects nonzero)"
            )
        elif name.startswith("sts_"):
            # Status inputs to config_regs from blocks not in the path.
            # Their "inactive" value is always 0 — an event hasn't happened,
            # a counter is empty, a flag is clear. This prevents X-propagation
            # into the CSR read data during mixed-mode status-register checks.
            default = 0

        if default is None:
            continue

        # Width-safe literal. For single-bit, use 1'b<n>.
        if width == 1:
            lit = f"1'b{default}"
        else:
            lit = f"{width}'d{default}"
        tieoff_lines.append(f"    assign {name} = {lit};  // default from spec")
        any_emitted = True

    if not any_emitted:
        return [], warnings  # drop the header if nothing was actually tied off

    tieoff_lines.append("")
    return tieoff_lines, warnings


def _parse_tb_input_declarations(wiring_sv: str) -> List[Tuple[str, int]]:
    """Parse the wiring template to find tb-driven inputs as (name, width)
    tuples. Uses the `// ---- Testbench-driven inputs ----` section marker.
    Extends _extract_tb_inputs_from_wiring() with width extraction.
    """
    pairs = []
    in_section = False
    for ln in wiring_sv.split("\n"):
        s = ln.strip()
        if s.startswith("// ---- Testbench-driven inputs"):
            in_section = True
            continue
        if in_section and s.startswith("// ----"):
            break
        if in_section:
            # Match: logic [W-1:0] name;  or  logic name;
            m = re.match(r"logic\s*(?:\[\s*(\d+)\s*:\s*\d+\s*\])?\s+(\w+)\s*;", s)
            if m:
                width_hi = m.group(1)
                name = m.group(2)
                width = int(width_hi) + 1 if width_hi else 1
                pairs.append((name, width))
    return pairs


def _extract_tb_inputs_from_wiring(wiring_sv: str) -> set:
    """Parse the wiring template to find testbench-driven input names.

    These appear between `// ---- Testbench-driven inputs ----` and the next
    header comment, as `logic [N:0] name;` or `logic name;` declarations.
    """
    names = set()
    in_section = False
    for ln in wiring_sv.split("\n"):
        s = ln.strip()
        if s.startswith("// ---- Testbench-driven inputs"):
            in_section = True
            continue
        if in_section and s.startswith("// ----"):
            break
        if in_section:
            m = re.match(r"logic(?:\s*\[[^\]]+\])?\s+(\w+)\s*;", s)
            if m:
                names.add(m.group(1))
    return names


# =============================================================================
# Task Library With Substitutions
# =============================================================================

def build_library_sv(event_spec: dict, tb_input_names: Optional[set] = None) -> str:
    """Produce the event-mode task library with sample_signal and event_start
    bodies filled in from the event_spec.
    """
    if generate_event_task_library_sv is None:
        raise RuntimeError(
            "Could not import generate_event_task_library_sv from path_scope_generator. "
            "Ensure path_scope_generator.py is in the same directory or on PYTHONPATH."
        )

    max_sig_id = event_spec.get("max_sig_id", 32)
    csr_enabled = bool(event_spec.get("csr_interface", {}).get("present", False))
    lib = generate_event_task_library_sv(max_sig_id=max_sig_id, csr_enabled=csr_enabled)

    # Substitute the two codegen hooks
    sample_body = build_sample_signal_cases(event_spec["signals"])
    start_body = build_event_start_body(event_spec["start"], tb_input_names)

    # The template has `// __SAMPLE_SIGNAL_CASES__` inside a plain function body
    # (returns 32'h0 by default). Replace the stub with a case statement.
    # We need to replace the two lines:
    #   sample_signal = 32'h0;
    #   // __SAMPLE_SIGNAL_CASES__
    # with a proper case (id) block.
    old_stub = (
        "        sample_signal = 32'h0;\n"
        "        // __SAMPLE_SIGNAL_CASES__"
    )
    new_stub = (
        "        sample_signal = 32'h0;\n"
        "        case (id)\n"
        f"{sample_body}\n"
        "            default: sample_signal = 32'h0;\n"
        "        endcase"
    )
    if old_stub not in lib:
        raise RuntimeError(
            "sample_signal substitution marker not found in library template. "
            "Check that path_scope_generator.py's EVENT_TASK_LIBRARY_TEMPLATE "
            "still contains '// __SAMPLE_SIGNAL_CASES__'."
        )
    lib = lib.replace(old_stub, new_stub)

    # Replace the event_start stub
    old_start = "        // __EVENT_START_BODY__"
    if old_start not in lib:
        raise RuntimeError(
            "event_start substitution marker not found in library template."
        )
    lib = lib.replace(old_start, start_body)

    return lib


# =============================================================================
# Dispatch Loop Generation
# =============================================================================

DISPATCH_LOOP_TEMPLATE = r"""
    // ==========================================================================
    // Vector File Dispatch Loop
    // ==========================================================================
    integer vec_file;
    integer n_matched;
    integer fgets_result;
    integer line_num;
    integer pc, fc, tt;
    integer k;
    reg [7:0]  op;
    reg [31:0] p_field;
    reg [31:0] d_field;
    reg [31:0] e_field;
    reg [1023:0] line_buf;

    initial begin
        pc = 0;
        fc = 0;
        tt = 0;
        line_num = 0;
        rst_n = 1'b0;

        vec_file = $fopen("__PATH_ID___vectors.hex", "r");
        if (vec_file == 0) begin
            $display("ERROR: Could not open vector file __PATH_ID___vectors.hex");
            $finish;
        end

        fgets_result = 1;
        while (fgets_result != 0) begin
            line_buf = 0;
            fgets_result = $fgets(line_buf, vec_file);
            if (fgets_result == 0) begin
                // EOF
            end else begin
                line_num = line_num + 1;
                // $sscanf returns the number of successful matches. Comment
                // lines ("// ...") and blanks return 0 — we simply skip them
                // by not entering the case block.
                n_matched = $sscanf(line_buf, "%h %h %h %h", op, p_field, d_field, e_field);
                if (n_matched == 4) begin
                    case (op)
                        8'h00: handle_reset();
                        8'h03: begin
                            for (k = 0; k < p_field; k = k + 1) event_tick();
                        end
                        8'h04: wait_for(p_field[7:0], d_field, e_field, line_num, pc, fc, tt);
                        8'h05: check_at(p_field[7:0], d_field, e_field, line_num, pc, fc, tt);
                        8'h06: check_not_yet(p_field[7:0], d_field, e_field, line_num, pc, fc, tt);
                        8'h07: expect_handshake(p_field[7:0], p_field[15:8], e_field, line_num, pc, fc, tt);
                        8'h08: check_order(p_field[7:0], p_field[15:8], e_field, line_num, pc, fc, tt);
                        8'h09: event_start();
                        // __CSR_DISPATCH__
                        default: $display("UNKNOWN OPCODE 0x%02X at line %0d", op, line_num);
                    endcase
                end
            end
        end

        $fclose(vec_file);
        $display("=========================================");
        $display("__PATH_ID__ EVENT-MODE SUMMARY");
        $display("  total_tests: %0d", tt);
        $display("  pass_count:  %0d", pc);
        $display("  fail_count:  %0d", fc);
        if (fc == 0 && tt > 0) $display("  RESULT: PASS");
        else                   $display("  RESULT: FAIL");
        $display("=========================================");
        $finish;
    end

    // Watchdog
    initial begin
        #(__SIM_TIMEOUT__ * 10);  // 10 ns per cycle @ 100 MHz ctrl clock
        $display("WATCHDOG TIMEOUT after __SIM_TIMEOUT__ cycles");
        $display("__PATH_ID__ EVENT-MODE SUMMARY");
        $display("  total_tests: %0d", tt);
        $display("  pass_count:  %0d", pc);
        $display("  fail_count:  %0d", fc);
        $display("  RESULT: WATCHDOG_FAIL");
        $finish;
    end
"""


def build_dispatch_loop(path_id: str, sim_timeout_cycles: int, csr_enabled: bool = False) -> str:
    csr_dispatch = ""
    if csr_enabled:
        csr_dispatch = (
            "8'h0A: csr_read(p_field[7:0], d_field, e_field, line_num, pc, fc, tt);\n"
            "                        "
            "8'h0B: csr_write(p_field[7:0], d_field, e_field, line_num, pc, fc, tt);"
        )
    return (DISPATCH_LOOP_TEMPLATE
            .replace("__PATH_ID__", path_id)
            .replace("__SIM_TIMEOUT__", str(sim_timeout_cycles))
            .replace("// __CSR_DISPATCH__", csr_dispatch))


# =============================================================================
# Full Testbench Assembly
# =============================================================================

TB_HEADER_TEMPLATE = r"""////////////////////////////////////////////////////////////////////////////////
// Event-Mode Testbench for {path_id}
// Generated by event_tb_codegen.py — DO NOT EDIT BY HAND
//
// Vector file format: OO PPPPPPPP DDDDDDDD EEEEEEEE
//   00 = reset        (calls handle_reset)
//   03 = step P       (advances P cycles via event_tick)
//   04 = wait_for     (P[7:0]=sig, D=value, E=timeout)
//   05 = check_at     (P[7:0]=sig, D=value, E=target_cycle)
//   06 = check_not_yet(P[7:0]=sig, D=value, E=until_cycle)
//   07 = expect_hs    (P[7:0]=valid, P[15:8]=ready, E=timeout)
//   08 = check_order  (P[7:0]=first, P[15:8]=second, E=min_gap)
//   09 = event_start
//   0A = csr_read     (P[7:0]=addr, D=expected, E=timeout)  [mixed mode only]
//   0B = csr_write    (P[7:0]=addr, D=data,     E=timeout)  [mixed mode only]
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps

module {path_id}_tb;

    // ---- Clock generation ----
    logic clk;
    logic rst_n;
    initial clk = 1'b0;
    always #5 clk = ~clk;  // 100 MHz

"""


def build_testbench(event_spec: dict, wiring_sv: str) -> str:
    """Assemble the full event-mode testbench SV file.

    wiring_sv must be the content of wiring_template.sv produced by
    path_scope_generator.generate_wiring. It contains internal wire
    declarations, tb-driven inputs, and module instantiations using
    the u_<block_id> convention.
    """
    path_id = event_spec["path_id"]
    sim_timeout = event_spec.get("sim_timeout_cycles", 200000)

    # Find testbench-driven inputs so pulse-start expressions can be rewritten
    tb_input_names = _extract_tb_inputs_from_wiring(wiring_sv)

    header = TB_HEADER_TEMPLATE.format(path_id=path_id)

    # The wiring template declares its own `logic clk, rst_n;` — we need to
    # strip those because we declare them in the TB header with our own clock
    # generator. Also strip the surrounding /* wiring */ comments if present.
    wiring_clean = _strip_wiring_clk_rst(wiring_sv)

    # Strip duplicate `logic` declarations and indent properly
    lines = [header]
    lines.append("    // ==========================================================================")
    lines.append("    // DUT Wiring (from wiring_template.sv)")
    lines.append("    // ==========================================================================")
    lines.append(wiring_clean)
    lines.append("")

    # Emit cfg_* and handshake-ack tie-offs for any tb-driven inputs that
    # would otherwise float. This is what lets refresh_ctrl actually run
    # without config_regs in the path.
    tieoff_lines, tieoff_warnings = _emit_cfg_tieoffs(wiring_sv)
    if tieoff_lines:
        lines.extend(tieoff_lines)
    for w in tieoff_warnings:
        print(f"[EventTBCodegen] WARNING: {w}")

    # Determine whether CSR support is needed
    csr_enabled = bool(event_spec.get("csr_interface", {}).get("present", False))

    # Task library with sample_signal and event_start substituted
    lib = build_library_sv(event_spec, tb_input_names)
    lines.append("    // ==========================================================================")
    lines.append("    // Event-Mode Task Library")
    lines.append("    // ==========================================================================")
    lines.append(lib)

    # handle_reset task — minimal, matches the library's expectation.
    # When CSR is enabled we must also clear the CSR request signals so the
    # first csr_read isn't racing with X values on cyc/stb/adr.
    # For non-CSR paths, we also need to initialize ALL tb-driven inputs to 0
    # so that DUT flops sampling those inputs during reset see clean 0 instead
    # of X. Otherwise a later event_start() that transitions X->1 won't produce
    # a clean rising edge (the flop already captured X and propagated it).
    # Signals that have an `assign` tie-off are skipped because they're driven
    # continuously and can't be assigned procedurally.
    tieoff_names = {name for name, _ in _parse_tb_input_declarations(wiring_sv)
                    if name in CFG_DEFAULTS or name in HANDSHAKE_TIEOFFS
                    or name in UPSTREAM_COMPLETION_TIEOFFS
                    or name.startswith("cfg_") or name.startswith("sts_")}
    tb_inputs_for_init = [
        (name, width) for name, width in _parse_tb_input_declarations(wiring_sv)
        if name not in tieoff_names
    ]

    lines.append("")
    lines.append("    // ==========================================================================")
    lines.append("    // Reset Handler")
    lines.append("    // ==========================================================================")
    lines.append("    task automatic handle_reset();")
    lines.append("        rst_n = 1'b0;")
    if csr_enabled:
        lines.append("        csr_cyc_i = 1'b0;")
        lines.append("        csr_stb_i = 1'b0;")
        lines.append("        csr_we_i  = 1'b0;")
        lines.append("        csr_adr_i = 8'b0;")
        lines.append("        csr_dat_i = 32'b0;")
        lines.append("        csr_sel_i = 4'b0;")
    # Initialize all other tb-driven inputs to 0 so DUT flops don't sample X
    # during reset. Skip ones already handled above (CSR) and skip width=0.
    csr_input_names = {"csr_cyc_i", "csr_stb_i", "csr_we_i", "csr_adr_i",
                       "csr_dat_i", "csr_sel_i"}
    for name, width in tb_inputs_for_init:
        if name in csr_input_names:
            continue
        if width == 1:
            lines.append(f"        {name} = 1'b0;")
        else:
            lines.append(f"        {name} = {width}'b0;")
    lines.append("        repeat(4) @(posedge clk);")
    lines.append("        rst_n = 1'b1;")
    lines.append("        @(posedge clk);")
    lines.append("        event_reset();")
    lines.append("        // Arm the latch after reset deassertion. event_start() will")
    lines.append("        // re-arm (and re-zero first_seen) for kind=pulse paths, but")
    lines.append("        // kind=none paths rely on this line to start observation.")
    lines.append("        latch_enabled = 1'b1;")
    lines.append("    endtask")

    # Dispatch loop
    lines.append(build_dispatch_loop(path_id, sim_timeout, csr_enabled=csr_enabled))

    lines.append("endmodule")
    lines.append("")

    return "\n".join(lines)


def _strip_wiring_clk_rst(wiring_sv: str) -> str:
    """Remove `logic clk, rst_n;` declaration from wiring template.

    The TB header already declares these with a clock generator attached,
    so the wiring template's copy would cause a duplicate declaration.
    """
    lines = wiring_sv.split("\n")
    kept = []
    for ln in lines:
        stripped = ln.strip()
        # Skip the clock/reset declaration line and its header comment
        if stripped == "logic clk, rst_n;":
            continue
        if stripped == "// ---- Clock and reset ----":
            continue
        kept.append(ln)
    return "\n".join(kept)


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Deterministic event-mode testbench codegen"
    )
    parser.add_argument("--event-spec", required=True,
                        help="Path to event_spec.json")
    parser.add_argument("--wiring", required=True,
                        help="Path to wiring_template.sv")
    parser.add_argument("--output-dir", required=True,
                        help="Directory to write <path_id>_tb.sv into")
    args = parser.parse_args()

    with open(args.event_spec) as f:
        spec = json.load(f)
    with open(args.wiring) as f:
        wiring_sv = f.read()

    tb_sv = build_testbench(spec, wiring_sv)

    os.makedirs(args.output_dir, exist_ok=True)
    out_path = os.path.join(args.output_dir, f"{spec['path_id']}_tb.sv")
    with open(out_path, "w") as f:
        f.write(tb_sv)

    print(f"[EventTBCodegen] Wrote {out_path} ({len(tb_sv.splitlines())} lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main())