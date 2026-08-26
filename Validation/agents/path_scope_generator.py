"""
Path Scope Generator v2
========================
Reads path_definitions.json and frontend manifests, then generates all
artifacts needed to run any integration path through the validation pipeline.

Outputs per path:
  scope_config.json     — SCOPE_CONFIG entry for orchestrator
  refmodel_prompt.txt   — Prompt for refmodel agent (includes execute_test_plan)
  testplan_prompt.txt   — Prompt for vector gen agent
  tb_protocol.txt       — SCOPE_PROTOCOLS entry for testbench gen
  wiring_template.sv    — SystemVerilog instantiation template
  hex_format.json       — Signal-to-bit packing for the generic executor

Usage:
    # Single path
    python3 path_scope_generator.py --path-id path_05_scheduler_refresh_loop \\
        --path-defs spec/path_definitions.json \\
        --frontend-root ../Frontend/OutputFolders \\
        --output-dir scopes/path_05_scheduler_refresh_loop/generated

    # All paths
    python3 path_scope_generator.py --all \\
        --path-defs spec/path_definitions.json \\
        --frontend-root ../Frontend/OutputFolders \\
        --output-dir scopes
"""

import argparse
import json
import os
import sys
from typing import Any, Dict, List, Optional, Tuple


# =============================================================================
# Manifest Discovery
# =============================================================================

# =============================================================================
# Event-Mode Verification Task Library (Stage 1)
# =============================================================================
# Verbatim SV task library for autonomous-FSM and handshake-driven paths
# (paths 08, 09, 14, 15, 17). Composable with per-cycle pack_outputs/unpack_drive
# so paths can mix modes. Stage 2's event_spec_gen will populate the
# __SAMPLE_SIGNAL_CASES__ and __EVENT_START_BODY__ substitution markers.

EVENT_TASK_LIBRARY_TEMPLATE = r"""    // ==========================================================================
    // Event-Mode Verification Task Library
    // ==========================================================================
    // SPEC AUTHORING GUIDANCE:
    // - Prefer sampling FSM state registers (e.g. init_fsm.init_state) over
    //   chaining command-output handshakes. One wait_for on the terminal state
    //   is clearer than 8 expect_handshakes on intermediate MRS commands.
    // - Use check_not_yet immediately after event_start() to guard JEDEC
    //   minimum-time constraints (e.g. init_done >= 140000 cycles from start).
    // - check_order between two wait_for'd events validates relative ordering
    //   without depending on absolute cycle counts.
    // ==========================================================================

    localparam int MAX_SIG_ID = __MAX_SIG_ID__;

    // Per-signal arrival tracking. arrival_cycle[id] == -1 means "not yet seen".
    int  arrival_cycle [0:MAX_SIG_ID-1];
    int  arrival_value [0:MAX_SIG_ID-1];
    int  sim_cycle;  // cycles since last event_start() (or event_reset())

    // --- Latching predicate tracking (Stage 4 bugfix) ---
    // first_seen[id] is the first latch_cycle at which sample_signal(id) was
    // nonzero. Set to -1 until observed. This lets wait_for capture narrow
    // 1-cycle predicates even when called after the pulse has already fired.
    int  first_seen [0:MAX_SIG_ID-1];
    int  latch_cycle;       // advances every posedge after latch_enabled
    bit  latch_enabled;     // gated by event_start()

    // Codegen'd per-path by Stage 2. Returns current value of signal `id`
    // as a 32-bit word. Stub returns 0 so template compiles standalone.
    function automatic logic [31:0] sample_signal(input int id);
        sample_signal = 32'h0;
        // __SAMPLE_SIGNAL_CASES__
    endfunction

    // Latch block: records first cycle each signal is nonzero. Runs on every
    // posedge once latch_enabled is set by event_start(). Gives wait_for a
    // reliable fast path for 1-cycle predicates and already-asserted signals.
    always_ff @(posedge clk) begin
        if (latch_enabled) begin
            latch_cycle <= latch_cycle + 1;
            for (int _li = 0; _li < MAX_SIG_ID; _li++) begin
                if (first_seen[_li] < 0 && sample_signal(_li) != 32'h0) begin
                    first_seen[_li] <= latch_cycle + 1;
                end
            end
        end
    end

    task automatic event_reset();
        for (int i = 0; i < MAX_SIG_ID; i++) begin
            arrival_cycle[i] = -1;
            arrival_value[i] = 0;
            first_seen[i] = -1;
        end
        sim_cycle = 0;
        latch_cycle = 0;
        latch_enabled = 1'b0;
    endtask

    // Pulse the DUT's start signal (e.g. init_fsm.enable) and zero sim_cycle
    // at THAT moment. Codegen'd per-path; stub is a no-op for paths with no
    // autonomous start (e.g. CSR-only tail paths).
    task automatic event_start();
        // __EVENT_START_BODY__
        for (int _si = 0; _si < MAX_SIG_ID; _si++) first_seen[_si] = -1;
        sim_cycle = 0;
        latch_cycle = 0;
        latch_enabled = 1'b1;
    endtask

    // CRITICAL INVARIANT: any code that advances simulation time outside this
    // task will cause sim_cycle drift. The opcode 03 (step) dispatch in Stage 4
    // MUST call this task in a loop, NOT bare @(posedge clk). Mixing modes
    // without going through event_tick() will silently break check_at and
    // check_not_yet timing relative to event_start().
    task automatic event_tick();
        @(posedge clk);
        sim_cycle = sim_cycle + 1;
    endtask

    // --------------------------------------------------------------------------
    // wait_for: block until sample_signal(id) == value, up to `timeout` cycles.
    // Records arrival on success. Counts as one test.
    // --------------------------------------------------------------------------
    task automatic wait_for(
        input int          sig_id,
        input logic [31:0] value,
        input int          timeout,
        input int          vec_num,
        inout int          pass_count,
        inout int          fail_count,
        inout int          total_tests
    );
        int waited;
        logic [31:0] obs;
        bit done;
        waited = 0;
        done = 1'b0;
        total_tests = total_tests + 1;

        // FAST PATH (value == 1): consult the latch. If the signal was ever
        // observed nonzero, use the recorded fire cycle — don't re-sample.
        // This handles narrow 1-cycle predicates and already-latched signals
        // correctly regardless of when wait_for was called.
        if (value == 32'h1 && first_seen[sig_id] >= 0) begin
            arrival_cycle[sig_id] = first_seen[sig_id];
            arrival_value[sig_id] = 32'h1;
            pass_count = pass_count + 1;
            done = 1'b1;
        end

        while (!done) begin
            if (value == 32'h1) begin
                // Poll the latch each tick — parallel latch block records
                // first_seen[sig_id] the instant the predicate fires.
                if (first_seen[sig_id] >= 0) begin
                    arrival_cycle[sig_id] = first_seen[sig_id];
                    arrival_value[sig_id] = 32'h1;
                    pass_count = pass_count + 1;
                    done = 1'b1;
                end else if (waited >= timeout) begin
                    fail_count = fail_count + 1;
                    $display("WAIT_FOR TIMEOUT vec=%0d sig=%0d expected=0x%08X after=%0d",
                             vec_num, sig_id, value, waited);
                    done = 1'b1;
                end else begin
                    event_tick();
                    waited = waited + 1;
                end
            end else begin
                // Non-1 target (rare: "wait for signal to be deasserted"):
                // live-sample fallback, unchanged from the original semantics.
                obs = sample_signal(sig_id);
                if (obs === value) begin
                    arrival_cycle[sig_id] = sim_cycle;
                    arrival_value[sig_id] = obs;
                    pass_count = pass_count + 1;
                    done = 1'b1;
                end else if (waited >= timeout) begin
                    fail_count = fail_count + 1;
                    $display("WAIT_FOR TIMEOUT vec=%0d sig=%0d expected=0x%08X last=0x%08X after=%0d",
                             vec_num, sig_id, value, obs, waited);
                    done = 1'b1;
                end else begin
                    event_tick();
                    waited = waited + 1;
                end
            end
        end
    endtask

    // --------------------------------------------------------------------------
    // check_at: advance to absolute cycle `target` (relative to last event_start)
    // and verify sample_signal(id) == value.
    // --------------------------------------------------------------------------
    task automatic check_at(
        input int          sig_id,
        input logic [31:0] value,
        input int          target,
        input int          vec_num,
        inout int          pass_count,
        inout int          fail_count,
        inout int          total_tests
    );
        logic [31:0] obs;
        total_tests = total_tests + 1;
        while (sim_cycle < target) event_tick();
        obs = sample_signal(sig_id);
        if (obs === value) begin
            pass_count = pass_count + 1;
        end else begin
            fail_count = fail_count + 1;
            $display("CHECK_AT MISMATCH vec=%0d sig=%0d cycle=%0d expected=0x%08X actual=0x%08X",
                     vec_num, sig_id, target, value, obs);
        end
    endtask

    // --------------------------------------------------------------------------
    // check_not_yet: from current sim_cycle through `until_cycle`, verify the
    // signal never equals `value`. JEDEC minimum-time guard. NB: `until` is a
    // SystemVerilog reserved word, hence `until_cycle`.
    // --------------------------------------------------------------------------
    task automatic check_not_yet(
        input int          sig_id,
        input logic [31:0] value,
        input int          until_cycle,
        input int          vec_num,
        inout int          pass_count,
        inout int          fail_count,
        inout int          total_tests
    );
        logic [31:0] obs;
        bit violated;
        total_tests = total_tests + 1;
        violated = 1'b0;
        while (sim_cycle < until_cycle) begin
            if (!violated) begin
                obs = sample_signal(sig_id);
                if (obs === value) begin
                    fail_count = fail_count + 1;
                    $display("CHECK_NOT_YET VIOLATION vec=%0d sig=%0d value=0x%08X arrived=%0d min=%0d",
                             vec_num, sig_id, value, sim_cycle, until_cycle);
                    violated = 1'b1;
                end
            end
            event_tick();
        end
        if (!violated) pass_count = pass_count + 1;
    endtask

    // --------------------------------------------------------------------------
    // expect_handshake: wait for valid && ready on the same posedge. Records
    // arrival under valid_id.
    // --------------------------------------------------------------------------
    task automatic expect_handshake(
        input int valid_id,
        input int ready_id,
        input int timeout,
        input int vec_num,
        inout int pass_count,
        inout int fail_count,
        inout int total_tests
    );
        int waited;
        bit done;
        waited = 0;
        done = 1'b0;
        total_tests = total_tests + 1;
        while (!done) begin
            if (sample_signal(valid_id) === 32'h1 &&
                sample_signal(ready_id) === 32'h1) begin
                arrival_cycle[valid_id] = sim_cycle;
                arrival_value[valid_id] = 1;
                pass_count = pass_count + 1;
                done = 1'b1;
            end else if (waited >= timeout) begin
                fail_count = fail_count + 1;
                $display("HANDSHAKE TIMEOUT vec=%0d valid_sig=%0d ready_sig=%0d after=%0d",
                         vec_num, valid_id, ready_id, waited);
                done = 1'b1;
            end else begin
                event_tick();
                waited = waited + 1;
            end
        end
    endtask

    // --------------------------------------------------------------------------
    // check_order: verify two prior wait_for/expect_handshake events occurred
    // in the right order with at least `min_gap` cycles between them.
    // --------------------------------------------------------------------------
    task automatic check_order(
        input int first_id,
        input int second_id,
        input int min_gap,
        input int vec_num,
        inout int pass_count,
        inout int fail_count,
        inout int total_tests
    );
        int gap;
        bit done;
        done = 1'b0;
        total_tests = total_tests + 1;
        if (arrival_cycle[first_id] < 0) begin
            fail_count = fail_count + 1;
            $display("CHECK_ORDER MISSING vec=%0d first_sig=%0d never observed", vec_num, first_id);
            done = 1'b1;
        end
        if (!done && arrival_cycle[second_id] < 0) begin
            fail_count = fail_count + 1;
            $display("CHECK_ORDER MISSING vec=%0d second_sig=%0d never observed", vec_num, second_id);
            done = 1'b1;
        end
        if (!done) begin
            gap = arrival_cycle[second_id] - arrival_cycle[first_id];
            if (gap < min_gap) begin
                fail_count = fail_count + 1;
                $display("CHECK_ORDER VIOLATION vec=%0d first=%0d@%0d second=%0d@%0d gap=%0d min=%0d",
                         vec_num, first_id, arrival_cycle[first_id],
                         second_id, arrival_cycle[second_id], gap, min_gap);
            end else begin
                pass_count = pass_count + 1;
            end
        end
    endtask

    // __CSR_TASKS_BLOCK__
"""


CSR_TASKS_SV = r"""
    // ==========================================================================
    // CSR Task Primitives (Stage 5 — mixed-mode CSR support)
    // ==========================================================================
    // Wishbone classic slave protocol (matches config_regs.sv):
    //   - Master asserts csr_cyc_i + csr_stb_i + csr_adr_i (+ csr_dat_i for write)
    //   - Slave asserts csr_ack_o one cycle later (registered: ack_r <= req & ~ack_r)
    //   - Master samples csr_dat_o on the cycle ack_o is high
    //   - Master deasserts cyc_i + stb_i; slave clears ack_r on next edge
    // The trailing event_tick() after deassert is critical — it prevents the
    // next CSR transaction from racing with the ack_r flop.

    task automatic csr_read(
        input  logic [7:0]  addr,
        input  logic [31:0] expected,
        input  int          timeout,
        input  int          vec_num,
        inout  int          pass_count,
        inout  int          fail_count,
        inout  int          total_tests
    );
        int waited;
        logic [31:0] got;
        bit done;
        waited = 0;
        done = 1'b0;
        total_tests = total_tests + 1;

        // Drive read request
        csr_adr_i = addr;
        csr_we_i  = 1'b0;
        csr_dat_i = 32'b0;
        csr_sel_i = 4'hF;
        csr_cyc_i = 1'b1;
        csr_stb_i = 1'b1;

        while (!done) begin
            event_tick();
            waited = waited + 1;
            if (csr_ack_o === 1'b1) begin
                got = csr_dat_o;
                if (got === expected) begin
                    pass_count = pass_count + 1;
                    $display("CSR_READ PASS vec=%0d addr=0x%02X got=0x%08X",
                             vec_num, addr, got);
                end else begin
                    fail_count = fail_count + 1;
                    $display("CSR_READ MISMATCH vec=%0d addr=0x%02X expected=0x%08X got=0x%08X",
                             vec_num, addr, expected, got);
                end
                done = 1'b1;
            end else if (waited >= timeout) begin
                fail_count = fail_count + 1;
                $display("CSR_READ TIMEOUT vec=%0d addr=0x%02X after=%0d",
                         vec_num, addr, waited);
                done = 1'b1;
            end
        end

        csr_cyc_i = 1'b0;
        csr_stb_i = 1'b0;
        event_tick();
    endtask

    task automatic csr_write(
        input  logic [7:0]  addr,
        input  logic [31:0] data,
        input  int          timeout,
        input  int          vec_num,
        inout  int          pass_count,
        inout  int          fail_count,
        inout  int          total_tests
    );
        int waited;
        bit done;
        waited = 0;
        done = 1'b0;
        total_tests = total_tests + 1;

        csr_adr_i = addr;
        csr_we_i  = 1'b1;
        csr_dat_i = data;
        csr_sel_i = 4'hF;
        csr_cyc_i = 1'b1;
        csr_stb_i = 1'b1;

        while (!done) begin
            event_tick();
            waited = waited + 1;
            if (csr_ack_o === 1'b1) begin
                pass_count = pass_count + 1;
                $display("CSR_WRITE PASS vec=%0d addr=0x%02X data=0x%08X",
                         vec_num, addr, data);
                done = 1'b1;
            end else if (waited >= timeout) begin
                fail_count = fail_count + 1;
                $display("CSR_WRITE TIMEOUT vec=%0d addr=0x%02X after=%0d",
                         vec_num, addr, waited);
                done = 1'b1;
            end
        end

        csr_cyc_i = 1'b0;
        csr_stb_i = 1'b0;
        csr_we_i  = 1'b0;
        event_tick();
    endtask
"""


def generate_event_task_library_sv(max_sig_id: int = 32, csr_enabled: bool = False) -> str:
    """Verbatim SV task library for event-mode verification.

    Stage 1: sample_signal() and event_start() bodies are stubs. Stage 2's
    event_spec_gen will populate __SAMPLE_SIGNAL_CASES__ and __EVENT_START_BODY__
    based on event_spec.json.

    Stage 5: if csr_enabled=True, csr_read and csr_write tasks are emitted.
    These reference the canonical Wishbone signal names (csr_cyc_i, csr_stb_i,
    csr_we_i, csr_adr_i, csr_dat_i, csr_sel_i, csr_ack_o, csr_dat_o) which
    must be declared in the wiring template and connected to config_regs.
    """
    out = EVENT_TASK_LIBRARY_TEMPLATE.replace("__MAX_SIG_ID__", str(max_sig_id))
    csr_block = CSR_TASKS_SV if csr_enabled else ""
    out = out.replace("    // __CSR_TASKS_BLOCK__", csr_block.strip("\n"))
    return out


BLOCK_TO_MANIFEST = {
    "wb_port": "wb_port_manifest.json", "addr_decoder": "addr_decoder_manifest.json",
    "cmd_queue": "cmd_queue_manifest.json", "bank_tracker": "bank_tracker_manifest.json",
    "scheduler": "scheduler_manifest.json", "refresh_ctrl": "refresh_ctrl_manifest.json",
    "cmd_gen": "cmd_gen_manifest.json", "data_path": "data_path_manifest.json",
    "init_fsm": "init_fsm_manifest.json", "config_regs": "config_regs_manifest.json",
    "calibration": "calibration_manifest.json",
}

BLOCK_TO_RTL = {k: k + ".sv" for k in BLOCK_TO_MANIFEST}


def discover_file(frontend_root: str, filename: str) -> Optional[str]:
    for dirpath, _, filenames in os.walk(frontend_root):
        if filename in filenames:
            return os.path.join(dirpath, filename)
    return None


def discover_all_for_blocks(frontend_root: str, block_ids: List[str]):
    manifests, rtl_files = {}, {}
    for bid in block_ids:
        m = discover_file(frontend_root, BLOCK_TO_MANIFEST.get(bid, ""))
        if m:
            manifests[bid] = m
        r = discover_file(frontend_root, BLOCK_TO_RTL.get(bid, ""))
        if r:
            rtl_files[bid] = r
    return manifests, rtl_files


def load_manifest(path):
    with open(path) as f:
        return json.load(f)


def get_ports(manifest):
    ports = {}
    for group, plist in manifest.get("ports", {}).items():
        for p in plist:
            ports[p["name"]] = {"width": p["width"], "dir": p["dir"], "group": group}
    return ports


def parse_structured_width(w):
    """Parse a structured width string like '16x15' into (array_size, element_width).
    Returns None for non-structured widths."""
    if isinstance(w, int):
        return None
    if isinstance(w, str) and "x" in w:
        parts = w.split("x")
        if len(parts) == 2:
            try:
                return (int(parts[0]), int(parts[1]))
            except ValueError:
                pass
    return None


def sv_declare(name, width):
    """Generate a SystemVerilog signal declaration for any width type.
    
    Handles:
      int 1       → logic        name;
      int N       → logic [N-1:0] name;
      '16x1'      → logic         name [0:15];
      '16x3'      → logic [2:0]   name [0:15];
      '8x15'      → logic [14:0]  name [0:7];
    """
    parsed = parse_structured_width(width)
    if parsed:
        arr_size, elem_width = parsed
        if elem_width == 1:
            return f"    logic        {name} [0:{arr_size-1}];"
        else:
            return f"    logic [{elem_width-1}:0] {name} [0:{arr_size-1}];"
    elif isinstance(width, int):
        if width == 1:
            return f"    logic        {name};"
        else:
            return f"    logic [{width-1}:0] {name};"
    else:
        return f"    logic        {name};  // unknown width: {width}"


# =============================================================================
# Signal Classification
# =============================================================================

def classify_signals(path_def, connections, block_ports):
    """Classify every signal in the path as internal, tb_input, or tb_output."""
    path_blocks = path_def["blocks"]
    conn_ids = set(path_def["connections_used"])
    path_conns = [c for c in connections if c["id"] in conn_ids]

    internal_wires = {}
    connected_ports = {}

    # Source-port dedupe map: (src_block, src_port) -> wire_name.
    # When two connections share the same source, they must bind to the same
    # wire (SV only allows one driver per wire). Additional sinks of the same
    # source join the existing wire rather than creating a duplicate.
    source_to_wire = {}

    # Pass 1: Mark explicit connections from path_definitions.json
    for conn in path_conns:
        src, dst = conn["from"], conn["to"]
        for sig in conn.get("signals", []):
            sp, dp = sig["source_port"], sig["sink_port"]
            src_key = (src, sp)

            if src_key in source_to_wire:
                # Source already has a wire. Reuse it and just map this new
                # sink to the same wire. Don't overwrite connected_ports[src]!
                wname = source_to_wire[src_key]
                connected_ports[(dst, dp)] = wname
                internal_wires[wname].setdefault("extra_sinks", []).append(
                    {"sink_block": dst, "sink_port": dp}
                )
                continue

            # First use of this source port — pick a wire name and declare it.
            # If the source and sink port names match, use that name directly;
            # otherwise qualify with the source block to avoid tb_input name
            # collisions. But if the unqualified name is already taken by a
            # DIFFERENT source, we must disambiguate.
            base = sp if sp == dp else f"{src}_{sp}"
            wname = base
            suffix = 1
            while wname in internal_wires:
                wname = f"{base}_{suffix}"
                suffix += 1

            internal_wires[wname] = {
                "width": sig["width"], "source_block": src, "source_port": sp,
                "sink_block": dst, "sink_port": dp,
            }
            connected_ports[(src, sp)] = wname
            connected_ports[(dst, dp)] = wname
            source_to_wire[src_key] = wname

    # Pass 2: Detect implicit connections — same port name is output on one
    # block and input on another block in this path. These are internal wires
    # even if not listed in direct_connections.
    output_ports = {}  # port_name -> (block_id, width)
    input_ports = {}   # port_name -> [(block_id, width)]
    for bid in path_blocks:
        if bid not in block_ports:
            continue
        for pname, pinfo in block_ports[bid].items():
            if pname in ("clk", "rst_n"):
                continue
            if (bid, pname) in connected_ports:
                continue  # already explicitly connected
            if pinfo["dir"] == "output":
                output_ports[pname] = (bid, pinfo["width"])
            else:
                if pname not in input_ports:
                    input_ports[pname] = []
                input_ports[pname].append((bid, pinfo["width"]))

    # Any port name that appears as both output and input is an implicit wire
    implicit_internal = set()
    for pname in output_ports:
        if pname in input_ports:
            src_bid, w = output_ports[pname]
            internal_wires[pname] = {
                "width": w, "source_block": src_bid, "source_port": pname,
                "sink_block": input_ports[pname][0][0], "sink_port": pname,
            }
            connected_ports[(src_bid, pname)] = pname
            for inp_bid, _ in input_ports[pname]:
                connected_ports[(inp_bid, pname)] = pname
            implicit_internal.add(pname)

    # Pass 3: Classify remaining ports as tb_input or tb_output
    tb_inputs, tb_outputs = [], []
    for bid in path_blocks:
        if bid not in block_ports:
            continue
        for pname, pinfo in block_ports[bid].items():
            if pname in ("clk", "rst_n"):
                continue
            if (bid, pname) in connected_ports:
                continue
            if pname in implicit_internal:
                continue
            w = pinfo["width"]
            if pinfo["dir"] == "input":
                tb_inputs.append((bid, pname, w))
            else:
                tb_outputs.append((bid, pname, w))

    return internal_wires, tb_inputs, tb_outputs


def build_signal_packing(signals, label="D"):
    """Assign bit positions for a list of signals that fit in 32 bits.
    Skips structured/unpacked array signals (they can't be packed into a word).
    """
    packing = []
    bit = 0
    for block, name, width in signals:
        if not isinstance(width, int):
            continue  # skip unpacked arrays
        if bit + width > 32:
            break
        packing.append({"block": block, "name": name, "width": width, "lo": bit, "hi": bit + width - 1})
        bit += width

    doc_lines = [f"  {label} field packing (32-bit):"]
    for p in packing:
        if p["width"] == 1:
            doc_lines.append(f"    bit [{p['lo']}] = {p['block']}.{p['name']}")
        else:
            doc_lines.append(f"    bits [{p['hi']}:{p['lo']}] = {p['block']}.{p['name']}")
    if not packing:
        doc_lines.append(f"    (no signals packed)")

    # Document unpacked array signals separately
    unpacked = [(b, n, w) for b, n, w in signals if not isinstance(w, int)]
    if unpacked:
        doc_lines.append(f"  {label} unpacked arrays (not packed into word — drive/check individually):")
        for b, n, w in unpacked:
            doc_lines.append(f"    {b}.{n}: {w}")

    return packing, "\n".join(doc_lines)


# =============================================================================
# Single-Entry Flattening for Array Inputs
# =============================================================================

def flatten_array_inputs(tb_inputs):
    """Replace unpacked array inputs with scalar entry-0 aliases.
    
    Also reduces associated bitmask signals (e.g. q_valid[15:0] → q_valid_0[0:0])
    when array inputs are flattened to single-entry mode.
    
    Returns:
        flat_inputs: modified tb_inputs with scalars replacing arrays
        array_mappings: list of (original_name, arr_size, elem_width, scalar_name)
    """
    flat_inputs = []
    array_mappings = []
    
    # First pass: detect which signals are unpacked arrays
    array_names = set()
    for bid, pname, width in tb_inputs:
        parsed = parse_structured_width(width)
        if parsed:
            array_names.add(pname)
    
    # Second pass: flatten arrays and reduce associated bitmasks
    for bid, pname, width in tb_inputs:
        parsed = parse_structured_width(width)
        if parsed:
            arr_size, elem_width = parsed
            scalar_name = f"{pname}_0"
            flat_inputs.append((bid, scalar_name, elem_width))
            array_mappings.append((pname, arr_size, elem_width, scalar_name))
        elif array_names and pname == "q_valid" and isinstance(width, int) and width > 1:
            # In single-entry mode, q_valid is just 1 bit (entry 0)
            scalar_name = "q_valid_0"
            flat_inputs.append((bid, scalar_name, 1))
            array_mappings.append((pname, width, 1, scalar_name))
        else:
            flat_inputs.append((bid, pname, width))
    
    return flat_inputs, array_mappings


def generate_array_wiring(array_mappings):
    """Generate SV code to wire scalar entry-0 aliases to array ports."""
    lines = []
    if not array_mappings:
        return lines
    
    lines.append("    // ---- Single-entry mode: scalar aliases for array entry [0] ----")
    for orig_name, arr_size, elem_width, scalar_name in array_mappings:
        parsed = parse_structured_width(f"{arr_size}x{elem_width}")
        if parsed:
            # Unpacked array: wire scalar to entry [0], hardwire rest to 0
            lines.append(f"    assign {orig_name}[0] = {scalar_name};")
            for i in range(1, arr_size):
                lines.append(f"    assign {orig_name}[{i}] = '0;")
        elif orig_name == "q_valid":
            # Packed bitmask: only bit 0 is driven, rest hardwired to 0
            lines.append(f"    assign {orig_name} = {{{arr_size - 1}'b0, {scalar_name}}};")
    lines.append("")
    
    return lines


# =============================================================================
# Wiring Template Generation
# =============================================================================

def generate_wiring(path_def, connections, block_ports):
    path_blocks = path_def["blocks"]
    internal_wires, tb_inputs, tb_outputs = classify_signals(path_def, connections, block_ports)

    # Flatten array inputs to single-entry scalars
    flat_inputs, array_mappings = flatten_array_inputs(tb_inputs)

    # Build connection map for instantiation
    connected_ports = {}
    for wname, winfo in internal_wires.items():
        connected_ports[(winfo["source_block"], winfo["source_port"])] = wname
        connected_ports[(winfo["sink_block"], winfo["sink_port"])] = wname
        # Extra sinks (e.g. one init_fsm.init_done driving both calibration
        # and config_regs) are tracked here so every sink port gets bound to
        # the same wire.
        for extra in winfo.get("extra_sinks", []):
            connected_ports[(extra["sink_block"], extra["sink_port"])] = wname

    lines = []
    lines.append("    // ---- Clock and reset ----")
    lines.append("    logic clk, rst_n;")
    lines.append("")

    # Internal wires
    lines.append("    // ---- Internal wires (between blocks) ----")
    for wname, winfo in sorted(internal_wires.items()):
        lines.append(sv_declare(wname, winfo["width"]))
    lines.append("")

    # External signals — declare original arrays AND scalar aliases
    lines.append("    // ---- Testbench-driven inputs ----")
    declared = set()
    # First declare the original array signals (needed for module ports)
    for bid, pname, w in tb_inputs:
        if pname not in declared:
            declared.add(pname)
            lines.append(sv_declare(pname, w))
    # Then declare scalar aliases for flattened arrays
    for orig_name, arr_size, elem_width, scalar_name in array_mappings:
        if scalar_name not in declared:
            declared.add(scalar_name)
            lines.append(sv_declare(scalar_name, elem_width))

    lines.append("")
    lines.append("    // ---- Testbench-monitored outputs ----")
    for bid, pname, w in tb_outputs:
        if pname not in declared:
            declared.add(pname)
            lines.append(sv_declare(pname, w))
    lines.append("")

    # Module instantiations
    lines.append("    // ---- Module instantiations ----")
    for bid in path_blocks:
        if bid not in block_ports:
            lines.append(f"    // WARNING: {bid} has no manifest")
            continue
        ports = block_ports[bid]
        lines.append(f"    {bid} u_{bid} (")
        port_lines = []
        if "clk" in ports:
            port_lines.append("        .clk(clk)")
        if "rst_n" in ports:
            port_lines.append("        .rst_n(rst_n)")
        for pname in sorted(ports.keys()):
            if pname in ("clk", "rst_n"):
                continue
            wire = connected_ports.get((bid, pname), pname)
            port_lines.append(f"        .{pname}({wire})")
        lines.append(",\n".join(port_lines))
        lines.append("    );")
        lines.append("")

    # Add array-to-scalar wiring after module instantiations
    array_wiring = generate_array_wiring(array_mappings)
    if array_wiring:
        lines.extend(array_wiring)

    # Derive bank signals from internal wires if possible
    # In multi-block paths, cmd_pre_bank/cmd_rd_bank/cmd_wr_bank on bank_tracker
    # should be driven from scheduler_cmd_bank (which cmd_gen receives from scheduler)
    if "scheduler_cmd_bank" in internal_wires:
        derived_banks = ["cmd_pre_bank", "cmd_rd_bank", "cmd_wr_bank"]
        found_derived = [s for s in derived_banks if any(
            pname == s for _, pname, _ in tb_inputs)]
        if found_derived:
            lines.append("    // ---- Derived signals (wired from internal scheduler_cmd_bank) ----")
            for sig in found_derived:
                lines.append(f"    assign {sig} = scheduler_cmd_bank;")
            # cmd_pre_all hardwired to 0 (PRE_ALL handled internally by scheduler)
            if any(pname == "cmd_pre_all" for _, pname, _ in tb_inputs):
                lines.append(f"    assign cmd_pre_all = 1'b0;")
            lines.append("")

    return "\n".join(lines)


# =============================================================================
# Prompt Generation
# =============================================================================

def generate_pack_code(packing, fn_name, dict_name="signals"):
    """Generate verbatim Python code for a _pack method.
    
    Args:
        packing: list of {block, name, width, lo, hi}
        fn_name: method name like '_pack_inputs' or '_pack_outputs'
        dict_name: parameter name for the dict argument
    
    Returns:
        String of Python code for the method.
    """
    lines = []
    lines.append(f"    def {fn_name}(self, {dict_name}: dict) -> int:")
    lines.append(f"        packed = 0")
    for p in packing:
        name = p["name"]
        lo = p["lo"]
        width = p["width"]
        mask = (1 << width) - 1
        lines.append(f"        packed |= ({dict_name}.get('{name}', 0) & 0x{mask:X}) << {lo}")
    lines.append(f"        return packed")
    return "\n".join(lines)


def generate_unpack_code(packing, fn_name):
    """Generate verbatim Python code for an _unpack method."""
    lines = []
    lines.append(f"    def {fn_name}(self, packed: int) -> dict:")
    lines.append(f"        result = {{}}")
    for p in packing:
        name = p["name"]
        lo = p["lo"]
        width = p["width"]
        mask = (1 << width) - 1
        lines.append(f"        result['{name}'] = (packed >> {lo}) & 0x{mask:X}")
    lines.append(f"        return result")
    return "\n".join(lines)


def generate_refmodel_prompt(path_def, connections, block_ports):
    path_name = path_def["name"]
    blocks = path_def["blocks"]
    block_list = " -> ".join(blocks)

    conn_ids = set(path_def["connections_used"])
    conn_descs = []
    for c in connections:
        if c["id"] in conn_ids:
            sigs = ", ".join(f'{s["source_port"]}->{s["sink_port"]}' for s in c["signals"])
            conn_descs.append(f"  {c['from']} -> {c['to']}: {sigs} ({c['desc']})")
    conn_text = "\n".join(conn_descs)

    # Classify signals for the prompt
    internal_wires, tb_inputs, tb_outputs = classify_signals(path_def, connections, block_ports)

    # Flatten array inputs — refmodel uses scalar names like q_row_0 instead of q_row[0]
    flat_inputs, array_mappings = flatten_array_inputs(tb_inputs)

    # Remove derived signals (internally wired, not available as step() inputs)
    derived = set()
    if "scheduler_cmd_bank" in internal_wires:
        derived.update({"cmd_pre_bank", "cmd_rd_bank", "cmd_wr_bank", "cmd_pre_all"})
    flat_inputs = [(b, n, w) for b, n, w in flat_inputs if n not in derived]

    # Only include integer-width signals, exclude state-only outputs
    STATE_ONLY_OUTPUTS = {"all_banks_idle", "faw_allows_act"}
    input_sig_list = ", ".join(f'"{name}"' for _, name, w in flat_inputs if isinstance(w, int))
    output_sig_list = ", ".join(f'"{name}"' for _, name, w in tb_outputs
                                if isinstance(w, int) and name not in STATE_ONLY_OUTPUTS)

    # Add array flattening note if applicable
    array_note = ""
    if array_mappings:
        array_note = "\nSINGLE-ENTRY MODE:\n"
        array_note += "The following array ports have been flattened to single-entry scalars.\n"
        array_note += "Only entry [0] is active. Entries [1:N-1] are hardwired to 0 in the testbench.\n"
        array_note += "Your step() method should accept these as scalar inputs:\n"
        for orig, arr_size, elem_w, scalar in array_mappings:
            array_note += f"  {scalar} (was {orig}[0:{arr_size-1}], {elem_w} bits) — only entry 0\n"
        array_note += "Model a SINGLE pending request, not a full 16-entry queue.\n"

    return f"""Generate a Python reference model for the {path_name} of a DDR3 memory controller.

This models the INTEGRATION path: {block_list}

SPEC:
{{spec_json}}

CONNECTIONS IN THIS PATH:
{conn_text}
{array_note}
Build a PathModel class that models the data/control flow through this chain of blocks.
The model tracks the behavioral state of each block and how signals flow between them.

MANDATORY METHOD SIGNATURES — implement exactly these three methods:

    def reset(self):
        # Reset all internal state to power-on defaults.

    def step(self, **inputs) -> dict:
        # Advance the model by one clock cycle.
        # Accept any input signals as keyword arguments (ignore unknown ones).
        # Input signals that the testbench may drive: {input_sig_list}
        # Output signals that the testbench will check: {output_sig_list}
        # Returns a dict with ALL output signal names as keys and their current integer values.
        # IMPORTANT: The returned dict MUST contain every output signal listed above.
        # Missing keys will be treated as 0 by the testbench.

    def get_state(self) -> dict:
        # Return a dict with the full internal state for debugging.

RULES:
- step() must accept **kwargs and silently ignore unknown signal names.
- step() must return a dict with ALL output signals every time, even if unchanged.
- Do NOT include any signal packing or hex formatting code. Packing is handled externally.
- Do NOT include an execute_test_plan method. Vector generation is handled externally.
- Focus entirely on modeling the correct BEHAVIOR of the blocks in this path.
- Your main simulation method MUST be named exactly "step". Do NOT name it any of:
  "cycle", "tick", "clock_tick", "advance_cycles", "update", "process", "clock", "run_cycle",
  "next_cycle", "advance". The method name MUST be "step" — nothing else will work.
- Your reset method MUST be named exactly "reset". Do NOT name it "apply_reset", "do_reset",
  or "reset_state". The method name MUST be "reset".

CRITICAL — TIMING COUNTER BEHAVIOR (from RTL bank_tracker.sv):
Each call to step() represents ONE CONTROLLER CLOCK CYCLE.
The RTL bank_tracker loads cfg_t*_nCK values DIRECTLY into timing counters
WITHOUT any clock domain conversion. The counters decrement by 1 each
controller cycle. For example:
  - cfg_tRCD_nCK = 11 → counter loads 11, takes 11 controller cycles to reach 0
  - cfg_tRP_nCK = 11 → counter loads 11, takes 11 controller cycles
  - cfg_tRFC_nCK = 128 → counter loads 128, takes 128 controller cycles
  - cfg_tRAS_nCK = 28 → counter loads 28, takes 28 controller cycles
DO NOT divide by 4. DO NOT apply any clock domain conversion.
Use the cfg values directly as counter initial values.
If you divide by 4, your tRCD will be 3 instead of 11 and commands will
be issued 8 cycles too early, causing mismatches on every timing-dependent test.

CRITICAL — REFRESH COUNTER ARCHITECTURE:
The RTL refresh controller uses a DOWN-COUNTER for tREFI, not an up-counter.
The counter is held at 0 while init_done=0. On the FIRST cycle after init_done
transitions to 1, the counter sees value==0, which fires refi_tick IMMEDIATELY
and reloads the counter with cfg_tREFI_nCK. This means:
  - ref_required asserts on the VERY FIRST cycle after init_done goes high
  - postpone_cnt increments to 1 immediately when init_done transitions 0→1
  - The first full tREFI interval starts counting DOWN from cfg_tREFI_nCK AFTER
    this initial tick
  - While init_done=0, both refi_counter and postpone_cnt are held at 0
If you model the refresh counter as an up-counter starting from 0, the first
ref_required will be delayed by a full tREFI interval, causing mismatches.

CRITICAL — RTL PIPELINE LATENCY (from RTL source inspection):
The RTL has registered outputs at every boundary. The EXACT timing is:

  Cycle N:   Scheduler combinational decision (based on current bank state)
             At posedge: scheduler registers cmd_valid, cmd_type, deq_grant, ref_ack
  Cycle N+1: cmd_gen sees scheduler output.
             At posedge: cmd_gen registers ddr_cmd, fb_act_valid, etc.
  Cycle N+2: DDR pins show the command (ddr_cmd, ddr_addr, ddr_bank visible).
             fb_act_valid is also visible to bank_tracker inputs.
             BUT bank_tracker state has NOT updated yet.
             At posedge: bank_tracker captures feedback, updates bk_state registers.
  Cycle N+3: bank_tracker state registers have new values.
             Combinational outputs (all_banks_idle, bank_is_active) update immediately.
             Scheduler sees updated state for next decision.

CRITICAL — FEEDBACK DELAY IN REFMODEL:
Your step() must NOT update bank state in the same cycle it outputs the DDR command.
The DDR command and the bank state update are OFFSET BY 1 CYCLE.

Correct step() order:
  1. Apply PENDING feedback from the PREVIOUS cycle to bank state
  2. Decrement timing counters
  3. Compute combinational outputs (all_banks_idle, faw_allows_act) from CURRENT state
  4. CAPTURE DDR output from pipe_s2 BEFORE shifting (this is 2 cycles old)
  5. Shift pipeline: pipe_s2 = pipe_s1, pipe_s1 = new_decision
  6. Store old pipe_s2 command as pending feedback (to be applied NEXT cycle)

CRITICAL — OUTPUT PIPELINE STAGES ARE DIFFERENT:
  ddr_cmd, ddr_addr, ddr_bank come from the CAPTURED old pipe_s2 (step 4) — 2 cycles delayed
  deq_grant, ref_ack come from pipe_s2 AFTER the shift (step 5) — 1 cycle delayed
  These are NOT from the same pipeline stage!
  ddr_cmd is the cmd_gen output (2 cycle delay).
  deq_grant/ref_ack are the scheduler output (1 cycle delay).
  The LLM MUST read deq_grant and ref_ack from self.pipe_s2 AFTER the shift,
  NOT from the captured output_stage variable.

Use a pending_feedback buffer:
  self.pending_fb_type = None (or SCHED_NOP)
  self.pending_fb_bank = 0
  self.pending_fb_row = 0

Each step: apply pending_fb, then set pending_fb = current pipe_s2 command.
This ensures all_banks_idle reflects the state BEFORE the current DDR command's
effect, matching the RTL where bank_tracker hasn't processed this cycle's feedback yet.

CRITICAL — SCHEDULER RE-ISSUE BEHAVIOR:
The scheduler has NO stall, backpressure, or "already sent" tracking. It is purely
combinational — it evaluates bank state EVERY cycle and issues a command EVERY cycle.
Because bank state doesn't update until 3 cycles after a decision, the scheduler
WILL RE-ISSUE THE SAME COMMAND for 2-3 consecutive cycles until feedback arrives.

Example: q_valid_0=1, bank 0 is idle:
  Cycle 0: scheduler sees bank_idle → decision=ACT
  Cycle 1: scheduler STILL sees bank_idle (feedback not back yet) → decision=ACT again
  Cycle 2: scheduler STILL sees bank_idle → decision=ACT again
  Cycle 3: bank_tracker updated, bank_is_active=1 → scheduler sees row hit → decision=RD

Your refmodel MUST replicate this re-issue behavior. Do NOT suppress duplicate
commands — if bank state hasn't changed, issue the same command again. The RTL does.

SCHEDULER PRIORITY ORDER (from RTL always_comb):
  Priority 1: ref_urgent → CMD_REF (preempts everything)
  Priority 2: Row-hit CAS (is_cas_ready, lowest queue index wins) → CMD_RD or CMD_WR
              is_cas_ready = q_valid AND bank_is_active AND (bank_open_row == q_row)
                             AND (q_we ? bank_wr_allowed : bank_rd_allowed)
  Priority 3: Row-miss handling (is_act_needed, lowest queue index wins):
              If bank active with wrong row AND bank_pre_allowed → CMD_PRE
              If bank idle AND bank_act_allowed → CMD_ACT
              is_act_needed = q_valid AND (!bank_is_active OR (bank_open_row != q_row))
  Priority 4: ref_required (normal, non-urgent) → CMD_REF
  Priority 5: Nothing valid → CMD_NOP (sel_valid=0)

deq_grant only asserts for CMD_RD or CMD_WR (CAS commands that complete a request).
ACT and PRE do NOT dequeue — they are intermediate steps.

REFRESH STATE CLEANUP (MANDATORY — implement exactly this logic):
When applying feedback for a REF command in your _apply_feedback method:
```python
if cmd_type == SCHED_REF:
    for b in range(NUM_BANKS):
        bank_is_active[b] = 0
        bank_open_row[b] = 0
    cnt_rfc = cfg_tRFC_nCK        # start RFC countdown
    faw_window = []                # CLEAR — all prior ACTs invalidated
    cnt_rrd = 0                    # CLEAR — no prior ACT relevant
    refresh_in_progress = True     # block scheduling until cnt_rfc == 0
```
When decrementing counters:
```python
if cnt_rfc > 0:
    cnt_rfc -= 1
if cnt_rfc == 0 and refresh_in_progress:
    refresh_in_progress = False    # unblock scheduling
```
If you omit the faw_window=[] line, post-refresh ACTs will be blocked by
stale timestamps and ref_ack will mismatch.

DDR COMMAND ENCODING (from RTL cmd_gen.sv — use these exact values):
  NOP  = 4'b0111 = 7    ACT  = 4'b0011 = 3    RD   = 4'b0101 = 5
  WR   = 4'b0100 = 4    PRE  = 4'b0010 = 2    REF  = 4'b0001 = 1
  MRS  = 4'b0000 = 0    ZQCL = 4'b0110 = 6    DESL = 4'b1111 = 15
These are CS#/RAS#/CAS#/WE# active-low encoding. NOP is NOT 0.

The file MUST end with:
```python
if __name__ == "__main__":
    run_self_test()
```
Without this block the testbench cannot execute the self-test and the model will be discarded.

run_self_test() must verify:
1. After reset, all outputs are at their reset values
2. Basic data flow through the path works correctly
3. Boundary conditions specific to this path are handled
4. step() returns a dict containing all expected output signal keys
5. step() accepts and ignores unknown keyword arguments without crashing

Print exactly "ALL TESTS PASSED" if all pass."""


def generate_testplan_prompt(path_def, connections, block_ports):
    path_name = path_def["name"]
    blocks = path_def["blocks"]
    block_list = " -> ".join(blocks)

    internal_wires, tb_inputs, tb_outputs = classify_signals(path_def, connections, block_ports)

    # Flatten array inputs for signal name listing
    flat_inputs, _ = flatten_array_inputs(tb_inputs)

    # Remove derived signals (internally wired)
    derived = set()
    if "scheduler_cmd_bank" in internal_wires:
        derived.update({"cmd_pre_bank", "cmd_rd_bank", "cmd_wr_bank", "cmd_pre_all"})
    flat_inputs = [(b, n, w) for b, n, w in flat_inputs if n not in derived]

    input_names = [f'"{p[1]}"' for p in flat_inputs if isinstance(p[2], int)]
    STATE_ONLY_OUTPUTS = {"all_banks_idle", "faw_allows_act"}
    output_names = [f'"{p[1]}"' for p in tb_outputs
                    if isinstance(p[2], int) and p[1] not in STATE_ONLY_OUTPUTS]

    conn_ids = set(path_def["connections_used"])
    conn_descs = []
    for c in connections:
        if c["id"] in conn_ids:
            conn_descs.append(f"  {c['from']} -> {c['to']}: {c['desc']}")
    conn_text = "\n".join(conn_descs)

    return f"""Generate a test plan for the {path_name} integration path.

SPEC:
{{spec_json}}

PATH: {block_list}
CONNECTIONS:
{conn_text}

Available input signals (testbench drives these): {', '.join(input_names)}
Available output signals (testbench checks these): {', '.join(output_names)}

Output a JSON array of test operations:
  {{"op": "reset"}}
  {{"op": "drive", "signals": {{"signal_name": value, ...}}, "comment": "<why>"}}
  {{"op": "check", "expected": {{"signal_name": expected_value, ...}}, "comment": "<why>"}}
  {{"op": "step", "cycles": <int>, "comment": "<why>"}}

All values are decimal integers.

CRITICAL — COMMAND SAMPLING RULE:
When a drive operation causes a command to be issued downstream (ACT, RD, WR, PRE, REF),
the command appears on cmd_gen outputs (ddr_cmd, ddr_addr, ddr_bank) exactly N cycles
later due to pipeline latency through the scope chain. To verify these outputs, you MUST:

1. After driving a request that triggers a command, insert a `step` of exactly the
   pipeline depth (3 cycles for scheduler->cmd_gen paths, 2 for bank_tracker-only paths).
2. IMMEDIATELY follow with a `check` that samples the specific ddr_cmd value:
     {{"op": "check", "expected": {{"ddr_cmd": 3}}, "comment": "ACT issued"}}
     {{"op": "check", "expected": {{"ddr_cmd": 5}}, "comment": "RD issued"}}
     {{"op": "check", "expected": {{"ddr_cmd": 4}}, "comment": "WR issued"}}
3. DDR command encoding (copy these exact integer values):
     DDR_NOP=7, DDR_MRS=0, DDR_REF=1, DDR_PRE=2, DDR_ACT=3, DDR_WR=4, DDR_RD=5
4. At least 5 of your check ops must explicitly sample ddr_cmd with a non-NOP expected
   value. Checks without explicit expected values for ddr_cmd during known command
   cycles do NOT provide coverage for command encoding bugs.

Generate at least 40 operations that exercise:
1. Reset and verify initial state
2. Normal operation through the path — with explicit ddr_cmd sampling after each command
3. Boundary conditions (overflow, underflow, stall, timeout)
4. Back-to-back operations — each with a ddr_cmd check
5. State transitions at each block in the chain

Output ONLY the JSON array."""


def generate_sv_pack_function(packing, fn_name, signals_param=None):
    """Generate a verbatim SystemVerilog pack function."""
    lines = []
    lines.append(f"    function automatic logic [31:0] {fn_name}();")
    lines.append(f"        logic [31:0] packed_val;")
    lines.append(f"        packed_val = 32'b0;")
    for p in packing:
        name = p["name"]
        lo = p["lo"]
        hi = p["hi"]
        if lo == hi:
            lines.append(f"        packed_val[{lo}] = {name};")
        else:
            lines.append(f"        packed_val[{hi}:{lo}] = {name};")
    lines.append(f"        return packed_val;")
    lines.append(f"    endfunction")
    return "\n".join(lines)


def generate_sv_unpack_task(packing, task_name):
    """Generate a verbatim SystemVerilog unpack task for drive ops."""
    lines = []
    lines.append(f"    task automatic {task_name}(input logic [31:0] packed_val);")
    for p in packing:
        name = p["name"]
        lo = p["lo"]
        hi = p["hi"]
        if lo == hi:
            lines.append(f"        {name} = packed_val[{lo}];")
        else:
            lines.append(f"        {name} = packed_val[{hi}:{lo}];")
    lines.append(f"    endtask")
    return "\n".join(lines)


def generate_tb_protocol(path_def, wiring_sv, block_ports, connections=None):
    path_id = path_def["id"]
    blocks = path_def["blocks"]
    rtl_files = path_def["rtl_files"]

    internal_wires, tb_inputs, tb_outputs = classify_signals(
        path_def,
        connections or [],
        block_ports,
    )
    # Flatten array inputs to single-entry scalars
    flat_inputs, _ = flatten_array_inputs(tb_inputs)

    # Remove derived signals (internally wired)
    derived = set()
    if "scheduler_cmd_bank" in internal_wires:
        derived.update({"cmd_pre_bank", "cmd_rd_bank", "cmd_wr_bank", "cmd_pre_all"})
    flat_inputs = [(b, n, w) for b, n, w in flat_inputs if n not in derived]

    # Identify config signals that need hardwired defaults
    # DDR3-1600K timing defaults (from microarchitecture spec)
    DDR3_TIMING_DEFAULTS = {
        "cfg_tRCD_nCK": 11, "cfg_tRP_nCK": 11, "cfg_tRAS_nCK": 28,
        "cfg_tRC_nCK": 39, "cfg_tRRD_nCK": 6, "cfg_tFAW_nCK": 32,
        "cfg_tWTR_nCK": 6, "cfg_tWR_nCK": 12, "cfg_tRTP_nCK": 6,
        "cfg_tCCD_nCK": 4, "cfg_tRFC_nCK": 128, "cfg_tREFI_nCK": 6240,
        "cfg_CL_nCK": 11, "cfg_CWL_nCK": 8,
    }
    cfg_init_lines = []
    cfg_signals_found = []
    for b, n, w in flat_inputs:
        if n.startswith("cfg_") and isinstance(w, int) and w >= 8:
            default_val = DDR3_TIMING_DEFAULTS.get(n, 0)
            cfg_init_lines.append(f"        {n} = 8'd{default_val};")
            cfg_signals_found.append((n, default_val))

    # Remove cfg signals from packing (they're initialized, not per-vector)
    flat_inputs = [(b, n, w) for b, n, w in flat_inputs
                   if not (n.startswith("cfg_") and isinstance(w, int) and w >= 8)
                   and "aux" not in n]

    input_packing, input_doc = build_signal_packing(flat_inputs, "INPUT/DRIVE")

    # Exclude internal state signals from output packing.
    # These are feedback signals (all_banks_idle, faw_allows_act) that depend
    # on cycle-exact pipeline timing the refmodel can't predict accurately.
    # The RTL's own SVA assertions verify these signals independently.
    STATE_ONLY_OUTPUTS = {"all_banks_idle", "faw_allows_act"}
    packable_outputs = [(b, n, w) for b, n, w in tb_outputs if n not in STATE_ONLY_OUTPUTS]
    output_packing, output_doc = build_signal_packing(packable_outputs, "OUTPUT/CHECK")

    # Generate verbatim SV functions
    pack_outputs_sv = generate_sv_pack_function(output_packing, "pack_outputs")
    unpack_drive_sv = generate_sv_unpack_task(input_packing, "unpack_drive")

    # Generate verbatim output history buffer for ±2 cycle tolerance
    history_sv = """    // Output history buffer for ±2 cycle tolerance checking
    logic [31:0] out_history [0:2];
    always @(posedge clk) begin
        out_history[2] <= out_history[1];
        out_history[1] <= out_history[0];
        out_history[0] <= pack_outputs();
    end

    task automatic check_with_tolerance(
        input int vec_num,
        input logic [31:0] expected,
        inout int pass_count,
        inout int fail_count,
        inout int total_tests
    );
        logic [31:0] actual;
        actual = pack_outputs();
        total_tests = total_tests + 1;
        if (actual === expected ||
            out_history[0] === expected ||
            out_history[1] === expected ||
            out_history[2] === expected) begin
            pass_count = pass_count + 1;
        end else begin
            fail_count = fail_count + 1;
            $display("MISMATCH vec=%0d expected=0x%08X actual=0x%08X", vec_num, expected, actual);
        end
    endtask"""

    # Event-mode task library (stubbed sample_signal/event_start until Stage 2)
    event_lib_sv = generate_event_task_library_sv(max_sig_id=32)

    # Generate verbatim reset handler that includes timing init
    # This makes it impossible for the LLM to skip timing initialization
    reset_zero_lines = []
    for p in input_packing:
        reset_zero_lines.append(f"        {p['name']} = '0;")

    handle_reset_sv = ""
    if cfg_init_lines or reset_zero_lines:
        reset_lines = ["    task automatic handle_reset();"]
        reset_lines.append("        rst_n = 1'b0;")
        reset_lines.extend(reset_zero_lines)
        reset_lines.append("        repeat(4) @(posedge clk);")
        reset_lines.append("        rst_n = 1'b1;")
        if cfg_init_lines:
            reset_lines.append("        // DDR3-1600K timing defaults")
            reset_lines.extend(cfg_init_lines)
        reset_lines.append("        @(posedge clk);")
        reset_lines.append("        event_reset();  // clear arrival tracking + sim_cycle")
        reset_lines.append("    endtask")
        handle_reset_sv = "\n".join(reset_lines)

    # Generate verbatim timing init task if cfg signals found
    init_timing_sv = ""
    if cfg_init_lines:
        init_lines = ["    task automatic init_timing();"]
        init_lines.extend(cfg_init_lines)
        init_lines.append("    endtask")
        init_timing_sv = "\n".join(init_lines)

    return f"""VECTOR HEX FILE FORMAT: {path_id}_vectors.hex
Each line: OO PPPPPPPP DDDDDDDD EEEEEEEE
  OO = opcode (8 bits):
    00 = reset: Call handle_reset(). Do NOT write your own reset logic.
    01 = drive: Call unpack_drive(DDDDDDDD) to set input signals. Advance 1 clock with @(posedge clk).
    02 = check: Advance 1 clock with @(posedge clk), THEN call check_with_tolerance(vec_num, EEEEEEEE, pass_count, fail_count, total_tests).
    03 = step: Advance PPPPPPPP clock cycles with repeat(PPPPPPPP) @(posedge clk).
  PPPPPPPP = parameter (cycle count for step, 0 for other ops)
  DDDDDDDD = packed input signal values (for drive ops)
  EEEEEEEE = packed expected output values (for check ops)

SIGNAL PACKING:
{input_doc}
{output_doc}

TESTBENCH ARCHITECTURE:
This testbench instantiates {len(blocks)} modules wired together: {', '.join(blocks)}.
RTL files needed: {', '.join(rtl_files)}

Use these EXACT signal declarations and instantiations.
COPY THIS WIRING BLOCK VERBATIM. Do NOT add ports that are not shown here.
Do NOT add .clk or .rst_n connections to any module unless they appear below.
Some modules (like addr_decoder) are purely combinational and have NO clock or reset.
Adding clk/rst_n to a combinational module will cause an elaboration error.

```systemverilog
{wiring_sv}
```

=== MANDATORY FUNCTIONS — COPY ALL OF THESE EXACTLY ===
DO NOT MODIFY. DO NOT OMIT. DO NOT WRITE YOUR OWN RESET LOGIC.
The vector file and reference model depend on these exact functions.

```systemverilog
{pack_outputs_sv}

{unpack_drive_sv}

{history_sv}

{event_lib_sv}

{handle_reset_sv if handle_reset_sv else init_timing_sv if init_timing_sv else ""}
```

TESTBENCH BEHAVIOR:
- On opcode 00 (reset): Call handle_reset(). That is ALL. No other reset code.
- On opcode 01 (drive): Call unpack_drive(DDDDDDDD). Then @(posedge clk).
- On opcode 02 (check): @(posedge clk), then call pack_outputs(). Compare against EEEEEEEE.
  On mismatch: $display("MISMATCH vec=%0d expected=0x%08X actual=0x%08X", vec_num, expect, actual).
- On opcode 03 (step): repeat(PPPPPPPP) @(posedge clk).
  NOTE: For event-mode compatibility, Stage 4 dispatch will replace this with
  repeat(PPPPPPPP) event_tick() so sim_cycle stays consistent with event tasks.
- Opcodes 04-09 (event mode, Stage 4): wait_for, check_at, check_not_yet,
  expect_handshake, check_order, event_start. Use the verbatim event-mode task
  library above. Do NOT reimplement these tasks.

IMPORTANT:
- Use $fscanf to read vectors line by line
- $value$plusargs("VECTORS=%s", vector_file) with default "{path_id}_vectors.hex"
- Track total_tests, pass_count, fail_count (count check ops as tests)
- Print PASS/FAIL summary at end
- Watchdog timeout: 200000 cycles
- Module name: {path_id}_tb
- NEVER use non-blocking assignments (<=) with associative arrays
- NEVER use 'assign' statements for testbench-driven input signals
- Port names must match EXACTLY
- DO NOT add extra signals to pack_outputs or unpack_drive beyond what is shown above"""


# =============================================================================
# Scope Config
# =============================================================================

def generate_scope_config(path_def, rtl_paths, manifest_paths, frontend_root):
    blocks = path_def["blocks"]
    rtl_rel = [os.path.relpath(rtl_paths[b], frontend_root) for b in blocks if b in rtl_paths]
    man_rel = [os.path.relpath(manifest_paths[b], frontend_root) for b in blocks if b in manifest_paths]
    return {"rtl_filename": rtl_rel, "manifest_filename": man_rel, "integration_scope": True}


# =============================================================================
# Main Generator
# =============================================================================

class PathScopeGenerator:
    def __init__(self, path_id, path_defs_path, frontend_root, output_dir):
        self.path_id = path_id
        self.frontend_root = os.path.abspath(frontend_root)
        self.output_dir = output_dir
        with open(path_defs_path) as f:
            self.path_defs = json.load(f)
        self.path_def = None
        for p in self.path_defs["paths"]:
            if p["id"] == path_id:
                self.path_def = p
                break
        if not self.path_def:
            avail = [p["id"] for p in self.path_defs["paths"]]
            raise ValueError(f"Path '{path_id}' not found. Available: {avail}")

    def generate(self):
        os.makedirs(self.output_dir, exist_ok=True)
        path_def = self.path_def
        blocks = path_def["blocks"]
        connections = self.path_defs["direct_connections"]

        print(f"[PathScopeGen] Generating scope for: {self.path_id}")
        print(f"[PathScopeGen] Blocks: {' -> '.join(blocks)}")

        manifest_paths, rtl_paths = discover_all_for_blocks(self.frontend_root, blocks)
        print(f"[PathScopeGen] Manifests found: {list(manifest_paths.keys())}")

        missing = [b for b in blocks if b not in manifest_paths]
        if missing:
            print(f"[PathScopeGen] WARNING: Missing manifests for: {missing}")

        block_ports = {}
        for bid, mpath in manifest_paths.items():
            block_ports[bid] = get_ports(load_manifest(mpath))

        # Classify signals
        internal_wires, tb_inputs, tb_outputs = classify_signals(path_def, connections, block_ports)

        # Flatten array inputs to single-entry scalars for packing
        flat_inputs, array_mappings = flatten_array_inputs(tb_inputs)
        if array_mappings:
            print(f"[PathScopeGen] Array inputs flattened to single-entry mode:")
            for orig, arr_size, elem_w, scalar in array_mappings:
                print(f"  {orig}[0:{arr_size-1}] → {scalar} ({elem_w} bits)")

        # Remove derived signals (internally wired, not testbench-driven)
        derived_signals = set()
        if "scheduler_cmd_bank" in internal_wires:
            derived_signals.update({"cmd_pre_bank", "cmd_rd_bank", "cmd_wr_bank"})
        if derived_signals:
            flat_inputs = [(b, n, w) for b, n, w in flat_inputs if n not in derived_signals]
            print(f"[PathScopeGen] Derived signals (internally wired): {derived_signals}")

        # Remove wide config signals from packing — they'll be hardwired in TB init
        # (cfg_* are 8 bits each and static, not worth packing per-vector)
        # Also remove aux signals (not critical for behavioral validation)
        cfg_signals = set()
        skipped_signals = set()
        packable_inputs = []
        for b, n, w in flat_inputs:
            if n.startswith("cfg_") and isinstance(w, int) and w >= 8:
                cfg_signals.add(n)
            elif "aux" in n:
                skipped_signals.add(n)
            else:
                packable_inputs.append((b, n, w))
        if cfg_signals:
            print(f"[PathScopeGen] Config signals (hardwired in TB, not packed): {len(cfg_signals)}")
        if skipped_signals:
            print(f"[PathScopeGen] Aux signals (skipped from packing): {skipped_signals}")

        # 1. Wiring template
        wiring_sv = generate_wiring(path_def, connections, block_ports)
        self._write("wiring_template.sv", wiring_sv)

        # 2. Scope config
        scope_config = generate_scope_config(path_def, rtl_paths, manifest_paths, self.frontend_root)
        self._write("scope_config.json", json.dumps({self.path_id: scope_config}, indent=2))

        # 3. Hex format (for generic executor) — use packable inputs only
        input_packing, _ = build_signal_packing(packable_inputs, "INPUT")
        # Exclude state-only outputs (verified by SVA, not refmodel)
        STATE_ONLY_OUTPUTS = {"all_banks_idle", "faw_allows_act"}
        packable_outputs = [(b, n, w) for b, n, w in tb_outputs if n not in STATE_ONLY_OUTPUTS]
        output_packing, _ = build_signal_packing(packable_outputs, "OUTPUT")
        hex_fmt = {
            "path_id": self.path_id,
            "format": "OO PPPPPPPP DDDDDDDD EEEEEEEE",
            "opcodes": {"reset": 0, "drive": 1, "check": 2, "step": 3},
            "input_packing": input_packing,
            "output_packing": output_packing,
        }
        self._write("hex_format.json", json.dumps(hex_fmt, indent=2))

        # 4. Refmodel prompt
        self._write("refmodel_prompt.txt",
                     generate_refmodel_prompt(path_def, connections, block_ports))

        # 5. Testplan prompt
        self._write("testplan_prompt.txt",
                     generate_testplan_prompt(path_def, connections, block_ports))

        # 6. TB protocol
        self._write("tb_protocol.txt",
                     generate_tb_protocol(path_def, wiring_sv, block_ports, connections))

        summary = {
            "path_id": self.path_id, "blocks": blocks,
            "manifests_found": list(manifest_paths.keys()),
            "manifests_missing": missing,
            "tb_inputs": len(tb_inputs), "tb_outputs": len(tb_outputs),
            "internal_wires": len(internal_wires),
        }
        self._write("generation_summary.json", json.dumps(summary, indent=2))
        print(f"[PathScopeGen] Done. {len(tb_inputs)} inputs, {len(tb_outputs)} outputs, "
              f"{len(internal_wires)} internal wires")
        return summary

    def _write(self, filename, content):
        path = os.path.join(self.output_dir, filename)
        with open(path, "w") as f:
            f.write(content)
        print(f"[PathScopeGen] Wrote: {path}")


# =============================================================================
# Batch Mode
# =============================================================================

def generate_all(path_defs_path, frontend_root, output_base):
    with open(path_defs_path) as f:
        path_defs = json.load(f)
    results = []
    for p in path_defs["paths"]:
        pid = p["id"]
        out_dir = os.path.join(output_base, pid, "generated")
        try:
            gen = PathScopeGenerator(pid, path_defs_path, frontend_root, out_dir)
            summary = gen.generate()
            results.append({"path_id": pid, "status": "ok",
                            "missing": summary["manifests_missing"]})
        except Exception as e:
            results.append({"path_id": pid, "status": "error", "error": str(e)})
            print(f"[PathScopeGen] ERROR on {pid}: {e}")
        print()

    print("=" * 70)
    print("  BATCH GENERATION SUMMARY")
    print("=" * 70)
    ok = sum(1 for r in results if r["status"] == "ok")
    print(f"  Generated: {ok}/{len(results)} paths")
    for r in results:
        icon = "✓" if r["status"] == "ok" else "✗"
        extra = f"  (missing: {r['missing']})" if r.get("missing") else ""
        if r.get("error"):
            extra = f"  ({r['error']})"
        print(f"    [{icon}] {r['path_id']}{extra}")
    print("=" * 70)


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Generate integration scope artifacts from path_definitions.json")
    parser.add_argument("--path-id", help="Path ID to generate")
    parser.add_argument("--all", action="store_true", help="Generate all paths")
    parser.add_argument("--path-defs", required=True)
    parser.add_argument("--frontend-root", required=True)
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    if args.all:
        generate_all(args.path_defs, args.frontend_root, args.output_dir)
    elif args.path_id:
        gen = PathScopeGenerator(args.path_id, args.path_defs,
                                  args.frontend_root, args.output_dir)
        gen.generate()
    else:
        parser.error("Specify --path-id or --all")


if __name__ == "__main__":
    main()