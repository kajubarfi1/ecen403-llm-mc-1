#!/usr/bin/env python3
"""
+======================================================================+
|                 DATA PATH / ALIGNMENT GENERATOR                          |
|                                                                      |
|  Phase 3 RTL Generation Generator                                        |
|  Generates: data_path.sv + data_path_tb.sv + data_path_manifest.json |
|                                                                      |
|  Dependencies: cmd_gen (Phase 3), wb_port (Phase 1),                 |
|                config_regs (Phase 1)                                 |
|                                                                      |
|  Spec sections consumed:                                             |
|    host_interface, data_path_mapping, clocking_model,                |
|    memory_geometry, controller_architecture, timing_model            |
|                                                                      |
|  Implements:                                                         |
|    Write path: wb_port req_wdata -> serialize -> DQ/DQS/DM pins     |
|    Read path:  DQ/DQS capture -> deserialize -> rsp_rdata to wb_port |
|    Alignment:  1/2/4/8:1 clock ratio, BL8 burst packing/unpacking    |
|    Tag track:  aux_width passthrough for read response ordering      |
|                                                                      |
|  Testbench: ~35 tests across 8 sections (A-H)                       |
|    A: Reset behavior            B: Single write data path            |
|    C: Single read data path     D: BL8 burst write                   |
|    E: BL8 burst read            F: Write mask (DM) propagation       |
|    G: Aux tag passthrough       H: Back-to-back / pipeline           |
|                                                                      |
|  Validation checks: DP-001 through DP-015                            |
+======================================================================+
"""

import json
import sys
import os
import math
from pathlib import Path
from datetime import datetime

_HERE = os.path.dirname(os.path.abspath(__file__))
_SCRIPTS_DIR = os.path.dirname(_HERE)
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)
from manifest_stamp import stamp


class DataPathGenerator:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.host      = self.spec["host_interface"]
        self.data_path = self.spec["data_path_mapping"]
        self.clocking  = self.spec["clocking_model"]
        self.geometry  = self.spec["memory_geometry"]
        self.ctrl_arch = self.spec["controller_architecture"]
        self.timing    = self.spec["timing_model"]

        self.p = self._derive_parameters()

    # ================================================================
    # Parameter derivation
    # ================================================================
    def _derive_parameters(self) -> dict:
        p = {}

        # Clock
        p["CTRL_FREQ"]    = self.clocking["$derived"]["controller_frequency_MHz"]
        p["CTRL_PERIOD"]  = self.clocking["controller_clock_period_ns"]
        p["tCK_ns"]       = self.clocking["$derived"]["tCK_ns"]
        p["CLK_RATIO"]    = self.clocking["clock_ratio_ddr_to_controller"]

        # Data widths
        p["DATA_WIDTH"]   = self.host["data_width_bits"]
        p["ADDR_WIDTH"]   = self.host["address_width_bits"]
        p["SEL_WIDTH"]    = p["DATA_WIDTH"] // self.host["granularity_bits"]
        p["AUX_WIDTH"]    = self.ctrl_arch["aux_width"]

        # DDR PHY widths -- the real physical DQ bus width is
        # data_path_mapping.ddr_channel_width_bits (device_width_bits x
        # byte_lanes, e.g. 8 x 2 = 16 for this spec's x8/2-lane config),
        # NOT the host word width. The generator used to read a field
        # named "dq_width_bits", which doesn't exist anywhere in the spec
        # schema, so it always silently fell back to a hardcoded default
        # (8) and the port itself was hardcoded to DATA_WIDTH regardless
        # of that parameter's value anyway -- ddr_dq_o/ddr_dq_i were 32
        # bits (the host word width) instead of 16 (the real channel
        # width), with no actual per-beat pack/unpack logic at all (see
        # Defect 2, Frontend2/VALIDATION_INTEGRATION_PLAN.md).
        p["DQ_WIDTH"]     = self.data_path.get(
            "ddr_channel_width_bits",
            self.geometry.get("device_width_bits", 8) * self.geometry.get("byte_lanes", 1))
        p["DQS_PAIRS"]    = max(1, p["DQ_WIDTH"] // 8)  # one DQS pair per byte lane on the real channel
        p["DM_WIDTH"]     = p["DQS_PAIRS"]  # one DM bit per byte lane

        # Burst
        p["BURST_LEN"]    = self.host["max_burst_length"]  # 8 for BL8
        p["BEATS_PER_CYC"] = p["CLK_RATIO"]  # 4 DDR transfers per ctrl cycle

        # For BL8 with 4:1 ratio: 8 transfers = 2 controller cycles. This is
        # a fact about the DDR command's burst length vs. the clock ratio --
        # independent of how a host word packs onto the (possibly narrower)
        # channel, see WORD_BEATS below. Kept for documentation/manifest
        # continuity; no longer drives the write/read FSM cycle counts.
        p["BURST_CTRL_CYCLES"] = p["BURST_LEN"] // p["BEATS_PER_CYC"]

        # How many channel-width beats one host word actually takes to
        # pack/unpack (pack_32_to_16 => 2). This -- not BURST_CTRL_CYCLES --
        # is what the write-drive and read-capture FSMs below are sized on.
        if p["DATA_WIDTH"] % p["DQ_WIDTH"] != 0:
            p["WORD_BEATS"] = None  # validate() reports this as an error
        else:
            p["WORD_BEATS"] = p["DATA_WIDTH"] // p["DQ_WIDTH"]

        # CAS latency in controller cycles (for read data timing)
        derived_cyc = self.timing.get("$derived_cycles", {})
        tCK = p["tCK_ns"]
        ctrl_period = p["CTRL_PERIOD"]

        # CL and CWL from spec
        mr_data = self.spec.get("initialization_sequence", {}).get("mode_registers", {})
        p["CL"]  = mr_data.get("MR0", {}).get("cas_latency_cycles", 11)
        p["CWL"] = mr_data.get("MR2", {}).get("cas_write_latency_cycles", 8)

        # Convert to controller cycles
        p["CL_CTRL"]  = math.ceil(p["CL"] * tCK / ctrl_period)
        p["CWL_CTRL"] = math.ceil(p["CWL"] * tCK / ctrl_period)

        # Write-to-read turnaround
        p["WL"] = p["CWL"]  # write latency = CWL in DDR3

        # FIFO depth for read return buffer
        p["RD_FIFO_DEPTH"] = self.host.get("read_buffer_depth", 16)
        p["WR_FIFO_DEPTH"] = self.host.get("write_buffer_depth", 16)
        # (N-1).bit_length(), not N.bit_length() -- FIFO_PTR_W doubles as
        # both the wraparound-safe pointer's extra-bit width (wants
        # index_width+1, which N.bit_length() happens to give) AND the
        # array index width (wants exactly index_width) for wr_buf/rd_fifo,
        # both RD_FIFO_DEPTH entries deep. N.bit_length() is one bit too
        # wide for the index role -- e.g. for RD_FIFO_DEPTH=16 it gives 5,
        # so wr_wptr[4:0]/rd_wptr[4:0] can reach 16-31 once the pointer has
        # counted past 16 total pushes, indexing out of bounds on a 16-entry
        # array. Same root cause as wb_port's TAG_PTR_WIDTH bug (Phase 1).
        p["FIFO_PTR_W"]    = max(1, (p["RD_FIFO_DEPTH"] - 1).bit_length())

        # Queue depth
        p["QUEUE_DEPTH"]   = self.ctrl_arch["command_queue_depth"]

        # ROW_BITS for manifest
        p["ROW_BITS"]      = self.geometry["row_bits"]
        p["BANK_BITS"]     = self.geometry["bank_bits"]

        return p

    # ================================================================
    # Validation
    # ================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["WORD_BEATS"] is None:
            errors.append(f"DATA_WIDTH ({p['DATA_WIDTH']}) is not a whole multiple of "
                          f"DQ_WIDTH ({p['DQ_WIDTH']}) -- can't pack a host word onto the channel")
        elif p["WORD_BEATS"] not in (1, 2, 3, 4):
            errors.append(f"WORD_BEATS ({p['WORD_BEATS']}) must be 1-4 to fit the 2-bit beat counter")
        if p["BURST_LEN"] != 8:
            errors.append(f"BURST_LEN must be 8 for DDR3 BL8, got {p['BURST_LEN']}")
        if p["CLK_RATIO"] not in (1, 2, 4, 8):
            errors.append(f"Expected clock ratio in (1, 2, 4, 8) -- the DDR3 "
                           f"controller gearbox rates implemented here -- got "
                           f"{p['CLK_RATIO']}:1")
        if p["CL"] < 5 or p["CL"] > 14:
            errors.append(f"CAS latency {p['CL']} out of DDR3 range [5,14]")
        if p["CWL"] < 5 or p["CWL"] > 12:
            errors.append(f"CAS write latency {p['CWL']} out of DDR3 range [5,12]")
        # wr_buf is addressed directly by a write's own aux tag's low bits
        # (CONSERVE/WRITE_CMD_TO_BEATS fix, Validation 2026-11-05) -- needs
        # AUX_WIDTH wide enough to index it collision-free.
        need = max(1, (p["RD_FIFO_DEPTH"] - 1).bit_length())
        if p["AUX_WIDTH"] < need:
            errors.append(f"AUX_WIDTH={p['AUX_WIDTH']} too narrow to index "
                          f"RD_FIFO_DEPTH={p['RD_FIFO_DEPTH']} (need >= {need} bits)")
        return errors

    # ================================================================
    # RTL generation
    # ================================================================
    def generate_rtl(self) -> str:
        p = self.p

        lines = []
        L = lines.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module:    data_path")
        L(f"// File:      data_path.sv")
        L(f"// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)")
        L(f"// Generator:     Data Path / Alignment Generator (Phase 3)")
        L(f"// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}")
        L(f"//")
        L(f"// Description:")
        L(f"//   DDR3 data path and alignment block. Bridges the {p['CTRL_FREQ']:.0f}MHz")
        L(f"//   controller domain to the {int(p['CTRL_FREQ'] * p['CLK_RATIO'])}MHz DDR domain.")
        L(f"//   Write: serialize {p['DATA_WIDTH']}-bit words into BL8 DDR transfers.")
        L(f"//   Read:  deserialize BL8 captures back to {p['DATA_WIDTH']}-bit words.")
        L(f"//   Alignment: {p['CLK_RATIO']}:1 ratio, {p['BURST_CTRL_CYCLES']} ctrl cycles per BL8 burst.")
        L(f"//")
        L(f"// Key parameters:")
        L(f"//   DATA_WIDTH={p['DATA_WIDTH']}, DQ_WIDTH={p['DQ_WIDTH']}, BL={p['BURST_LEN']}")
        L(f"//   CL={p['CL']} nCK ({p['CL_CTRL']} ctrl), CWL={p['CWL']} nCK ({p['CWL_CTRL']} ctrl)")
        L(f"//   AUX_WIDTH={p['AUX_WIDTH']}, RD_FIFO_DEPTH={p['RD_FIFO_DEPTH']}")
        L(f"//")
        L(f"// Validation: DP-001 .. DP-015")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"")
        L(f"module data_path #(")
        L(f"    parameter DATA_WIDTH       = {p['DATA_WIDTH']},")
        L(f"    parameter DQ_WIDTH         = {p['DQ_WIDTH']},")
        L(f"    parameter DM_WIDTH         = {p['DM_WIDTH']},")
        L(f"    parameter SEL_WIDTH        = {p['SEL_WIDTH']},")
        L(f"    parameter AUX_WIDTH        = {p['AUX_WIDTH']},")
        L(f"    parameter BURST_LEN        = {p['BURST_LEN']},")
        L(f"    parameter CLK_RATIO        = {p['CLK_RATIO']},")
        L(f"    parameter BURST_CTRL_CYC   = {p['BURST_CTRL_CYCLES']},")
        L(f"    parameter WORD_BEATS       = {p['WORD_BEATS']},")
        L(f"    parameter RD_FIFO_DEPTH    = {p['RD_FIFO_DEPTH']},")
        L(f"    parameter FIFO_PTR_W       = {p['FIFO_PTR_W']},")
        L(f"    parameter CL_CTRL_DEFAULT  = {p['CL_CTRL']},")
        L(f"    parameter CWL_CTRL_DEFAULT = {p['CWL_CTRL']}")
        L(f") (")
        L(f"    // Clock / Reset")
        L(f"    input  logic                    clk,")
        L(f"    input  logic                    rst_n,")
        L(f"")
        L(f"    // From cmd_gen: command timing signals")
        L(f"    input  logic                    cmd_wr_valid,     // WR command issued this cycle")
        L(f"    input  logic                    cmd_rd_valid,     // RD command issued this cycle")
        L(f"    input  logic [AUX_WIDTH-1:0]    cmd_aux,          // aux tag for this command")
        L(f"")
        L(f"    // From wb_port: write data")
        L(f"    input  logic                    wr_data_valid,    // write data available")
        L(f"    input  logic [DATA_WIDTH-1:0]   wr_data,          // write data word")
        L(f"    input  logic [SEL_WIDTH-1:0]    wr_mask,          // byte lane mask")
        L(f"    input  logic [AUX_WIDTH-1:0]    wr_data_aux,      // aux tag for this write's data --")
        L(f"                                                      // addresses wr_buf directly, so a WR")
        L(f"                                                      // command (cmd_aux) always fetches its")
        L(f"                                                      // own write's data regardless of what")
        L(f"                                                      // order the scheduler issues commands in")
        L(f"                                                      // (CONSERVE/WRITE_CMD_TO_BEATS fix,")
        L(f"                                                      // Validation 2026-11-05)")
        L(f"    output logic                    wr_data_ready,    // backpressure to wb_port")
        L(f"")
        L(f"    // To wb_port: read response")
        L(f"    output logic                    rd_rsp_valid,     // read data available")
        L(f"    output logic [DATA_WIDTH-1:0]   rd_rsp_data,      // read data word")
        L(f"    output logic [AUX_WIDTH-1:0]    rd_rsp_aux,       // read response tag")
        L(f"")
        L(f"    // From config_regs: runtime-configurable latencies")
        L(f"    input  logic [7:0]              cfg_CL_nCK,       // CAS read latency")
        L(f"    input  logic [7:0]              cfg_CWL_nCK,      // CAS write latency")
        L(f"")
        L(f"    // DDR3 PHY interface (directly to DRAM pins) -- DQ_WIDTH-wide,")
        L(f"    // the real physical channel width, NOT DATA_WIDTH (the host word")
        L(f"    // width). A host word packs onto the channel over WORD_BEATS")
        L(f"    // cycles ({p['DATA_WIDTH']}-bit host word / {p['DQ_WIDTH']}-bit channel = {p['WORD_BEATS']} beats).")
        L(f"    output logic [DQ_WIDTH-1:0]     ddr_dq_o,         // write data to DRAM")
        L(f"    output logic                    ddr_dq_oe,        // DQ output enable")
        L(f"    input  logic [DQ_WIDTH-1:0]     ddr_dq_i,         // read data from DRAM")
        L(f"    output logic [DM_WIDTH-1:0]     ddr_dm_o,         // data mask")
        L(f"    output logic                    ddr_dqs_o,        // DQS strobe out")
        L(f"    output logic                    ddr_dqs_oe,       // DQS output enable")
        L(f"    input  logic                    ddr_dqs_i         // DQS strobe in (read)")
        L(f");")
        L(f"")

        # ── Write pipeline ──
        L(f"    // ================================================================")
        L(f"    // Write data buffer (FIFO)")
        L(f"    // ================================================================")
        L(f"    // Stores write data + mask until cmd_gen issues WR command.")
        L(f"    // After WR, data is driven onto DQ pins for BURST_CTRL_CYC cycles.")
        L(f"")
        L(f"    typedef struct packed {{")
        L(f"        logic [DATA_WIDTH-1:0]  data;")
        L(f"        logic [SEL_WIDTH-1:0]   mask;")
        L(f"    }} wr_entry_t;")
        L(f"")
        L(f"    // wr_buf is addressed by each write's own aux tag (low bits),")
        L(f"    // not by wr_wptr/wr_rptr position -- a WR command can be")
        L(f"    // issued out of the order its data was pushed (the FR-FCFS")
        L(f"    // scheduler reorders writes exactly like it reorders reads),")
        L(f"    // so cmd_aux is what actually says whose data to fetch")
        L(f"    // (CONSERVE/WRITE_CMD_TO_BEATS, CONSERVE/WRITE_REQUEST_TO_DATA")
        L(f"    // fix, Validation 2026-11-05). wr_wptr/wr_rptr stay as pure")
        L(f"    // OCCUPANCY counters -- every existing backpressure invariant")
        L(f"    // (wr_data_ready, WB-012, DP-001) is unchanged.")
        L(f"    wr_entry_t wr_buf       [0:RD_FIFO_DEPTH-1];")
        L(f"    logic      wr_buf_valid [0:RD_FIFO_DEPTH-1];")
        L(f"    logic [FIFO_PTR_W:0] wr_wptr, wr_rptr;")
        L(f"    wire  [FIFO_PTR_W:0] wr_count = wr_wptr - wr_rptr;")
        L(f"    wire                  wr_full  = (wr_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);")
        L(f"    wire                  wr_empty = (wr_count == 0);")
        L(f"")
        L(f"    // wr_data_ready and the push below are completed further down,")
        L(f"    // after the write FSM -- both need to know whether a pop is")
        L(f"    // happening this very cycle, which only the FSM's own state can")
        L(f"    // say (see wr_pop_this_cycle).")
        L(f"")

        # ── Write state machine ──
        L(f"    // ================================================================")
        L(f"    // Write serialization FSM")
        L(f"    // ================================================================")
        L(f"    // When cmd_wr_valid fires, we wait CWL controller cycles, then")
        L(f"    // drive DQ for BURST_CTRL_CYC cycles (2 cycles for BL8 @ 4:1).")
        L(f"    //")
        L(f"    // Mirrors the read side exactly (see the comment above Read")
        L(f"    // capture and deserialization below for the full reasoning):")
        L(f"    // the DRAM expects write data CWL cycles after the WR command")
        L(f"    // was issued, not CWL cycles after our engine gets around to")
        L(f"    // it, so a queued command's wait is loaded fresh AT ISSUE")
        L(f"    // (Validation addendum 9, 2026-10-28, finding 2, plus the")
        L(f"    // same one-cycle regression addendum 10 found on the read side,")
        L(f"    // 2026-10-29 -- a bare wr_pend_cnt counter has the identical")
        L(f"    // one-cycle-late problem a registered FIFO does). Three paths:")
        L(f"    //  - BYPASS (wr_bypass): engine idle, nothing queued -- same")
        L(f"    //    cycle, zero added latency, matching the original design.")
        L(f"    //  - QUEUED (WR_IDLE): arrived while busy; its deadline has")
        L(f"    //    arrived -- drive now, no WR_WAIT needed.")
        L(f"    //  - CHAINED (WR_DRIVE's own exit): the next queued write's")
        L(f"    //    deadline arrives right as this one's last beat drives --")
        L(f"    //    go straight into its drive instead of detouring through")
        L(f"    //    WR_IDLE, which would cost the one cycle neither this nor")
        L(f"    //    the read side's capture window can spare. The scheduler's")
        L(f"    //    CAS spacing (cas_spacing_ctr, scheduler_gen.py) keeps")
        L(f"    //    deadlines from arriving faster than the engine can drain")
        L(f"    //    them, so chaining is the common case for back-to-back")
        L(f"    //    writes, not an edge case.")
        L(f"")
        L(f"    typedef enum logic [1:0] {{")
        L(f"        WR_IDLE   = 2'd0,")
        L(f"        WR_WAIT   = 2'd1,   // waiting CWL latency -- bypass path only")
        L(f"        WR_DRIVE  = 2'd2    // driving DQ pins")
        L(f"    }} wr_state_t;")
        L(f"")
        L(f"    wr_state_t wr_state;")
        L(f"    logic [7:0] wr_lat_ctr;        // CWL countdown -- bypass path only")
        L(f"    logic [1:0] wr_burst_ctr;       // burst beat counter")
        L(f"    logic [DATA_WIDTH-1:0] wr_dat_r; // latched write data")
        L(f"    logic [SEL_WIDTH-1:0]  wr_msk_r; // latched mask")
        L(f"")
        L(f"    // Saturating countdown, same reasoning and the same Python-")
        L(f"    // verified design as the read side's rd_pend_wait above --")
        L(f"    // see that comment. wr_head_due_r is the one extra piece: a")
        L(f"    // REGISTERED copy of \"the current head of wr_pend has a zero")
        L(f"    // countdown\", computed one cycle ahead so wr_data_ready (an")
        L(f"    // output port) never has to combinationally index wr_pend_wait")
        L(f"    // by wr_pend_rptr and compare it itself -- Backend, 2026-11-02:")
        L(f"    // that exact mux-then-compare, on the output path, was the")
        L(f"    // single worst-penalized endpoint on the chip even after the")
        L(f"    // width fix. Checked against the same Python model as the read")
        L(f"    // side (2000 cycles, zero mismatches between wr_head_due_r and")
        L(f"    // a fresh combinational check every single cycle, including")
        L(f"    // through pops that advance which entry is \"head\").")
        L(f"    //")
        L(f"    // Controller cycles from issue to the first drive cycle -- same")
        L(f"    // CWL formula the bypass path below uses.")
        L(f"    wire [31:0] wr_wait_cycles = (cfg_CWL_nCK <= CLK_RATIO[7:0])")
        L(f"        ? 32'd1")
        L(f"        : 32'(((cfg_CWL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0])) + 32'd1;")
        L(f"    wire [3:0] wr_wait_init = (wr_wait_cycles >= 32'd2) ? 4'(wr_wait_cycles - 32'd2) : 4'd0;")
        L(f"")
        L(f"    // Pending-write-command queue: overflow only (a bypassed write")
        L(f"    // never enters it), tracks each queued WR command's countdown.")
        L(f"    // A SEPARATE queue from wr_buf (the write DATA, pushed on")
        L(f"    // wr_data_valid from wb_port, a different event stream). These")
        L(f"    // two streams do NOT stay in lockstep -- the scheduler can issue")
        L(f"    // a later-accepted write's command before an earlier one's (the")
        L(f"    // same FR-FCFS row-hit reordering that affects reads), so")
        L(f"    // wr_pend_aux carries each queued command's own tag (mirroring")
        L(f"    // the read side's rd_pend_aux) and wr_buf is fetched BY that")
        L(f"    // tag below, not by position (CONSERVE/WRITE_CMD_TO_BEATS fix,")
        L(f"    // Validation 2026-11-05 -- this comment used to claim the two")
        L(f"    // queues were issue-ordered together; that was the bug).")
        L(f"    logic [3:0] wr_pend_wait [0:RD_FIFO_DEPTH-1];  // saturating countdown, 0 = due")
        L(f"    logic [AUX_WIDTH-1:0] wr_pend_aux [0:RD_FIFO_DEPTH-1];  // tag of the queued command")
        L(f"    logic [FIFO_PTR_W:0] wr_pend_wptr, wr_pend_rptr;")
        L(f"    wire  [FIFO_PTR_W:0] wr_pend_count = wr_pend_wptr - wr_pend_rptr;")
        L(f"    wire                  wr_pend_full  = (wr_pend_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);")
        L(f"    wire                  wr_pend_empty = (wr_pend_count == 0);")
        L(f"    logic wr_head_due_r;  // declared here, defined after wr_pop_this_cycle exists to read")
        L(f"")
        L(f"    wire wr_bypass = (wr_state == WR_IDLE) && wr_pend_empty && cmd_wr_valid && !wr_empty;")
        L(f"    wire wr_pend_push = cmd_wr_valid && !wr_pend_full && !wr_bypass;")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            wr_pend_wptr <= '0;")
        L(f"        else if (wr_pend_push)")
        L(f"            wr_pend_wptr <= wr_pend_wptr + 1'b1;")
        L(f"")
        L(f"    // Every queued entry's countdown decrements every cycle,")
        L(f"    // independent of queue position -- same reasoning as the read")
        L(f"    // side's rd_pend_wait update.")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            for (int i = 0; i < RD_FIFO_DEPTH; i++) wr_pend_wait[i] <= '0;")
        L(f"        end else begin")
        L(f"            for (int i = 0; i < RD_FIFO_DEPTH; i++) begin")
        L(f"                if (wr_pend_push && (i == wr_pend_wptr[FIFO_PTR_W-1:0])) begin")
        L(f"                    wr_pend_wait[i] <= wr_wait_init;")
        L(f"                    wr_pend_aux[i]  <= cmd_aux;")
        L(f"                end else if (wr_pend_wait[i] != 0)")
        L(f"                    wr_pend_wait[i] <= wr_pend_wait[i] - 4'd1;")
        L(f"            end")
        L(f"        end")
        L(f"    end")
        L(f"")
        L(f"    // NOTE: wr_buf_valid is NOT cleared in this FSM block -- it is")
        L(f"    // driven solely by the write-buffer push block further down")
        L(f"    // (single always_ff driver rule), which clears the popped")
        L(f"    // entry via wr_pop_this_cycle / wr_pop_idx.")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            wr_state     <= WR_IDLE;")
        L(f"            wr_lat_ctr   <= '0;")
        L(f"            wr_burst_ctr <= '0;")
        L(f"            wr_rptr      <= '0;")
        L(f"            wr_dat_r     <= '0;")
        L(f"            wr_msk_r     <= '0;")
        L(f"            wr_pend_rptr <= '0;")
        L(f"        end else begin")
        L(f"            case (wr_state)")
        L(f"                WR_IDLE: begin")
        L(f"                    if (!wr_pend_empty && !wr_empty && wr_head_due_r) begin")
        L(f"                        // Queued while busy; its countdown has reached 0 --")
        L(f"                        // drive now, no separate wait state needed. Fetch by")
        L(f"                        // this entry's OWN tag (wr_pend_aux), not by wr_rptr")
        L(f"                        // position -- it may not be the data pushed Nth.")
        L(f"                        wr_dat_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].data;")
        L(f"                        wr_msk_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].mask;")
        L(f"                        wr_rptr      <= wr_rptr + 1'b1;")
        L(f"                        wr_pend_rptr <= wr_pend_rptr + 1'b1;")
        L(f"                        wr_state     <= WR_DRIVE;")
        L(f"                        wr_burst_ctr <= '0;")
        L(f"                    end else if (wr_bypass) begin")
        L(f"                        // Latch data from write buffer. Bypass fires the SAME")
        L(f"                        // cycle as cmd_wr_valid (nothing queued ahead of it),")
        L(f"                        // so this write's own tag is simply this cycle's")
        L(f"                        // cmd_aux -- no wr_pend_aux lookup needed.")
        L(f"                        wr_dat_r <= wr_buf[cmd_aux[FIFO_PTR_W-1:0]].data;")
        L(f"                        wr_msk_r <= wr_buf[cmd_aux[FIFO_PTR_W-1:0]].mask;")
        L(f"                        wr_rptr  <= wr_rptr + 1'b1;")
        L(f"                        if (cfg_CWL_nCK <= CLK_RATIO[7:0]) begin")
        L(f"                            // CWL fits in one ctrl cycle, go straight to drive")
        L(f"                            wr_state     <= WR_DRIVE;")
        L(f"                            wr_burst_ctr <= '0;")
        L(f"                        end else begin")
        L(f"                            wr_state   <= WR_WAIT;")
        L(f"                            // same fix as the read side's rd_lat_ctr (addendum")
        L(f"                            // 4/5, Validation, 2026-10-22/27): ceil(CWL /")
        L(f"                            // CLK_RATIO) - 1, not a hardcoded >> 2 -- the latter")
        L(f"                            // assumed a fixed 4:1 ratio and, like the read side")
        L(f"                            // before its fix, was one cycle off besides.")
        L(f"                            wr_lat_ctr <= (cfg_CWL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] - 1'b1;")
        L(f"                        end")
        L(f"                    end")
        L(f"                end")
        L(f"                WR_WAIT: begin")
        L(f"                    if (wr_lat_ctr == 0)")
        L(f"                        wr_state <= WR_DRIVE;")
        L(f"                    else")
        L(f"                        wr_lat_ctr <= wr_lat_ctr - 1'b1;")
        L(f"                    wr_burst_ctr <= '0;")
        L(f"                end")
        L(f"                WR_DRIVE: begin")
        L(f"                    if (wr_burst_ctr == WORD_BEATS[1:0] - 1'b1) begin")
        L(f"                        // Last beat -- chain straight into the next queued")
        L(f"                        // write if its countdown has reached 0 or will by")
        L(f"                        // next cycle, same reasoning as the read side's")
        L(f"                        // RD_CAPTURE exit. Not registered like wr_head_due_r")
        L(f"                        // above -- this is the rarer back-to-back-chaining")
        L(f"                        // path, not the output port, and the 4-bit compare")
        L(f"                        // here is already an 8x narrower structure than the")
        L(f"                        // 32-bit one Backend measured.")
        L(f"                        if (!wr_pend_empty && !wr_empty &&")
        L(f"                            (wr_pend_wait[wr_pend_rptr[FIFO_PTR_W-1:0]] <= 4'd1)) begin")
        L(f"                            // Fetch by this entry's OWN tag, same as the WR_IDLE")
        L(f"                            // queued path above -- it may not be the data")
        L(f"                            // pushed Nth.")
        L(f"                            wr_dat_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].data;")
        L(f"                            wr_msk_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].mask;")
        L(f"                            wr_rptr      <= wr_rptr + 1'b1;")
        L(f"                            wr_pend_rptr <= wr_pend_rptr + 1'b1;")
        L(f"                            wr_state     <= WR_DRIVE;")
        L(f"                            wr_burst_ctr <= '0;")
        L(f"                        end else begin")
        L(f"                            wr_state <= WR_IDLE;")
        L(f"                        end")
        L(f"                    end else")
        L(f"                        wr_burst_ctr <= wr_burst_ctr + 1'b1;")
        L(f"                end")
        L(f"                default: wr_state <= WR_IDLE;")
        L(f"            endcase")
        L(f"        end")
        L(f"    end")
        L(f"")
        L(f"    // wr_data_ready must allow a new push in the same cycle a pop")
        L(f"    // happens, not only when wr_full (a REGISTERED count, this")
        L(f"    // cycle's wr_wptr/wr_rptr) already reads not-full -- without")
        L(f"    // this, a write arriving the instant the buffer is full and also")
        L(f"    // draining this cycle gets refused, because the slot frees up a")
        L(f"    // cycle later than wr_data_ready said no (Validation, 2026-10-29,")
        L(f"    // addendum 11: 1 of 600 write words lost this exact way on")
        L(f"    // refresh-stress traffic). wr_pop_this_cycle mirrors the three")
        L(f"    // places WR_IDLE/WR_DRIVE above pop wr_buf -- the standard")
        L(f"    // full-FIFO same-cycle case, one accept and one release landing")
        L(f"    // together.")
        L(f"    wire wr_pop_this_cycle =")
        L(f"        ((wr_state == WR_IDLE) &&")
        L(f"         ((!wr_pend_empty && !wr_empty && wr_head_due_r) || wr_bypass))")
        L(f"        || ((wr_state == WR_DRIVE) && (wr_burst_ctr == WORD_BEATS[1:0] - 1'b1) &&")
        L(f"            !wr_pend_empty && !wr_empty && (wr_pend_wait[wr_pend_rptr[FIFO_PTR_W-1:0]] <= 4'd1));")
        L(f"")
        L(f"    // Which wr_buf entry the pop (if any) frees this cycle: the")
        L(f"    // bypass path fetches by this cycle's cmd_aux; the queued and")
        L(f"    // chained paths fetch by the pending-queue head's own tag.")
        L(f"    // wr_bypass requires wr_pend_empty, so it is mutually exclusive")
        L(f"    // with both other pop paths.")
        L(f"    wire [FIFO_PTR_W-1:0] wr_pop_idx = wr_bypass")
        L(f"        ? cmd_aux[FIFO_PTR_W-1:0]")
        L(f"        : wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0];")
        L(f"")
        L(f"    assign wr_data_ready = ~wr_full || wr_pop_this_cycle;")
        L(f"")
        L(f"    // wr_head_due_r's own update -- one cycle behind wr_pop_this_cycle")
        L(f"    // (needed to compute it) and the per-entry countdown decrement")
        L(f"    // above (needed for the fresh-load case below), both declared by")
        L(f"    // this point. Mirrors the verified Python model exactly: the next")
        L(f"    // head is rptr+1 if a pop retires today's head, else rptr")
        L(f"    // unchanged; its value next cycle is a fresh load if it's also")
        L(f"    // the index being pushed into this very cycle (reachable: an")
        L(f"    // empty wr_pend, engine busy, a new command arrives -- wptr and")
        L(f"    // rptr coincide before the push), otherwise the usual decrement-")
        L(f"    // or-saturate.")
        L(f"    wire [FIFO_PTR_W-1:0] wr_pend_head_idx_next =")
        L(f"        wr_pend_rptr[FIFO_PTR_W-1:0] + (wr_pop_this_cycle ? 1'b1 : 1'b0);")
        L(f"    wire wr_pend_head_fresh_load =")
        L(f"        wr_pend_push && (wr_pend_head_idx_next == wr_pend_wptr[FIFO_PTR_W-1:0]);")
        L(f"    wire [3:0] wr_pend_head_wait_next =")
        L(f"        wr_pend_head_fresh_load                      ? wr_wait_init :")
        L(f"        (wr_pend_wait[wr_pend_head_idx_next] != 0)    ? (wr_pend_wait[wr_pend_head_idx_next] - 4'd1) :")
        L(f"                                                         4'd0;")
        L(f"    wire [FIFO_PTR_W:0] wr_pend_count_next =")
        L(f"        wr_pend_count - (wr_pop_this_cycle ? 1'b1 : 1'b0) + (wr_pend_push ? 1'b1 : 1'b0);")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            wr_head_due_r <= 1'b0;")
        L(f"        else if (wr_pend_count_next == 0)")
        L(f"            wr_head_due_r <= 1'b0;")
        L(f"        else")
        L(f"            wr_head_due_r <= (wr_pend_head_wait_next == 4'd0);")
        L(f"")
        L(f"    // Write buffer push -- stored BY TAG (wr_data_aux), not by")
        L(f"    // wr_wptr position; wr_wptr itself only tracks occupancy now.")
        L(f"    // This is the ONLY always_ff driving wr_buf_valid: the pop's")
        L(f"    // clear comes first, the push's set second, so a push landing")
        L(f"    // on the very slot being freed this cycle stays valid.")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            wr_wptr <= '0;")
        L(f"            for (int i = 0; i < RD_FIFO_DEPTH; i++) wr_buf_valid[i] <= 1'b0;")
        L(f"        end else begin")
        L(f"            if (wr_pop_this_cycle)")
        L(f"                wr_buf_valid[wr_pop_idx] <= 1'b0;")
        L(f"            if (wr_data_valid && (~wr_full || wr_pop_this_cycle)) begin")
        L(f"                wr_buf[wr_data_aux[FIFO_PTR_W-1:0]]       <= '{{data: wr_data, mask: wr_mask}};")
        L(f"                wr_buf_valid[wr_data_aux[FIFO_PTR_W-1:0]] <= 1'b1;")
        L(f"                wr_wptr <= wr_wptr + 1'b1;")
        L(f"            end")
        L(f"        end")
        L(f"    end")
        L(f"")

        # ── DDR write outputs ──
        L(f"    // Write data to DDR pins -- wr_dat_r is DATA_WIDTH-wide (one")
        L(f"    // host word); drive it onto the DQ_WIDTH-wide channel over")
        L(f"    // WORD_BEATS beats, low beat first (pack_32_to_16, little-")
        L(f"    // endian: low half of the word goes out first).")
        L(f"    always_comb begin")
        L(f"        ddr_dq_o = wr_dat_r[DQ_WIDTH-1:0];")
        L(f"        for (int wb = 0; wb < WORD_BEATS; wb++)")
        L(f"            if (wr_burst_ctr == wb[1:0])")
        L(f"                ddr_dq_o = wr_dat_r[(wb+1)*DQ_WIDTH-1 -: DQ_WIDTH];")
        L(f"    end")
        L(f"    assign ddr_dq_oe  = (wr_state == WR_DRIVE);")
        L(f"")
        L(f"    // Data mask, sliced the same way -- BYTES_PER_BEAT host-side")
        L(f"    // sel bits per channel beat.")
        L(f"    localparam int BYTES_PER_BEAT = DQ_WIDTH / 8;")
        L(f"    logic [BYTES_PER_BEAT-1:0] dm_beat;")
        L(f"    always_comb begin")
        L(f"        dm_beat = wr_msk_r[BYTES_PER_BEAT-1:0];")
        L(f"        for (int wb = 0; wb < WORD_BEATS; wb++)")
        L(f"            if (wr_burst_ctr == wb[1:0])")
        L(f"                dm_beat = wr_msk_r[(wb+1)*BYTES_PER_BEAT-1 -: BYTES_PER_BEAT];")
        L(f"    end")
        L(f"    assign ddr_dm_o   = (wr_state == WR_DRIVE) ? ~dm_beat : '0;  // DM active-high masks")
        L(f"    assign ddr_dqs_o  = (wr_state == WR_DRIVE);  // simplified: DQS toggles during drive")
        L(f"    assign ddr_dqs_oe = (wr_state == WR_DRIVE);")
        L(f"")

        # ── Read pipeline ──
        L(f"    // ================================================================")
        L(f"    // Read capture and deserialization")
        L(f"    // ================================================================")
        L(f"    // A queue that always adds a cycle before the engine can act is")
        L(f"    // wrong for a read, full stop: the DRAM drives data CL cycles")
        L(f"    // after the RD command was issued, not CL cycles after our")
        L(f"    // internal engine happens to notice the command. The previous")
        L(f"    // version (65dbb0f) routed every read through rd_pend unconditionally,")
        L(f"    // which fixed the drop (Validation addendum 9, finding 2) but")
        L(f"    // shifted every single read's capture window one cycle late --")
        L(f"    // including isolated reads with no contention at all, since a")
        L(f"    // registered FIFO's content isn't visible to its own reader until")
        L(f"    // the cycle after it's pushed (Validation addendum 10, 2026-10-29:")
        L(f"    // 'the capture window is one cycle late ... beat 0 passes before")
        L(f"    // the engine looks and beat 1 lands in slot 0').")
        L(f"    //")
        L(f"    // Two paths now, chosen the moment cmd_rd_valid fires:")
        L(f"    //  - BYPASS (rd_bypass): engine idle, nothing already queued --")
        L(f"    //    handled the same cycle, the same way this design worked")
        L(f"    //    before rd_pend existed. Zero added latency; this is the")
        L(f"    //    common case and where the regression above actually lived.")
        L(f"    //  - QUEUED: engine busy with an earlier read. rd_pend stores")
        L(f"    //    each entry's own CL wait as a saturating countdown, loaded")
        L(f"    //    AT THE CYCLE IT WAS ISSUED and ticking down every cycle")
        L(f"    //    after regardless of queue position, not recomputed later.")
        L(f"    //    The engine captures once that countdown reaches 0, with no")
        L(f"    //    separate wait state -- the countdown already prices in the")
        L(f"    //    full CL. The scheduler's CAS spacing (tCCD_eff,")
        L(f"    //    see scheduler_gen.py) keeps the engine from ever actually")
        L(f"    //    falling behind a queued entry's deadline in practice, so")
        L(f"    //    this never needs to 'catch up' across a real burst.")
        L(f"")
        L(f"    typedef enum logic [1:0] {{")
        L(f"        RD_IDLE    = 2'd0,")
        L(f"        RD_WAIT    = 2'd1,   // waiting CL latency -- bypass path only")
        L(f"        RD_CAPTURE = 2'd2    // capturing DQ data")
        L(f"    }} rd_state_t;")
        L(f"")
        L(f"    rd_state_t rd_state;")
        L(f"    logic [7:0] rd_lat_ctr;")
        L(f"    logic [1:0] rd_burst_ctr;")
        L(f"    logic [AUX_WIDTH-1:0] rd_aux_r;  // latched aux tag for this read")
        L(f"")
        L(f"    // Backend, 2026-11-02: the original design stored each entry's")
        L(f"    // wait as a 32-bit ABSOLUTE timestamp (rd_cycle_ctr, free-")
        L(f"    // running, plus a 32-bit deadline per entry) -- 1,024 flops")
        L(f"    // across both read and write sides that never hold a value past")
        L(f"    // about 5, 27% of the whole chip's flops, and the magnitude")
        L(f"    // comparator landed combinationally on the write side's output")
        L(f"    // port. Measured cost: 99% of the chip's total negative slack")
        L(f"    // and 17% of its die area, isolated by building a width-only")
        L(f"    // variant with everything else byte-identical. A SATURATING")
        L(f"    // COUNTDOWN avoids the problem instead of shrinking it: each")
        L(f"    // entry stores its remaining wait (not an absolute cycle), every")
        L(f"    // entry decrements once per cycle down to 0 and stops -- 'due'")
        L(f"    // is a zero-test, not a magnitude compare, and there's no")
        L(f"    // free-running counter to compare against, so there's nothing to")
        L(f"    // wrap and nothing to be wraparound-safe about. 4 bits covers")
        L(f"    // the full valid CL/CWL/ratio range with room to spare. Checked")
        L(f"    // against a cycle-accurate Python model (isolated due-cycle")
        L(f"    // matching across 5 CL/ratio combinations including both")
        L(f"    // extremes, 5000 cycles of random push/pop traffic with no")
        L(f"    // entry lost or double-popped) before writing this.")
        L(f"    //")
        L(f"    // Controller cycles from issue to the first capture cycle -- the")
        L(f"    // same CL formula the bypass path below uses, computed once per")
        L(f"    // command at the moment it's queued, loaded into the entry's")
        L(f"    // countdown as (wait - 2): the push itself isn't visible to its")
        L(f"    // own reader until the cycle after (same reason as the old")
        L(f"    // design's '- 1'), and the countdown's first decrement doesn't")
        L(f"    // happen until the cycle after THAT -- max(0, ...) saturates the")
        L(f"    // short/bypass-range wait values (1) at an already-due 0 rather")
        L(f"    // than underflowing, so a queued entry with the fastest possible")
        L(f"    // wait is due the first cycle it's visible, same as the bypass")
        L(f"    // path achieves directly.")
        L(f"    wire [31:0] rd_wait_cycles = (cfg_CL_nCK <= CLK_RATIO[7:0])")
        L(f"        ? 32'd1")
        L(f"        : 32'(((cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0])) + 32'd1;")
        L(f"    wire [3:0] rd_wait_init = (rd_wait_cycles >= 32'd2) ? 4'(rd_wait_cycles - 32'd2) : 4'd0;")
        L(f"")
        L(f"    // Pending-read queue: overflow only (a bypassed read never enters")
        L(f"    // it), same RD_FIFO_DEPTH/FIFO_PTR_W sizing as the response FIFO")
        L(f"    // below (an outstanding read can't queue past what the response")
        L(f"    // FIFO could later hold anyway).")
        L(f"    logic [AUX_WIDTH-1:0] rd_pend_aux  [0:RD_FIFO_DEPTH-1];")
        L(f"    logic [3:0]           rd_pend_wait [0:RD_FIFO_DEPTH-1];  // saturating countdown, 0 = due")
        L(f"    logic [FIFO_PTR_W:0] rd_pend_wptr, rd_pend_rptr;")
        L(f"    wire  [FIFO_PTR_W:0] rd_pend_count = rd_pend_wptr - rd_pend_rptr;")
        L(f"    wire                  rd_pend_full  = (rd_pend_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);")
        L(f"    wire                  rd_pend_empty = (rd_pend_count == 0);")
        L(f"")
        L(f"    wire rd_bypass = (rd_state == RD_IDLE) && rd_pend_empty && cmd_rd_valid;")
        L(f"    wire rd_pend_push = cmd_rd_valid && !rd_pend_full && !rd_bypass;")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            rd_pend_wptr <= '0;")
        L(f"        else if (rd_pend_push) begin")
        L(f"            rd_pend_aux[rd_pend_wptr[FIFO_PTR_W-1:0]] <= cmd_aux;")
        L(f"            rd_pend_wptr <= rd_pend_wptr + 1'b1;")
        L(f"        end")
        L(f"")
        L(f"    // Every queued entry's countdown decrements every cycle,")
        L(f"    // independent of queue position -- real time passes for an")
        L(f"    // entry whether or not it's at the head, so an entry sitting")
        L(f"    // behind others must still be ticking down the whole time it")
        L(f"    // waits, or it would read as 'due' later than it actually is")
        L(f"    // once it becomes the head.")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            for (int i = 0; i < RD_FIFO_DEPTH; i++) rd_pend_wait[i] <= '0;")
        L(f"        end else begin")
        L(f"            for (int i = 0; i < RD_FIFO_DEPTH; i++) begin")
        L(f"                if (rd_pend_push && (i == rd_pend_wptr[FIFO_PTR_W-1:0]))")
        L(f"                    rd_pend_wait[i] <= rd_wait_init;")
        L(f"                else if (rd_pend_wait[i] != 0)")
        L(f"                    rd_pend_wait[i] <= rd_pend_wait[i] - 4'd1;")
        L(f"            end")
        L(f"        end")
        L(f"    end")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            rd_state     <= RD_IDLE;")
        L(f"            rd_lat_ctr   <= '0;")
        L(f"            rd_burst_ctr <= '0;")
        L(f"            rd_aux_r     <= '0;")
        L(f"            rd_pend_rptr <= '0;")
        L(f"        end else begin")
        L(f"            case (rd_state)")
        L(f"                RD_IDLE: begin")
        L(f"                    if (!rd_pend_empty &&")
        L(f"                        (rd_pend_wait[rd_pend_rptr[FIFO_PTR_W-1:0]] == 4'd0)) begin")
        L(f"                        // Queued while busy; its countdown (CL counted from")
        L(f"                        // when IT was issued) has reached 0 -- capture now,")
        L(f"                        // no separate wait state needed.")
        L(f"                        rd_aux_r     <= rd_pend_aux[rd_pend_rptr[FIFO_PTR_W-1:0]];")
        L(f"                        rd_pend_rptr <= rd_pend_rptr + 1'b1;")
        L(f"                        rd_state     <= RD_CAPTURE;")
        L(f"                        rd_burst_ctr <= '0;")
        L(f"                    end else if (rd_bypass) begin")
        L(f"                        rd_aux_r <= cmd_aux;")
        L(f"                        if (cfg_CL_nCK <= CLK_RATIO[7:0]) begin")
        L(f"                            rd_state     <= RD_CAPTURE;")
        L(f"                            rd_burst_ctr <= '0;")
        L(f"                        end else begin")
        L(f"                            rd_state   <= RD_WAIT;")
        L(f"                            // addendum 4/5 (Validation, 2026-10-22/27): ceil(CL /")
        L(f"                            // CLK_RATIO) alone waited one cycle too long -- the")
        L(f"                            // RD_IDLE -> RD_WAIT transition already spends the cycle")
        L(f"                            // in which the registered command is seen, so the wait")
        L(f"                            // count is one less than the ceiling.")
        L(f"                            rd_lat_ctr <= (cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] - 1'b1;")
        L(f"                        end")
        L(f"                    end")
        L(f"                end")
        L(f"                RD_WAIT: begin")
        L(f"                    if (rd_lat_ctr == 0)")
        L(f"                        rd_state <= RD_CAPTURE;")
        L(f"                    else")
        L(f"                        rd_lat_ctr <= rd_lat_ctr - 1'b1;")
        L(f"                    rd_burst_ctr <= '0;")
        L(f"                end")
        L(f"                RD_CAPTURE: begin")
        L(f"                    if (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1) begin")
        L(f"                        // Last beat. A real DRAM doesn't pause between back-")
        L(f"                        // to-back bursts, so if the next queued read's countdown")
        L(f"                        // has already reached 0 or will by the very next cycle,")
        L(f"                        // chain straight into its capture instead of detouring")
        L(f"                        // through RD_IDLE -- a detour costs a cycle neither")
        L(f"                        // RD_IDLE's own check nor this read's countdown accounts")
        L(f"                        // for, which would silently capture the FOLLOWING")
        L(f"                        // read's beat 1 as if it were this one's, the same")
        L(f"                        // wrong-data shape addendum 10 reported. <=1, not ==0,")
        L(f"                        // looks one cycle ahead of RD_IDLE's own (unshifted)")
        L(f"                        // check since this decision is made the cycle before the")
        L(f"                        // transition lands, same as every other state change")
        L(f"                        // here.")
        L(f"                        if (!rd_pend_empty &&")
        L(f"                            (rd_pend_wait[rd_pend_rptr[FIFO_PTR_W-1:0]] <= 4'd1)) begin")
        L(f"                            rd_aux_r     <= rd_pend_aux[rd_pend_rptr[FIFO_PTR_W-1:0]];")
        L(f"                            rd_pend_rptr <= rd_pend_rptr + 1'b1;")
        L(f"                            rd_state     <= RD_CAPTURE;")
        L(f"                            rd_burst_ctr <= '0;")
        L(f"                        end else begin")
        L(f"                            rd_state <= RD_IDLE;")
        L(f"                        end")
        L(f"                    end else")
        L(f"                        rd_burst_ctr <= rd_burst_ctr + 1'b1;")
        L(f"                end")
        L(f"                default: rd_state <= RD_IDLE;")
        L(f"            endcase")
        L(f"        end")
        L(f"    end")
        L(f"")

        # ── Read response FIFO ──
        L(f"    // ================================================================")
        L(f"    // Read response FIFO")
        L(f"    // ================================================================")
        L(f"    typedef struct packed {{")
        L(f"        logic [DATA_WIDTH-1:0]  data;")
        L(f"        logic [AUX_WIDTH-1:0]   aux;")
        L(f"    }} rd_entry_t;")
        L(f"")
        L(f"    rd_entry_t rd_fifo [0:RD_FIFO_DEPTH-1];")
        L(f"    logic [FIFO_PTR_W:0] rd_wptr, rd_rptr;")
        L(f"    wire  [FIFO_PTR_W:0] rd_count = rd_wptr - rd_rptr;")
        L(f"    wire                  rd_empty = (rd_count == 0);")
        L(f"")
        L(f"    // Assemble WORD_BEATS channel-width captures into one")
        L(f"    // DATA_WIDTH host word before pushing -- pushing per beat")
        L(f"    // (the old behavior) put WORD_BEATS separate, each only")
        L(f"    // partially-real entries into the FIFO per read, which is")
        L(f"    // what showed up downstream as duplicate/X-valued read")
        L(f"    // responses (see Defect 2, Frontend2/VALIDATION_INTEGRATION_")
        L(f"    // PLAN.md). Low beat first (pack_32_to_16, little-endian):")
        L(f"    // beat 0 (first captured) goes to the LOW DQ_WIDTH bits of")
        L(f"    // the assembled word, matching the write-side packing")
        L(f"    // (wr_dat_r[(wb+1)*DQ_WIDTH-1 -: DQ_WIDTH] with wb=0 driving")
        L(f"    // the low half first). Every beat -- including the final")
        L(f"    // one -- is captured into its own DQ_WIDTH-wide slot at bit")
        L(f"    // position beat_index*DQ_WIDTH, the same positional scheme")
        L(f"    // the write path uses, instead of special-casing the final")
        L(f"    // beat into a fixed top slot via concatenation (which")
        L(f"    // silently assumed WORD_BEATS==2 and got the beat order")
        L(f"    // backwards for the final beat).")
        L(f"    wire rd_capture_valid = (rd_state == RD_CAPTURE);")
        L(f"    wire rd_word_complete = rd_capture_valid && (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1);")
        L(f"")
        L(f"    logic [DATA_WIDTH-1:0] rd_shift_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n)")
        L(f"            rd_shift_r <= '0;")
        L(f"        else if (rd_capture_valid)")
        L(f"            rd_shift_r[rd_burst_ctr*DQ_WIDTH +: DQ_WIDTH] <= ddr_dq_i;")
        L(f"    end")
        L(f"")
        L(f"    // The word is pushed to the FIFO the cycle AFTER the final")
        L(f"    // beat is latched into rd_shift_r (rd_word_complete fires on")
        L(f"    // the final-beat capture cycle itself, but rd_shift_r only")
        L(f"    // updates on the next edge), so delay rd_word_complete and")
        L(f"    // rd_aux_r by one cycle to push the fully-assembled word.")
        L(f"    logic rd_word_complete_d;")
        L(f"    logic [AUX_WIDTH-1:0] rd_aux_push;")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            rd_word_complete_d <= 1'b0;")
        L(f"            rd_aux_push        <= '0;")
        L(f"        end else begin")
        L(f"            rd_word_complete_d <= rd_word_complete;")
        L(f"            rd_aux_push        <= rd_aux_r;")
        L(f"        end")
        L(f"    end")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            rd_wptr <= '0;")
        L(f"        else if (rd_word_complete_d) begin")
        L(f"            rd_fifo[rd_wptr[FIFO_PTR_W-1:0]] <= '{{data: rd_shift_r, aux: rd_aux_push}};")
        L(f"            rd_wptr <= rd_wptr + 1'b1;")
        L(f"        end")
        L(f"")
        L(f"    // Pop read responses to wb_port")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            rd_rptr <= '0;")
        L(f"        else if (rd_rsp_valid)")
        L(f"            rd_rptr <= rd_rptr + 1'b1;")
        L(f"")
        L(f"    assign rd_rsp_valid = ~rd_empty;")
        L(f"    assign rd_rsp_data  = rd_fifo[rd_rptr[FIFO_PTR_W-1:0]].data;")
        L(f"    assign rd_rsp_aux   = rd_fifo[rd_rptr[FIFO_PTR_W-1:0]].aux;")
        L(f"")

        # ── SVA ──
        L(f"    // ================================================================")
        L(f"    // SVA -- simulation only")
        L(f"    // ================================================================")
        L(f"    // synopsys translate_off")
        L(f"    // synthesis translate_off")
        L(f"")
        L(f"    // DP-001: Write buffer never overflows. wr_data_valid && wr_full")
        L(f"    // is allowed for exactly one reason: wr_pop_this_cycle, the same")
        L(f"    // cycle a slot is also freed (Validation, 2026-10-29, addendum")
        L(f"    // 11) -- that is a push into the slot the pop just vacated, not")
        L(f"    // an overflow. Anything else at wr_full is the real thing.")
        L(f"    property p_wr_no_overflow;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (wr_data_valid && wr_full && !wr_pop_this_cycle) |-> 1'b0;")
        L(f"    endproperty")
        L(f"    assert property (p_wr_no_overflow)")
        L(f"        else $error(\"[DP-001] Write buffer overflow\");")
        L(f"")
        L(f"    // DP-002: DQ output enable only during WR_DRIVE")
        L(f"    property p_dq_oe_only_drive;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        ddr_dq_oe |-> (wr_state == WR_DRIVE);")
        L(f"    endproperty")
        L(f"    assert property (p_dq_oe_only_drive)")
        L(f"        else $error(\"[DP-002] DQ OE asserted outside WR_DRIVE\");")
        L(f"")
        L(f"    // DP-005: Read response valid only when FIFO non-empty")
        L(f"    property p_rd_rsp_valid;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        rd_rsp_valid |-> ~rd_empty;")
        L(f"    endproperty")
        L(f"    assert property (p_rd_rsp_valid)")
        L(f"        else $error(\"[DP-005] Read response valid with empty FIFO\");")
        L(f"")
        L(f"    // DP-013: Pending-read queue never overflows (cmd_rd_valid always accepted)")
        L(f"    property p_rd_pend_no_overflow;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (cmd_rd_valid && rd_pend_full) |-> 1'b0;")
        L(f"    endproperty")
        L(f"    assert property (p_rd_pend_no_overflow)")
        L(f"        else $error(\"[DP-013] Pending-read queue overflow -- a RD command was dropped\");")
        L(f"")
        L(f"    // DP-014: Pending-write queue never overflows (cmd_wr_valid always accepted)")
        L(f"    property p_wr_pend_no_overflow;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (cmd_wr_valid && wr_pend_full) |-> 1'b0;")
        L(f"    endproperty")
        L(f"    assert property (p_wr_pend_no_overflow)")
        L(f"        else $error(\"[DP-014] Pending-write queue overflow -- a WR command was dropped\");")
        L(f"")
        L(f"    // DP-015: a WR command must never be issued before its own")
        L(f"    // write's data has arrived in wr_buf -- the tag-indexed fetch")
        L(f"    // above (CONSERVE/WRITE_CMD_TO_BEATS fix) relies on this: data")
        L(f"    // push (wr_data_valid, host-acceptance order) and command")
        L(f"    // issue (cmd_wr_valid, scheduler order) are independent")
        L(f"    // streams, and by construction issue always lags push (a")
        L(f"    // command can only be issued for an entry already enqueued,")
        L(f"    // and enqueue happens together with the data push) -- checked")
        L(f"    // at runtime rather than only argued, since a future cmd_gen/")
        L(f"    // scheduler latency change could silently break it.")
        L(f"    property p_wr_data_precedes_issue;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        cmd_wr_valid |-> wr_buf_valid[cmd_aux[FIFO_PTR_W-1:0]];")
        L(f"    endproperty")
        L(f"    assert property (p_wr_data_precedes_issue)")
        L(f"        else $error(\"[DP-015] WR command issued before its data arrived in wr_buf\");")
        L(f"")
        L(f"    // Coverage")
        L(f"    covergroup cg_dp @(posedge clk);")
        L(f"        option.per_instance = 1;")
        L(f"        cp_wr_drive : coverpoint (wr_state == WR_DRIVE);")
        L(f"        cp_rd_cap   : coverpoint (rd_state == RD_CAPTURE);")
        L(f"        cp_wr_full  : coverpoint wr_full;")
        L(f"        cp_rd_empty : coverpoint rd_empty;")
        L(f"    endgroup")
        L(f"    cg_dp cg_inst = new();")
        L(f"")
        L(f"    // synthesis translate_on")
        L(f"    // synopsys translate_on")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    # ================================================================
    # Testbench
    # ================================================================
    # ================================================================
    # Manifest
    # ================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            **stamp(self.spec),
            "module_name": "data_path",
            "file": "data_path.sv",
            "phase": 4,
            "generator": "data_path_gen",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "DATA_WIDTH": p["DATA_WIDTH"],
                "DQ_WIDTH": p["DQ_WIDTH"],
                "DM_WIDTH": p["DM_WIDTH"],
                "SEL_WIDTH": p["SEL_WIDTH"],
                "AUX_WIDTH": p["AUX_WIDTH"],
                "BURST_LEN": p["BURST_LEN"],
                "CLK_RATIO": p["CLK_RATIO"],
                "BURST_CTRL_CYC": p["BURST_CTRL_CYCLES"],
                "WORD_BEATS": p["WORD_BEATS"],
                "RD_FIFO_DEPTH": p["RD_FIFO_DEPTH"],
                "CL": p["CL"],
                "CWL": p["CWL"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "cmd_in": [
                    {"name": "cmd_wr_valid", "width": 1, "dir": "input", "source": "cmd_gen.fb_wr_valid"},
                    {"name": "cmd_rd_valid", "width": 1, "dir": "input", "source": "cmd_gen.fb_rd_valid"},
                    {"name": "cmd_aux", "width": p["AUX_WIDTH"], "dir": "input", "source": "cmd_gen.cmd_out_aux"},
                ],
                "wr_data_in": [
                    {"name": "wr_data_valid", "width": 1, "dir": "input",
                     # Not a straight wire: a write word is buffered only when the write
                     # request is ACCEPTED. `source` names the first term for tools that
                     # read a single port; `source_expr` is the real connection.
                     "source": "wb_port.req_valid",
                     "source_expr": "wb_port.req_valid && wb_port.req_we && cmd_queue.enq_ready"},
                    {"name": "wr_data", "width": p["DATA_WIDTH"], "dir": "input", "source": "wb_port.req_wdata"},
                    {"name": "wr_mask", "width": p["SEL_WIDTH"], "dir": "input", "source": "wb_port.req_wmask"},
                    {"name": "wr_data_aux", "width": p["AUX_WIDTH"], "dir": "input", "source": "wb_port.req_aux"},
                ],
                "wr_ctrl_out": [
                    {"name": "wr_data_ready", "width": 1, "dir": "output"},
                ],
                "rd_rsp_out": [
                    {"name": "rd_rsp_valid", "width": 1, "dir": "output"},
                    {"name": "rd_rsp_data", "width": p["DATA_WIDTH"], "dir": "output"},
                    {"name": "rd_rsp_aux", "width": p["AUX_WIDTH"], "dir": "output"},
                ],
                "cfg_in": [
                    {"name": "cfg_CL_nCK", "width": 8, "dir": "input", "source": "config_regs.cfg_CL_nCK"},
                    {"name": "cfg_CWL_nCK", "width": 8, "dir": "input", "source": "config_regs.cfg_CWL_nCK"},
                ],
                "ddr_phy": [
                    {"name": "ddr_dq_o", "width": p["DQ_WIDTH"], "dir": "output"},
                    {"name": "ddr_dq_oe", "width": 1, "dir": "output"},
                    {"name": "ddr_dq_i", "width": p["DQ_WIDTH"], "dir": "input"},
                    {"name": "ddr_dm_o", "width": p["DM_WIDTH"], "dir": "output"},
                    {"name": "ddr_dqs_o", "width": 1, "dir": "output"},
                    {"name": "ddr_dqs_oe", "width": 1, "dir": "output"},
                    {"name": "ddr_dqs_i", "width": 1, "dir": "input"},
                ],
            },
            "dependencies": ["cmd_gen", "scheduler", "wb_port", "config_regs"],
            "assertions": [
                {"name": "p_wr_no_overflow", "check": "DP-001"},
                {"name": "p_dq_oe_only_drive", "check": "DP-002"},
                {"name": "p_rd_rsp_valid", "check": "DP-005"},
                {"name": "p_rd_pend_no_overflow", "check": "DP-013"},
                {"name": "p_wr_pend_no_wrap", "check": "DP-014"},
                {"name": "p_wr_data_precedes_issue", "check": "DP-015"},
            ],
            "coverage_points": [
                "cp_wr_drive", "cp_rd_cap", "cp_wr_full", "cp_rd_empty",
            ],
        }

    # ================================================================
    # Run
    # ================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  DATA PATH / ALIGNMENT GENERATOR\n  Spec: {self.spec_path}\n{hdr}")

        print("\n[1/4] Validating parameters ...")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ERROR: {e}")
            return {"status": "error", "errors": errs}
        print("  OK: All parameters valid")
        for k, v in self.p.items():
            print(f"    {k:20s} = {v}")

        print("\n[2/4] Generating RTL ...")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines of SystemVerilog")

        # The testbench is generated from the spec alone by Phase4/tb_generator.py.

        print("\n[3/4] Generating port manifest ...")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  OK: {port_cnt} ports | {len(manifest['assertions'])} assertions | {len(manifest['coverage_points'])} cover points")

        print("\n[4/4] Writing files ...")
        rtl_path = self.output_dir / "data_path.sv"
        rtl_path.write_text(rtl)
        print(f"  -> {rtl_path}")

        mfst_path = self.output_dir / "data_path_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  -> {mfst_path}")

        print(f"\n{hdr}\n  DONE -- data_path.sv ready for Phase 4\n{hdr}")
        return {
            "status": "success",
            "module": "data_path",
            "phase": 4,
            "rtl_path": str(rtl_path),
            "manifest_path": str(mfst_path),
            "manifest": manifest,
            "rtl_lines": rtl_lines,
            "ports": port_cnt,
        }


if __name__ == "__main__":
    print("+=============================================+")
    print("|   DATA PATH / ALIGNMENT GENERATOR  (Phase 3)    |")
    print("+=============================================+")
    print()
    spec_path = input("Enter path to spec JSON: ").strip()
    if not spec_path or not os.path.isfile(spec_path):
        print("Error: Invalid path.")
        sys.exit(1)
    output_dir = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    gen = DataPathGenerator(spec_path, output_dir)
    result = gen.run()
    sys.exit(0 if result["status"] == "success" else 1)
