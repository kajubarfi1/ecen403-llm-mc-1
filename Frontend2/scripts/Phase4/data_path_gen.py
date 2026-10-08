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
|    Alignment:  4:1 clock ratio, BL8 burst packing/unpacking         |
|    Tag track:  aux_width passthrough for read response ordering      |
|                                                                      |
|  Testbench: ~35 tests across 8 sections (A-H)                       |
|    A: Reset behavior            B: Single write data path            |
|    C: Single read data path     D: BL8 burst write                   |
|    E: BL8 burst read            F: Write mask (DM) propagation       |
|    G: Aux tag passthrough       H: Back-to-back / pipeline           |
|                                                                      |
|  Validation checks: DP-001 through DP-012                            |
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
        if p["CLK_RATIO"] != 4:
            errors.append(f"Expected 4:1 clock ratio, got {p['CLK_RATIO']}:1")
        if p["BURST_CTRL_CYCLES"] != 2:
            errors.append(f"BL8 with 4:1 ratio should be 2 ctrl cycles, got {p['BURST_CTRL_CYCLES']}")
        if p["CL"] < 5 or p["CL"] > 14:
            errors.append(f"CAS latency {p['CL']} out of DDR3 range [5,14]")
        if p["CWL"] < 5 or p["CWL"] > 12:
            errors.append(f"CAS write latency {p['CWL']} out of DDR3 range [5,12]")
        return errors

    # ================================================================
    # RTL generation
    # ================================================================
    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        lines = []
        L = lines.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module:    data_path")
        L(f"// File:      data_path.sv")
        L(f"// Generated: {ts}")
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
        L(f"// Validation: DP-001 .. DP-012")
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
        L(f"    wr_entry_t wr_buf [0:RD_FIFO_DEPTH-1];")
        L(f"    logic [FIFO_PTR_W:0] wr_wptr, wr_rptr;")
        L(f"    wire  [FIFO_PTR_W:0] wr_count = wr_wptr - wr_rptr;")
        L(f"    wire                  wr_full  = (wr_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);")
        L(f"    wire                  wr_empty = (wr_count == 0);")
        L(f"")
        L(f"    assign wr_data_ready = ~wr_full;")
        L(f"")
        L(f"    // Write buffer push")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            wr_wptr <= '0;")
        L(f"        else if (wr_data_valid && ~wr_full) begin")
        L(f"            wr_buf[wr_wptr[FIFO_PTR_W-1:0]] <= '{{data: wr_data, mask: wr_mask}};")
        L(f"            wr_wptr <= wr_wptr + 1'b1;")
        L(f"        end")
        L(f"")

        # ── Write state machine ──
        L(f"    // ================================================================")
        L(f"    // Write serialization FSM")
        L(f"    // ================================================================")
        L(f"    // When cmd_wr_valid fires, we wait CWL controller cycles, then")
        L(f"    // drive DQ for BURST_CTRL_CYC cycles (2 cycles for BL8 @ 4:1).")
        L(f"")
        L(f"    typedef enum logic [1:0] {{")
        L(f"        WR_IDLE   = 2'd0,")
        L(f"        WR_WAIT   = 2'd1,   // waiting CWL latency")
        L(f"        WR_DRIVE  = 2'd2    // driving DQ pins")
        L(f"    }} wr_state_t;")
        L(f"")
        L(f"    wr_state_t wr_state;")
        L(f"    logic [7:0] wr_lat_ctr;        // CWL countdown")
        L(f"    logic [1:0] wr_burst_ctr;       // burst beat counter")
        L(f"    logic [DATA_WIDTH-1:0] wr_dat_r; // latched write data")
        L(f"    logic [SEL_WIDTH-1:0]  wr_msk_r; // latched mask")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            wr_state     <= WR_IDLE;")
        L(f"            wr_lat_ctr   <= '0;")
        L(f"            wr_burst_ctr <= '0;")
        L(f"            wr_rptr      <= '0;")
        L(f"            wr_dat_r     <= '0;")
        L(f"            wr_msk_r     <= '0;")
        L(f"        end else begin")
        L(f"            case (wr_state)")
        L(f"                WR_IDLE: begin")
        L(f"                    if (cmd_wr_valid && !wr_empty) begin")
        L(f"                        // Latch data from write buffer")
        L(f"                        wr_dat_r <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].data;")
        L(f"                        wr_msk_r <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].mask;")
        L(f"                        wr_rptr  <= wr_rptr + 1'b1;")
        L(f"                        if (cfg_CWL_nCK <= CLK_RATIO[7:0]) begin")
        L(f"                            // CWL fits in one ctrl cycle, go straight to drive")
        L(f"                            wr_state     <= WR_DRIVE;")
        L(f"                            wr_burst_ctr <= '0;")
        L(f"                        end else begin")
        L(f"                            wr_state   <= WR_WAIT;")
        L(f"                            wr_lat_ctr <= (cfg_CWL_nCK >> 2) - 1'b1; // nCK to ctrl cycles")
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
        L(f"                    if (wr_burst_ctr == WORD_BEATS[1:0] - 1'b1)")
        L(f"                        wr_state <= WR_IDLE;")
        L(f"                    else")
        L(f"                        wr_burst_ctr <= wr_burst_ctr + 1'b1;")
        L(f"                end")
        L(f"                default: wr_state <= WR_IDLE;")
        L(f"            endcase")
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
        L(f"    // When cmd_rd_valid fires, we start a CL countdown. After CL,")
        L(f"    // we capture DQ data for BURST_CTRL_CYC cycles and push to")
        L(f"    // the read response FIFO with the aux tag.")
        L(f"")
        L(f"    typedef enum logic [1:0] {{")
        L(f"        RD_IDLE    = 2'd0,")
        L(f"        RD_WAIT    = 2'd1,   // waiting CL latency")
        L(f"        RD_CAPTURE = 2'd2    // capturing DQ data")
        L(f"    }} rd_state_t;")
        L(f"")
        L(f"    rd_state_t rd_state;")
        L(f"    logic [7:0] rd_lat_ctr;")
        L(f"    logic [1:0] rd_burst_ctr;")
        L(f"    logic [AUX_WIDTH-1:0] rd_aux_r;  // latched aux tag for this read")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            rd_state     <= RD_IDLE;")
        L(f"            rd_lat_ctr   <= '0;")
        L(f"            rd_burst_ctr <= '0;")
        L(f"            rd_aux_r     <= '0;")
        L(f"        end else begin")
        L(f"            case (rd_state)")
        L(f"                RD_IDLE: begin")
        L(f"                    if (cmd_rd_valid) begin")
        L(f"                        rd_aux_r <= cmd_aux;")
        L(f"                        if (cfg_CL_nCK <= CLK_RATIO[7:0]) begin")
        L(f"                            rd_state     <= RD_CAPTURE;")
        L(f"                            rd_burst_ctr <= '0;")
        L(f"                        end else begin")
        L(f"                            rd_state   <= RD_WAIT;")
        L(f"                            rd_lat_ctr <= (cfg_CL_nCK >> 2) - 1'b1;")
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
        L(f"                    if (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1)")
        L(f"                        rd_state <= RD_IDLE;")
        L(f"                    else")
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
        L(f"    // PLAN.md). Low beat first (pack_32_to_16, little-endian).")
        L(f"    wire rd_capture_valid = (rd_state == RD_CAPTURE);")
        L(f"    wire rd_word_complete = rd_capture_valid && (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1);")
        L(f"")
        L(f"    logic [DATA_WIDTH-1:0] rd_shift_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n)")
        L(f"            rd_shift_r <= '0;")
        L(f"        else if (rd_capture_valid && rd_burst_ctr != WORD_BEATS[1:0] - 1'b1)")
        L(f"            rd_shift_r[(rd_burst_ctr+1)*DQ_WIDTH-1 -: DQ_WIDTH] <= ddr_dq_i;")
        L(f"    end")
        L(f"")
        L(f"    // Final beat combines the just-arrived ddr_dq_i directly with")
        L(f"    // the earlier beats already shifted into rd_shift_r -- avoids")
        L(f"    // a spurious extra cycle of latency for the last beat.")
        L(f"    wire [DATA_WIDTH-1:0] rd_word_assembled =")
        L(f"        {{ddr_dq_i, rd_shift_r[DATA_WIDTH-DQ_WIDTH-1:0]}};")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            rd_wptr <= '0;")
        L(f"        else if (rd_word_complete) begin")
        L(f"            rd_fifo[rd_wptr[FIFO_PTR_W-1:0]] <= '{{data: rd_word_assembled, aux: rd_aux_r}};")
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
        L(f"    // DP-001: Write buffer never overflows")
        L(f"    property p_wr_no_overflow;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (wr_data_valid && wr_full) |-> 1'b0;")
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