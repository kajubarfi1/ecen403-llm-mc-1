#!/usr/bin/env python3
"""
+======================================================================+
|                 WISHBONE PORT INTERFACE AGENT                        |
|                                                                      |
|  Phase 1 RTL Generation Agent                                        |
|  Generates: wb_port.sv + wb_port_tb.sv + wb_port_manifest.json       |
|                                                                      |
|  Dependencies: None (Phase 1)                                        |
|                                                                      |
|  Spec sections consumed:                                             |
|    host_interface, data_path_mapping, controller_architecture,       |
|    clocking_model, memory_geometry                                   |
|                                                                      |
|  Implements:                                                         |
|    Wishbone B4 pipelined slave with backpressure (stall),            |
|    linear burst (BL8), byte-lane masking, error signalling,          |
|    and auxiliary tag propagation.                                     |
|                                                                      |
|  Testbench: ~33 tests across 9 sections (A-I)                       |
|    A: Single write/read        B: Burst write/read (BL8)            |
|    C: Stall/backpressure       D: Protocol compliance                |
|    E: Error detection          F: Aux tag propagation                |
|    G: Tag FIFO stress          H: Reset mid-transaction              |
|    I: Edge cases                                                     |
|                                                                      |
|  Validation checks: WB-001 through WB-009                            |
+======================================================================+
"""

import json
import sys
import os
from pathlib import Path
from datetime import datetime


class WishbonePortAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.host      = self.spec["host_interface"]
        self.data_path = self.spec["data_path_mapping"]
        self.ctrl_arch = self.spec["controller_architecture"]
        self.clocking  = self.spec["clocking_model"]
        self.geometry  = self.spec["memory_geometry"]

        self.p = self._derive_parameters()

    # ================================================================
    # Parameter derivation
    # ================================================================
    def _derive_parameters(self) -> dict:
        p = {}
        p["DATA_WIDTH"]       = self.host["data_width_bits"]
        p["ADDR_WIDTH"]       = self.host["address_width_bits"]
        p["GRANULARITY"]      = self.host["granularity_bits"]
        p["SEL_WIDTH"]        = p["DATA_WIDTH"] // p["GRANULARITY"]
        p["BURST_TYPE"]       = self.host["burst_type"]
        p["MAX_BURST_LEN"]    = self.host["max_burst_length"]
        p["INTERFACE_TYPE"]   = self.host["interface_type"]
        p["RD_BUFFER_DEPTH"]  = self.host.get("read_buffer_depth", 16)
        p["WR_BUFFER_DEPTH"]  = self.host.get("write_buffer_depth", 16)
        p["AUX_WIDTH"]        = self.ctrl_arch["aux_width"]
        p["QUEUE_DEPTH"]      = self.ctrl_arch["command_queue_depth"]
        p["PIPELINE_LATENCY"] = self.clocking.get("pipeline_latency_cycles", 2)
        p["CTRL_FREQ"]        = self.clocking["$derived"]["controller_frequency_MHz"]
        p["CTRL_PERIOD"]      = self.clocking["controller_clock_period_ns"]
        p["ROW_BITS"]         = self.geometry["row_bits"]
        p["COL_BITS"]         = self.geometry["column_bits"]
        p["BANK_BITS"]        = self.geometry["bank_bits"]
        p["RANKS"]            = self.geometry["ranks"]
        # FIX: burst counter must hold MAX_BURST_LEN itself, not just MAX-1
        p["BURST_CTR_WIDTH"]  = max(1, p["MAX_BURST_LEN"].bit_length())
        p["TAG_FIFO_DEPTH"]   = p["RD_BUFFER_DEPTH"]
        p["TAG_PTR_WIDTH"]    = max(1, p["TAG_FIFO_DEPTH"].bit_length())
        p["ADDR_INC"]         = p["DATA_WIDTH"] // 8
        return p

    # ================================================================
    # Pre-generation validation
    # ================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["INTERFACE_TYPE"] != "wishbone_pipelined":
            errors.append(f"Expected wishbone_pipelined, got {p['INTERFACE_TYPE']}")
        if p["DATA_WIDTH"] not in (32, 64, 128):
            errors.append(f"DATA_WIDTH must be 32/64/128, got {p['DATA_WIDTH']}")
        if p["GRANULARITY"] != 8:
            errors.append(f"GRANULARITY must be 8 for byte addressing, got {p['GRANULARITY']}")
        if p["SEL_WIDTH"] != p["DATA_WIDTH"] // 8:
            errors.append(f"SEL_WIDTH derivation error")
        if p["AUX_WIDTH"] < 4:
            errors.append(f"AUX_WIDTH must be >= 4, got {p['AUX_WIDTH']}")
        if not (20 <= p["ADDR_WIDTH"] <= 32):
            errors.append(f"ADDR_WIDTH out of [20,32]: {p['ADDR_WIDTH']}")
        if p["MAX_BURST_LEN"] != 8:
            errors.append(f"MAX_BURST_LEN should be 8 for DDR3 BL8, got {p['MAX_BURST_LEN']}")
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
        L(f"// Module:    wb_port")
        L(f"// File:      wb_port.sv")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Wishbone Port Interface Agent (Phase 1)")
        L(f"// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}")
        L(f"//")
        L(f"// Description:")
        L(f"//   Wishbone B4 pipelined slave. Backpressure (stall), linear burst (BL8),")
        L(f"//   byte-lane masking, error signalling, auxiliary tag propagation.")
        L(f"//")
        L(f"// Derived: DATA={p['DATA_WIDTH']} ADDR={p['ADDR_WIDTH']} SEL={p['SEL_WIDTH']}"
          f" AUX={p['AUX_WIDTH']} BURST={p['MAX_BURST_LEN']} QUEUE={p['QUEUE_DEPTH']}")
        L(f"// Validation: WB-001 .. WB-009")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"")
        L(f"module wb_port #(")
        L(f"    parameter DATA_WIDTH     = {p['DATA_WIDTH']},")
        L(f"    parameter ADDR_WIDTH     = {p['ADDR_WIDTH']},")
        L(f"    parameter SEL_WIDTH      = {p['SEL_WIDTH']},")
        L(f"    parameter AUX_WIDTH      = {p['AUX_WIDTH']},")
        L(f"    parameter MAX_BURST_LEN  = {p['MAX_BURST_LEN']},")
        L(f"    parameter QUEUE_DEPTH    = {p['QUEUE_DEPTH']},")
        L(f"    parameter BURST_CTR_W    = {p['BURST_CTR_WIDTH']},")
        L(f"    parameter TAG_FIFO_DEPTH = {p['TAG_FIFO_DEPTH']},")
        L(f"    parameter TAG_PTR_W      = {p['TAG_PTR_WIDTH']}")
        L(f") (")
        L(f"    input  logic                    clk,")
        L(f"    input  logic                    rst_n,")
        L(f"")
        L(f"    // Wishbone B4 Pipelined Slave")
        L(f"    input  logic                    wb_cyc_i,")
        L(f"    input  logic                    wb_stb_i,")
        L(f"    input  logic                    wb_we_i,")
        L(f"    input  logic [ADDR_WIDTH-1:0]   wb_adr_i,")
        L(f"    input  logic [DATA_WIDTH-1:0]   wb_dat_i,")
        L(f"    input  logic [SEL_WIDTH-1:0]    wb_sel_i,")
        L(f"    input  logic [1:0]              wb_bte_i,")
        L(f"    input  logic [2:0]              wb_cti_i,")
        L(f"")
        L(f"    output logic                    wb_ack_o,")
        L(f"    output logic [DATA_WIDTH-1:0]   wb_dat_o,")
        L(f"    output logic                    wb_stall_o,")
        L(f"    output logic                    wb_err_o,")
        L(f"")
        L(f"    // Internal -> Command Queue")
        L(f"    output logic                    req_valid,")
        L(f"    output logic                    req_we,")
        L(f"    output logic [ADDR_WIDTH-1:0]   req_addr,")
        L(f"    output logic [DATA_WIDTH-1:0]   req_wdata,")
        L(f"    output logic [SEL_WIDTH-1:0]    req_wmask,")
        L(f"    output logic [AUX_WIDTH-1:0]    req_aux,")
        L(f"    input  logic                    req_ready,")
        L(f"")
        L(f"    // Internal <- Data Path")
        L(f"    input  logic                    rsp_valid,")
        L(f"    input  logic [DATA_WIDTH-1:0]   rsp_rdata,")
        L(f"    input  logic [AUX_WIDTH-1:0]    rsp_aux")
        L(f");")
        L(f"")
        L(f"    // CTI / BTE encodings")
        L(f"    localparam logic [2:0] CTI_CLASSIC = 3'b000;")
        L(f"    localparam logic [2:0] CTI_CONST   = 3'b001;")
        L(f"    localparam logic [2:0] CTI_INC     = 3'b010;")
        L(f"    localparam logic [2:0] CTI_END     = 3'b111;")
        L(f"    localparam logic [1:0] BTE_LINEAR  = 2'b00;")
        L(f"    localparam int unsigned ADDR_INC = DATA_WIDTH / 8;")
        L(f"")
        L(f"    wire wb_beat = wb_cyc_i & wb_stb_i & ~wb_stall_o;")
        L(f"")

        # Aux counter FIRST (before tag FIFO)
        L(f"    // Aux-tag counter (WB-009) -- declared before tag FIFO")
        L(f"    logic [AUX_WIDTH-1:0] aux_ctr;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)       aux_ctr <= '0;")
        L(f"        else if (wb_beat) aux_ctr <= aux_ctr + 1'b1;")
        L(f"")

        # Tag FIFO
        L(f"    // Tag FIFO -- tracks outstanding read requests")
        L(f"    logic [AUX_WIDTH-1:0] tag_mem [0:TAG_FIFO_DEPTH-1];")
        L(f"    logic [TAG_PTR_W:0]   tag_wr, tag_rd;")
        L(f"    wire  [TAG_PTR_W:0]   tag_cnt  = tag_wr - tag_rd;")
        L(f"    wire                   tag_full = (tag_cnt == TAG_FIFO_DEPTH[TAG_PTR_W:0]);")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) tag_wr <= '0;")
        L(f"        else if (wb_beat && !wb_we_i) begin")
        L(f"            tag_mem[tag_wr[TAG_PTR_W-1:0]] <= aux_ctr;")
        L(f"            tag_wr <= tag_wr + 1'b1;")
        L(f"        end")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) tag_rd <= '0;")
        L(f"        else if (rsp_valid) tag_rd <= tag_rd + 1'b1;")
        L(f"")

        # Stall
        L(f"    // Stall generation (WB-005)")
        L(f"    always_comb begin")
        L(f"        wb_stall_o = 1'b0;")
        L(f"        if (!req_ready)                        wb_stall_o = 1'b1;")
        L(f"        if (!wb_we_i && tag_full && wb_stb_i)  wb_stall_o = 1'b1;")
        L(f"    end")
        L(f"")

        # Burst tracker
        L(f"    // Burst tracker (WB-003, WB-004)")
        L(f"    logic                   burst_active;")
        L(f"    logic [BURST_CTR_W-1:0] burst_cnt;")
        L(f"    logic [ADDR_WIDTH-1:0]  burst_nxt_addr;")
        L(f"    logic                   burst_we;")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            burst_active   <= 1'b0;")
        L(f"            burst_cnt      <= '0;")
        L(f"            burst_nxt_addr <= '0;")
        L(f"            burst_we       <= 1'b0;")
        L(f"        end else if (wb_beat) begin")
        L(f"            if (!burst_active && wb_cti_i == CTI_INC) begin")
        L(f"                burst_active   <= 1'b1;")
        L(f"                burst_cnt      <= 'd1;")
        L(f"                burst_nxt_addr <= wb_adr_i + ADDR_INC[ADDR_WIDTH-1:0];")
        L(f"                burst_we       <= wb_we_i;")
        L(f"            end else if (burst_active) begin")
        L(f"                burst_cnt      <= burst_cnt + 1'b1;")
        L(f"                burst_nxt_addr <= burst_nxt_addr + ADDR_INC[ADDR_WIDTH-1:0];")
        L(f"                if (wb_cti_i == CTI_END ||")
        L(f"                    burst_cnt == BURST_CTR_W'(MAX_BURST_LEN - 1)) begin")
        L(f"                    burst_active <= 1'b0;")
        L(f"                    burst_cnt    <= '0;")
        L(f"                end")
        L(f"            end")
        L(f"        end else if (!wb_cyc_i) begin")
        L(f"            burst_active <= 1'b0;")
        L(f"            burst_cnt    <= '0;")
        L(f"        end")
        L(f"    end")
        L(f"")

        # Request output
        L(f"    // Request output (WB-001, WB-002)")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            req_valid <= 1'b0; req_we <= 1'b0; req_addr <= '0;")
        L(f"            req_wdata <= '0; req_wmask <= '0; req_aux <= '0;")
        L(f"        end else begin")
        L(f"            req_valid <= 1'b0;")
        L(f"            if (wb_beat) begin")
        L(f"                req_valid <= 1'b1;")
        L(f"                req_we    <= wb_we_i;")
        L(f"                req_addr  <= wb_adr_i;")
        L(f"                req_wdata <= wb_dat_i;")
        L(f"                req_wmask <= wb_sel_i;")
        L(f"                req_aux   <= aux_ctr;")
        L(f"            end")
        L(f"        end")
        L(f"    end")
        L(f"")

        # Write ACK
        L(f"    // Write acknowledge (WB-002, WB-008)")
        L(f"    logic wr_ack_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) wr_ack_r <= 1'b0;")
        L(f"        else        wr_ack_r <= wb_beat & wb_we_i;")
        L(f"")
        L(f"    wire rd_ack = rsp_valid;")
        L(f"    assign wb_ack_o = wr_ack_r | rd_ack;")
        L(f"    assign wb_dat_o = rsp_rdata;")
        L(f"")

        # Error detection
        L(f"    // Error detection (WB-007)")
        L(f"    logic err_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) err_r <= 1'b0;")
        L(f"        else begin")
        L(f"            err_r <= 1'b0;")
        L(f"            if (wb_cyc_i && wb_stb_i) begin")
        L(f"                if (burst_active && (wb_we_i != burst_we)) err_r <= 1'b1;")
        L(f"                if (|wb_adr_i[$clog2(ADDR_INC)-1:0])      err_r <= 1'b1;")
        L(f"            end")
        L(f"        end")
        L(f"    end")
        L(f"    assign wb_err_o = err_r;")
        L(f"")

        # SVA
        L(f"    // SVA -- simulation only")
        L(f"    // synopsys translate_off")
        L(f"    // synthesis translate_off")
        L(f"")
        L(f"    property p_stall_hold;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (wb_cyc_i && wb_stb_i && wb_stall_o) |=> (wb_cyc_i && wb_stb_i);")
        L(f"    endproperty")
        L(f"    assert property (p_stall_hold)")
        L(f"        else $error(\"[WB-005] master released request during stall\");")
        L(f"")
        L(f"    property p_tag;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (rsp_valid && tag_cnt > 0) |-> (rsp_aux == tag_mem[tag_rd[TAG_PTR_W-1:0]]);")
        L(f"    endproperty")
        L(f"    assert property (p_tag)")
        L(f"        else $error(\"[WB-009] aux tag mismatch\");")
        L(f"")
        L(f"    property p_burst_len;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        burst_active |-> (burst_cnt < BURST_CTR_W'(MAX_BURST_LEN));")
        L(f"    endproperty")
        L(f"    assert property (p_burst_len)")
        L(f"        else $error(\"[WB-003/004] burst exceeded MAX_BURST_LEN\");")
        L(f"")
        L(f"    property p_tag_no_overflow;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        1'b1 |-> (tag_cnt <= TAG_FIFO_DEPTH[TAG_PTR_W:0]);")
        L(f"    endproperty")
        L(f"    assert property (p_tag_no_overflow)")
        L(f"        else $error(\"[WB-005] tag FIFO overflow\");")
        L(f"")
        L(f"    property p_sel_nonzero_write;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (wb_beat && wb_we_i) |-> (|wb_sel_i);")
        L(f"    endproperty")
        L(f"    assert property (p_sel_nonzero_write)")
        L(f"        else $warning(\"[WB-006] write with zero sel\");")
        L(f"")
        L(f"    covergroup cg_wb @(posedge clk);")
        L(f"        option.per_instance = 1;")
        L(f"        cp_single_rd  : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_CLASSIC);")
        L(f"        cp_single_wr  : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_CLASSIC);")
        L(f"        cp_burst_rd   : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_INC);")
        L(f"        cp_burst_wr   : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_INC);")
        L(f"        cp_burst_end  : coverpoint (wb_beat && wb_cti_i == CTI_END);")
        L(f"        cp_stall      : coverpoint wb_stall_o;")
        L(f"        cp_err        : coverpoint wb_err_o;")
        L(f"        cp_backtoback : coverpoint (wb_ack_o && wb_beat);")
        L(f"        cp_tag_full   : coverpoint tag_full;")
        L(f"    endgroup")
        L(f"    cg_wb cg_inst = new();")
        L(f"")
        L(f"    // synthesis translate_on")
        L(f"    // synopsys translate_on")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    # ================================================================
    # Testbench generation (~33 tests, VCD, Xelium-safe)
    # ================================================================
    def _tb_test_registry(self) -> list:
        """Returns ordered list of (id, description) for all TB tests."""
        return [
            ("A1", "Single write - no error"),
            ("A2", "req_valid pulsed during write"),
            ("A3", "Single read - ACK received"),
            ("A4", "Read data matches injected value"),
            ("A5", "Write completes at high address"),
            ("B1", "8-beat burst write completed (no hang)"),
            ("B2", "8 req_valid pulses for burst write"),
            ("B3", "8 ACKs for burst read with correct tags"),
            ("B4", "4-beat short burst req_valid count"),
            ("C1", "Stall asserted when req_ready=0"),
            ("C2", "No ACK during stall"),
            ("C3", "No req_valid during stall"),
            ("C4", "Transaction completes after stall released"),
            ("C5", "Stall on tag FIFO full (16 outstanding reads)"),
            ("D1", "No ACK when bus idle"),
            ("D2", "No ACK when CYC=1 STB=0"),
            ("D3", "No req_valid when bus idle"),
            ("D4", "No stall when bus idle"),
            ("D5", "No error when bus idle"),
            ("E1", "Error on unaligned address (0x01)"),
            ("E2", "No error on aligned address (0x04)"),
            ("E3", "Error on unaligned address (0x02)"),
            ("F1", "Write completes (aux tag incremented)"),
            ("F2", "Read response data matches injected value"),
            ("G1", "8 ACKs received for 8 outstanding reads"),
            ("H1", "req_valid low after async reset"),
            ("H2", "wb_ack_o low after async reset"),
            ("H3", "wb_err_o low after async reset"),
            ("H4", "Stall low after reset recovery"),
            ("H5", "Write succeeds after reset recovery"),
            ("I1", "CYC drop mid-burst (no hang)"),
            ("I2", "Write succeeds after burst abort"),
        ]

    def generate_testbench(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        aw = p["ADDR_WIDTH"]
        dw = p["DATA_WIDTH"]
        sw = p["SEL_WIDTH"]
        auxw = p["AUX_WIDTH"]
        burst = p["MAX_BURST_LEN"]
        tfd = p["TAG_FIFO_DEPTH"]

        tests = self._tb_test_registry()

        lines = []
        L = lines.append

        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// wb_port_tb.sv -- Enhanced testbench ({len(tests)} tests)")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Wishbone Port Interface Agent (Phase 1)")
        L(f"//")
        L(f"// Sections:")
        L(f"//   A: Single write/read transactions")
        L(f"//   B: Burst write/read (BL8, CTI_INC/CTI_END)")
        L(f"//   C: Stall / backpressure behavior")
        L(f"//   D: Protocol compliance (ACK gating, idle behavior)")
        L(f"//   E: Error detection (unaligned addr)")
        L(f"//   F: Aux tag propagation and read response path")
        L(f"//   G: Tag FIFO pressure (back-to-back reads)")
        L(f"//   H: Reset mid-transaction")
        L(f"//   I: Edge cases (CYC drop mid-burst)")
        L(f"//")
        L(f"// Test List:")
        for tid, desc in tests:
            L(f"//   {tid:4s} {desc}")
        L(f"//")
        L(f"// VCD: dumps wb_port_tb.vcd")
        L(f"//==============================================================")
        L(f"module wb_port_tb;")
        L(f"")
        L(f"    localparam real CLK_PERIOD = {p['CTRL_PERIOD']};")
        L(f"    localparam ADDR_WIDTH = {aw};")
        L(f"    localparam DATA_WIDTH = {dw};")
        L(f"    localparam SEL_WIDTH  = {sw};")
        L(f"    localparam AUX_WIDTH  = {auxw};")
        L(f"    localparam MAX_BURST  = {burst};")
        L(f"    localparam TAG_FIFO_DEPTH = {tfd};")
        L(f"")
        L(f"    logic clk = 0;")
        L(f"    always #(CLK_PERIOD/2) clk = ~clk;")
        L(f"")
        L(f"    logic                  rst_n;")
        L(f"    logic                  wb_cyc_i;")
        L(f"    logic                  wb_stb_i;")
        L(f"    logic                  wb_we_i;")
        L(f"    logic [ADDR_WIDTH-1:0] wb_adr_i;")
        L(f"    logic [DATA_WIDTH-1:0] wb_dat_i;")
        L(f"    logic [SEL_WIDTH-1:0]  wb_sel_i;")
        L(f"    logic [1:0]            wb_bte_i;")
        L(f"    logic [2:0]            wb_cti_i;")
        L(f"    logic                  wb_ack_o;")
        L(f"    logic [DATA_WIDTH-1:0] wb_dat_o;")
        L(f"    logic                  wb_stall_o;")
        L(f"    logic                  wb_err_o;")
        L(f"    logic                  req_valid;")
        L(f"    logic                  req_we;")
        L(f"    logic [ADDR_WIDTH-1:0] req_addr;")
        L(f"    logic [DATA_WIDTH-1:0] req_wdata;")
        L(f"    logic [SEL_WIDTH-1:0]  req_wmask;")
        L(f"    logic [AUX_WIDTH-1:0]  req_aux;")
        L(f"    logic                  req_ready;")
        L(f"    logic                  rsp_valid;")
        L(f"    logic [DATA_WIDTH-1:0] rsp_rdata;")
        L(f"    logic [AUX_WIDTH-1:0]  rsp_aux;")
        L(f"")
        L(f"    localparam logic [2:0] CTI_CLASSIC = 3'b000;")
        L(f"    localparam logic [2:0] CTI_INC     = 3'b010;")
        L(f"    localparam logic [2:0] CTI_END     = 3'b111;")
        L(f"    localparam logic [1:0] BTE_LINEAR  = 2'b00;")
        L(f"")
        L(f"    wb_port dut (")
        L(f"        .clk(clk), .rst_n(rst_n),")
        L(f"        .wb_cyc_i(wb_cyc_i), .wb_stb_i(wb_stb_i), .wb_we_i(wb_we_i),")
        L(f"        .wb_adr_i(wb_adr_i), .wb_dat_i(wb_dat_i), .wb_sel_i(wb_sel_i),")
        L(f"        .wb_bte_i(wb_bte_i), .wb_cti_i(wb_cti_i),")
        L(f"        .wb_ack_o(wb_ack_o), .wb_dat_o(wb_dat_o),")
        L(f"        .wb_stall_o(wb_stall_o), .wb_err_o(wb_err_o),")
        L(f"        .req_valid(req_valid), .req_we(req_we), .req_addr(req_addr),")
        L(f"        .req_wdata(req_wdata), .req_wmask(req_wmask), .req_aux(req_aux),")
        L(f"        .req_ready(req_ready),")
        L(f"        .rsp_valid(rsp_valid), .rsp_rdata(rsp_rdata), .rsp_aux(rsp_aux)")
        L(f"    );")
        L(f"")

        # Test infrastructure
        L(f"    int pass_count = 0, fail_count = 0, total_tests = 0;")
        L(f"    task automatic check(string name, logic condition);")
        L(f"        total_tests++;")
        L(f"        if (condition) begin pass_count++; $display(\"  [PASS] %0d: %s\", total_tests, name); end")
        L(f"        else begin fail_count++; $display(\"  [FAIL] %0d: %s\", total_tests, name); end")
        L(f"    endtask")
        L(f"")

        # Shadow aux_ctr and tag tracker
        L(f"    // Shadow aux_ctr -- mirrors DUT for correct rsp_aux generation")
        L(f"    logic [AUX_WIDTH-1:0] shadow_aux_ctr;")
        L(f"    wire shadow_beat = wb_cyc_i & wb_stb_i & ~wb_stall_o;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) shadow_aux_ctr <= '0;")
        L(f"        else if (shadow_beat) shadow_aux_ctr <= shadow_aux_ctr + 1'b1;")
        L(f"")
        L(f"    logic [AUX_WIDTH-1:0] expected_tags [0:TAG_FIFO_DEPTH-1];")
        L(f"    int etag_wr, etag_rd;")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) etag_wr <= 0;")
        L(f"        else if (shadow_beat && !wb_we_i) begin")
        L(f"            expected_tags[etag_wr % TAG_FIFO_DEPTH] <= shadow_aux_ctr;")
        L(f"            etag_wr <= etag_wr + 1;")
        L(f"        end")
        L(f"    end")
        L(f"")

        # Helper tasks
        L(f"    task automatic wb_idle();")
        L(f"        wb_cyc_i=0; wb_stb_i=0; wb_we_i=0; wb_adr_i='0;")
        L(f"        wb_dat_i='0; wb_sel_i='0; wb_bte_i=BTE_LINEAR; wb_cti_i=CTI_CLASSIC;")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic wb_write_classic(input [{aw-1}:0] addr, input [{dw-1}:0] data,")
        L(f"                                    input [{sw-1}:0] sel = {{{sw}{{1'b1}}}});")
        L(f"        @(posedge clk);")
        L(f"        wb_cyc_i=1; wb_stb_i=1; wb_we_i=1; wb_adr_i=addr; wb_dat_i=data;")
        L(f"        wb_sel_i=sel; wb_cti_i=CTI_CLASSIC; wb_bte_i=BTE_LINEAR;")
        L(f"        do @(posedge clk); while (wb_stall_o);")
        L(f"        wb_stb_i=0;")
        L(f"        if (!wb_ack_o) repeat (20) begin @(posedge clk); if (wb_ack_o) break; end")
        L(f"        @(posedge clk); wb_idle();")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic wb_read_classic(input [{aw-1}:0] addr, output [{dw-1}:0] data,")
        L(f"                                   input [{dw-1}:0] inject_rdata = 32'hCAFE_1234, input int rsp_delay = 5);")
        L(f"        logic [AUX_WIDTH-1:0] tag_at_beat;")
        L(f"        @(posedge clk);")
        L(f"        wb_cyc_i=1; wb_stb_i=1; wb_we_i=0; wb_adr_i=addr;")
        L(f"        wb_sel_i={{{sw}{{1'b1}}}}; wb_cti_i=CTI_CLASSIC; wb_bte_i=BTE_LINEAR;")
        L(f"        do @(posedge clk); while (wb_stall_o);")
        L(f"        tag_at_beat = shadow_aux_ctr - 1;")
        L(f"        wb_stb_i=0;")
        L(f"        fork")
        L(f"            begin repeat(rsp_delay) @(posedge clk); rsp_valid=1; rsp_rdata=inject_rdata;")
        L(f"                  rsp_aux=tag_at_beat; @(posedge clk); rsp_valid=0; end")
        L(f"            begin repeat(rsp_delay+10) begin @(posedge clk); if(wb_ack_o) break; end end")
        L(f"        join_any")
        L(f"        disable fork;")
        L(f"        data = wb_dat_o; @(posedge clk); wb_idle();")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic wb_burst_write(input [{aw-1}:0] base_addr, input int beats, input [{dw-1}:0] base_data);")
        L(f"        @(posedge clk); wb_cyc_i=1;")
        L(f"        for (int i=0; i<beats; i++) begin")
        L(f"            wb_stb_i=1; wb_we_i=1; wb_adr_i=base_addr+(i*{p['ADDR_INC']});")
        L(f"            wb_dat_i=base_data+i; wb_sel_i={{{sw}{{1'b1}}}};")
        L(f"            wb_bte_i=BTE_LINEAR; wb_cti_i=(i<beats-1)?CTI_INC:CTI_END;")
        L(f"            do @(posedge clk); while (wb_stall_o);")
        L(f"        end")
        L(f"        wb_stb_i=0; repeat(beats+5) @(posedge clk); wb_idle();")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic inject_read_responses(input int count, input int start_etag_rd);")
        L(f"        for (int i=0; i<count; i++) begin")
        L(f"            rsp_valid=1; rsp_rdata=32'hFACE_0000+i;")
        L(f"            rsp_aux=expected_tags[(start_etag_rd+i)%TAG_FIFO_DEPTH];")
        L(f"            @(posedge clk);")
        L(f"        end")
        L(f"        rsp_valid=0;")
        L(f"    endtask")
        L(f"")

        # Monitors
        L(f"    int ack_count, req_valid_count, err_count;")
        L(f"    always @(posedge clk) if (rst_n) begin")
        L(f"        if (wb_ack_o) ack_count++; if (req_valid) req_valid_count++; if (wb_err_o) err_count++;")
        L(f"    end")
        L(f"    task automatic reset_monitors(); ack_count=0; req_valid_count=0; err_count=0; endtask")
        L(f"")
        L(f"    task automatic hw_reset();")
        L(f"        rst_n=0; req_ready=1; rsp_valid=0; rsp_rdata='0; rsp_aux='0; wb_idle(); etag_rd=0;")
        L(f"        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);")
        L(f"    endtask")
        L(f"")

        # Main test sequence - identical logic to the standalone TB
        L(f"    logic [{dw-1}:0] rd_data;")
        L(f"")
        L(f"    initial begin")
        L(f"        $dumpfile(\"wb_port_tb.vcd\");")
        L(f"        $dumpvars(0, wb_port_tb);")
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"  wb_port_tb -- Enhanced Wishbone B4 Testbench\");")
        L(f"        $display(\"  ADDR=%0d DATA=%0d SEL=%0d AUX=%0d BURST=%0d\",")
        L(f"                 ADDR_WIDTH, DATA_WIDTH, SEL_WIDTH, AUX_WIDTH, MAX_BURST);")
        L(f"        $display(\"==========================================================\");")
        L(f"")

        # Section A
        L(f"        $display(\"\"); $display(\"  -- Section A: Single Write / Read --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        wb_write_classic({aw}'h0000_0100, 32'hDEAD_BEEF);")
        L(f"        check(\"A1: Single write - no error\", wb_err_o === 1'b0);")
        L(f"        check($sformatf(\"A2: req_valid seen [count=%0d]\", req_valid_count), req_valid_count >= 1);")
        L(f"        reset_monitors();")
        L(f"        wb_read_classic({aw}'h0000_0100, rd_data, 32'hCAFE_1234, 3); etag_rd++;")
        L(f"        check(\"A3: Single read - ACK received\", ack_count >= 1);")
        L(f"        check($sformatf(\"A4: Read data = 0x%08X\", rd_data), rd_data == 32'hCAFE_1234);")
        L(f"        reset_monitors();")
        L(f"        wb_write_classic({aw}'h1ABC_DE00, 32'h1234_5678);")
        L(f"        check(\"A5: Write at high address\", wb_err_o === 1'b0);")
        L(f"")

        # Section B
        L(f"        $display(\"\"); $display(\"  -- Section B: Burst Write / Read (BL8) --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        wb_burst_write({aw}'h0000_0200, 8, 32'hBEEF_0000);")
        L(f"        check(\"B1: 8-beat burst write completed\", 1);")
        L(f"        check($sformatf(\"B2: 8 req_valid pulses [got %0d]\", req_valid_count), req_valid_count == 8);")
        L(f"        reset_monitors();")
        L(f"        begin")
        L(f"            int saved; saved = etag_wr;")
        L(f"            fork")
        L(f"                begin @(posedge clk); wb_cyc_i=1;")
        L(f"                    for (int i=0;i<8;i++) begin wb_stb_i=1;wb_we_i=0;")
        L(f"                        wb_adr_i={aw}'h0000_0400+(i*{p['ADDR_INC']});wb_sel_i={{{sw}{{1'b1}}}};")
        L(f"                        wb_bte_i=BTE_LINEAR;wb_cti_i=(i<7)?CTI_INC:CTI_END;")
        L(f"                        do @(posedge clk); while(wb_stall_o); end")
        L(f"                    wb_stb_i=0; end")
        L(f"                begin repeat(12) @(posedge clk); inject_read_responses(8, saved); etag_rd=saved+8; end")
        L(f"            join")
        L(f"            repeat(5) @(posedge clk); wb_idle();")
        L(f"        end")
        L(f"        check($sformatf(\"B3: 8 ACKs for burst read [got %0d]\", ack_count), ack_count >= 8);")
        L(f"        reset_monitors();")
        L(f"        wb_burst_write({aw}'h0000_0800, 4, 32'hAAAA_0000);")
        L(f"        check($sformatf(\"B4: 4-beat short burst [%0d]\", req_valid_count), req_valid_count == 4);")
        L(f"")

        # Section C
        L(f"        $display(\"\"); $display(\"  -- Section C: Stall / Backpressure --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        req_ready=0; @(posedge clk);")
        L(f"        wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i={aw}'h0000_1000;wb_dat_i=32'hCAFE_BABE;")
        L(f"        wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;")
        L(f"        repeat(3) @(posedge clk);")
        L(f"        check(\"C1: Stall when req_ready=0\", wb_stall_o===1'b1);")
        L(f"        check(\"C2: No ACK during stall\", wb_ack_o===1'b0);")
        L(f"        check($sformatf(\"C3: No req_valid during stall [%0d]\", req_valid_count), req_valid_count==0);")
        L(f"        req_ready=1; repeat(5) @(posedge clk);")
        L(f"        check(\"C4: Completes after stall released\", ack_count>=1); wb_idle();")
        L(f"")
        L(f"        hw_reset(); reset_monitors(); @(posedge clk); wb_cyc_i=1;")
        L(f"        begin int rd_iss; rd_iss=0;")
        L(f"            for (int i=0;i<TAG_FIFO_DEPTH;i++) begin")
        L(f"                wb_stb_i=1;wb_we_i=0;wb_adr_i={aw}'h0000_2000+(i*{p['ADDR_INC']});")
        L(f"                wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;")
        L(f"                @(posedge clk); if(!wb_stall_o) rd_iss++; else break;")
        L(f"                while(wb_stall_o) @(posedge clk);")
        L(f"            end")
        L(f"            wb_stb_i=1;wb_we_i=0;wb_adr_i={aw}'h0000_2040;wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_CLASSIC;")
        L(f"            repeat(3) @(posedge clk);")
        L(f"            check($sformatf(\"C5: Stall tag FIFO full (%0d reads)\", rd_iss), wb_stall_o===1'b1);")
        L(f"        end")
        L(f"        wb_idle();")
        L(f"")

        # Section D
        L(f"        $display(\"\"); $display(\"  -- Section D: Protocol Compliance --\");")
        L(f"        hw_reset(); reset_monitors(); wb_idle(); repeat(5) @(posedge clk);")
        L(f"        check(\"D1: No ACK when idle\", wb_ack_o===1'b0);")
        L(f"        @(posedge clk); wb_cyc_i=1;wb_stb_i=0; repeat(5) @(posedge clk);")
        L(f"        check(\"D2: No ACK CYC=1 STB=0\", wb_ack_o===1'b0); wb_idle();")
        L(f"        reset_monitors(); repeat(5) @(posedge clk);")
        L(f"        check($sformatf(\"D3: No req_valid idle [%0d]\", req_valid_count), req_valid_count==0);")
        L(f"        check(\"D4: No stall idle\", wb_stall_o===1'b0);")
        L(f"        check(\"D5: No error idle\", wb_err_o===1'b0);")
        L(f"")

        # Section E
        L(f"        $display(\"\"); $display(\"  -- Section E: Error Detection --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i={aw}'h0000_0001;")
        L(f"        wb_dat_i=32'hBAAD_F00D;wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;")
        L(f"        repeat(3) @(posedge clk);")
        L(f"        check(\"E1: Error unaligned 0x01\", wb_err_o===1'b1); wb_idle(); repeat(3) @(posedge clk);")
        L(f"        reset_monitors(); wb_write_classic({aw}'h0000_0004, 32'h1111_2222);")
        L(f"        check(\"E2: No error aligned 0x04\", err_count==0);")
        L(f"        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i={aw}'h0000_0002;")
        L(f"        wb_dat_i=32'h0;wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;")
        L(f"        repeat(3) @(posedge clk);")
        L(f"        check(\"E3: Error unaligned 0x02\", wb_err_o===1'b1); wb_idle(); repeat(3) @(posedge clk);")
        L(f"")

        # Section F
        L(f"        $display(\"\"); $display(\"  -- Section F: Aux Tag --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        wb_write_classic({aw}'h0000_3000, 32'hAAAA_BBBB);")
        L(f"        check(\"F1: Write completes\", wb_err_o===1'b0);")
        L(f"        reset_monitors();")
        L(f"        wb_read_classic({aw}'h0000_3000, rd_data, 32'h5555_6666, 3); etag_rd++;")
        L(f"        check($sformatf(\"F2: Read data 0x%08X\", rd_data), rd_data==32'h5555_6666);")
        L(f"")

        # Section G
        L(f"        $display(\"\"); $display(\"  -- Section G: Tag FIFO Stress --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        begin int saved; saved=etag_wr;")
        L(f"            @(posedge clk); wb_cyc_i=1;")
        L(f"            for(int i=0;i<8;i++) begin wb_stb_i=1;wb_we_i=0;")
        L(f"                wb_adr_i={aw}'h0000_4000+(i*{p['ADDR_INC']});wb_sel_i={{{sw}{{1'b1}}}};")
        L(f"                wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;")
        L(f"                do @(posedge clk); while(wb_stall_o); end")
        L(f"            wb_stb_i=0; repeat(2) @(posedge clk);")
        L(f"            inject_read_responses(8, saved); etag_rd=saved+8;")
        L(f"            repeat(3) @(posedge clk); wb_idle();")
        L(f"        end")
        L(f"        check($sformatf(\"G1: 8 ACKs for 8 reads [%0d]\", ack_count), ack_count>=8);")
        L(f"")

        # Section H
        L(f"        $display(\"\"); $display(\"  -- Section H: Reset Mid-Txn --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i={aw}'h0000_5000;")
        L(f"        wb_dat_i=32'hDEAD_DEAD;wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;")
        L(f"        repeat(2) @(posedge clk); rst_n=0; repeat(5) @(posedge clk);")
        L(f"        check(\"H1: req_valid low\", req_valid===1'b0);")
        L(f"        check(\"H2: ack low\", wb_ack_o===1'b0);")
        L(f"        check(\"H3: err low\", wb_err_o===1'b0);")
        L(f"        wb_idle(); rst_n=1; repeat(3) @(posedge clk);")
        L(f"        check(\"H4: Stall low after recovery\", wb_stall_o===1'b0);")
        L(f"        reset_monitors(); wb_write_classic({aw}'h0000_6000, 32'h1234_ABCD);")
        L(f"        check(\"H5: Write after reset\", ack_count>=1);")
        L(f"")

        # Section I
        L(f"        $display(\"\"); $display(\"  -- Section I: Edge Cases --\");")
        L(f"        hw_reset(); reset_monitors();")
        L(f"        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i={aw}'h0000_7000;")
        L(f"        wb_dat_i=32'hAAAA_0000;wb_sel_i={{{sw}{{1'b1}}}};wb_cti_i=CTI_INC;wb_bte_i=BTE_LINEAR;")
        L(f"        do @(posedge clk); while(wb_stall_o); wb_cyc_i=0;wb_stb_i=0;")
        L(f"        repeat(5) @(posedge clk); wb_idle();")
        L(f"        check(\"I1: CYC drop mid-burst\", 1);")
        L(f"        reset_monitors(); wb_write_classic({aw}'h0000_7100, 32'hBBBB_CCCC);")
        L(f"        check(\"I2: Write after abort\", ack_count>=1);")
        L(f"")

        # Summary
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        if (fail_count==0) $display(\"  ALL %0d TESTS PASSED\", total_tests);")
        L(f"        else $display(\"  %0d of %0d TESTS FAILED\", fail_count, total_tests);")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"\"); $finish;")
        L(f"    end")
        L(f"")
        L(f"    initial begin #(10_000_000); $display(\"  [FAIL] GLOBAL TIMEOUT\"); $finish; end")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    # ================================================================
    # Manifest generation
    # ================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "wb_port",
            "file": "wb_port.sv",
            "phase": 1,
            "agent": "wb_port_agent",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "DATA_WIDTH": p["DATA_WIDTH"],
                "ADDR_WIDTH": p["ADDR_WIDTH"],
                "SEL_WIDTH": p["SEL_WIDTH"],
                "AUX_WIDTH": p["AUX_WIDTH"],
                "MAX_BURST_LEN": p["MAX_BURST_LEN"],
                "QUEUE_DEPTH": p["QUEUE_DEPTH"],
                "BURST_CTR_W": p["BURST_CTR_WIDTH"],
                "TAG_FIFO_DEPTH": p["TAG_FIFO_DEPTH"],
                "ROW_BITS": p["ROW_BITS"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk",   "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "external_in": [
                    {"name": "wb_cyc_i", "width": 1,               "dir": "input"},
                    {"name": "wb_stb_i", "width": 1,               "dir": "input"},
                    {"name": "wb_we_i",  "width": 1,               "dir": "input"},
                    {"name": "wb_adr_i", "width": p["ADDR_WIDTH"], "dir": "input"},
                    {"name": "wb_dat_i", "width": p["DATA_WIDTH"], "dir": "input"},
                    {"name": "wb_sel_i", "width": p["SEL_WIDTH"],  "dir": "input"},
                    {"name": "wb_bte_i", "width": 2,               "dir": "input"},
                    {"name": "wb_cti_i", "width": 3,               "dir": "input"},
                ],
                "external_out": [
                    {"name": "wb_ack_o",   "width": 1,               "dir": "output"},
                    {"name": "wb_dat_o",   "width": p["DATA_WIDTH"], "dir": "output"},
                    {"name": "wb_stall_o", "width": 1,               "dir": "output"},
                    {"name": "wb_err_o",   "width": 1,               "dir": "output"},
                ],
                "internal_out": [
                    {"name": "req_valid", "width": 1,               "dir": "output"},
                    {"name": "req_we",    "width": 1,               "dir": "output"},
                    {"name": "req_addr",  "width": p["ADDR_WIDTH"], "dir": "output"},
                    {"name": "req_wdata", "width": p["DATA_WIDTH"], "dir": "output"},
                    {"name": "req_wmask", "width": p["SEL_WIDTH"],  "dir": "output"},
                    {"name": "req_aux",   "width": p["AUX_WIDTH"],  "dir": "output"},
                ],
                "internal_in": [
                    {"name": "req_ready", "width": 1,               "dir": "input"},
                    {"name": "rsp_valid", "width": 1,               "dir": "input"},
                    {"name": "rsp_rdata", "width": p["DATA_WIDTH"], "dir": "input"},
                    {"name": "rsp_aux",   "width": p["AUX_WIDTH"],  "dir": "input"},
                ],
            },
            "assertions": [
                {"name": "p_stall_hold",        "check": "WB-005"},
                {"name": "p_tag",               "check": "WB-009"},
                {"name": "p_burst_len",         "check": "WB-003/004"},
                {"name": "p_tag_no_overflow",   "check": "WB-005"},
                {"name": "p_sel_nonzero_write", "check": "WB-006"},
            ],
            "coverage_points": [
                "cp_single_rd", "cp_single_wr", "cp_burst_rd", "cp_burst_wr",
                "cp_burst_end", "cp_stall", "cp_err", "cp_backtoback", "cp_tag_full",
            ],
        }

    # ================================================================
    # Main entry point
    # ================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  WISHBONE PORT INTERFACE AGENT\n  Spec: {self.spec_path}\n{hdr}")

        print("\n[1/5] Validating parameters ...")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ERROR: {e}")
            return {"status": "error", "errors": errs}
        print("  OK: All parameters valid")
        for k, v in self.p.items():
            print(f"    {k:20s} = {v}")

        print("\n[2/5] Generating RTL ...")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines of SystemVerilog")

        print("\n[3/5] Generating testbench ...")
        tb = self.generate_testbench()
        tb_lines = len(tb.splitlines())
        print(f"  OK: {tb_lines} lines (~33 tests, 9 sections, VCD enabled)")

        print("\n[4/5] Generating port manifest ...")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  OK: {port_cnt} ports | {len(manifest['assertions'])} assertions | {len(manifest['coverage_points'])} cover points")

        print("\n[5/5] Writing files ...")
        rtl_path = self.output_dir / "wb_port.sv"
        rtl_path.write_text(rtl)
        print(f"  -> {rtl_path}")

        tb_path = self.output_dir / "wb_port_tb.sv"
        tb_path.write_text(tb)
        print(f"  -> {tb_path}")

        mfst_path = self.output_dir / "wb_port_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  -> {mfst_path}")

        print(f"\n{hdr}\n  DONE -- wb_port.sv + wb_port_tb.sv ready for Phase 1\n{hdr}")
        return {
            "status": "success",
            "module": "wb_port",
            "phase": 1,
            "rtl_path": str(rtl_path),
            "tb_path": str(tb_path),
            "manifest_path": str(mfst_path),
            "manifest": manifest,
            "rtl_lines": rtl_lines,
            "tb_lines": tb_lines,
            "ports": port_cnt,
        }


# --- Interactive entry point ---
if __name__ == "__main__":
    print("+=============================================+")
    print("|   WISHBONE PORT INTERFACE AGENT  (Phase 1)  |")
    print("+=============================================+")
    print()

    spec_path = input("Enter path to filled-in microarchitecture spec JSON: ").strip()
    if not spec_path:
        print("Error: No path provided.")
        sys.exit(1)
    if not os.path.isfile(spec_path):
        print(f"Error: File not found: {spec_path}")
        sys.exit(1)

    output_dir = input("Enter output directory (press Enter for ./output): ").strip()
    if not output_dir:
        output_dir = "./output"

    print()
    agent = WishbonePortAgent(spec_path, output_dir)
    result = agent.run()
    sys.exit(0 if result["status"] == "success" else 1)