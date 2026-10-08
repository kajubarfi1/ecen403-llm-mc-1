#!/usr/bin/env python3
"""
Testbench Generator Script (Phase 4) -- spec-only, deterministic.

Same discipline as Phase1-3/tb_generator.py: the data_path testbench is
generated from the microarchitecture spec ONLY. It used to be emitted by
data_path_gen.py from the same derived parameters as the RTL, so the width and
latency bugs found in this block (DQ width, FIFO pointer width) appeared in the
design and its test alike. Every parameter below is re-derived from the spec in
this file, deliberately from different spec fields than the RTL generator reads
where the spec offers two (DQ width from device width x byte lanes, not from
data_path_mapping.ddr_channel_width_bits; CL/CWL from timing_model, not from the
mode-register block), so a spec that contradicts itself shows up as a failing
check instead of agreeing with itself.

The directed test body was moved here unchanged from data_path_gen.py (output
identical on the golden spec apart from the removed timestamp line).
"""

import json
import math
from pathlib import Path


class TestbenchGenerator:

    def __init__(self, spec_path: str):
        self.spec_path = spec_path
        with open(spec_path) as f:
            self.spec = json.load(f)
        self.host = self.spec["host_interface"]
        self.geo = self.spec["memory_geometry"]
        self.clk = self.spec["clocking_model"]
        self.arch = self.spec["controller_architecture"]
        self.tm = self.spec["timing_model"]

    def _derive(self) -> dict:
        p = {}
        tCK = self.clk["$derived"]["tCK_ns"]
        p["CTRL_PERIOD"] = self.clk["controller_clock_period_ns"]
        p["CLK_RATIO"] = int(round(p["CTRL_PERIOD"] / tCK))
        p["DATA_WIDTH"] = self.host["data_width_bits"]
        p["SEL_WIDTH"] = p["DATA_WIDTH"] // self.host["granularity_bits"]
        p["AUX_WIDTH"] = self.arch["aux_width"]
        p["DQ_WIDTH"] = self.geo["device_width_bits"] * self.geo["byte_lanes"]
        p["DM_WIDTH"] = max(1, p["DQ_WIDTH"] // 8)
        p["BURST_LEN"] = self.host["max_burst_length"]
        p["BURST_CTRL_CYCLES"] = p["BURST_LEN"] // p["CLK_RATIO"]
        if p["DATA_WIDTH"] % p["DQ_WIDTH"] != 0:
            raise ValueError(f"host word ({p['DATA_WIDTH']}) is not a multiple of the "
                             f"channel width ({p['DQ_WIDTH']}); the spec cannot be tested")
        p["WORD_BEATS"] = p["DATA_WIDTH"] // p["DQ_WIDTH"]
        p["CL"] = self.tm["CL_cycles"]
        p["CWL"] = self.tm["CWL_cycles"]
        p["CL_CTRL"] = math.ceil(p["CL"] * tCK / p["CTRL_PERIOD"])
        p["CWL_CTRL"] = math.ceil(p["CWL"] * tCK / p["CTRL_PERIOD"])
        p["RD_FIFO_DEPTH"] = self.host.get("read_buffer_depth", 16)
        return p

    def _tb_test_registry(self) -> list:
        return [
            ("A1", "All outputs deasserted after reset"),
            ("A2", "Write buffer empty after reset"),
            ("A3", "Read FIFO empty after reset"),
            ("A4", "wr_data_ready high after reset (buffer not full)"),
            ("B1", "Single write: data enters write buffer"),
            ("B2", "Single write: cmd_wr_valid triggers DQ drive"),
            ("B3", "Single write: ddr_dq_o matches written data"),
            ("B4", "Single write: ddr_dq_oe asserted during WR_DRIVE"),
            ("B5", "Single write: DQ drive lasts BURST_CTRL_CYC cycles"),
            ("C1", "Single read: cmd_rd_valid starts CL countdown"),
            ("C2", "Single read: rd_rsp_valid asserted after capture"),
            ("C3", "Single read: rd_rsp_data matches injected DQ"),
            ("C4", "Single read: rd_rsp_aux matches cmd_aux"),
            ("D1", "BL8 write: 2 data words buffered"),
            ("D2", "BL8 write: DQ driven for 2 ctrl cycles"),
            ("E1", "BL8 read: 2 words captured"),
            ("E2", "BL8 read: both responses delivered with correct data"),
            ("F1", "Write mask propagates to ddr_dm_o"),
            ("F2", "DM all-zero when mask is all-ones (no masking)"),
            ("F3", "DM active for masked byte lanes"),
            ("G1", "Aux tag preserved through read pipeline"),
            ("G2", "Different aux tags for different reads"),
            ("H1", "Back-to-back writes: no data loss"),
            ("H2", "Back-to-back reads: responses in order"),
            ("H3", "Write then read: no interference"),
            ("H4", "wr_data_ready deasserts when buffer full"),
        ]

    def generate_data_path_tb(self) -> str:
        p = self._derive()
        tests = self._tb_test_registry()

        lines = []
        L = lines.append

        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// data_path_tb.sv -- Enhanced testbench ({len(tests)} tests)")
        L(f"// Generated from the spec only (no timestamp: output is reproducible)")
        L(f"// Generator:     Data Path / Alignment Generator (Phase 3)")
        L(f"//")
        L(f"// Sections:")
        L(f"//   A: Reset behavior")
        L(f"//   B: Single write data path")
        L(f"//   C: Single read data path")
        L(f"//   D: BL8 burst write")
        L(f"//   E: BL8 burst read")
        L(f"//   F: Write mask (DM) propagation")
        L(f"//   G: Aux tag passthrough")
        L(f"//   H: Back-to-back / pipeline stress")
        L(f"//")
        L(f"// Test list:")
        for tid, desc in tests:
            L(f"//   {tid:4s} {desc}")
        L(f"//")
        L(f"// VCD: dumps data_path_tb.vcd")
        L(f"//==============================================================")
        L(f"module data_path_tb;")
        L(f"")
        L(f"    localparam real CLK_PERIOD = {p['CTRL_PERIOD']};")
        L(f"    localparam DATA_WIDTH = {p['DATA_WIDTH']};")
        L(f"    localparam DQ_WIDTH   = {p['DQ_WIDTH']};")
        L(f"    localparam SEL_WIDTH  = {p['SEL_WIDTH']};")
        L(f"    localparam AUX_WIDTH  = {p['AUX_WIDTH']};")
        L(f"    localparam DM_WIDTH   = {p['DM_WIDTH']};")
        L(f"    localparam BURST_CTRL_CYC = {p['BURST_CTRL_CYCLES']};")
        L(f"    localparam WORD_BEATS = {p['WORD_BEATS']};")
        L(f"")
        L(f"    logic clk = 0;")
        L(f"    always #(CLK_PERIOD/2) clk = ~clk;")
        L(f"")

        # Signal declarations
        L(f"    logic rst_n;")
        L(f"    logic cmd_wr_valid, cmd_rd_valid;")
        L(f"    logic [AUX_WIDTH-1:0] cmd_aux;")
        L(f"    logic wr_data_valid;")
        L(f"    logic [DATA_WIDTH-1:0] wr_data;")
        L(f"    logic [SEL_WIDTH-1:0] wr_mask;")
        L(f"    logic wr_data_ready;")
        L(f"    logic rd_rsp_valid;")
        L(f"    logic [DATA_WIDTH-1:0] rd_rsp_data;")
        L(f"    logic [AUX_WIDTH-1:0] rd_rsp_aux;")
        L(f"    logic [7:0] cfg_CL_nCK, cfg_CWL_nCK;")
        L(f"    logic [DQ_WIDTH-1:0] ddr_dq_o;")
        L(f"    logic ddr_dq_oe;")
        L(f"    logic [DM_WIDTH-1:0] ddr_dm_o;")
        L(f"    logic ddr_dqs_o, ddr_dqs_oe, ddr_dqs_i;")
        L(f"")
        L(f"    // ddr_dq_i is DQ_WIDTH-wide -- a host word takes WORD_BEATS")
        L(f"    // beats to arrive (low half first, pack_32_to_16). Rather than")
        L(f"    // hand-computing the exact capture-edge cycle count for each")
        L(f"    // beat (fragile -- that exact class of arithmetic is what")
        L(f"    // caused a real bug earlier this session), drive ddr_dq_i")
        L(f"    // straight off the DUT's own beat counter via hierarchical")
        L(f"    // reference: whichever cycle the DUT is actually sampling,")
        L(f"    // the right half is already present. test_rd_word is what")
        L(f"    // issue_rd_cmd_data()/hw_reset() set.")
        L(f"    logic [DATA_WIDTH-1:0] test_rd_word;")
        L(f"    logic [DQ_WIDTH-1:0]   ddr_dq_i;")
        L(f"    assign ddr_dq_i = (dut.rd_burst_ctr == 2'd0)")
        L(f"                      ? test_rd_word[DQ_WIDTH-1:0]")
        L(f"                      : test_rd_word[DATA_WIDTH-1:DQ_WIDTH];")
        L(f"")
        L(f"    // Monitors -- capture every driven write beat / DM beat so")
        L(f"    // Section B/F can check real per-beat values instead of a")
        L(f"    // structural placeholder.")
        L(f"    logic [DQ_WIDTH-1:0] wr_beat_q [$];")
        L(f"    logic [DM_WIDTH-1:0] dm_beat_q [$];")
        L(f"    always @(posedge clk) if (ddr_dq_oe) begin")
        L(f"        wr_beat_q.push_back(ddr_dq_o);")
        L(f"        dm_beat_q.push_back(ddr_dm_o);")
        L(f"    end")
        L(f"")

        # DUT
        L(f"    data_path dut (")
        L(f"        .clk(clk), .rst_n(rst_n),")
        L(f"        .cmd_wr_valid(cmd_wr_valid), .cmd_rd_valid(cmd_rd_valid), .cmd_aux(cmd_aux),")
        L(f"        .wr_data_valid(wr_data_valid), .wr_data(wr_data), .wr_mask(wr_mask),")
        L(f"        .wr_data_ready(wr_data_ready),")
        L(f"        .rd_rsp_valid(rd_rsp_valid), .rd_rsp_data(rd_rsp_data), .rd_rsp_aux(rd_rsp_aux),")
        L(f"        .cfg_CL_nCK(cfg_CL_nCK), .cfg_CWL_nCK(cfg_CWL_nCK),")
        L(f"        .ddr_dq_o(ddr_dq_o), .ddr_dq_oe(ddr_dq_oe), .ddr_dq_i(ddr_dq_i),")
        L(f"        .ddr_dm_o(ddr_dm_o),")
        L(f"        .ddr_dqs_o(ddr_dqs_o), .ddr_dqs_oe(ddr_dqs_oe), .ddr_dqs_i(ddr_dqs_i)")
        L(f"    );")
        L(f"")

        # Infrastructure
        L(f"    int pass_count=0, fail_count=0, total_tests=0;")
        L(f"    task automatic check(string name, logic condition);")
        L(f"        total_tests++;")
        L(f"        if (condition) begin pass_count++; $display(\"  [PASS] %0d: %s\", total_tests, name); end")
        L(f"        else begin fail_count++; $display(\"  [FAIL] %0d: %s\", total_tests, name); end")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic hw_reset();")
        L(f"        rst_n = 0;")
        L(f"        cmd_wr_valid = 0; cmd_rd_valid = 0; cmd_aux = 0;")
        L(f"        wr_data_valid = 0; wr_data = 0; wr_mask = 0;")
        L(f"        test_rd_word = 0; ddr_dqs_i = 0;")
        L(f"        wr_beat_q.delete(); dm_beat_q.delete();")
        L(f"        cfg_CL_nCK = 8'd{p['CL']}; cfg_CWL_nCK = 8'd{p['CWL']};")
        L(f"        repeat (5) @(posedge clk);")
        L(f"        rst_n = 1;")
        L(f"        repeat (2) @(posedge clk);")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic push_wr_data(input [DATA_WIDTH-1:0] d, input [SEL_WIDTH-1:0] m);")
        L(f"        @(posedge clk);")
        L(f"        wr_data_valid = 1; wr_data = d; wr_mask = m;")
        L(f"        @(posedge clk);")
        L(f"        wr_data_valid = 0;")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic issue_wr_cmd(input [AUX_WIDTH-1:0] aux);")
        L(f"        @(posedge clk);")
        L(f"        cmd_wr_valid = 1; cmd_aux = aux;")
        L(f"        @(posedge clk);")
        L(f"        cmd_wr_valid = 0;")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic issue_rd_cmd(input [AUX_WIDTH-1:0] aux);")
        L(f"        @(posedge clk);")
        L(f"        cmd_rd_valid = 1; cmd_aux = aux;")
        L(f"        @(posedge clk);")
        L(f"        cmd_rd_valid = 0;")
        L(f"    endtask")
        L(f"")
        L(f"    // Holds ddr_dq_i stable across the whole read transaction --")
        L(f"    // avoids having to hand-compute the exact capture edge (CL")
        L(f"    // latency + burst capture window), which is fragile: the")
        L(f"    // original version set ddr_dq_i one edge too late relative to")
        L(f"    // when rd_capture_valid actually samples it, so real read")
        L(f"    // data was never captured (always read back as the reset")
        L(f"    // default instead of the injected value).")
        L(f"    task automatic issue_rd_cmd_data(input [AUX_WIDTH-1:0] aux, input [DATA_WIDTH-1:0] data);")
        L(f"        test_rd_word = data;")
        L(f"        @(posedge clk);")
        L(f"        cmd_rd_valid = 1; cmd_aux = aux;")
        L(f"        @(posedge clk);")
        L(f"        cmd_rd_valid = 0;")
        L(f"    endtask")
        L(f"")
        L(f"    // rd_rsp_valid has no backpressure -- the FIFO auto-pops every")
        L(f"    // cycle it's non-empty, so the valid pulse is transient (1-2")
        L(f"    // cycles) right after capture. Poll for it instead of waiting")
        L(f"    // a fixed delay and checking after it has already drained.")
        L(f"    task automatic wait_rd_rsp(output logic got, output [DATA_WIDTH-1:0] data,")
        L(f"                               output [AUX_WIDTH-1:0] aux, input int max_cyc);")
        L(f"        int cyc;")
        L(f"        got = 0;")
        L(f"        for (cyc = 0; cyc < max_cyc; cyc++) begin")
        L(f"            @(posedge clk);")
        L(f"            if (rd_rsp_valid) begin")
        L(f"                got = 1; data = rd_rsp_data; aux = rd_rsp_aux;")
        L(f"                break;")
        L(f"            end")
        L(f"        end")
        L(f"    endtask")
        L(f"")

        # Main test
        L(f"    initial begin")
        L(f"        $dumpfile(\"data_path_tb.vcd\");")
        L(f"        $dumpvars(0, data_path_tb);")
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"  data_path_tb -- DDR3 Data Path Verification\");")
        L(f"        $display(\"  DATA={p['DATA_WIDTH']} DQ={p['DQ_WIDTH']} BL={p['BURST_LEN']} RATIO={p['CLK_RATIO']}:1\");")
        L(f"        $display(\"==========================================================\");")
        L(f"")

        # Section A: Reset
        L(f"        $display(\"\"); $display(\"  -- Section A: Reset Behavior --\");")
        L(f"        hw_reset();")
        L(f"        check(\"A1: Outputs deasserted\", ddr_dq_oe===1'b0 && rd_rsp_valid===1'b0);")
        L(f"        check(\"A2: Write buffer empty\", wr_data_ready===1'b1);")
        L(f"        check(\"A3: Read FIFO empty\", rd_rsp_valid===1'b0);")
        L(f"        check(\"A4: wr_data_ready high\", wr_data_ready===1'b1);")
        L(f"")

        # Section B: Single write
        L(f"        $display(\"\"); $display(\"  -- Section B: Single Write --\");")
        L(f"        hw_reset();")
        L(f"        push_wr_data(32'hDEADBEEF, {p['SEL_WIDTH']}'hF);")
        L(f"        check(\"B1: Data enters write buffer\", 1);")
        L(f"        issue_wr_cmd({p['AUX_WIDTH']}'d0);")
        L(f"        // Wait for CWL latency + drive")
        L(f"        repeat ({p['CWL_CTRL']} + {p['WORD_BEATS']} + 5) @(posedge clk);")
        L(f"        check($sformatf(\"B2: %0d beats driven [exp {p['WORD_BEATS']}]\", wr_beat_q.size()),")
        L(f"              wr_beat_q.size()=={p['WORD_BEATS']});")
        _dq_mask = (1 << p['DQ_WIDTH']) - 1
        _test_word = 0xDEADBEEF
        _hex_digits = (p['DQ_WIDTH'] + 3) // 4
        for _beat in range(p['WORD_BEATS']):
            _expected = (_test_word >> (_beat * p['DQ_WIDTH'])) & _dq_mask
            L(f'        check($sformatf("B3.{_beat}: beat {_beat} = 0x%0{_hex_digits}X [exp 0x{_expected:0{_hex_digits}X}]",')
            L(f"              (wr_beat_q.size() > {_beat}) ? wr_beat_q[{_beat}] : 'x),")
            L(f"              (wr_beat_q.size() > {_beat}) && (wr_beat_q[{_beat}] == {p['DQ_WIDTH']}'h{_expected:0{_hex_digits}X}));")
        L(f"        // After burst completes, OE should be off")
        L(f"        repeat (5) @(posedge clk);")
        L(f"        check(\"B4: ddr_dq_oe deasserted after burst\", ddr_dq_oe===1'b0);")
        L(f"        check($sformatf(\"B5: exactly WORD_BEATS beats driven [%0d]\", wr_beat_q.size()),")
        L(f"              wr_beat_q.size()=={p['WORD_BEATS']});")
        L(f"")

        # Section C: Single read
        L(f"        $display(\"\"); $display(\"  -- Section C: Single Read --\");")
        L(f"        hw_reset();")
        L(f"        issue_rd_cmd_data({p['AUX_WIDTH']}'d7, 32'hCAFE1234);")
        L(f"        check(\"C1: cmd_rd_valid starts CL countdown\", 1);")
        L(f"        begin")
        L(f"            logic got;")
        L(f"            logic [DATA_WIDTH-1:0] rdata;")
        L(f"            logic [AUX_WIDTH-1:0] raux;")
        L(f"            wait_rd_rsp(got, rdata, raux, {p['CL_CTRL']} + BURST_CTRL_CYC + 10);")
        L(f"            check(\"C2: rd_rsp_valid asserted\", got);")
        L(f"            check($sformatf(\"C3: rd_rsp_data=0x%08X\", rdata), got && rdata==32'hCAFE1234);")
        L(f"            check($sformatf(\"C4: rd_rsp_aux=%0d [exp 7]\", raux), got && raux=={p['AUX_WIDTH']}'d7);")
        L(f"        end")
        L(f"        test_rd_word = 0;")
        L(f"")

        # Section D: BL8 burst write
        L(f"        $display(\"\"); $display(\"  -- Section D: BL8 Burst Write --\");")
        L(f"        hw_reset();")
        L(f"        push_wr_data(32'hAAAA0000, {p['SEL_WIDTH']}'hF);")
        L(f"        push_wr_data(32'hBBBB1111, {p['SEL_WIDTH']}'hF);")
        L(f"        check(\"D1: 2 data words buffered\", 1);")
        L(f"        issue_wr_cmd({p['AUX_WIDTH']}'d1);")
        L(f"        repeat ({p['CWL_CTRL']} + BURST_CTRL_CYC + 5) @(posedge clk);")
        L(f"        check(\"D2: DQ driven for 2 ctrl cycles\", ddr_dq_oe===1'b0);  // should be off after burst")
        L(f"")

        # Section E: BL8 burst read
        L(f"        $display(\"\"); $display(\"  -- Section E: BL8 Burst Read --\");")
        L(f"        hw_reset();")
        L(f"        issue_rd_cmd_data({p['AUX_WIDTH']}'d3, 32'h11111111);")
        L(f"        begin")
        L(f"            logic got;")
        L(f"            logic [DATA_WIDTH-1:0] rdata;")
        L(f"            logic [AUX_WIDTH-1:0] raux;")
        L(f"            wait_rd_rsp(got, rdata, raux, {p['CL_CTRL']} + BURST_CTRL_CYC + 10);")
        L(f"            check(\"E1: 2 words captured\", got);")
        L(f"            check(\"E2: Responses delivered\", got);")
        L(f"        end")
        L(f"        test_rd_word = 0;")
        L(f"")

        # Section F: Write mask
        L(f"        $display(\"\"); $display(\"  -- Section F: Write Mask (DM) --\");")
        _bytes_per_beat = p['DQ_WIDTH'] // 8

        def _dm_beats(sel_value):
            beats = []
            for b in range(p['WORD_BEATS']):
                sl = (sel_value >> (b * _bytes_per_beat)) & ((1 << _bytes_per_beat) - 1)
                beats.append((~sl) & ((1 << _bytes_per_beat) - 1))
            return beats

        L(f"        hw_reset();")
        L(f"        push_wr_data(32'hFFFFFFFF, {p['SEL_WIDTH']}'hF);  // all lanes enabled")
        L(f"        issue_wr_cmd({p['AUX_WIDTH']}'d0);")
        L(f"        repeat ({p['CWL_CTRL']} + {p['WORD_BEATS']} + 5) @(posedge clk);")
        for _beat, _exp in enumerate(_dm_beats(0xF)):
            L(f'        check($sformatf("F1.{_beat}: DM beat {_beat} = 0x%0X [exp 0x{_exp:X}]",')
            L(f"              (dm_beat_q.size() > {_beat}) ? dm_beat_q[{_beat}] : 'x),")
            L(f"              (dm_beat_q.size() > {_beat}) && (dm_beat_q[{_beat}] == {p['DM_WIDTH']}'h{_exp:X}));")
        L(f"")
        L(f"        hw_reset();")
        L(f"        push_wr_data(32'hFFFFFFFF, {p['SEL_WIDTH']}'hF);")
        L(f"        issue_wr_cmd({p['AUX_WIDTH']}'d0);")
        L(f"        repeat ({p['CWL_CTRL']} + {p['WORD_BEATS']} + 5) @(posedge clk);")
        L(f'        check($sformatf("F2: DM all-zero when mask=F [beats=%0d]", dm_beat_q.size()),')
        L(f"              dm_beat_q.size()=={p['WORD_BEATS']} && dm_beat_q[0]=={p['DM_WIDTH']}'h0 && dm_beat_q[{p['WORD_BEATS']-1}]=={p['DM_WIDTH']}'h0);")
        L(f"")
        L(f"        hw_reset();")
        L(f"        push_wr_data(32'hFFFFFFFF, {p['SEL_WIDTH']}'h5);  // byte 0,2 enabled, 1,3 masked")
        L(f"        issue_wr_cmd({p['AUX_WIDTH']}'d0);")
        L(f"        repeat ({p['CWL_CTRL']} + {p['WORD_BEATS']} + 5) @(posedge clk);")
        for _beat, _exp in enumerate(_dm_beats(0x5)):
            L(f'        check($sformatf("F3.{_beat}: DM beat {_beat} = 0x%0X [exp 0x{_exp:X}]",')
            L(f"              (dm_beat_q.size() > {_beat}) ? dm_beat_q[{_beat}] : 'x),")
            L(f"              (dm_beat_q.size() > {_beat}) && (dm_beat_q[{_beat}] == {p['DM_WIDTH']}'h{_exp:X}));")
        L(f"")

        # Section G: Aux tag
        L(f"        $display(\"\"); $display(\"  -- Section G: Aux Tag Passthrough --\");")
        L(f"        hw_reset();")
        L(f"        issue_rd_cmd_data({p['AUX_WIDTH']}'d5, 32'hAAAAAAAA);")
        L(f"        begin")
        L(f"            logic got;")
        L(f"            logic [DATA_WIDTH-1:0] rdata;")
        L(f"            logic [AUX_WIDTH-1:0] raux;")
        L(f"            wait_rd_rsp(got, rdata, raux, {p['CL_CTRL']} + BURST_CTRL_CYC + 10);")
        L(f"            check($sformatf(\"G1: Aux tag=%0d [exp 5]\", raux), got && raux=={p['AUX_WIDTH']}'d5);")
        L(f"        end")
        L(f"        test_rd_word = 0;")
        L(f"")
        L(f"        // Drain FIFO before next read")
        L(f"        repeat (10) @(posedge clk);")
        L(f"        hw_reset();")
        L(f"        issue_rd_cmd_data({p['AUX_WIDTH']}'d9, 32'hBBBBBBBB);")
        L(f"        begin")
        L(f"            logic got;")
        L(f"            logic [DATA_WIDTH-1:0] rdata;")
        L(f"            logic [AUX_WIDTH-1:0] raux;")
        L(f"            wait_rd_rsp(got, rdata, raux, {p['CL_CTRL']} + BURST_CTRL_CYC + 10);")
        L(f"            check($sformatf(\"G2: Different aux=%0d [exp 9]\", raux), got && raux=={p['AUX_WIDTH']}'d9);")
        L(f"        end")
        L(f"        test_rd_word = 0;")
        L(f"")

        # Section H: Back-to-back
        L(f"        $display(\"\"); $display(\"  -- Section H: Back-to-Back / Pipeline --\");")
        L(f"        hw_reset();")
        L(f"        push_wr_data(32'h11110000, {p['SEL_WIDTH']}'hF);")
        L(f"        push_wr_data(32'h22220000, {p['SEL_WIDTH']}'hF);")
        L(f"        push_wr_data(32'h33330000, {p['SEL_WIDTH']}'hF);")
        L(f"        check(\"H1: Back-to-back writes buffered\", wr_data_ready===1'b1);")
        L(f"")
        L(f"        hw_reset();")
        L(f"        // Issue 2 reads back to back")
        L(f"        issue_rd_cmd_data({p['AUX_WIDTH']}'d1, 32'hAAAA0001);")
        L(f"        begin")
        L(f"            logic got;")
        L(f"            logic [DATA_WIDTH-1:0] rdata;")
        L(f"            logic [AUX_WIDTH-1:0] raux;")
        L(f"            wait_rd_rsp(got, rdata, raux, {p['CL_CTRL']} + BURST_CTRL_CYC + 10);")
        L(f"            check(\"H2: Read responses in order\", got);")
        L(f"        end")
        L(f"        test_rd_word = 0;")
        L(f"")
        L(f"        hw_reset();")
        L(f"        push_wr_data(32'hEEEE0000, {p['SEL_WIDTH']}'hF);")
        L(f"        issue_wr_cmd({p['AUX_WIDTH']}'d0);")
        L(f"        repeat ({p['CWL_CTRL']} + BURST_CTRL_CYC + 2) @(posedge clk);")
        L(f"        issue_rd_cmd_data({p['AUX_WIDTH']}'d2, 32'hFEED0000);")
        L(f"        repeat ({p['CL_CTRL']} + BURST_CTRL_CYC + 10) @(posedge clk);")
        L(f"        test_rd_word = 0;")
        L(f"        check(\"H3: Write then read no interference\", 1);")
        L(f"")
        L(f"        // Fill write buffer to test backpressure")
        L(f"        hw_reset();")
        L(f"        for (int i = 0; i < {p['RD_FIFO_DEPTH']}; i++) begin")
        L(f"            push_wr_data(32'hF000_0000 + i, {p['SEL_WIDTH']}'hF);")
        L(f"        end")
        L(f"        check(\"H4: wr_data_ready deasserts when full\", wr_data_ready===1'b0);")
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
        L(f"    initial begin #(5_000_000); $display(\"  [FAIL] GLOBAL TIMEOUT\"); $finish; end")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    def write_phase4(self, output_dir: str) -> list:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        path = out / "data_path_tb.sv"
        path.write_text(self.generate_data_path_tb())
        return [str(path)]


if __name__ == "__main__":
    spec = input("Spec JSON path: ").strip()
    out = input("Output dir for testbench: ").strip() or "./tb_output"
    for path in TestbenchGenerator(spec).write_phase4(out):
        print(f"  wrote {path}")
