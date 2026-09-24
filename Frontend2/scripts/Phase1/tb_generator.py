#!/usr/bin/env python3
"""
Testbench Generator Script (Phase 1) — spec-only, deterministic.

Generates testbenches from the microarchitecture spec ONLY. Never reads
the generated RTL. This is a deliberate correctness property, not a
style choice: a testbench that reads its expected values out of the
RTL it's supposed to be checking can rubber-stamp a wrong value the
generator computed, since both sides agree by construction.

Concrete finding this replaces: the old
`Frontend/Agents/phase1_validation_agent.py::generate_init_fsm_tb` opened
`init_fsm.sv` and regexed MR0_VAL/MR1_VAL/MR2_VAL/MR3_VAL out of it into a
`mr_vals` dict -- which turned out to be dead code (never referenced again
in that file), so it wasn't actually causing false passes today, but it
was RTL-dependent for no reason and checked nothing. This version computes
the expected MR encodings directly from the spec (ported from
`init_fsm_agent.py`'s `_encode_mr0..3`, which are already pure functions of
the spec) and asserts the DUT's MR*_VAL localparams against them --
turning a dead computation into a real check.
"""

import json
import math
from pathlib import Path


class TestbenchGenerator:

    def __init__(self, spec_path: str):
        self.spec_path = spec_path
        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geometry = self.spec["memory_geometry"]
        self.clocking = self.spec["clocking_model"]
        self.init_seq = self.spec["initialization_sequence"]
        self.csrs = self.spec["csr_register_map"]
        self.host = self.spec["host_interface"]
        self.ctrl_arch = self.spec["controller_architecture"]

    # ════════════════════════════════════════════════════════════
    # MR register encoding -- ported verbatim from
    # Frontend/Agents/init_fsm_agent.py (already spec-only, no RTL).
    # ════════════════════════════════════════════════════════════
    def _encode_mr0(self) -> str:
        mr0 = self.init_seq["mode_registers"]["MR0"]
        cl = mr0["cas_latency_cycles"]
        wr_nCK = math.ceil(mr0["write_recovery_ns"] / self.clocking["$derived"]["tCK_ns"])
        cl_map = {5: 0b0001, 6: 0b0010, 7: 0b0011, 8: 0b0100, 9: 0b0101,
                  10: 0b0110, 11: 0b0111, 13: 0b1000, 14: 0b1001}
        wr_map = {5: 0b001, 6: 0b010, 7: 0b011, 8: 0b100, 10: 0b101,
                  12: 0b110, 14: 0b111, 16: 0b000}
        cl_enc = cl_map.get(cl, 0b0111)
        wr_enc = wr_map.get(wr_nCK, 0b110)
        val = 0
        val |= (cl_enc & 1) << 2
        val |= ((cl_enc >> 1) & 0b111) << 4
        val |= 1 << 8
        val |= (wr_enc & 0b111) << 9
        val |= (1 if mr0.get("precharge_pd_mode") == "fast_exit" else 0) << 12
        return f"{val:04X}"

    def _encode_mr1(self) -> str:
        mr1 = self.init_seq["mode_registers"]["MR1"]
        val = 0
        val |= (0 if mr1.get("dll_enable", True) else 1)
        if mr1.get("output_drive_strength") == "RZQ_7":
            val |= 1 << 1
        rtt_map = {"disabled": 0, "RZQ_4": 1, "RZQ_2": 2, "RZQ_6": 3, "RZQ_12": 4, "RZQ_8": 5}
        rtt = rtt_map.get(mr1.get("rtt_nom", "RZQ_4"), 1)
        val |= (rtt & 1) << 2
        val |= ((rtt >> 1) & 1) << 6
        val |= ((rtt >> 2) & 1) << 9
        if mr1.get("write_leveling_enable", False):
            val |= 1 << 7
        return f"{val:04X}"

    def _encode_mr2(self) -> str:
        mr2 = self.init_seq["mode_registers"]["MR2"]
        cwl_enc = mr2["cas_write_latency_cycles"] - 5
        rtt_wr_map = {"disabled": 0, "RZQ_4": 1, "RZQ_2": 2}
        rtt_wr = rtt_wr_map.get(mr2.get("rtt_wr", "RZQ_4"), 1)
        val = ((cwl_enc & 0b111) << 3) | ((rtt_wr & 0b11) << 9)
        return f"{val:04X}"

    def _encode_mr3(self) -> str:
        mr3 = self.init_seq["mode_registers"]["MR3"]
        val = (1 << 2) if mr3.get("mpr_enable", False) else 0
        return f"{val:04X}"

    # ════════════════════════════════════════════════════════════
    # INIT_FSM testbench -- spec-only (fixed: no RTL read)
    # ════════════════════════════════════════════════════════════
    def generate_init_fsm_tb(self) -> str:
        ctrl_period = self.clocking["controller_clock_period_ns"]
        reset_us = self.init_seq["reset_hold_us"]
        cke_us = self.init_seq["cke_delay_us"]
        wait_reset = math.ceil(reset_us * 1000 / ctrl_period)
        wait_cke = math.ceil(cke_us * 1000 / ctrl_period)
        tXPR = math.ceil(self.init_seq["tXPR_ns"] / ctrl_period)
        tZQ = math.ceil(self.init_seq["tZQinit_ns"] / ctrl_period)
        ddr_addr_w = max(self.geometry["row_bits"], self.geometry["column_bits"])

        mr0_hex = self._encode_mr0()
        mr1_hex = self._encode_mr1()
        mr2_hex = self._encode_mr2()
        mr3_hex = self._encode_mr3()

        timeout_cycles = wait_reset + wait_cke + tXPR + tZQ + 500

        return f"""`timescale 1ns / 1ps
module init_fsm_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    logic rst_n, enable, init_done, init_fail, init_cmd_valid;
    logic [3:0] init_cmd;
    logic [{ddr_addr_w-1}:0] init_addr;
    logic [2:0] init_bank;
    logic init_cke, init_reset_n;

    init_fsm dut (.*);

    localparam CMD_MRS = 4'b0000, CMD_ZQCL = 4'b0110;
    int pass_count=0, fail_count=0, total_tests=0, cycle_count=0;
    int cke_rise=0, resetn_rise=0, first_mrs=0, done_cycle=0, mr_cmd_count=0;
    logic [2:0] mr_bank_order[$];

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    always @(posedge clk) begin
        cycle_count++;
        if (init_cke && cke_rise==0 && cycle_count>10) cke_rise=cycle_count;
        if (init_reset_n && resetn_rise==0 && cycle_count>10) resetn_rise=cycle_count;
        if (init_cmd_valid && init_cmd==CMD_MRS) begin
            if (first_mrs==0) first_mrs=cycle_count;
            mr_bank_order.push_back(init_bank);
            mr_cmd_count++;
        end
        if (init_done && done_cycle==0) done_cycle=cycle_count;
    end

    initial begin
        $dumpfile("init_fsm_tb.vcd"); $dumpvars(0, init_fsm_tb);
        rst_n=0; enable=0; repeat(10) @(posedge clk); rst_n=1; enable=1;
        fork
            wait(init_done);
            begin repeat({timeout_cycles}) @(posedge clk); $display("[FAIL] TIMEOUT"); end
        join_any
        disable fork;
        repeat(10) @(posedge clk);

        check($sformatf("Reset hold >= {wait_reset} cyc (got %0d)", resetn_rise), resetn_rise>={wait_reset});
        check($sformatf("CKE delay >= {wait_cke} cyc"), (cke_rise-resetn_rise)>={wait_cke} || cke_rise>={wait_cke});
        check("init_done asserted", init_done===1'b1);
        check("init_fail not asserted", init_fail===1'b0);
        check($sformatf("4 MRS commands (got %0d)", mr_cmd_count), mr_cmd_count==4);
        if (mr_bank_order.size()>=4)
            check("MR order 2->3->1->0", mr_bank_order[0]==3'd2 && mr_bank_order[1]==3'd3 && mr_bank_order[2]==3'd1 && mr_bank_order[3]==3'd0);
        else check("MR order (insufficient cmds)", 0);
        check("Sequence completed", init_done===1'b1);

        // Spec-derived MR encoding checks -- computed independently of the
        // RTL (see _encode_mr0..3), not extracted from it.
        check($sformatf("MR0 encoding matches spec (exp 15'h{mr0_hex})"), dut.MR0_VAL === 15'h{mr0_hex});
        check($sformatf("MR1 encoding matches spec (exp 15'h{mr1_hex})"), dut.MR1_VAL === 15'h{mr1_hex});
        check($sformatf("MR2 encoding matches spec (exp 15'h{mr2_hex})"), dut.MR2_VAL === 15'h{mr2_hex});
        check($sformatf("MR3 encoding matches spec (exp 15'h{mr3_hex})"), dut.MR3_VAL === 15'h{mr3_hex});

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    # ════════════════════════════════════════════════════════════
    # CONFIG_REGS testbench -- spec-only, matching the REAL port
    # contract (csr_adr_i/csr_cyc_i/csr_sel_i). Ported from the
    # richer, 19-test version in config_regs_agent.py's own
    # generate_testbench() -- that one had it right; a separate,
    # independently-maintained copy in phase1_validation_agent.py had
    # drifted to a stale port list (csr_addr_i, missing csr_cyc_i/
    # csr_sel_i) that fails Xcelium elaboration outright. Confirmed
    # against a real xrun run: that stale version is what silently
    # made every real Phase 1 sim run fail on config_regs. This is
    # exactly the drift problem a single spec-only generator is
    # supposed to eliminate.
    # ════════════════════════════════════════════════════════════
    def _config_regs_tb_test_registry(self, regs) -> list:
        tests = []
        for i, r in enumerate(regs):
            rv = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
            tests.append((f"A{i+1}", f"{r['name']} reset = 0x{rv:08X}"))
        bi = 1
        for r in regs:
            if r["access"] in ("RW", "RW1C") and r["name"] not in ("ERROR_STATUS", "CTRL_STATUS"):
                tests.append((f"B{bi}", f"{r['name']} write/readback"))
                bi += 1
        tests += [
            ("C1", "CTRL_STATUS reflects status inputs"), ("C2", "CTRL_STATUS ignores writes (RO)"),
            ("D1", "bist_start self-clears after 1 cycle"), ("D2", "force_refresh self-clears after 1 cycle"),
            ("E1", "ERROR_STATUS latches ecc_ue event"), ("E2", "ERROR_STATUS W1C clears ecc_ue flag"),
            ("E3", "ERROR_STATUS flag stays clear after W1C"),
            ("F1", "Invalid address returns error"), ("F2", "Valid address no error"),
            ("G1", "cfg_tRCD_nCK matches TIMING_0[7:0]"), ("G2", "cfg_sched_policy matches CTRL_CONFIG[0]"),
            ("G3", "cfg_max_postpone matches REFRESH_CONFIG[3:0]"),
            ("H1", "Registers return to reset values after reset"), ("H2", "Normal operation after reset recovery"),
            ("I1", "Back-to-back writes to different registers"), ("I2", "Readback after back-to-back writes correct"),
        ]
        return tests

    def generate_config_regs_tb(self) -> str:
        ctrl_period = self.clocking["controller_clock_period_ns"]
        csr_map = self.csrs if isinstance(self.csrs, dict) else {"registers": self.csrs}
        regs = csr_map.get("registers", self.csrs if isinstance(self.csrs, list) else [])
        tests = self._config_regs_tb_test_registry(regs)

        lines = []
        L = lines.append
        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// config_regs_tb.sv -- spec-only testbench ({len(tests)} tests)")
        L(f"//==============================================================")
        L(f"module config_regs_tb;")
        L(f"")
        L(f"    localparam real CLK_PERIOD = {ctrl_period};")
        L(f"    logic clk = 0;")
        L(f"    always #(CLK_PERIOD/2) clk = ~clk;")
        L(f"")
        L(f"    logic        rst_n;")
        L(f"    logic        csr_cyc_i, csr_stb_i, csr_we_i;")
        L(f"    logic [7:0]  csr_adr_i;")
        L(f"    logic [31:0] csr_dat_i, csr_dat_o;")
        L(f"    logic [3:0]  csr_sel_i;")
        L(f"    logic        csr_ack_o, csr_err_o;")
        L(f"    logic        sts_init_done, sts_cal_done, sts_cal_fail;")
        L(f"    logic        sts_bist_done, sts_bist_fail;")
        L(f"    logic [2:0]  sts_ref_pending_cnt;")
        L(f"    logic        sts_self_refresh_active;")
        L(f"    logic [15:0] sts_ecc_ce_count;")
        L(f"    logic        sts_ecc_ue_event, sts_ref_starve_event, sts_init_fail_event;")
        L(f"    logic [12:0] sts_bist_fail_addr;")
        L(f"")
        L(f"    logic [7:0]  cfg_tRCD_nCK, cfg_tRP_nCK, cfg_tRAS_nCK, cfg_tRC_nCK;")
        L(f"    logic [7:0]  cfg_tRRD_nCK, cfg_tWTR_nCK, cfg_tFAW_nCK, cfg_tRFC_nCK;")
        L(f"    logic [7:0]  cfg_tWR_nCK, cfg_tRTP_nCK, cfg_CL_nCK, cfg_CWL_nCK;")
        L(f"    logic [7:0]  cfg_tCCD_nCK;  logic [23:0] cfg_tREFI_nCK;")
        L(f"    logic        cfg_sched_policy, cfg_row_policy, cfg_ecc_enable;")
        L(f"    logic [1:0]  cfg_self_ref_mode;")
        L(f"    logic        cfg_bist_start, cfg_force_refresh, cfg_force_self_ref;")
        L(f"    logic [3:0]  cfg_max_postpone, cfg_urgent_threshold;")
        L(f"    logic        cfg_ref_priority;")
        L(f"    logic [2:0]  cfg_bist_pattern; logic cfg_bist_addr_mode;")
        L(f"    logic [28:0] cfg_bist_addr_start, cfg_bist_addr_end;")
        L(f"")
        L(f"    config_regs dut (")
        L(f"        .clk(clk), .rst_n(rst_n),")
        L(f"        .csr_cyc_i(csr_cyc_i), .csr_stb_i(csr_stb_i), .csr_we_i(csr_we_i),")
        L(f"        .csr_adr_i(csr_adr_i), .csr_dat_i(csr_dat_i), .csr_sel_i(csr_sel_i),")
        L(f"        .csr_ack_o(csr_ack_o), .csr_dat_o(csr_dat_o), .csr_err_o(csr_err_o),")
        L(f"        .sts_init_done(sts_init_done), .sts_cal_done(sts_cal_done), .sts_cal_fail(sts_cal_fail),")
        L(f"        .sts_bist_done(sts_bist_done), .sts_bist_fail(sts_bist_fail),")
        L(f"        .sts_ref_pending_cnt(sts_ref_pending_cnt), .sts_self_refresh_active(sts_self_refresh_active),")
        L(f"        .sts_ecc_ce_count(sts_ecc_ce_count), .sts_ecc_ue_event(sts_ecc_ue_event),")
        L(f"        .sts_ref_starve_event(sts_ref_starve_event), .sts_init_fail_event(sts_init_fail_event),")
        L(f"        .sts_bist_fail_addr(sts_bist_fail_addr),")
        L(f"        .cfg_tRCD_nCK(cfg_tRCD_nCK), .cfg_tRP_nCK(cfg_tRP_nCK),")
        L(f"        .cfg_tRAS_nCK(cfg_tRAS_nCK), .cfg_tRC_nCK(cfg_tRC_nCK),")
        L(f"        .cfg_tRRD_nCK(cfg_tRRD_nCK), .cfg_tWTR_nCK(cfg_tWTR_nCK),")
        L(f"        .cfg_tFAW_nCK(cfg_tFAW_nCK), .cfg_tRFC_nCK(cfg_tRFC_nCK),")
        L(f"        .cfg_tWR_nCK(cfg_tWR_nCK), .cfg_tRTP_nCK(cfg_tRTP_nCK),")
        L(f"        .cfg_CL_nCK(cfg_CL_nCK), .cfg_CWL_nCK(cfg_CWL_nCK),")
        L(f"        .cfg_tCCD_nCK(cfg_tCCD_nCK), .cfg_tREFI_nCK(cfg_tREFI_nCK),")
        L(f"        .cfg_sched_policy(cfg_sched_policy), .cfg_row_policy(cfg_row_policy),")
        L(f"        .cfg_self_ref_mode(cfg_self_ref_mode), .cfg_ecc_enable(cfg_ecc_enable),")
        L(f"        .cfg_bist_start(cfg_bist_start), .cfg_force_refresh(cfg_force_refresh),")
        L(f"        .cfg_force_self_ref(cfg_force_self_ref),")
        L(f"        .cfg_max_postpone(cfg_max_postpone), .cfg_urgent_threshold(cfg_urgent_threshold),")
        L(f"        .cfg_ref_priority(cfg_ref_priority),")
        L(f"        .cfg_bist_pattern(cfg_bist_pattern), .cfg_bist_addr_mode(cfg_bist_addr_mode),")
        L(f"        .cfg_bist_addr_start(cfg_bist_addr_start), .cfg_bist_addr_end(cfg_bist_addr_end)")
        L(f"    );")
        L(f"")
        L(f"    int pass_count=0, fail_count=0, total_tests=0;")
        L(f"    task automatic check(string name, logic condition);")
        L(f"        total_tests++;")
        L(f'        if (condition) begin pass_count++; $display("  [PASS] %0d: %s", total_tests, name); end')
        L(f'        else begin fail_count++; $display("  [FAIL] %0d: %s", total_tests, name); end')
        L(f"    endtask")
        L(f"    logic [31:0] rdata;")
        L(f"    task automatic csr_idle(); csr_cyc_i=0;csr_stb_i=0;csr_we_i=0;csr_adr_i=0;csr_dat_i=0;csr_sel_i=4'hF; endtask")
        L(f"    task automatic csr_write(input [7:0] addr, input [31:0] data);")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=1;csr_adr_i=addr;csr_dat_i=data;csr_sel_i=4'hF;")
        L(f"        @(posedge clk); wait(csr_ack_o||csr_err_o); @(posedge clk); csr_idle();")
        L(f"    endtask")
        L(f"    task automatic csr_read(input [7:0] addr, output [31:0] data);")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=addr;csr_sel_i=4'hF;")
        L(f"        @(posedge clk); wait(csr_ack_o||csr_err_o); data=csr_dat_o; @(posedge clk); csr_idle();")
        L(f"    endtask")
        L(f"    task automatic hw_reset();")
        L(f"        rst_n=0; csr_idle();")
        L(f"        sts_init_done=0;sts_cal_done=0;sts_cal_fail=0;sts_bist_done=0;sts_bist_fail=0;")
        L(f"        sts_ref_pending_cnt=0;sts_self_refresh_active=0;sts_ecc_ce_count=0;")
        L(f"        sts_ecc_ue_event=0;sts_ref_starve_event=0;sts_init_fail_event=0;sts_bist_fail_addr=0;")
        L(f"        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);")
        L(f"    endtask")
        L(f"")
        L(f"    localparam [31:0] CTRL_CONFIG_WO_MASK = 32'hFFFFFF1F;")
        L(f"")
        L(f"    initial begin")
        L(f'        $dumpfile("config_regs_tb.vcd");')
        L(f"        $dumpvars(0, config_regs_tb);")
        L(f'        $display("");')
        L(f'        $display("==========================================================");')
        L(f'        $display("  config_regs_tb -- CSR Register Verification");')
        L(f'        $display("==========================================================");')
        L(f"        hw_reset();")
        L(f"")
        L(f'        $display(""); $display("  -- Section A: Reset Values --");')
        for i, r in enumerate(regs):
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            rst = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
            L(f'        csr_read(8\'h{off:02X}, rdata); check($sformatf("A{i+1}: {r["name"]} reset = 0x%08X", rdata), rdata == 32\'h{rst:08X});')
        L(f"")
        L(f'        $display(""); $display("  -- Section B: Write / Readback --");')
        bi = 1
        vi = 0
        test_vals = [0x0000001F, 0x12345678, 0xDEADBEEF, 0xCAFEBABE,
                     0xFACEFEED, 0x000001FF, 0x0000000F, 0x1ABC0000, 0x1FFFFFFF]
        for r in regs:
            if r["access"] == "RO" or r["name"] == "ERROR_STATUS":
                continue
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            val = test_vals[vi % len(test_vals)]
            vi += 1
            L(f"        csr_write(8'h{off:02X}, 32'h{val:08X}); csr_read(8'h{off:02X}, rdata);")
            if r["name"] == "CTRL_CONFIG":
                L(f'        check($sformatf("B{bi}: {r["name"]} write/readback (0x%08X, WO masked)", rdata),')
                L(f"              (rdata & CTRL_CONFIG_WO_MASK) == (32'h{val:08X} & CTRL_CONFIG_WO_MASK));")
            else:
                L(f'        check("B{bi}: {r["name"]} write/readback", rdata == 32\'h{val:08X});')
            bi += 1
        L(f"")
        L(f'        $display(""); $display("  -- Section C: CTRL_STATUS (RO) --");')
        L(f"        hw_reset();")
        L(f"        sts_init_done=1; sts_cal_done=1; sts_ref_pending_cnt=3'd5;")
        L(f"        repeat(2) @(posedge clk);")
        L(f"        csr_read(8'h00, rdata);")
        L(f'        check($sformatf("C1: CTRL_STATUS reflects inputs (0x%08X)", rdata),')
        L(f"              rdata[0]==1'b1 && rdata[1]==1'b1 && rdata[7:5]==3'd5);")
        L(f"        csr_write(8'h00, 32'hFFFFFFFF); csr_read(8'h00, rdata);")
        L(f'        check("C2: CTRL_STATUS ignores writes", rdata[0]==1\'b1 && rdata[1]==1\'b1);')
        L(f"")
        L(f'        $display(""); $display("  -- Section D: WO Self-Clearing --");')
        L(f"        hw_reset();")
        L(f"        csr_write(8'h04, 32'h00000029); repeat(1) @(posedge clk); csr_read(8'h04, rdata);")
        L(f'        check($sformatf("D1: bist_start self-clears (bit5=%0b)", rdata[5]), rdata[5]==1\'b0);')
        L(f"        csr_write(8'h04, 32'h00000049); repeat(1) @(posedge clk); csr_read(8'h04, rdata);")
        L(f'        check($sformatf("D2: force_refresh self-clears (bit6=%0b)", rdata[6]), rdata[6]==1\'b0);')
        L(f"")
        L(f'        $display(""); $display("  -- Section E: RW1C (ERROR_STATUS) --");')
        L(f"        hw_reset();")
        L(f"        sts_ecc_ue_event=1; @(posedge clk); sts_ecc_ue_event=0; repeat(2) @(posedge clk);")
        L(f'        csr_read(8\'h1C, rdata); check($sformatf("E1: ecc_ue latched (0x%08X)", rdata), rdata[16]==1\'b1);')
        L(f"        csr_write(8'h1C, 32'h00010000); csr_read(8'h1C, rdata);")
        L(f'        check($sformatf("E2: ecc_ue W1C clears (0x%08X)", rdata), rdata[16]==1\'b0);')
        L(f'        csr_read(8\'h1C, rdata); check("E3: Flag stays clear", rdata[16]==1\'b0);')
        L(f"")
        L(f'        $display(""); $display("  -- Section F: Error Handling --");')
        L(f"        hw_reset();")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=8'hFF;csr_sel_i=4'hF;")
        L(f"        begin")
        L(f"            logic saw_err; saw_err=0;")
        L(f"            repeat(10) begin @(posedge clk); if(csr_err_o) begin saw_err=1; break; end end")
        L(f'            check("F1: Invalid addr error", saw_err);')
        L(f"        end")
        L(f"        csr_idle(); repeat(2) @(posedge clk);")
        L(f'        csr_read(8\'h04, rdata); check("F2: Valid addr no error", csr_err_o===1\'b0);')
        L(f"")
        L(f'        $display(""); $display("  -- Section G: cfg_* Outputs --");')
        L(f"        hw_reset();")
        L(f"        csr_write(8'h08, 32'h44332211); repeat(2) @(posedge clk);")
        L(f'        check($sformatf("G1: cfg_tRCD_nCK=0x%02X", cfg_tRCD_nCK), cfg_tRCD_nCK==8\'h11);')
        L(f"        csr_write(8'h04, 32'h00000001); repeat(2) @(posedge clk);")
        L(f'        check($sformatf("G2: cfg_sched_policy=%0b", cfg_sched_policy), cfg_sched_policy==1\'b1);')
        L(f"        csr_write(8'h18, 32'h0000006A); repeat(2) @(posedge clk);")
        L(f'        check($sformatf("G3: cfg_max_postpone=%0d", cfg_max_postpone), cfg_max_postpone==4\'hA);')
        L(f"")
        L(f'        $display(""); $display("  -- Section H: Reset --");')
        L(f"        csr_write(8'h08, 32'hFFFFFFFF); csr_write(8'h0C, 32'hFFFFFFFF);")
        L(f"        rst_n=0; repeat(5) @(posedge clk); rst_n=1; csr_idle(); repeat(2) @(posedge clk);")
        L(f'        csr_read(8\'h08, rdata); check($sformatf("H1: TIMING_0 reset (0x%08X)", rdata), rdata==32\'h271C0B0B);')
        L(f'        csr_write(8\'h08, 32\'h11223344); csr_read(8\'h08, rdata); check("H2: Normal after reset", rdata==32\'h11223344);')
        L(f"")
        L(f'        $display(""); $display("  -- Section I: Edge Cases --");')
        L(f"        hw_reset();")
        L(f"        csr_write(8'h08, 32'hAAAAAAAA); csr_write(8'h0C, 32'hBBBBBBBB);")
        L(f'        csr_read(8\'h08, rdata); check("I1: Back-to-back TIMING_0", rdata==32\'hAAAAAAAA);')
        L(f'        csr_read(8\'h0C, rdata); check("I2: Back-to-back TIMING_1", rdata==32\'hBBBBBBBB);')
        L(f"")
        L(f'        $display("");')
        L(f'        $display("==========================================================");')
        L(f'        if (fail_count==0) $display("  ALL %0d TESTS PASSED", total_tests);')
        L(f'        else $display("  %0d of %0d TESTS FAILED", fail_count, total_tests);')
        L(f'        $display("==========================================================");')
        L(f'        $display(""); $finish;')
        L(f"    end")
        L(f'    initial begin #(1_000_000); $display("  [FAIL] GLOBAL TIMEOUT"); $finish; end')
        L(f"endmodule")
        return "\n".join(lines)

    # ════════════════════════════════════════════════════════════
    # WB_PORT testbench -- already spec-only in the original;
    # ported unchanged.
    # ════════════════════════════════════════════════════════════
    def generate_wb_port_tb(self) -> str:
        ctrl_period = self.clocking["controller_clock_period_ns"]
        addr_w = self.host["address_width_bits"]
        data_w = self.host["data_width_bits"]
        sel_w = data_w // 8
        aux_w = self.ctrl_arch["aux_width"]

        return f"""`timescale 1ns / 1ps
module wb_port_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    localparam ADDR_WIDTH={addr_w}, DATA_WIDTH={data_w}, SEL_WIDTH={sel_w}, AUX_WIDTH={aux_w};
    logic clk=0;
    always #(CLK_PERIOD/2) clk=~clk;

    logic wb_cyc_i, wb_stb_i, wb_we_i;
    logic [ADDR_WIDTH-1:0] wb_adr_i;
    logic [DATA_WIDTH-1:0] wb_dat_i, wb_dat_o;
    logic [SEL_WIDTH-1:0] wb_sel_i;
    logic wb_ack_o, wb_stall_o, wb_err_o;
    logic req_valid, req_we, req_ready;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [DATA_WIDTH-1:0] req_wdata;
    // Response-path inputs from the (unmodeled) memory backend. Must be
    // driven -- left unconnected, rsp_valid floats X, and since
    // wb_ack_o = wr_ack_r | rsp_valid, that X poisons wb_ack_o back to X
    // any time the write-ack path is 0, failing every "ack deasserted"
    // check even though the RTL itself is correct.
    logic rsp_valid;
    logic [DATA_WIDTH-1:0] rsp_rdata;
    logic [AUX_WIDTH-1:0] rsp_aux;
    logic rst_n;
    int pass_count=0, fail_count=0, total_tests=0;

    wb_port dut (.*);

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    task wb_idle(); wb_cyc_i=0; wb_stb_i=0; wb_we_i=0; wb_adr_i=0; wb_dat_i=0; wb_sel_i=0; endtask

    initial begin
        $dumpfile("wb_port_tb.vcd"); $dumpvars(0, wb_port_tb);
        rst_n=0; req_ready=1; rsp_valid=0; rsp_rdata=0; rsp_aux=0; wb_idle();
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);

        // Single write
        @(posedge clk); wb_cyc_i=1; wb_stb_i=1; wb_we_i=1;
        wb_adr_i={addr_w}'h100; wb_dat_i=32'hDEADBEEF; wb_sel_i={{SEL_WIDTH{{1'b1}}}};
        do @(posedge clk); while(wb_stall_o);
        wb_stb_i=0; if(!wb_ack_o) begin repeat(20) begin @(posedge clk); if(wb_ack_o) break; end end
        @(posedge clk); wb_idle();
        check("Single write OK", wb_err_o===1'b0);

        // ACK idle
        wb_idle(); repeat(3) @(posedge clk);
        check("ACK deasserted when idle", wb_ack_o===1'b0);

        // CYC without STB
        @(posedge clk); wb_cyc_i=1; wb_stb_i=0; repeat(3) @(posedge clk);
        check("No ACK when CYC=1 STB=0", wb_ack_o===1'b0);
        wb_idle();

        // Stall
        req_ready=0; @(posedge clk);
        wb_cyc_i=1; wb_stb_i=1; wb_we_i=1; wb_adr_i={addr_w}'h300;
        wb_dat_i=32'hCAFEBABE; wb_sel_i={{SEL_WIDTH{{1'b1}}}};
        repeat(3) @(posedge clk);
        check("Stall when backend busy", wb_stall_o===1'b1);
        req_ready=1; repeat(5) @(posedge clk); wb_idle();

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    # ════════════════════════════════════════════════════════════
    # Write all Phase 1 testbenches to a directory
    # ════════════════════════════════════════════════════════════
    def write_phase1(self, output_dir: str) -> list:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        written = []
        for filename, gen_fn in [
            ("init_fsm_tb.sv", self.generate_init_fsm_tb),
            ("config_regs_tb.sv", self.generate_config_regs_tb),
            ("wb_port_tb.sv", self.generate_wb_port_tb),
        ]:
            path = out / filename
            path.write_text(gen_fn())
            written.append(str(path))
        return written


if __name__ == "__main__":
    spec = input("Spec JSON path: ").strip()
    out = input("Output dir for testbenches: ").strip() or "./tb_output"
    tbg = TestbenchGenerator(spec)
    for path in tbg.write_phase1(out):
        print(f"  wrote {path}")
