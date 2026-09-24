#!/usr/bin/env python3
"""
Testbench Generator Script (Phase 2) — spec-only, deterministic.

Same discipline as Frontend2/scripts/Phase1/tb_generator.py: generates
testbenches from the microarchitecture spec ONLY, never reads generated RTL.
Port lists below were read directly from each Phase 2 generator's actual
generate_rtl()/generate_manifest() output (not from memory, not from the old
Frontend/Agents/*_agent.py files) — see Frontend2/scripts/Phase2/{addr_decoder,
calibration,refresh_ctrl,bank_tracker}_gen.py.

Every DUT port used with `dut (.*)` below has an explicitly declared,
explicitly driven local signal — per the Phase 1 postmortem (init_fsm/
wb_port), an undeclared port doesn't error, it silently floats X and
poisons downstream checks.

refresh_ctrl and bank_tracker take their timing parameters (cfg_tRCD_nCK
etc.) as runtime INPUTS, not RTL parameters, so their testbenches drive
small directed constants directly rather than the spec's real (large)
timing numbers — this keeps simulation short and keeps expected-cycle
arithmetic easy to hand-verify, exactly like Phase 1's config_regs_tb
drives directed CSR values rather than spec-scale ones.
"""

import json
import math
from pathlib import Path


class TestbenchGenerator:

    def __init__(self, spec_path: str):
        self.spec_path = spec_path
        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geo = self.spec["memory_geometry"]
        self.host = self.spec["host_interface"]
        self.cal = self.spec["calibration"]
        self.clocking = self.spec["clocking_model"]
        self.ca = self.spec["controller_architecture"]
        self.tm = self.spec["timing_model"]
        self.dc = self.tm["$derived_cycles"]
        self.rp = self.ca["refresh_policy"]

    # ════════════════════════════════════════════════════════════
    # ADDR_DECODER — combinational, no clk/rst_n port at all.
    # Bit-slicing derived independently from spec (ported from
    # addr_decoder_gen.py's _derive(), not read out of the RTL).
    # ════════════════════════════════════════════════════════════
    def _derive_addr_decoder(self) -> dict:
        p = {}
        p["ROW_BITS"] = self.geo["row_bits"]
        p["COL_BITS"] = self.geo["column_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["BL"] = self.geo["burst_length"]
        p["ADDR_WIDTH"] = self.host["address_width_bits"]
        p["RANK_BITS"] = max(1, 1 if self.geo["ranks"] > 1 else 0)

        channel_bytes = (self.geo["byte_lanes"] * self.geo["device_width_bits"]) // 8
        p["BURST_OFFSET"] = int(math.log2(p["BL"] * channel_bytes))
        col_low_skip = int(math.log2(p["BL"]))
        p["COL_USED"] = p["COL_BITS"] - col_low_skip

        p["col_lo"] = p["BURST_OFFSET"]
        p["col_hi"] = p["col_lo"] + p["COL_USED"] - 1
        p["bank_lo"] = p["col_hi"] + 1
        p["bank_hi"] = p["bank_lo"] + p["BANK_BITS"] - 1
        p["row_lo"] = p["bank_hi"] + 1
        p["row_hi"] = p["row_lo"] + p["ROW_BITS"] - 1
        return p

    def generate_addr_decoder_tb(self) -> str:
        p = self._derive_addr_decoder()
        aw, rb, bb, cb = p["ADDR_WIDTH"], p["ROW_BITS"], p["BANK_BITS"], p["COL_BITS"]

        def slice_addr(addr: int):
            row = (addr >> p["row_lo"]) & ((1 << rb) - 1)
            bank = (addr >> p["bank_lo"]) & ((1 << bb) - 1)
            col_upper = (addr >> p["col_lo"]) & ((1 << p["COL_USED"]) - 1)
            col = (col_upper << 3) & ((1 << cb) - 1)
            return row, bank, col

        vectors = []
        vectors.append(0)
        vectors.append((1 << aw) - 1)
        vectors.append(((1 << rb) - 1) << p["row_lo"])          # row field only
        vectors.append(((1 << bb) - 1) << p["bank_lo"])          # bank field only
        vectors.append(((1 << p["COL_USED"]) - 1) << p["col_lo"])  # col field only
        vectors.append(0x1_5A5A5 & ((1 << aw) - 1))               # mixed pattern

        lines = []
        L = lines.append
        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// addr_decoder_tb.sv -- spec-only testbench (combinational DUT)")
        L(f"//==============================================================")
        L(f"module addr_decoder_tb;")
        L(f"")
        L(f"    localparam ADDR_WIDTH={aw}, ROW_BITS={rb}, BANK_BITS={bb}, COL_BITS={cb}, RANK_BITS={p['RANK_BITS']};")
        L(f"")
        L(f"    logic [ADDR_WIDTH-1:0] req_addr;")
        L(f"    logic [ROW_BITS-1:0]   dec_row;")
        L(f"    logic [BANK_BITS-1:0]  dec_bank;")
        L(f"    logic [COL_BITS-1:0]   dec_col;")
        L(f"    logic [RANK_BITS-1:0]  dec_rank;")
        L(f"")
        L(f"    addr_decoder dut (.*);")
        L(f"")
        L(f"    int pass_count=0, fail_count=0, total_tests=0;")
        L(f"    task automatic check(string name, logic cond);")
        L(f"        total_tests++;")
        L(f'        if (cond) begin pass_count++; $display("  [PASS] %s", name); end')
        L(f'        else begin fail_count++; $display("  [FAIL] %s", name); end')
        L(f"    endtask")
        L(f"")
        L(f"    initial begin")
        L(f'        $dumpfile("addr_decoder_tb.vcd"); $dumpvars(0, addr_decoder_tb);')
        for i, addr in enumerate(vectors):
            row, bank, col = slice_addr(addr)
            L(f"        req_addr = {aw}'h{addr:0{(aw+3)//4}X}; #10;")
            L(f'        check($sformatf("V{i+1}: addr=0x%0h row", req_addr), dec_row === {rb}\'h{row:0{(rb+3)//4}X});')
            L(f'        check($sformatf("V{i+1}: addr=0x%0h bank", req_addr), dec_bank === {bb}\'h{bank:0{(bb+3)//4}X});')
            L(f'        check($sformatf("V{i+1}: addr=0x%0h col", req_addr), dec_col === {cb}\'h{col:0{(cb+3)//4}X});')
            L(f'        check($sformatf("V{i+1}: addr=0x%0h rank", req_addr), dec_rank === \'0);')
        L(f"")
        L(f'        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);')
        L(f'        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);')
        L(f"        $finish;")
        L(f"    end")
        L(f'    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end')
        L(f"endmodule")
        return "\n".join(lines)

    # ════════════════════════════════════════════════════════════
    # CALIBRATION — sticky cal_done latch, periodic ZQCS.
    # ════════════════════════════════════════════════════════════
    def _derive_calibration(self) -> dict:
        p = {}
        zqcs_nCK = self.cal.get("$derived", {}).get("periodic_zqcs_interval_nCK", 512000)
        ctrl_period = self.clocking["controller_clock_period_ns"]
        tCK = self.clocking["$derived"]["tCK_ns"]
        p["ZQCS_CTRL_CYC"] = math.ceil(zqcs_nCK * tCK / ctrl_period)
        p["ZQCS_CTR_W"] = max(1, p["ZQCS_CTRL_CYC"].bit_length())
        p["ctrl_period"] = ctrl_period
        return p

    def generate_calibration_tb(self) -> str:
        p = self._derive_calibration()
        ctrl_period = p["ctrl_period"]
        wait = p["ZQCS_CTRL_CYC"]

        return f"""`timescale 1ns / 1ps
module calibration_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    localparam ZQCS_CTR_W = {p['ZQCS_CTR_W']};
    localparam ZQCS_WAIT  = {wait};
    localparam TZQCS_CYC  = 1;

    logic rst_n, init_done, cal_done, cal_fail, zqcs_req, zqcs_ack;
    int pass_count=0, fail_count=0, total_tests=0;

    calibration #(.ZQCS_CTR_W(ZQCS_CTR_W), .ZQCS_WAIT(ZQCS_WAIT), .TZQCS_CYC(TZQCS_CYC)) dut (.*);

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    initial begin
        $dumpfile("calibration_tb.vcd"); $dumpvars(0, calibration_tb);
        rst_n=0; init_done=0; zqcs_ack=0;
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);

        // -- Section A: reset / pre-init_done defaults --
        check("A1: cal_done low before init_done", cal_done===1'b0);
        check("A2: cal_fail always low", cal_fail===1'b0);
        check("A3: zqcs_req low before cal_done", zqcs_req===1'b0);

        // -- Section B: cal_done sticky latch --
        @(posedge clk); init_done=1;
        @(posedge clk); init_done=0;  // one-cycle pulse
        repeat(2) @(posedge clk);
        check("B1: cal_done latched high after init_done pulse", cal_done===1'b1);
        check("B2: cal_fail still low", cal_fail===1'b0);
        repeat(20) @(posedge clk);
        check("B3: cal_done stays high after init_done deasserts (sticky)", cal_done===1'b1);

        // -- Section C: periodic ZQCS request timing --
        // zqcs_pending loads ZQCS_WAIT on the first cycle cal_done_r is
        // observed high inside the counter block -- one cycle after
        // cal_done itself rises (registered visibility lag) -- then
        // counts down; zqcs_req = zqcs_pending & cal_done_r.
        begin
            int cyc;
            logic seen;
            seen = 0;
            for (cyc = 0; cyc < ZQCS_WAIT + 20; cyc++) begin
                @(posedge clk);
                if (zqcs_req) begin seen = 1; break; end
            end
            check($sformatf("C1: zqcs_req asserts within ~ZQCS_WAIT cycles of cal_done (got %0d)", cyc), seen);
        end

        // -- Section D: zqcs_ack clears pending --
        @(posedge clk); zqcs_ack=1;
        @(posedge clk); zqcs_ack=0;
        repeat(2) @(posedge clk);
        check("D1: zqcs_req deasserts after ack", zqcs_req===1'b0);

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    # ════════════════════════════════════════════════════════════
    # REFRESH_CTRL — tREFI counter, postpone tracking, urgent
    # escalation, starvation detect. cfg_* are runtime inputs, so
    # the TB drives small directed constants (not spec-scale ones).
    # ════════════════════════════════════════════════════════════
    def generate_refresh_ctrl_tb(self) -> str:
        ctrl_period = self.clocking["controller_clock_period_ns"]
        # Directed, TB-owned test constants (independent of spec scale).
        trefi, max_postpone, urgent_thresh = 8, 4, 2

        return f"""`timescale 1ns / 1ps
module refresh_ctrl_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    logic        rst_n, init_done, cfg_force_refresh, cfg_ref_priority;
    logic [23:0] cfg_tREFI_nCK;
    logic [3:0]  cfg_max_postpone, cfg_urgent_threshold;
    logic        ref_required, ref_urgent, ref_ack, ref_starve_flag;
    logic [2:0]  ref_pending_cnt;
    int pass_count=0, fail_count=0, total_tests=0;

    refresh_ctrl dut (.*);

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    // Poll until ref_pending_cnt changes from its value at call time, or
    // give up after max_cyc cycles. Black-box: doesn't assume exact
    // internal tick timing, just that a change eventually happens.
    task automatic wait_for_pending_change(input int max_cyc, output logic changed);
        logic [2:0] start_val;
        int cyc;
        start_val = ref_pending_cnt;
        changed = 0;
        for (cyc = 0; cyc < max_cyc; cyc++) begin
            @(posedge clk);
            if (ref_pending_cnt !== start_val) begin changed = 1; break; end
        end
    endtask

    initial begin
        $dumpfile("refresh_ctrl_tb.vcd"); $dumpvars(0, refresh_ctrl_tb);
        rst_n=0; init_done=0; cfg_force_refresh=0; ref_ack=0;
        cfg_tREFI_nCK={trefi}; cfg_max_postpone={max_postpone};
        cfg_urgent_threshold={urgent_thresh}; cfg_ref_priority=1;
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);

        // -- Section A: reset / pre-init_done defaults --
        check("A1: ref_required low before init_done", ref_required===1'b0);
        check("A2: ref_pending_cnt zero before init_done", ref_pending_cnt===3'd0);
        check("A3: ref_starve_flag low before init_done", ref_starve_flag===1'b0);

        // -- Section B: tREFI ticks accumulate postpone count --
        @(posedge clk); init_done=1;
        begin
            logic changed;
            wait_for_pending_change(200, changed);
            check("B1: ref_pending_cnt increments after init_done (tick 1)", changed && ref_pending_cnt > 3'd0);
            check("B2: ref_required asserted once pending > 0", ref_required===1'b1);
        end

        // -- Section C: urgent escalation at cfg_urgent_threshold --
        begin
            logic changed;
            int guard;
            guard = 0;
            while (ref_pending_cnt < {urgent_thresh} && guard < 500) begin
                wait_for_pending_change(200, changed);
                guard++;
            end
            check($sformatf("C1: ref_urgent asserts at pending>=%0d (got %0d)", {urgent_thresh}, ref_pending_cnt),
                  ref_urgent===1'b1);
        end

        // -- Section D: saturation at cfg_max_postpone --
        begin
            logic changed;
            int guard;
            guard = 0;
            while (ref_pending_cnt < {max_postpone} && guard < 500) begin
                wait_for_pending_change(200, changed);
                guard++;
            end
            repeat({trefi} * 3) @(posedge clk);  // let several more ticks try to fire
            check($sformatf("D1: ref_pending_cnt saturates at %0d (got %0d)", {max_postpone}, ref_pending_cnt),
                  ref_pending_cnt === {max_postpone});
        end

        // -- Section E: ref_starve_flag pulses when saturated --
        begin
            logic seen;
            int cyc;
            seen = 0;
            for (cyc = 0; cyc < {trefi} * 2; cyc++) begin
                @(posedge clk);
                if (ref_starve_flag) begin seen = 1; break; end
            end
            check("E1: ref_starve_flag pulses while saturated", seen);
        end

        // -- Section F: ref_ack decrements pending count --
        begin
            logic [2:0] before_val;
            before_val = ref_pending_cnt;
            @(posedge clk); ref_ack=1;
            @(posedge clk); ref_ack=0;
            repeat(2) @(posedge clk);
            check($sformatf("F1: ref_ack decrements pending (before=%0d after=%0d)", before_val, ref_pending_cnt),
                  ref_pending_cnt < before_val);
        end

        // -- Section G: cfg_force_refresh acts like a tick --
        begin
            logic [2:0] before_val;
            // Drain to a known low count first via repeated acks.
            repeat(8) begin
                if (ref_pending_cnt > 0) begin
                    @(posedge clk); ref_ack=1; @(posedge clk); ref_ack=0; @(posedge clk);
                end
            end
            before_val = ref_pending_cnt;
            @(posedge clk); cfg_force_refresh=1;
            @(posedge clk); cfg_force_refresh=0;
            repeat(2) @(posedge clk);
            check($sformatf("G1: cfg_force_refresh increments pending (before=%0d after=%0d)", before_val, ref_pending_cnt),
                  ref_pending_cnt > before_val);
        end

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    # ════════════════════════════════════════════════════════════
    # BANK_TRACKER — 8 per-bank state machines + shared timing
    # counters + tFAW window. Behavior asserted below is the fixed
    # implementation committed to by bank_tracker_gen.py's
    # generate_rtl() (same status as a spec-derived formula: it's
    # not spec-conditional beyond port widths, so it's the load-
    # bearing contract for any spec). cfg_t*_nCK are runtime inputs
    # -- TB drives small directed constants, not spec-scale ones.
    # ════════════════════════════════════════════════════════════
    def _derive_bank_tracker(self) -> dict:
        p = {}
        p["ROW_BITS"] = self.geo["row_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["NUM_BANKS"] = 2 ** p["BANK_BITS"]
        timing_params = ["tRCD_nCK", "tRP_nCK", "tRAS_nCK", "tRC_nCK", "tRRD_nCK",
                          "tFAW_nCK", "tWTR_nCK", "tWR_nCK", "tRTP_nCK", "tCCD_nCK", "tRFC_nCK"]
        max_val = max(self.dc[tp] for tp in timing_params)
        p["CTR_WIDTH"] = max(1, max_val.bit_length())
        return p

    def generate_bank_tracker_tb(self) -> str:
        p = self._derive_bank_tracker()
        nb, bb, rb = p["NUM_BANKS"], p["BANK_BITS"], p["ROW_BITS"]
        if nb != 8:
            raise ValueError(f"bank_tracker_tb assumes 8 banks, spec derives {nb}")

        # Directed, TB-owned timing constants -- chosen so each check
        # isolates one counter (see tb_generator design notes / handoff doc).
        tRCD, tRP, tRAS, tRC = 3, 2, 5, 6
        tRRD, tFAW, tWTR, tWR, tRTP, tCCD, tRFC = 2, 10, 4, 3, 2, 2, 5
        row_test = 0x1234

        return f"""`timescale 1ns / 1ps
module bank_tracker_tb;
    localparam real CLK_PERIOD = 1.0;
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    localparam NUM_BANKS={nb}, BANK_BITS={bb}, ROW_BITS={rb};

    logic rst_n;
    logic cmd_act_valid, cmd_pre_valid, cmd_pre_all, cmd_rd_valid, cmd_wr_valid, cmd_ref_valid;
    logic [BANK_BITS-1:0] cmd_act_bank, cmd_pre_bank, cmd_rd_bank, cmd_wr_bank;
    logic [ROW_BITS-1:0]  cmd_act_row;

    logic [7:0] cfg_tRCD_nCK, cfg_tRP_nCK, cfg_tRAS_nCK, cfg_tRC_nCK, cfg_tRRD_nCK;
    logic [7:0] cfg_tFAW_nCK, cfg_tWTR_nCK, cfg_tWR_nCK, cfg_tRTP_nCK, cfg_tCCD_nCK, cfg_tRFC_nCK;

    logic [NUM_BANKS-1:0] bank_is_active, bank_act_allowed, bank_rd_allowed, bank_wr_allowed, bank_pre_allowed;
    logic [ROW_BITS-1:0]  bank_open_row [NUM_BANKS];
    logic all_banks_idle, faw_allows_act;

    int pass_count=0, fail_count=0, total_tests=0;

    bank_tracker dut (.*);

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    task automatic clear_cmds();
        cmd_act_valid=0; cmd_act_bank=0; cmd_act_row=0;
        cmd_pre_valid=0; cmd_pre_bank=0; cmd_pre_all=0;
        cmd_rd_valid=0; cmd_rd_bank=0;
        cmd_wr_valid=0; cmd_wr_bank=0;
        cmd_ref_valid=0;
    endtask

    task automatic hw_reset();
        rst_n=0; clear_cmds();
        cfg_tRCD_nCK={tRCD}; cfg_tRP_nCK={tRP}; cfg_tRAS_nCK={tRAS}; cfg_tRC_nCK={tRC};
        cfg_tRRD_nCK={tRRD}; cfg_tFAW_nCK={tFAW}; cfg_tWTR_nCK={tWTR}; cfg_tWR_nCK={tWR};
        cfg_tRTP_nCK={tRTP}; cfg_tCCD_nCK={tCCD}; cfg_tRFC_nCK={tRFC};
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);
    endtask

    task automatic do_act(input [BANK_BITS-1:0] bank, input [ROW_BITS-1:0] row);
        @(posedge clk); cmd_act_valid=1; cmd_act_bank=bank; cmd_act_row=row;
        @(posedge clk); cmd_act_valid=0;
    endtask

    task automatic do_pre(input [BANK_BITS-1:0] bank, input all);
        @(posedge clk); cmd_pre_valid=1; cmd_pre_bank=bank; cmd_pre_all=all;
        @(posedge clk); cmd_pre_valid=0;
    endtask

    task automatic do_rd(input [BANK_BITS-1:0] bank);
        @(posedge clk); cmd_rd_valid=1; cmd_rd_bank=bank;
        @(posedge clk); cmd_rd_valid=0;
    endtask

    task automatic do_wr(input [BANK_BITS-1:0] bank);
        @(posedge clk); cmd_wr_valid=1; cmd_wr_bank=bank;
        @(posedge clk); cmd_wr_valid=0;
    endtask

    task automatic do_ref();
        @(posedge clk); cmd_ref_valid=1;
        @(posedge clk); cmd_ref_valid=0;
    endtask

    initial begin
        $dumpfile("bank_tracker_tb.vcd"); $dumpvars(0, bank_tracker_tb);

        // -- Section A: reset defaults --
        hw_reset();
        check("A1: all_banks_idle at reset", all_banks_idle===1'b1);
        check("A2: bank_is_active all zero at reset", bank_is_active===8'h00);
        check("A3: bank_act_allowed all one at reset", bank_act_allowed===8'hFF);
        check("A4: bank_rd_allowed all zero at reset (no bank active)", bank_rd_allowed===8'h00);
        check("A5: bank_pre_allowed all zero at reset (no bank active)", bank_pre_allowed===8'h00);

        // -- Section B: ACT to bank 0 -- state + row + RCD/RAS gating --
        do_act(3'd0, {rb}'h{row_test:X});
        check("B1: bank_is_active[0] set after ACT", bank_is_active[0]===1'b1);
        check("B2: bank_open_row[0] captures row", bank_open_row[0]==={rb}'h{row_test:X});
        check("B3: all_banks_idle clears", all_banks_idle===1'b0);
        check("B4: bank_act_allowed[0] clears (state ACTIVE)", bank_act_allowed[0]===1'b0);
        check("B5: bank_rd_allowed[0] blocked (tRCD not elapsed)", bank_rd_allowed[0]===1'b0);
        check("B6: bank_pre_allowed[0] blocked (tRAS not elapsed)", bank_pre_allowed[0]===1'b0);

        // -- Section C: tRCD elapses -> RD/WR allowed --
        repeat({tRCD}) @(posedge clk);
        check($sformatf("C1: bank_rd_allowed[0] after tRCD=%0d", {tRCD}), bank_rd_allowed[0]===1'b1);
        check($sformatf("C2: bank_wr_allowed[0] after tRCD=%0d", {tRCD}), bank_wr_allowed[0]===1'b1);

        // -- Section D: tRAS elapses -> PRE allowed --
        repeat({tRAS} - {tRCD}) @(posedge clk);
        check($sformatf("D1: bank_pre_allowed[0] after tRAS=%0d", {tRAS}), bank_pre_allowed[0]===1'b1);

        // -- Section E: PRE -> tRP gates re-ACT --
        do_pre(3'd0, 1'b0);
        check("E1: bank_is_active[0] clears after PRE", bank_is_active[0]===1'b0);
        check("E2: all_banks_idle after PRE (only bank active)", all_banks_idle===1'b1);
        check("E3: bank_act_allowed[0] blocked (tRP not elapsed)", bank_act_allowed[0]===1'b0);
        repeat({tRP}) @(posedge clk);
        check($sformatf("E4: bank_act_allowed[0] after tRP=%0d", {tRP}), bank_act_allowed[0]===1'b1);

        // -- Section F: tRRD shared gate across banks --
        hw_reset();
        do_act(3'd0, 16'h0);
        check("F1: bank_act_allowed[3] blocked right after ACT (tRRD)", bank_act_allowed[3]===1'b0);
        repeat({tRRD}) @(posedge clk);
        check($sformatf("F2: bank_act_allowed[3] after tRRD=%0d", {tRRD}), bank_act_allowed[3]===1'b1);

        // -- Section G: tFAW window (4-ACT burst blocks a 5th) --
        hw_reset();
        do_act(3'd0, 16'h0);
        do_act(3'd1, 16'h0);
        do_act(3'd2, 16'h0);
        check("G1: faw_allows_act still high after 3 ACTs", faw_allows_act===1'b1);
        do_act(3'd3, 16'h0);
        check("G2: faw_allows_act low right after 4th ACT in window", faw_allows_act===1'b0);
        // Each do_act() spans 2 edges (assert, then deassert-on-next-edge),
        // so 3 subsequent ACTs after the 1st span 6 edges, not 3 -- the
        // oldest slot (loaded on the 1st ACT) must still be counting down
        // past that point for this to actually exercise the 4-deep window.
        repeat({tFAW} - 6) @(posedge clk);
        check($sformatf("G3: faw_allows_act recovers ~tFAW=%0d cycles after 1st ACT", {tFAW}), faw_allows_act===1'b1);

        // -- Section H: tCCD shared gate (RD blocks WR to any bank) --
        hw_reset();
        do_act(3'd0, 16'h0);
        repeat({tRCD}) @(posedge clk);  // clear RCD so bank0 is genuinely RD/WR-eligible
        do_rd(3'd0);
        check("H1: bank_wr_allowed[0] blocked right after RD (tCCD)", bank_wr_allowed[0]===1'b0);
        repeat({tCCD}) @(posedge clk);
        check($sformatf("H2: bank_wr_allowed[0] after tCCD=%0d", {tCCD}), bank_wr_allowed[0]===1'b1);

        // -- Section I: tWTR gates PRE after a WR --
        hw_reset();
        do_act(3'd0, 16'h0);
        repeat({tRAS}) @(posedge clk);  // let RAS clear first so WTR is the sole limiter below
        do_wr(3'd0);
        check("I1: bank_pre_allowed[0] blocked right after WR (tWTR)", bank_pre_allowed[0]===1'b0);
        repeat({tWTR}) @(posedge clk);
        check($sformatf("I2: bank_pre_allowed[0] after tWTR=%0d", {tWTR}), bank_pre_allowed[0]===1'b1);

        // -- Section J: REF forces all-idle + tRFC gate --
        hw_reset();
        do_act(3'd0, 16'h0);
        do_act(3'd1, 16'h1);
        do_ref();
        check("J1: bank_is_active all clear after REF", bank_is_active===8'h00);
        check("J2: all_banks_idle after REF", all_banks_idle===1'b1);
        check("J3: bank_act_allowed[0] blocked right after REF (tRFC)", bank_act_allowed[0]===1'b0);
        repeat({tRFC}) @(posedge clk);
        check($sformatf("J4: bank_act_allowed[0] after tRFC=%0d", {tRFC}), bank_act_allowed[0]===1'b1);

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    # ════════════════════════════════════════════════════════════
    # Write all Phase 2 testbenches to a directory
    # ════════════════════════════════════════════════════════════
    def write_phase2(self, output_dir: str) -> list:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        written = []
        for filename, gen_fn in [
            ("addr_decoder_tb.sv", self.generate_addr_decoder_tb),
            ("calibration_tb.sv", self.generate_calibration_tb),
            ("refresh_ctrl_tb.sv", self.generate_refresh_ctrl_tb),
            ("bank_tracker_tb.sv", self.generate_bank_tracker_tb),
        ]:
            path = out / filename
            path.write_text(gen_fn())
            written.append(str(path))
        return written


if __name__ == "__main__":
    spec = input("Spec JSON path: ").strip()
    out = input("Output dir for testbenches: ").strip() or "./tb_output"
    tbg = TestbenchGenerator(spec)
    for path in tbg.write_phase2(out):
        print(f"  wrote {path}")
