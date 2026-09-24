`timescale 1ns / 1ps
module bank_tracker_tb;
    localparam real CLK_PERIOD = 1.0;
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    localparam NUM_BANKS=8, BANK_BITS=3, ROW_BITS=15;

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
        cfg_tRCD_nCK=3; cfg_tRP_nCK=2; cfg_tRAS_nCK=5; cfg_tRC_nCK=6;
        cfg_tRRD_nCK=2; cfg_tFAW_nCK=10; cfg_tWTR_nCK=4; cfg_tWR_nCK=3;
        cfg_tRTP_nCK=2; cfg_tCCD_nCK=2; cfg_tRFC_nCK=5;
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
        do_act(3'd0, 15'h1234);
        check("B1: bank_is_active[0] set after ACT", bank_is_active[0]===1'b1);
        check("B2: bank_open_row[0] captures row", bank_open_row[0]===15'h1234);
        check("B3: all_banks_idle clears", all_banks_idle===1'b0);
        check("B4: bank_act_allowed[0] clears (state ACTIVE)", bank_act_allowed[0]===1'b0);
        check("B5: bank_rd_allowed[0] blocked (tRCD not elapsed)", bank_rd_allowed[0]===1'b0);
        check("B6: bank_pre_allowed[0] blocked (tRAS not elapsed)", bank_pre_allowed[0]===1'b0);

        // -- Section C: tRCD elapses -> RD/WR allowed --
        repeat(3) @(posedge clk);
        check($sformatf("C1: bank_rd_allowed[0] after tRCD=%0d", 3), bank_rd_allowed[0]===1'b1);
        check($sformatf("C2: bank_wr_allowed[0] after tRCD=%0d", 3), bank_wr_allowed[0]===1'b1);

        // -- Section D: tRAS elapses -> PRE allowed --
        repeat(5 - 3) @(posedge clk);
        check($sformatf("D1: bank_pre_allowed[0] after tRAS=%0d", 5), bank_pre_allowed[0]===1'b1);

        // -- Section E: PRE -> tRP gates re-ACT --
        do_pre(3'd0, 1'b0);
        check("E1: bank_is_active[0] clears after PRE", bank_is_active[0]===1'b0);
        check("E2: all_banks_idle after PRE (only bank active)", all_banks_idle===1'b1);
        check("E3: bank_act_allowed[0] blocked (tRP not elapsed)", bank_act_allowed[0]===1'b0);
        repeat(2) @(posedge clk);
        check($sformatf("E4: bank_act_allowed[0] after tRP=%0d", 2), bank_act_allowed[0]===1'b1);

        // -- Section F: tRRD shared gate across banks --
        hw_reset();
        do_act(3'd0, 16'h0);
        check("F1: bank_act_allowed[3] blocked right after ACT (tRRD)", bank_act_allowed[3]===1'b0);
        repeat(2) @(posedge clk);
        check($sformatf("F2: bank_act_allowed[3] after tRRD=%0d", 2), bank_act_allowed[3]===1'b1);

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
        repeat(10 - 6) @(posedge clk);
        check($sformatf("G3: faw_allows_act recovers ~tFAW=%0d cycles after 1st ACT", 10), faw_allows_act===1'b1);

        // -- Section H: tCCD shared gate (RD blocks WR to any bank) --
        hw_reset();
        do_act(3'd0, 16'h0);
        repeat(3) @(posedge clk);  // clear RCD so bank0 is genuinely RD/WR-eligible
        do_rd(3'd0);
        check("H1: bank_wr_allowed[0] blocked right after RD (tCCD)", bank_wr_allowed[0]===1'b0);
        repeat(2) @(posedge clk);
        check($sformatf("H2: bank_wr_allowed[0] after tCCD=%0d", 2), bank_wr_allowed[0]===1'b1);

        // -- Section I: tWTR gates PRE after a WR --
        hw_reset();
        do_act(3'd0, 16'h0);
        repeat(5) @(posedge clk);  // let RAS clear first so WTR is the sole limiter below
        do_wr(3'd0);
        check("I1: bank_pre_allowed[0] blocked right after WR (tWTR)", bank_pre_allowed[0]===1'b0);
        repeat(4) @(posedge clk);
        check($sformatf("I2: bank_pre_allowed[0] after tWTR=%0d", 4), bank_pre_allowed[0]===1'b1);

        // -- Section J: REF forces all-idle + tRFC gate --
        hw_reset();
        do_act(3'd0, 16'h0);
        do_act(3'd1, 16'h1);
        do_ref();
        check("J1: bank_is_active all clear after REF", bank_is_active===8'h00);
        check("J2: all_banks_idle after REF", all_banks_idle===1'b1);
        check("J3: bank_act_allowed[0] blocked right after REF (tRFC)", bank_act_allowed[0]===1'b0);
        repeat(5) @(posedge clk);
        check($sformatf("J4: bank_act_allowed[0] after tRFC=%0d", 5), bank_act_allowed[0]===1'b1);

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
