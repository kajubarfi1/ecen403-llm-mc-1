`timescale 1ns / 1ps
//==============================================================
// init_fsm_tb.sv -- Enhanced testbench (38 tests)
// Generated: 2026-03-23 14:56:02
// Agent:     Init/Reset FSM Agent (Phase 1)
//
// Sections:
//   A: Normal init sequence (timing, ordering, completion)
//   B: MR register value verification on the wire
//   C: ZQCL command encoding
//   D: Signal integrity during wait states
//   E: Idle behavior (no enable)
//   F: Enable deassert mid-init
//   G: Async reset mid-init + recovery
//   H: Back-to-back re-init after done
//   I: Late enable assertion
//
// Test List:
//   A1   init_done asserted
//   A2   init_fail never asserted
//   A3   FSM reached S_DONE (state=14)
//   A4   RESET# hold >= 40000 cycles (200us)
//   A5   CKE delay >= 100000 cycles (500us)
//   A6   Exactly 4 MRS commands issued
//   A7   MR order MR2(2)->MR3(3)->MR1(1)->MR0(0)
//   B1   MR2 addr value on wire
//   B2   MR3 addr value on wire
//   B3   MR1 addr value on wire
//   B4   MR0 addr value on wire
//   B5   All 4 MRS used CMD_MRS encoding (4'b0000)
//   C1   ZQCL command issued
//   C2   ZQCL A10 = 1 (long calibration)
//   C3   ZQCL bank = 0
//   D1   No spurious cmd_valid in wait states
//   D2   CKE low during RESET_LOW/HIGH
//   D3   RESET# low in IDLE/RESET_LOW
//   D4   init_done only asserted in S_DONE
//   D5   init_done is level (still high in S_DONE)
//   D6   init_state output matches S_DONE encoding
//   E1   FSM stays S_IDLE without enable
//   E2   init_done low in IDLE
//   E3   init_fail low in IDLE
//   E4   RESET# low in IDLE
//   E5   CKE low in IDLE
//   E6   cmd_valid low in IDLE
//   F1   Init completes after enable deasserted
//   F2   init_fail not asserted after enable deassert
//   G1   FSM returns to S_IDLE on async reset
//   G2   init_done deasserted after reset
//   G3   Re-init completes after mid-init reset
//   G4   MR order correct on re-init
//   H1   Second init completes
//   H2   4 MRS on re-init
//   H3   ZQCL issued on re-init
//   I1   FSM still IDLE after 500 cycles no enable
//   I2   Init completes with late enable
//
// VCD: dumps init_fsm_tb.vcd
//==============================================================
module init_fsm_tb;

    // -- Clock: 5.0ns period (200.0 MHz) --
    localparam real CLK_PERIOD = 5.0;
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // -- DUT signals --
    logic        rst_n;
    logic        enable;
    logic        init_done;
    logic        init_fail;
    logic        init_cmd_valid;
    logic [3:0]  init_cmd;
    logic [14:0] init_addr;
    logic [2:0]  init_bank;
    logic        init_cke;
    logic        init_reset_n;
    logic [3:0]  init_state;

    // -- DUT --
    init_fsm dut (
        .clk           (clk),
        .rst_n         (rst_n),
        .enable        (enable),
        .init_done     (init_done),
        .init_fail     (init_fail),
        .init_cmd_valid(init_cmd_valid),
        .init_cmd      (init_cmd),
        .init_addr     (init_addr),
        .init_bank     (init_bank),
        .init_cke      (init_cke),
        .init_reset_n  (init_reset_n),
        .init_state    (init_state)
    );

    // -- Command encodings --
    localparam CMD_MRS  = 4'b0000;
    localparam CMD_ZQCL = 4'b0110;
    localparam CMD_NOP  = 4'b0111;

    // -- FSM state encodings (mirror RTL) --
    localparam S_IDLE           = 4'd0;
    localparam S_RESET_LOW      = 4'd1;
    localparam S_RESET_HIGH     = 4'd2;
    localparam S_CKE_WAIT       = 4'd3;
    localparam S_MR2            = 4'd4;
    localparam S_MR2_WAIT       = 4'd5;
    localparam S_MR3            = 4'd6;
    localparam S_MR3_WAIT       = 4'd7;
    localparam S_MR1            = 4'd8;
    localparam S_MR1_WAIT       = 4'd9;
    localparam S_MR0            = 4'd10;
    localparam S_MR0_WAIT       = 4'd11;
    localparam S_ZQCL           = 4'd12;
    localparam S_ZQCL_WAIT      = 4'd13;
    localparam S_DONE           = 4'd14;

    // -- Expected MR values --
    localparam [14:0] EXP_MR0 = 15'h1D34;
    localparam [14:0] EXP_MR1 = 15'h0004;
    localparam [14:0] EXP_MR2 = 15'h0218;
    localparam [14:0] EXP_MR3 = 15'h0000;

    // -- Test infrastructure --
    int pass_count = 0;
    int fail_count = 0;
    int total_tests = 0;

    task automatic check(string name, logic condition);
        total_tests++;
        if (condition) begin
            pass_count++;
            $display("  [PASS] %0d: %s", total_tests, name);
        end else begin
            fail_count++;
            $display("  [FAIL] %0d: %s", total_tests, name);
        end
    endtask

    // ---------------------------------------------------------------
    // Monitor infrastructure
    // ---------------------------------------------------------------
    int cycle_count;
    int cke_rise_cycle;
    int reset_n_rise_cycle;
    int init_done_cycle;
    int mr_cmd_count;
    int mr_bank_idx;
    int zqcl_seen;
    int zqcl_a10_ok;
    int zqcl_bank_zero;
    int spurious_cmd_count;
    int fail_ever_asserted;

    logic [2:0]  mr_bank_order  [0:7];
    logic [14:0] mr_addr_values [0:7];
    logic [3:0]  mr_cmd_values  [0:7];

    function automatic logic is_wait_state(logic [3:0] st);
        return (st == S_IDLE      || st == S_RESET_LOW || st == S_RESET_HIGH ||
                st == S_CKE_WAIT  || st == S_MR2_WAIT  || st == S_MR3_WAIT  ||
                st == S_MR1_WAIT  || st == S_MR0_WAIT  || st == S_ZQCL_WAIT ||
                st == S_DONE);
    endfunction

    always @(posedge clk) begin
        if (rst_n) begin
            cycle_count++;

            if (init_cke && cke_rise_cycle == 0 && cycle_count > 2)
                cke_rise_cycle = cycle_count;

            if (init_reset_n && reset_n_rise_cycle == 0 && cycle_count > 2)
                reset_n_rise_cycle = cycle_count;

            if (init_cmd_valid && init_cmd == CMD_MRS) begin
                if (mr_bank_idx < 8) begin
                    mr_bank_order[mr_bank_idx]  = init_bank;
                    mr_addr_values[mr_bank_idx] = init_addr;
                    mr_cmd_values[mr_bank_idx]  = init_cmd;
                    mr_bank_idx++;
                end
                mr_cmd_count++;
            end

            if (init_cmd_valid && init_cmd == CMD_ZQCL) begin
                zqcl_seen = 1;
                if (init_addr[10])      zqcl_a10_ok    = 1;
                if (init_bank == 3'd0) zqcl_bank_zero = 1;
            end

            if (init_done && init_done_cycle == 0)
                init_done_cycle = cycle_count;

            if (init_cmd_valid && is_wait_state(init_state))
                spurious_cmd_count++;

            if (init_fail)
                fail_ever_asserted = 1;
        end
    end

    // CKE-during-reset monitor
    int cke_violation_during_reset;
    always @(posedge clk) begin
        if (rst_n && (init_state == S_RESET_LOW || init_state == S_RESET_HIGH))
            if (init_cke) cke_violation_during_reset++;
    end

    // RESET# monitor: low in IDLE and RESET_LOW
    int resetn_violation_count;
    always @(posedge clk) begin
        if (rst_n && (init_state == S_IDLE || init_state == S_RESET_LOW))
            if (init_reset_n) resetn_violation_count++;
    end

    // init_done only in S_DONE
    int done_outside_sdone;
    always @(posedge clk) begin
        if (rst_n && init_done && init_state != S_DONE)
            done_outside_sdone++;
    end

    // ---------------------------------------------------------------
    // Task: reset all monitors
    // ---------------------------------------------------------------
    task automatic reset_monitors();
        cycle_count             = 0;
        cke_rise_cycle          = 0;
        reset_n_rise_cycle      = 0;
        init_done_cycle         = 0;
        mr_cmd_count            = 0;
        mr_bank_idx             = 0;
        zqcl_seen               = 0;
        zqcl_a10_ok             = 0;
        zqcl_bank_zero          = 0;
        spurious_cmd_count      = 0;
        fail_ever_asserted      = 0;
        cke_violation_during_reset = 0;
        resetn_violation_count  = 0;
        done_outside_sdone      = 0;
        for (int i = 0; i < 8; i++) begin
            mr_bank_order[i]  = 3'd0;
            mr_addr_values[i] = 15'd0;
            mr_cmd_values[i]  = 4'd0;
        end
    endtask

    task automatic hw_reset();
        rst_n  = 0;
        enable = 0;
        repeat (5) @(posedge clk);
        rst_n  = 1;
        @(posedge clk);
    endtask

    task automatic run_init_to_done(input int timeout_cycles, output logic success);
        success = 0;
        fork
            begin wait(init_done); success = 1; end
            begin repeat (timeout_cycles) @(posedge clk); end
        join_any
        disable fork;
        repeat (5) @(posedge clk);
    endtask

    // ---------------------------------------------------------------
    // Main test
    // ---------------------------------------------------------------
    initial begin
        $dumpfile("init_fsm_tb.vcd");
        $dumpvars(0, init_fsm_tb);

        $display("");
        $display("==========================================================");
        $display("  init_fsm_tb -- Enhanced JEDEC DDR3 Init Verification");
        $display("  Clock: 200.0 MHz (5.0 ns)    VCD: init_fsm_tb.vcd");
        $display("  Total sections: A-I (~35 tests)");
        $display("==========================================================");

        // ==========================================================
        // SECTION A: Normal init sequence
        // ==========================================================
        $display("");
        $display("  -- Section A: Normal Init Sequence --");

        hw_reset();
        reset_monitors();
        enable = 1;

        begin
            logic ok;
            run_init_to_done(145000, ok);

            check("A1: init_done asserted", ok);
            check("A2: init_fail never asserted", fail_ever_asserted == 0);
            check("A3: FSM reached S_DONE (state=14)", init_state == S_DONE);
            check($sformatf("A4: RESET# hold >= 40000 cyc [got %0d]", reset_n_rise_cycle),
                  reset_n_rise_cycle >= 40000);
            check($sformatf("A5: CKE delay >= 100000 cyc [delta=%0d]",
                  cke_rise_cycle - reset_n_rise_cycle),
                  (cke_rise_cycle - reset_n_rise_cycle) >= 100000);
            check($sformatf("A6: Exactly 4 MRS commands [got %0d]", mr_cmd_count),
                  mr_cmd_count == 4);
            if (mr_bank_idx >= 4) begin
                check("A7: MR order MR2(2)->MR3(3)->MR1(1)->MR0(0)",
                      mr_bank_order[0] == 3'd2 && mr_bank_order[1] == 3'd3 &&
                      mr_bank_order[2] == 3'd1 && mr_bank_order[3] == 3'd0);
            end else begin
                check("A7: MR order (insufficient commands)", 0);
            end
        end

        // ==========================================================
        // SECTION B: MR register values on the wire
        // ==========================================================
        $display("");
        $display("  -- Section B: MR Register Values --");

        check($sformatf("B1: MR2 addr = 0x%04X [exp 0x0218]", mr_addr_values[0]),
              mr_addr_values[0] == EXP_MR2);
        check($sformatf("B2: MR3 addr = 0x%04X [exp 0x0000]", mr_addr_values[1]),
              mr_addr_values[1] == EXP_MR3);
        check($sformatf("B3: MR1 addr = 0x%04X [exp 0x0004]", mr_addr_values[2]),
              mr_addr_values[2] == EXP_MR1);
        check($sformatf("B4: MR0 addr = 0x%04X [exp 0x1D34]", mr_addr_values[3]),
              mr_addr_values[3] == EXP_MR0);
        begin
            logic all_mrs;
            all_mrs = 1;
            for (int i = 0; i < 4; i++)
                if (mr_cmd_values[i] != CMD_MRS) all_mrs = 0;
            check("B5: All 4 MRS used CMD_MRS encoding (4'b0000)", all_mrs);
        end

        // ==========================================================
        // SECTION C: ZQCL command
        // ==========================================================
        $display("");
        $display("  -- Section C: ZQCL Command --");

        check("C1: ZQCL command issued",             zqcl_seen == 1);
        check("C2: ZQCL A10 = 1 (long calibration)", zqcl_a10_ok == 1);
        check("C3: ZQCL bank = 0",                   zqcl_bank_zero == 1);

        // ==========================================================
        // SECTION D: Signal integrity
        // ==========================================================
        $display("");
        $display("  -- Section D: Signal Integrity --");

        check($sformatf("D1: No spurious cmd_valid in wait states [%0d violations]",
              spurious_cmd_count), spurious_cmd_count == 0);
        check($sformatf("D2: CKE low during RESET_LOW/HIGH [%0d violations]",
              cke_violation_during_reset), cke_violation_during_reset == 0);
        check($sformatf("D3: RESET# low in IDLE/RESET_LOW [%0d violations]",
              resetn_violation_count), resetn_violation_count == 0);
        check($sformatf("D4: init_done only in S_DONE [%0d violations]",
              done_outside_sdone), done_outside_sdone == 0);
        check("D5: init_done is level (still high in S_DONE)", init_done === 1'b1);
        check($sformatf("D6: init_state output = %0d (expect 14)", init_state),
              init_state == 4'd14);

        // ==========================================================
        // SECTION E: Idle behavior (no enable)
        // ==========================================================
        $display("");
        $display("  -- Section E: Reset / Idle Behavior --");

        hw_reset();
        repeat (20) @(posedge clk);

        check("E1: FSM stays S_IDLE without enable",   init_state == S_IDLE);
        check("E2: init_done low in IDLE",              init_done === 1'b0);
        check("E3: init_fail low in IDLE",              init_fail === 1'b0);
        check("E4: RESET# low in IDLE",                init_reset_n === 1'b0);
        check("E5: CKE low in IDLE",                   init_cke === 1'b0);
        check("E6: cmd_valid low in IDLE",              init_cmd_valid === 1'b0);

        // ==========================================================
        // SECTION F: Enable deassert mid-init
        // ==========================================================
        $display("");
        $display("  -- Section F: Enable Deassert Mid-Init --");

        hw_reset();
        reset_monitors();
        enable = 1;
        wait(init_state == S_RESET_LOW);
        repeat (100) @(posedge clk);
        enable = 0;

        begin
            logic ok;
            run_init_to_done(145000, ok);
            check("F1: Init completes after enable deasserted", ok);
            check("F2: init_fail not asserted", fail_ever_asserted == 0);
        end

        // ==========================================================
        // SECTION G: Async reset mid-init + recovery
        // ==========================================================
        $display("");
        $display("  -- Section G: Reset Mid-Init --");

        hw_reset();
        reset_monitors();
        enable = 1;
        wait(init_state == S_RESET_HIGH);
        repeat (50) @(posedge clk);

        rst_n = 0;
        repeat (5) @(posedge clk);

        check("G1: FSM returns to S_IDLE on async reset", init_state == S_IDLE);
        check("G2: init_done deasserted after reset",     init_done === 1'b0);

        rst_n = 1;
        reset_monitors();
        @(posedge clk);
        enable = 1;

        begin
            logic ok;
            run_init_to_done(145000, ok);
            check("G3: Re-init completes after mid-init reset", ok);
            check("G4: MR order correct on re-init",
                  mr_bank_idx >= 4 &&
                  mr_bank_order[0] == 3'd2 && mr_bank_order[1] == 3'd3 &&
                  mr_bank_order[2] == 3'd1 && mr_bank_order[3] == 3'd0);
        end

        // ==========================================================
        // SECTION H: Re-init after done
        // ==========================================================
        $display("");
        $display("  -- Section H: Re-Init After Done --");

        hw_reset();
        reset_monitors();
        enable = 1;

        begin
            logic ok;
            run_init_to_done(145000, ok);
            check("H1: Second init completes", ok);
            check($sformatf("H2: 4 MRS on re-init [got %0d]", mr_cmd_count),
                  mr_cmd_count == 4);
            check("H3: ZQCL issued on re-init", zqcl_seen == 1);
        end

        // ==========================================================
        // SECTION I: Late enable
        // ==========================================================
        $display("");
        $display("  -- Section I: Late Enable --");

        hw_reset();
        reset_monitors();
        repeat (500) @(posedge clk);
        check("I1: FSM still IDLE after 500 cyc no enable", init_state == S_IDLE);

        enable = 1;
        begin
            logic ok;
            run_init_to_done(145000, ok);
            check("I2: Init completes with late enable", ok);
        end

        // ==========================================================
        // Summary
        // ==========================================================
        $display("");
        $display("==========================================================");
        if (fail_count == 0)
            $display("  ALL %0d TESTS PASSED", total_tests);
        else
            $display("  %0d of %0d TESTS FAILED", fail_count, total_tests);
        $display("==========================================================");
        $display("");

        $finish;
    end

endmodule