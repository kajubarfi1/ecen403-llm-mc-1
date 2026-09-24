`timescale 1ns / 1ps
module refresh_ctrl_tb;
    localparam real CLK_PERIOD = 5.0;
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
        cfg_tREFI_nCK=8; cfg_max_postpone=4;
        cfg_urgent_threshold=2; cfg_ref_priority=1;
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
            while (ref_pending_cnt < 2 && guard < 500) begin
                wait_for_pending_change(200, changed);
                guard++;
            end
            check($sformatf("C1: ref_urgent asserts at pending>=%0d (got %0d)", 2, ref_pending_cnt),
                  ref_urgent===1'b1);
        end

        // -- Section D: saturation at cfg_max_postpone --
        begin
            logic changed;
            int guard;
            guard = 0;
            while (ref_pending_cnt < 4 && guard < 500) begin
                wait_for_pending_change(200, changed);
                guard++;
            end
            repeat(8 * 3) @(posedge clk);  // let several more ticks try to fire
            check($sformatf("D1: ref_pending_cnt saturates at %0d (got %0d)", 4, ref_pending_cnt),
                  ref_pending_cnt === 4);
        end

        // -- Section E: ref_starve_flag pulses when saturated --
        begin
            logic seen;
            int cyc;
            seen = 0;
            for (cyc = 0; cyc < 8 * 2; cyc++) begin
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
