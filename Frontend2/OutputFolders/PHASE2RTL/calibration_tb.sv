`timescale 1ns / 1ps
module calibration_tb;
    localparam real CLK_PERIOD = 5.0;
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    localparam ZQCS_CTR_W = 17;
    localparam ZQCS_WAIT  = 128000;
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
