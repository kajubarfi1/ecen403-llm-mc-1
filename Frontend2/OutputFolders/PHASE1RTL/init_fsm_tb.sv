`timescale 1ns / 1ps
module init_fsm_tb;
    localparam real CLK_PERIOD = 5.0;
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    logic rst_n, enable, init_done, init_fail, init_cmd_valid;
    logic [3:0] init_cmd;
    logic [14:0] init_addr;
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
            begin repeat(140662) @(posedge clk); $display("[FAIL] TIMEOUT"); end
        join_any
        disable fork;
        repeat(10) @(posedge clk);

        check($sformatf("Reset hold >= 40000 cyc (got %0d)", resetn_rise), resetn_rise>=40000);
        check($sformatf("CKE delay >= 100000 cyc"), (cke_rise-resetn_rise)>=100000 || cke_rise>=100000);
        check("init_done asserted", init_done===1'b1);
        check("init_fail not asserted", init_fail===1'b0);
        check($sformatf("4 MRS commands (got %0d)", mr_cmd_count), mr_cmd_count==4);
        if (mr_bank_order.size()>=4)
            check("MR order 2->3->1->0", mr_bank_order[0]==3'd2 && mr_bank_order[1]==3'd3 && mr_bank_order[2]==3'd1 && mr_bank_order[3]==3'd0);
        else check("MR order (insufficient cmds)", 0);
        check("Sequence completed", init_done===1'b1);

        // Spec-derived MR encoding checks -- computed independently of the
        // RTL (see _encode_mr0..3), not extracted from it.
        check($sformatf("MR0 encoding matches spec (exp 15'h1D34)"), dut.MR0_VAL === 15'h1D34);
        check($sformatf("MR1 encoding matches spec (exp 15'h0004)"), dut.MR1_VAL === 15'h0004);
        check($sformatf("MR2 encoding matches spec (exp 15'h0218)"), dut.MR2_VAL === 15'h0218);
        check($sformatf("MR3 encoding matches spec (exp 15'h0000)"), dut.MR3_VAL === 15'h0000);

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
