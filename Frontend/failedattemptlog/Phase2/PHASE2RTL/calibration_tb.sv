`timescale 1ns/1ps
module calibration_tb;
    localparam ZQCS_CTR_W=6,ZQCS_WAIT=20,TZQCS_CYC=4;
    logic clk=0; always #2.5 clk=~clk;
    logic init_done,rst_n,cal_done,cal_fail,zqcs_req,zqcs_ack;
    calibration #(.ZQCS_CTR_W(ZQCS_CTR_W),.ZQCS_WAIT(ZQCS_WAIT),.TZQCS_CYC(TZQCS_CYC)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c); test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s",test_num,n); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask
    task automatic ack_zqcs(); @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); endtask
    initial begin
        $display("\n== calibration_tb ==\n");
        // --- Reset state ---
        rst_n=0;init_done=0;zqcs_ack=0;
        wc(3); check("Rst done=0",cal_done===0); check("Rst fail=0",cal_fail===0); check("Rst zqcs=0",zqcs_req===0);
        @(posedge clk);rst_n=1;wc(2); check("Post done=0",cal_done===0); check("Post zqcs=0",zqcs_req===0);
        // --- cal_done latches high after init_done ---
        @(posedge clk);init_done=1;
        wc(2); check("cal_done after init",cal_done===1);
        wc(5); check("Stays high",cal_done===1); check("Fail=0",cal_fail===0); check("Fail=0 always",cal_fail===0);
        // --- Sticky: dropping init_done keeps cal_done high ---
        init_done=0;wc(3); check("Sticky after drop",cal_done===1); check("Fail off",cal_fail===0);
        init_done=1;wc(3); check("Sticky re-assert",cal_done===1); check("Fail re",cal_fail===0);
        // --- Reset clears ---
        rst_n=0;wc(2); check("Rst clears cal",cal_done===0); check("Fail post rst",cal_fail===0);
        rst_n=1;init_done=0;wc(2);
        @(posedge clk);init_done=1;wc(3); check("Re-cal after rst",cal_done===1);
        // --- 1st ZQCS cycle ---
        wc(ZQCS_WAIT+3); check("ZQCS fires",zqcs_req===1);
        wc(3); check("ZQCS stays",zqcs_req===1);
        ack_zqcs(); check("ZQCS clr after ack",zqcs_req===0);
        wc(3); check("ZQCS stays low post-ack",zqcs_req===0);
        // --- 2nd ZQCS cycle (fresh reset to decouple counter state) ---
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);
        @(posedge clk);init_done=1;wc(2); check("Re-cal 2",cal_done===1);
        wc(ZQCS_WAIT+3); check("2nd ZQCS fires",zqcs_req===1);
        ack_zqcs(); check("2nd ack clears",zqcs_req===0);
        // --- init_done drop does not clear cal_done ---
        init_done=0;wc(5); check("cal persists on drop",cal_done===1);
        // --- Reset again, confirm clear ---
        rst_n=0;wc(2); check("Rst clr 2",cal_done===0); rst_n=1;wc(2);
        // --- init_done toggle still latches ---
        init_done=1;@(posedge clk);init_done=0;@(posedge clk);init_done=1;wc(3); check("Toggle latches",cal_done===1);
        // --- 1-cycle pulse latches ---
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);
        @(posedge clk);init_done=1;@(posedge clk);init_done=0;wc(3); check("1cyc pulse latches",cal_done===1);
        // --- Pre-cal has no ZQCS ---
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(5); check("No zqcs pre-cal",zqcs_req===0);
        // --- Final integration check ---
        @(posedge clk);init_done=1;wc(3); check("Final cal",cal_done===1);
        wc(ZQCS_WAIT+3); check("Final zqcs",zqcs_req===1);
        $display("\n== %0d/%0d passed ==\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #1_000_000; $display("TIMEOUT"); $finish; end
endmodule
