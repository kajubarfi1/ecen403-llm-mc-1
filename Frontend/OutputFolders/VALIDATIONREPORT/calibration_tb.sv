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
    initial begin
        $display("\n== calibration_tb ==\n");
        rst_n=0;init_done=0;zqcs_ack=0;
        wc(3); check("Rst done=0",cal_done===0); check("Rst fail=0",cal_fail===0); check("Rst zqcs=0",zqcs_req===0);
        @(posedge clk);rst_n=1;wc(2); check("Post done=0",cal_done===0); check("Post zqcs=0",zqcs_req===0);
        @(posedge clk);init_done=1;@(posedge clk); check("Not same cyc",cal_done===0);
        @(posedge clk); check("1cyc after",cal_done===1);
        wc(5); check("Stays",cal_done===1); check("Fail=0",cal_fail===0); check("Fail=0 always",cal_fail===0);
        init_done=0;wc(3); check("Fail off",cal_fail===0);
        init_done=1;wc(3); check("Fail re",cal_fail===0);
        rst_n=0;wc(2);rst_n=1;wc(2); check("Fail post rst",cal_fail===0);
        init_done=0;wc(2);@(posedge clk);init_done=1;wc(3); check("Re-cal",cal_done===1);
        wc(1); check("ZQCS fires",zqcs_req===1);
        wc(5); check("ZQCS stays",zqcs_req===1);
        @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); check("ZQCS clr",zqcs_req===0);
        wc(ZQCS_WAIT+2); check("ZQCS re",zqcs_req===1);
        @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); check("2nd ack",zqcs_req===0);
        zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); check("Spurious",zqcs_req===0);
        wc(ZQCS_WAIT+2); check("3rd zqcs",zqcs_req===1);
        @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;wc(2); check("3rd ack",zqcs_req===0);
        wc(ZQCS_WAIT+2); zqcs_ack=1;wc(3);zqcs_ack=0;@(posedge clk); check("Multi ack",zqcs_req===0);
        init_done=0;wc(5); check("Persists",cal_done===1);
        rst_n=0;wc(2); check("Rst clr",cal_done===0); rst_n=1;wc(2);
        init_done=1;@(posedge clk);init_done=0;@(posedge clk);init_done=1;wc(3); check("Toggle",cal_done===1);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);
        @(posedge clk);init_done=1;@(posedge clk);init_done=0;wc(3); check("1cyc pulse",cal_done===1);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(5); check("No zqcs pre",zqcs_req===0);
        @(posedge clk);init_done=1;wc(3); check("Final cal",cal_done===1);
        wc(2); check("Final zqcs",zqcs_req===1);
        $display("\n== %0d/%0d passed ==\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #1_000_000; $display("TIMEOUT"); $finish; end
endmodule
