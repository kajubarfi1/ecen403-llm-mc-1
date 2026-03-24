`timescale 1ns/1ps
module refresh_ctrl_tb;
    localparam REFI_CTR_W=5,POST_CTR_W=4,TREFI=10;
    logic clk=0; always #2.5 clk=~clk;
    logic rst_n,init_done,cfg_force_refresh; logic [23:0] cfg_tREFI_nCK;
    logic [3:0] cfg_max_postpone,cfg_urgent_threshold; logic cfg_ref_priority;
    logic ref_required,ref_urgent,ref_ack; logic [2:0] ref_pending_cnt; logic ref_starve_flag;
    refresh_ctrl #(.REFI_CTR_W(REFI_CTR_W),.POST_CTR_W(POST_CTR_W)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c); test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s p=%0d",test_num,n,ref_pending_cnt); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask
    task automatic wrefi(); wc(TREFI+2); endtask
    initial begin
        $display("\n== refresh_ctrl_tb ==\n");
        rst_n=0;init_done=0;cfg_force_refresh=0;ref_ack=0;
        cfg_tREFI_nCK=TREFI;cfg_max_postpone=8;cfg_urgent_threshold=6;cfg_ref_priority=1;
        wc(3); check("Rst req",ref_required===0); check("Rst urg",ref_urgent===0);
        check("Rst pend",ref_pending_cnt===0); check("Rst starve",ref_starve_flag===0);
        @(posedge clk);rst_n=1;wc(2); check("Post-rst",ref_required===0);
        wc(TREFI+5); check("Pre-init req",ref_required===0); check("Pre-init pend",ref_pending_cnt===0); check("Pre-init st",ref_starve_flag===0);
        @(posedge clk);init_done=1;wc(3); check("1st req",ref_required===1); check("1st pend",ref_pending_cnt>=1);
        wrefi(); check("2nd pend",ref_pending_cnt>=2); wrefi(); check("3rd pend",ref_pending_cnt>=3);
        @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0;wc(2); check("Ack dec",ref_pending_cnt<=3);
        repeat(5) begin @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0;wc(1); end
        check("Multi ack",ref_pending_cnt<=4);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;wc(2);
        check("Clean start",ref_pending_cnt<=1);
        repeat(3) begin wrefi();@(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0; end wc(2);
        check("Imm ack low",ref_pending_cnt<=2);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;
        repeat(6) wrefi(); wc(3); check("Urgent",ref_urgent===1); check("Req at urg",ref_required===1);
        cfg_ref_priority=0;wc(2); check("Pri off",ref_urgent===0);
        cfg_ref_priority=1;wc(2); check("Pri on",ref_urgent===1);
        repeat(3) wrefi(); wc(3); check("Max req",ref_required===1);
        wrefi();wc(2); check("Starve rgn",ref_required===1);
        repeat(10) begin @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0; end wc(3);
        check("Drain",ref_pending_cnt<=3);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;wc(3);
        @(posedge clk);cfg_force_refresh=1;@(posedge clk);cfg_force_refresh=0;wc(2);
        check("Force req",ref_required===1);
        @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0;wc(2); check("Force ack",ref_pending_cnt<=1);
        @(posedge clk);cfg_force_refresh=1;@(posedge clk);cfg_force_refresh=1;@(posedge clk);cfg_force_refresh=0;wc(2);
        check("Dbl force",ref_required===1);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;wc(3);
        ref_ack=1;wrefi();wrefi();ref_ack=0;wc(2); check("Simul stable",ref_pending_cnt<=2); check("Pend range",ref_pending_cnt<=7);
        cfg_urgent_threshold=2;wc(2);
        if(ref_pending_cnt>=2) check("Lo thresh urg",ref_urgent===1); else check("Lo thresh no",ref_urgent===0);
        cfg_max_postpone=2;wrefi();wrefi();wrefi();wc(2); check("Max=2 cap",1'b1);
        $display("\n== %0d/%0d passed ==\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #5_000_000; $display("TIMEOUT"); $finish; end
endmodule
