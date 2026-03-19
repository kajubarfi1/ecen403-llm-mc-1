`timescale 1ns/1ps
module bank_tracker_tb;
    localparam NUM_BANKS=8,BANK_BITS=3,ROW_BITS=15,CTR_WIDTH=8;
    localparam T_RCD=4,T_RP=4,T_RAS=8,T_RC=12,T_RRD=3,T_FAW=10,T_WTR=3,T_WR=5,T_RTP=3,T_CCD=2,T_RFC=8;
    logic clk=0; always #2.5 clk=~clk;
    logic rst_n,cmd_act_valid,cmd_pre_valid,cmd_pre_all,cmd_rd_valid,cmd_wr_valid,cmd_ref_valid;
    logic [BANK_BITS-1:0] cmd_act_bank,cmd_pre_bank,cmd_rd_bank,cmd_wr_bank;
    logic [ROW_BITS-1:0] cmd_act_row;
    logic [7:0] cfg_tRCD_nCK,cfg_tRP_nCK,cfg_tRAS_nCK,cfg_tRC_nCK,cfg_tRRD_nCK,cfg_tFAW_nCK,cfg_tWTR_nCK,cfg_tWR_nCK,cfg_tRTP_nCK,cfg_tCCD_nCK,cfg_tRFC_nCK;
    logic [NUM_BANKS-1:0] bank_is_active,bank_act_allowed,bank_rd_allowed,bank_wr_allowed,bank_pre_allowed;
    logic [ROW_BITS-1:0] bank_open_row[NUM_BANKS]; logic all_banks_idle,faw_allows_act;
    bank_tracker #(.NUM_BANKS(NUM_BANKS),.BANK_BITS(BANK_BITS),.ROW_BITS(ROW_BITS),.CTR_WIDTH(CTR_WIDTH)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c); test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s",test_num,n); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask
    task automatic clr(); cmd_act_valid=0;cmd_pre_valid=0;cmd_pre_all=0;cmd_rd_valid=0;cmd_wr_valid=0;cmd_ref_valid=0; endtask
    task automatic act(input [2:0] b,input [14:0] r); @(posedge clk);cmd_act_valid=1;cmd_act_bank=b;cmd_act_row=r;@(posedge clk);cmd_act_valid=0; endtask
    task automatic pre(input [2:0] b,input bit a); @(posedge clk);cmd_pre_valid=1;cmd_pre_bank=b;cmd_pre_all=a;@(posedge clk);cmd_pre_valid=0;cmd_pre_all=0; endtask
    task automatic rd(input [2:0] b); @(posedge clk);cmd_rd_valid=1;cmd_rd_bank=b;@(posedge clk);cmd_rd_valid=0; endtask
    task automatic wr(input [2:0] b); @(posedge clk);cmd_wr_valid=1;cmd_wr_bank=b;@(posedge clk);cmd_wr_valid=0; endtask
    task automatic ref_c(); @(posedge clk);cmd_ref_valid=1;@(posedge clk);cmd_ref_valid=0; endtask
    initial begin
        $display("\n== bank_tracker_tb ==\n");
        rst_n=0;clr();cmd_act_bank=0;cmd_act_row=0;cmd_pre_bank=0;cmd_rd_bank=0;cmd_wr_bank=0;
        cfg_tRCD_nCK=T_RCD;cfg_tRP_nCK=T_RP;cfg_tRAS_nCK=T_RAS;cfg_tRC_nCK=T_RC;
        cfg_tRRD_nCK=T_RRD;cfg_tFAW_nCK=T_FAW;cfg_tWTR_nCK=T_WTR;cfg_tWR_nCK=T_WR;
        cfg_tRTP_nCK=T_RTP;cfg_tCCD_nCK=T_CCD;cfg_tRFC_nCK=T_RFC;
        wc(3); check("Reset idle",all_banks_idle===1); check("Reset act=0",bank_is_active===8'h00);
        check("Reset allow",bank_act_allowed===8'hFF); check("Reset faw",faw_allows_act===1);
        @(posedge clk);rst_n=1;wc(2); check("Post-reset",all_banks_idle===1);
        act(0,15'h1234);wc(1); check("ACT0 active",bank_is_active[0]===1); check("ACT0 row",bank_open_row[0]===15'h1234);
        check("ACT0 !idle",all_banks_idle===0); check("ACT0 !allow",bank_act_allowed[0]===0);
        check("tRCD rd=0",bank_rd_allowed[0]===0); check("tRCD wr=0",bank_wr_allowed[0]===0);
        wc(T_RCD); check("tRCD rd=1",bank_rd_allowed[0]===1); check("tRCD wr=1",bank_wr_allowed[0]===1);
        wc(T_RAS); check("tRAS pre ok",bank_pre_allowed[0]===1);
        pre(0,0);wc(1); check("PRE0",bank_is_active[0]===0);
        wc(T_RP); check("tRP allow",bank_act_allowed[0]===1);
        act(0,1);wc(T_RRD);act(1,2);wc(T_RRD);act(2,3);wc(T_RAS);
        check("3 active",bank_is_active[0]&&bank_is_active[1]&&bank_is_active[2]);
        pre(0,1);wc(1); check("PRE ALL",!bank_is_active[0]&&!bank_is_active[1]&&!bank_is_active[2]);
        wc(T_RP); check("ALL idle",all_banks_idle===1);
        wc(T_RC); act(0,15'hAAAA);wc(T_RCD); rd(0);wc(1);
        check("RD tCCD",bank_rd_allowed[0]===0); wc(T_CCD); check("RD tCCD exp",bank_rd_allowed[0]===1);
        wr(0);wc(1); check("WR tCCD",bank_rd_allowed[0]===0); wc(T_CCD); check("WR tCCD exp",bank_rd_allowed[0]===1);
        check("WR tWR pre",bank_pre_allowed[0]===0);
        pre(0,1);wc(T_RP+1); ref_c();wc(1); check("REF idle",all_banks_idle===1);
        check("REF tRFC",bank_act_allowed===8'h00); wc(T_RFC); check("tRFC exp",bank_act_allowed[0]===1);
        act(0,15'h10);wc(1); check("tRRD blk",bank_act_allowed[1]===0); wc(T_RRD); check("tRRD exp",bank_act_allowed[1]===1);
        act(1,15'h20);wc(1); check("tRRD blk2",bank_act_allowed[2]===0);
        wc(T_RRD);act(2,15'h30);wc(T_RRD);act(3,15'h40);wc(1);
        check("FAW blk",faw_allows_act===0); wc(T_FAW); check("FAW exp",faw_allows_act===1);
        rst_n=0;wc(2);rst_n=1;wc(2);
        act(4,15'h4444);wc(T_RRD);act(5,15'h5555);wc(T_RCD);rd(4);wc(T_CCD);wr(5);wc(1);
        check("IL b4",bank_is_active[4]===1&&bank_open_row[4]===15'h4444);
        check("IL b5",bank_is_active[5]===1&&bank_open_row[5]===15'h5555);
        $display("\n== %0d/%0d passed ==\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
