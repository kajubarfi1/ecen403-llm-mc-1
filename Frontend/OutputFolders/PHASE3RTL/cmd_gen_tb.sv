`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// cmd_gen_tb.sv — 36 self-checking tests
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module cmd_gen_tb;
    localparam DDR_ADDR_W=15,DDR_BANK_W=3,ROW_BITS=15;
    localparam COL_BITS=10,BANK_BITS=3,AUX_WIDTH=4;
    // DDR encodings
    localparam DDR_NOP=4'b0111,DDR_ACT=4'b0011,DDR_RD=4'b0101,DDR_WR=4'b0100,DDR_PRE=4'b0010,DDR_REF=4'b0001;
    // Scheduler types
    localparam SCMD_NOP=0,SCMD_ACT=1,SCMD_RD=2,SCMD_WR=3,SCMD_PRE=4,SCMD_REF=5;

    logic clk=0; always #2.5 clk=~clk;
    logic rst_n;
    logic sched_valid; logic [3:0] sched_type;
    logic [ROW_BITS-1:0] sched_row; logic [COL_BITS-1:0] sched_col;
    logic [BANK_BITS-1:0] sched_bank; logic sched_we; logic [AUX_WIDTH-1:0] sched_aux;
    logic [3:0] ddr_cmd; logic [DDR_ADDR_W-1:0] ddr_addr; logic [DDR_BANK_W-1:0] ddr_bank;
    logic ddr_cke, ddr_reset_n, ddr_odt;
    logic fb_act_valid,fb_pre_valid,fb_rd_valid,fb_wr_valid,fb_ref_valid,fb_pre_all;
    logic [BANK_BITS-1:0] fb_act_bank,fb_pre_bank,fb_rd_bank,fb_wr_bank;
    logic [ROW_BITS-1:0] fb_act_row;
    logic cmd_out_valid,cmd_out_we; logic [AUX_WIDTH-1:0] cmd_out_aux;

    cmd_gen #(.DDR_ADDR_W(DDR_ADDR_W),.DDR_BANK_W(DDR_BANK_W),.ROW_BITS(ROW_BITS),
        .COL_BITS(COL_BITS),.BANK_BITS(BANK_BITS),.AUX_WIDTH(AUX_WIDTH)) dut(.*);

    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c);
        test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s ddr=%04b",test_num,n,ddr_cmd); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask

    task automatic issue(input [3:0] typ, input [ROW_BITS-1:0] row,
                         input [COL_BITS-1:0] col, input [BANK_BITS-1:0] bank,
                         input we, input [AUX_WIDTH-1:0] aux);
        @(posedge clk);
        sched_valid=1; sched_type=typ; sched_row=row; sched_col=col;
        sched_bank=bank; sched_we=we; sched_aux=aux;
        @(posedge clk);
        sched_valid=0;
        @(posedge clk);  // wait for registered output
    endtask

    initial begin
        $display("\n== cmd_gen_tb ==\n");
        rst_n=0; sched_valid=0; sched_type=0; sched_row=0; sched_col=0;
        sched_bank=0; sched_we=0; sched_aux=0;
        wc(3);
        check("Reset: NOP",          ddr_cmd===DDR_NOP);
        check("Reset: CKE=1",        ddr_cke===1);
        check("Reset: reset_n=1",    ddr_reset_n===1);
        check("Reset: fb_act=0",     fb_act_valid===0);
        check("Reset: fb_rd=0",      fb_rd_valid===0);
        check("Reset: out=0",        cmd_out_valid===0);

        @(posedge clk); rst_n=1; wc(2);

        // T07–T10: ACT command
        issue(SCMD_ACT, 15'd1234, 0, 3'd2, 0, 0);
        check("ACT: ddr=ACT",        ddr_cmd===DDR_ACT);
        check("ACT: addr=row",       ddr_addr==15'd1234);
        check("ACT: bank=2",         ddr_bank===3'd2);
        check("ACT: fb_act=1",       fb_act_valid===1);

        // T11–T15: RD command
        issue(SCMD_RD, 0, 10'd50, 3'd0, 0, 4'd7);
        check("RD: ddr=RD",          ddr_cmd===DDR_RD);
        check("RD: col in addr",     ddr_addr[COL_BITS-1:0]===10'd50);
        check("RD: fb_rd=1",         fb_rd_valid===1);
        check("RD: out_valid",       cmd_out_valid===1);
        check("RD: out_we=0",        cmd_out_we===0);

        // T16–T21: WR command
        issue(SCMD_WR, 0, 10'd99, 3'd5, 1, 4'hA);
        check("WR: ddr=WR",          ddr_cmd===DDR_WR);
        check("WR: bank=5",          ddr_bank===3'd5);
        check("WR: fb_wr=1",         fb_wr_valid===1);
        check("WR: ODT=1",           ddr_odt===1);
        check("WR: out_valid",       cmd_out_valid===1);
        check("WR: out_we=1",        cmd_out_we===1);

        // T22–T25: PRE command
        issue(SCMD_PRE, 0, 0, 3'd3, 0, 0);
        check("PRE: ddr=PRE",        ddr_cmd===DDR_PRE);
        check("PRE: bank=3",         ddr_bank===3'd3);
        check("PRE: fb_pre=1",       fb_pre_valid===1);
        check("PRE: A10=0 (single)", ddr_addr[10]===0);

        // T26–T27: REF command
        issue(SCMD_REF, 0, 0, 0, 0, 0);
        check("REF: ddr=REF",        ddr_cmd===DDR_REF);
        check("REF: fb_ref=1",       fb_ref_valid===1);

        // T28–T29: NOP (no valid)
        @(posedge clk); sched_valid=0; @(posedge clk); @(posedge clk);
        check("NOP: ddr=NOP",        ddr_cmd===DDR_NOP);
        check("NOP: fb all 0",       fb_act_valid===0 && fb_rd_valid===0 && fb_wr_valid===0);

        // T30–T31: Aux passthrough
        issue(SCMD_RD, 0, 10'd1, 3'd0, 0, 4'hF);
        check("Aux: 0xF",            cmd_out_aux===4'hF);
        issue(SCMD_WR, 0, 10'd2, 3'd1, 1, 4'h5);
        check("Aux: 0x5",            cmd_out_aux===4'h5);

        // T32–T33: CKE stays high
        check("CKE stays 1",         ddr_cke===1);
        check("reset_n stays 1",     ddr_reset_n===1);

        // T34: Back-to-back commands
        issue(SCMD_ACT, 15'd500, 0, 3'd4, 0, 0);
        issue(SCMD_RD, 0, 10'd25, 3'd4, 0, 4'd2);
        check("B2B: RD after ACT",   ddr_cmd===DDR_RD);

        // T35–T36: All banks addressable
        issue(SCMD_ACT, 0, 0, 3'd7, 0, 0);
        check("Bank 7 ACT",          ddr_bank===3'd7 && ddr_cmd===DDR_ACT);
        issue(SCMD_ACT, 0, 0, 3'd0, 0, 0);
        check("Bank 0 ACT",          ddr_bank===3'd0 && ddr_cmd===DDR_ACT);

        $display("\n== %0d/%0d passed ==\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
