`timescale 1ns/1ps
module addr_decoder_tb;
    localparam ADDR_WIDTH=29,ROW_BITS=15,COL_BITS=10,BANK_BITS=3,RANK_BITS=1;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [ROW_BITS-1:0] dec_row; logic [BANK_BITS-1:0] dec_bank;
    logic [COL_BITS-1:0] dec_col; logic [RANK_BITS-1:0] dec_rank;
    addr_decoder #(.ADDR_WIDTH(ADDR_WIDTH),.ROW_BITS(ROW_BITS),.COL_BITS(COL_BITS),.BANK_BITS(BANK_BITS),.RANK_BITS(RANK_BITS)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,logic [14:0] er,logic [2:0] eb,logic [9:0] ec,logic erk);
        test_num++;#1;
        if(dec_row!==er||dec_bank!==eb||dec_col!==ec||dec_rank!==erk) begin
            $display("  X T%02d FAIL: %s row=%0d/%0d bank=%0d/%0d",test_num,n,er,dec_row,eb,dec_bank); fail_count++;
        end else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    function automatic [28:0] build(input [14:0] row,input [2:0] bank,input [6:0] col_u,input [3:0] bo);
        return {row,bank,col_u,bo};
    endfunction
    initial begin
        $display("\n== addr_decoder_tb ==\n");
        req_addr=0; check("All zeros",0,0,0,0);
        req_addr=29'h1FFFFFFF; check("All ones",15'h7FFF,3'h7,{7'h7F,3'b000},0);
        for(int b=0;b<8;b++) begin req_addr=build(100,b[2:0],10,0); check($sformatf("Bank %0d",b),100,b[2:0],{7'd10,3'b000},0); end
        req_addr=build(0,0,0,0); check("Row 0",0,0,0,0);
        req_addr=build(32767,0,0,0); check("Row max",32767,0,0,0);
        req_addr=build(500,2,0,0); check("Col min",500,2,0,0);
        req_addr=build(500,2,127,0); check("Col max",500,2,{7'd127,3'b000},0);
        req_addr=build(500,2,64,0); check("Col mid",500,2,{7'd64,3'b000},0);
        req_addr=build(999,3,42,0); check("Off=0",999,3,{7'd42,3'b000},0);
        req_addr=build(999,3,42,5); check("Off=5",999,3,{7'd42,3'b000},0);
        req_addr=build(999,3,42,15); check("Off=15",999,3,{7'd42,3'b000},0);
        req_addr=build(999,3,42,8); check("Off=8",999,3,{7'd42,3'b000},0);
        req_addr=build(1234,5,56,0); check("Recon1",1234,5,{7'd56,3'b000},0);
        req_addr=build(8191,3,100,0); check("Recon2",8191,3,{7'd100,3'b000},0);
        req_addr=29'h1FFFFFFF; check("Rank=0",15'h7FFF,3'h7,{7'h7F,3'b000},0);
        req_addr=29'h0|(1<<4); check("Bit4",0,0,{7'd1,3'b000},0);
        req_addr=29'h0|(1<<11); check("Bit11",0,1,0,0);
        req_addr=29'h0|(1<<14); check("Bit14",1,0,0,0);
        req_addr=29'h0|(1<<28); check("BitMSB",16384,0,0,0);
        req_addr=build(0,7,127,0); check("MaxCol+Bank",0,7,{7'd127,3'b000},0);
        req_addr=29'h10; check("Addr16",0,0,{7'd1,3'b000},0);
        // Extra: walking bank bits
        req_addr=29'h0|(1<<12); check("Bank bit1",0,2,0,0);
        req_addr=29'h0|(1<<13); check("Bank bit2",0,4,0,0);
        // Power of 2
        req_addr=29'h4000; check("Addr 0x4000",req_addr[28:14],req_addr[13:11],{req_addr[10:4],3'b000},0);
        req_addr=build(16384,4,64,0); check("Mid all",16384,4,{7'd64,3'b000},0);
        req_addr=build(32767,7,127,15); check("All max",32767,7,{7'h7F,3'b000},0);
        $display("\n== %0d/%0d passed ==\n",pass_count,pass_count+fail_count);
        $finish;
    end
endmodule
