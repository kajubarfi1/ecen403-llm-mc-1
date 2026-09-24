`timescale 1ns / 1ps
//==============================================================
// addr_decoder_tb.sv -- spec-only testbench (combinational DUT)
//==============================================================
module addr_decoder_tb;

    localparam ADDR_WIDTH=29, ROW_BITS=15, BANK_BITS=3, COL_BITS=10, RANK_BITS=1;

    logic [ADDR_WIDTH-1:0] req_addr;
    logic [ROW_BITS-1:0]   dec_row;
    logic [BANK_BITS-1:0]  dec_bank;
    logic [COL_BITS-1:0]   dec_col;
    logic [RANK_BITS-1:0]  dec_rank;

    addr_decoder dut (.*);

    int pass_count=0, fail_count=0, total_tests=0;
    task automatic check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    initial begin
        $dumpfile("addr_decoder_tb.vcd"); $dumpvars(0, addr_decoder_tb);
        req_addr = 29'h00000000; #10;
        check($sformatf("V1: addr=0x%0h row", req_addr), dec_row === 15'h0000);
        check($sformatf("V1: addr=0x%0h bank", req_addr), dec_bank === 3'h0);
        check($sformatf("V1: addr=0x%0h col", req_addr), dec_col === 10'h000);
        check($sformatf("V1: addr=0x%0h rank", req_addr), dec_rank === '0);
        req_addr = 29'h1FFFFFFF; #10;
        check($sformatf("V2: addr=0x%0h row", req_addr), dec_row === 15'h7FFF);
        check($sformatf("V2: addr=0x%0h bank", req_addr), dec_bank === 3'h7);
        check($sformatf("V2: addr=0x%0h col", req_addr), dec_col === 10'h3F8);
        check($sformatf("V2: addr=0x%0h rank", req_addr), dec_rank === '0);
        req_addr = 29'h1FFFC000; #10;
        check($sformatf("V3: addr=0x%0h row", req_addr), dec_row === 15'h7FFF);
        check($sformatf("V3: addr=0x%0h bank", req_addr), dec_bank === 3'h0);
        check($sformatf("V3: addr=0x%0h col", req_addr), dec_col === 10'h000);
        check($sformatf("V3: addr=0x%0h rank", req_addr), dec_rank === '0);
        req_addr = 29'h00003800; #10;
        check($sformatf("V4: addr=0x%0h row", req_addr), dec_row === 15'h0000);
        check($sformatf("V4: addr=0x%0h bank", req_addr), dec_bank === 3'h7);
        check($sformatf("V4: addr=0x%0h col", req_addr), dec_col === 10'h000);
        check($sformatf("V4: addr=0x%0h rank", req_addr), dec_rank === '0);
        req_addr = 29'h000007F0; #10;
        check($sformatf("V5: addr=0x%0h row", req_addr), dec_row === 15'h0000);
        check($sformatf("V5: addr=0x%0h bank", req_addr), dec_bank === 3'h0);
        check($sformatf("V5: addr=0x%0h col", req_addr), dec_col === 10'h3F8);
        check($sformatf("V5: addr=0x%0h rank", req_addr), dec_rank === '0);
        req_addr = 29'h0015A5A5; #10;
        check($sformatf("V6: addr=0x%0h row", req_addr), dec_row === 15'h0056);
        check($sformatf("V6: addr=0x%0h bank", req_addr), dec_bank === 3'h4);
        check($sformatf("V6: addr=0x%0h col", req_addr), dec_col === 10'h2D0);
        check($sformatf("V6: addr=0x%0h rank", req_addr), dec_rank === '0);

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule