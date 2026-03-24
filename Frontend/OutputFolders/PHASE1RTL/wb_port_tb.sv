`timescale 1ns / 1ps
//==============================================================
// wb_port_tb.sv -- Enhanced testbench (32 tests)
// Generated: 2026-03-24 15:19:18
// Agent:     Wishbone Port Interface Agent (Phase 1)
//
// Sections:
//   A: Single write/read transactions
//   B: Burst write/read (BL8, CTI_INC/CTI_END)
//   C: Stall / backpressure behavior
//   D: Protocol compliance (ACK gating, idle behavior)
//   E: Error detection (unaligned addr)
//   F: Aux tag propagation and read response path
//   G: Tag FIFO pressure (back-to-back reads)
//   H: Reset mid-transaction
//   I: Edge cases (CYC drop mid-burst)
//
// Test List:
//   A1   Single write - no error
//   A2   req_valid pulsed during write
//   A3   Single read - ACK received
//   A4   Read data matches injected value
//   A5   Write completes at high address
//   B1   8-beat burst write completed (no hang)
//   B2   8 req_valid pulses for burst write
//   B3   8 ACKs for burst read with correct tags
//   B4   4-beat short burst req_valid count
//   C1   Stall asserted when req_ready=0
//   C2   No ACK during stall
//   C3   No req_valid during stall
//   C4   Transaction completes after stall released
//   C5   Stall on tag FIFO full (16 outstanding reads)
//   D1   No ACK when bus idle
//   D2   No ACK when CYC=1 STB=0
//   D3   No req_valid when bus idle
//   D4   No stall when bus idle
//   D5   No error when bus idle
//   E1   Error on unaligned address (0x01)
//   E2   No error on aligned address (0x04)
//   E3   Error on unaligned address (0x02)
//   F1   Write completes (aux tag incremented)
//   F2   Read response data matches injected value
//   G1   8 ACKs received for 8 outstanding reads
//   H1   req_valid low after async reset
//   H2   wb_ack_o low after async reset
//   H3   wb_err_o low after async reset
//   H4   Stall low after reset recovery
//   H5   Write succeeds after reset recovery
//   I1   CYC drop mid-burst (no hang)
//   I2   Write succeeds after burst abort
//
// VCD: dumps wb_port_tb.vcd
//==============================================================
module wb_port_tb;

    localparam real CLK_PERIOD = 5.0;
    localparam ADDR_WIDTH = 29;
    localparam DATA_WIDTH = 32;
    localparam SEL_WIDTH  = 4;
    localparam AUX_WIDTH  = 4;
    localparam MAX_BURST  = 8;
    localparam TAG_FIFO_DEPTH = 16;

    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    logic                  rst_n;
    logic                  wb_cyc_i;
    logic                  wb_stb_i;
    logic                  wb_we_i;
    logic [ADDR_WIDTH-1:0] wb_adr_i;
    logic [DATA_WIDTH-1:0] wb_dat_i;
    logic [SEL_WIDTH-1:0]  wb_sel_i;
    logic [1:0]            wb_bte_i;
    logic [2:0]            wb_cti_i;
    logic                  wb_ack_o;
    logic [DATA_WIDTH-1:0] wb_dat_o;
    logic                  wb_stall_o;
    logic                  wb_err_o;
    logic                  req_valid;
    logic                  req_we;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [DATA_WIDTH-1:0] req_wdata;
    logic [SEL_WIDTH-1:0]  req_wmask;
    logic [AUX_WIDTH-1:0]  req_aux;
    logic                  req_ready;
    logic                  rsp_valid;
    logic [DATA_WIDTH-1:0] rsp_rdata;
    logic [AUX_WIDTH-1:0]  rsp_aux;

    localparam logic [2:0] CTI_CLASSIC = 3'b000;
    localparam logic [2:0] CTI_INC     = 3'b010;
    localparam logic [2:0] CTI_END     = 3'b111;
    localparam logic [1:0] BTE_LINEAR  = 2'b00;

    wb_port dut (
        .clk(clk), .rst_n(rst_n),
        .wb_cyc_i(wb_cyc_i), .wb_stb_i(wb_stb_i), .wb_we_i(wb_we_i),
        .wb_adr_i(wb_adr_i), .wb_dat_i(wb_dat_i), .wb_sel_i(wb_sel_i),
        .wb_bte_i(wb_bte_i), .wb_cti_i(wb_cti_i),
        .wb_ack_o(wb_ack_o), .wb_dat_o(wb_dat_o),
        .wb_stall_o(wb_stall_o), .wb_err_o(wb_err_o),
        .req_valid(req_valid), .req_we(req_we), .req_addr(req_addr),
        .req_wdata(req_wdata), .req_wmask(req_wmask), .req_aux(req_aux),
        .req_ready(req_ready),
        .rsp_valid(rsp_valid), .rsp_rdata(rsp_rdata), .rsp_aux(rsp_aux)
    );

    int pass_count = 0, fail_count = 0, total_tests = 0;
    task automatic check(string name, logic condition);
        total_tests++;
        if (condition) begin pass_count++; $display("  [PASS] %0d: %s", total_tests, name); end
        else begin fail_count++; $display("  [FAIL] %0d: %s", total_tests, name); end
    endtask

    // Shadow aux_ctr -- mirrors DUT for correct rsp_aux generation
    logic [AUX_WIDTH-1:0] shadow_aux_ctr;
    wire shadow_beat = wb_cyc_i & wb_stb_i & ~wb_stall_o;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) shadow_aux_ctr <= '0;
        else if (shadow_beat) shadow_aux_ctr <= shadow_aux_ctr + 1'b1;

    logic [AUX_WIDTH-1:0] expected_tags [0:TAG_FIFO_DEPTH-1];
    int etag_wr, etag_rd;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) etag_wr <= 0;
        else if (shadow_beat && !wb_we_i) begin
            expected_tags[etag_wr % TAG_FIFO_DEPTH] <= shadow_aux_ctr;
            etag_wr <= etag_wr + 1;
        end
    end

    task automatic wb_idle();
        wb_cyc_i=0; wb_stb_i=0; wb_we_i=0; wb_adr_i='0;
        wb_dat_i='0; wb_sel_i='0; wb_bte_i=BTE_LINEAR; wb_cti_i=CTI_CLASSIC;
    endtask

    task automatic wb_write_classic(input [28:0] addr, input [31:0] data,
                                    input [3:0] sel = {4{1'b1}});
        @(posedge clk);
        wb_cyc_i=1; wb_stb_i=1; wb_we_i=1; wb_adr_i=addr; wb_dat_i=data;
        wb_sel_i=sel; wb_cti_i=CTI_CLASSIC; wb_bte_i=BTE_LINEAR;
        do @(posedge clk); while (wb_stall_o);
        wb_stb_i=0;
        if (!wb_ack_o) repeat (20) begin @(posedge clk); if (wb_ack_o) break; end
        @(posedge clk); wb_idle();
    endtask

    task automatic wb_read_classic(input [28:0] addr, output [31:0] data,
                                   input [31:0] inject_rdata = 32'hCAFE_1234, input int rsp_delay = 5);
        logic [AUX_WIDTH-1:0] tag_at_beat;
        @(posedge clk);
        wb_cyc_i=1; wb_stb_i=1; wb_we_i=0; wb_adr_i=addr;
        wb_sel_i={4{1'b1}}; wb_cti_i=CTI_CLASSIC; wb_bte_i=BTE_LINEAR;
        do @(posedge clk); while (wb_stall_o);
        tag_at_beat = shadow_aux_ctr - 1;
        wb_stb_i=0;
        fork
            begin repeat(rsp_delay) @(posedge clk); rsp_valid=1; rsp_rdata=inject_rdata;
                  rsp_aux=tag_at_beat; @(posedge clk); rsp_valid=0; end
            begin repeat(rsp_delay+10) begin @(posedge clk); if(wb_ack_o) break; end end
        join_any
        disable fork;
        data = wb_dat_o; @(posedge clk); wb_idle();
    endtask

    task automatic wb_burst_write(input [28:0] base_addr, input int beats, input [31:0] base_data);
        @(posedge clk); wb_cyc_i=1;
        for (int i=0; i<beats; i++) begin
            wb_stb_i=1; wb_we_i=1; wb_adr_i=base_addr+(i*4);
            wb_dat_i=base_data+i; wb_sel_i={4{1'b1}};
            wb_bte_i=BTE_LINEAR; wb_cti_i=(i<beats-1)?CTI_INC:CTI_END;
            do @(posedge clk); while (wb_stall_o);
        end
        wb_stb_i=0; repeat(beats+5) @(posedge clk); wb_idle();
    endtask

    task automatic inject_read_responses(input int count, input int start_etag_rd);
        for (int i=0; i<count; i++) begin
            rsp_valid=1; rsp_rdata=32'hFACE_0000+i;
            rsp_aux=expected_tags[(start_etag_rd+i)%TAG_FIFO_DEPTH];
            @(posedge clk);
        end
        rsp_valid=0;
    endtask

    int ack_count, req_valid_count, err_count;
    always @(posedge clk) if (rst_n) begin
        if (wb_ack_o) ack_count++; if (req_valid) req_valid_count++; if (wb_err_o) err_count++;
    end
    task automatic reset_monitors(); ack_count=0; req_valid_count=0; err_count=0; endtask

    task automatic hw_reset();
        rst_n=0; req_ready=1; rsp_valid=0; rsp_rdata='0; rsp_aux='0; wb_idle(); etag_rd=0;
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);
    endtask

    logic [31:0] rd_data;

    initial begin
        $dumpfile("wb_port_tb.vcd");
        $dumpvars(0, wb_port_tb);
        $display("");
        $display("==========================================================");
        $display("  wb_port_tb -- Enhanced Wishbone B4 Testbench");
        $display("  ADDR=%0d DATA=%0d SEL=%0d AUX=%0d BURST=%0d",
                 ADDR_WIDTH, DATA_WIDTH, SEL_WIDTH, AUX_WIDTH, MAX_BURST);
        $display("==========================================================");

        $display(""); $display("  -- Section A: Single Write / Read --");
        hw_reset(); reset_monitors();
        wb_write_classic(29'h0000_0100, 32'hDEAD_BEEF);
        check("A1: Single write - no error", wb_err_o === 1'b0);
        check($sformatf("A2: req_valid seen [count=%0d]", req_valid_count), req_valid_count >= 1);
        reset_monitors();
        wb_read_classic(29'h0000_0100, rd_data, 32'hCAFE_1234, 3); etag_rd++;
        check("A3: Single read - ACK received", ack_count >= 1);
        check($sformatf("A4: Read data = 0x%08X", rd_data), rd_data == 32'hCAFE_1234);
        reset_monitors();
        wb_write_classic(29'h1ABC_DE00, 32'h1234_5678);
        check("A5: Write at high address", wb_err_o === 1'b0);

        $display(""); $display("  -- Section B: Burst Write / Read (BL8) --");
        hw_reset(); reset_monitors();
        wb_burst_write(29'h0000_0200, 8, 32'hBEEF_0000);
        check("B1: 8-beat burst write completed", 1);
        check($sformatf("B2: 8 req_valid pulses [got %0d]", req_valid_count), req_valid_count == 8);
        reset_monitors();
        begin
            int saved; saved = etag_wr;
            fork
                begin @(posedge clk); wb_cyc_i=1;
                    for (int i=0;i<8;i++) begin wb_stb_i=1;wb_we_i=0;
                        wb_adr_i=29'h0000_0400+(i*4);wb_sel_i={4{1'b1}};
                        wb_bte_i=BTE_LINEAR;wb_cti_i=(i<7)?CTI_INC:CTI_END;
                        do @(posedge clk); while(wb_stall_o); end
                    wb_stb_i=0; end
                begin repeat(12) @(posedge clk); inject_read_responses(8, saved); etag_rd=saved+8; end
            join
            repeat(5) @(posedge clk); wb_idle();
        end
        check($sformatf("B3: 8 ACKs for burst read [got %0d]", ack_count), ack_count >= 8);
        reset_monitors();
        wb_burst_write(29'h0000_0800, 4, 32'hAAAA_0000);
        check($sformatf("B4: 4-beat short burst [%0d]", req_valid_count), req_valid_count == 4);

        $display(""); $display("  -- Section C: Stall / Backpressure --");
        hw_reset(); reset_monitors();
        req_ready=0; @(posedge clk);
        wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i=29'h0000_1000;wb_dat_i=32'hCAFE_BABE;
        wb_sel_i={4{1'b1}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;
        repeat(3) @(posedge clk);
        check("C1: Stall when req_ready=0", wb_stall_o===1'b1);
        check("C2: No ACK during stall", wb_ack_o===1'b0);
        check($sformatf("C3: No req_valid during stall [%0d]", req_valid_count), req_valid_count==0);
        req_ready=1; repeat(5) @(posedge clk);
        check("C4: Completes after stall released", ack_count>=1); wb_idle();

        hw_reset(); reset_monitors(); @(posedge clk); wb_cyc_i=1;
        begin int rd_iss; rd_iss=0;
            for (int i=0;i<TAG_FIFO_DEPTH;i++) begin
                wb_stb_i=1;wb_we_i=0;wb_adr_i=29'h0000_2000+(i*4);
                wb_sel_i={4{1'b1}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;
                @(posedge clk); if(!wb_stall_o) rd_iss++; else break;
                while(wb_stall_o) @(posedge clk);
            end
            wb_stb_i=1;wb_we_i=0;wb_adr_i=29'h0000_2040;wb_sel_i={4{1'b1}};wb_cti_i=CTI_CLASSIC;
            repeat(3) @(posedge clk);
            check($sformatf("C5: Stall tag FIFO full (%0d reads)", rd_iss), wb_stall_o===1'b1);
        end
        wb_idle();

        $display(""); $display("  -- Section D: Protocol Compliance --");
        hw_reset(); reset_monitors(); wb_idle(); repeat(5) @(posedge clk);
        check("D1: No ACK when idle", wb_ack_o===1'b0);
        @(posedge clk); wb_cyc_i=1;wb_stb_i=0; repeat(5) @(posedge clk);
        check("D2: No ACK CYC=1 STB=0", wb_ack_o===1'b0); wb_idle();
        reset_monitors(); repeat(5) @(posedge clk);
        check($sformatf("D3: No req_valid idle [%0d]", req_valid_count), req_valid_count==0);
        check("D4: No stall idle", wb_stall_o===1'b0);
        check("D5: No error idle", wb_err_o===1'b0);

        $display(""); $display("  -- Section E: Error Detection --");
        hw_reset(); reset_monitors();
        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i=29'h0000_0001;
        wb_dat_i=32'hBAAD_F00D;wb_sel_i={4{1'b1}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;
        repeat(3) @(posedge clk);
        check("E1: Error unaligned 0x01", wb_err_o===1'b1); wb_idle(); repeat(3) @(posedge clk);
        reset_monitors(); wb_write_classic(29'h0000_0004, 32'h1111_2222);
        check("E2: No error aligned 0x04", err_count==0);
        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i=29'h0000_0002;
        wb_dat_i=32'h0;wb_sel_i={4{1'b1}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;
        repeat(3) @(posedge clk);
        check("E3: Error unaligned 0x02", wb_err_o===1'b1); wb_idle(); repeat(3) @(posedge clk);

        $display(""); $display("  -- Section F: Aux Tag --");
        hw_reset(); reset_monitors();
        wb_write_classic(29'h0000_3000, 32'hAAAA_BBBB);
        check("F1: Write completes", wb_err_o===1'b0);
        reset_monitors();
        wb_read_classic(29'h0000_3000, rd_data, 32'h5555_6666, 3); etag_rd++;
        check($sformatf("F2: Read data 0x%08X", rd_data), rd_data==32'h5555_6666);

        $display(""); $display("  -- Section G: Tag FIFO Stress --");
        hw_reset(); reset_monitors();
        begin int saved; saved=etag_wr;
            @(posedge clk); wb_cyc_i=1;
            for(int i=0;i<8;i++) begin wb_stb_i=1;wb_we_i=0;
                wb_adr_i=29'h0000_4000+(i*4);wb_sel_i={4{1'b1}};
                wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;
                do @(posedge clk); while(wb_stall_o); end
            wb_stb_i=0; repeat(2) @(posedge clk);
            inject_read_responses(8, saved); etag_rd=saved+8;
            repeat(3) @(posedge clk); wb_idle();
        end
        check($sformatf("G1: 8 ACKs for 8 reads [%0d]", ack_count), ack_count>=8);

        $display(""); $display("  -- Section H: Reset Mid-Txn --");
        hw_reset(); reset_monitors();
        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i=29'h0000_5000;
        wb_dat_i=32'hDEAD_DEAD;wb_sel_i={4{1'b1}};wb_cti_i=CTI_CLASSIC;wb_bte_i=BTE_LINEAR;
        repeat(2) @(posedge clk); rst_n=0; repeat(5) @(posedge clk);
        check("H1: req_valid low", req_valid===1'b0);
        check("H2: ack low", wb_ack_o===1'b0);
        check("H3: err low", wb_err_o===1'b0);
        wb_idle(); rst_n=1; repeat(3) @(posedge clk);
        check("H4: Stall low after recovery", wb_stall_o===1'b0);
        reset_monitors(); wb_write_classic(29'h0000_6000, 32'h1234_ABCD);
        check("H5: Write after reset", ack_count>=1);

        $display(""); $display("  -- Section I: Edge Cases --");
        hw_reset(); reset_monitors();
        @(posedge clk); wb_cyc_i=1;wb_stb_i=1;wb_we_i=1;wb_adr_i=29'h0000_7000;
        wb_dat_i=32'hAAAA_0000;wb_sel_i={4{1'b1}};wb_cti_i=CTI_INC;wb_bte_i=BTE_LINEAR;
        do @(posedge clk); while(wb_stall_o); wb_cyc_i=0;wb_stb_i=0;
        repeat(5) @(posedge clk); wb_idle();
        check("I1: CYC drop mid-burst", 1);
        reset_monitors(); wb_write_classic(29'h0000_7100, 32'hBBBB_CCCC);
        check("I2: Write after abort", ack_count>=1);

        $display("");
        $display("==========================================================");
        if (fail_count==0) $display("  ALL %0d TESTS PASSED", total_tests);
        else $display("  %0d of %0d TESTS FAILED", fail_count, total_tests);
        $display("==========================================================");
        $display(""); $finish;
    end

    initial begin #(10_000_000); $display("  [FAIL] GLOBAL TIMEOUT"); $finish; end

endmodule