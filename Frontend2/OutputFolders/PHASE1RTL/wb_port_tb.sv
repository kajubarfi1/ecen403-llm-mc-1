`timescale 1ns / 1ps
module wb_port_tb;
    localparam real CLK_PERIOD = 5.0;
    localparam ADDR_WIDTH=29, DATA_WIDTH=32, SEL_WIDTH=4, AUX_WIDTH=4;
    logic clk=0;
    always #(CLK_PERIOD/2) clk=~clk;

    logic wb_cyc_i, wb_stb_i, wb_we_i;
    logic [ADDR_WIDTH-1:0] wb_adr_i;
    logic [DATA_WIDTH-1:0] wb_dat_i, wb_dat_o;
    logic [SEL_WIDTH-1:0] wb_sel_i;
    logic wb_ack_o, wb_stall_o, wb_err_o;
    logic req_valid, req_we, req_ready;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [DATA_WIDTH-1:0] req_wdata;
    // Response-path inputs from the (unmodeled) memory backend. Must be
    // driven -- left unconnected, rsp_valid floats X, and since
    // wb_ack_o = wr_ack_deliver | rsp_valid, that X poisons wb_ack_o back
    // to X any time the write-ack path is 0, failing every "ack
    // deasserted" check even though the RTL itself is correct.
    logic rsp_valid;
    logic [DATA_WIDTH-1:0] rsp_rdata;
    logic [AUX_WIDTH-1:0] rsp_aux;
    // Tied high: this testbench doesn't model data_path's write buffer, so
    // it never exercises WB-012's backpressure path (same reasoning as
    // req_ready above -- an unmodeled backend should look always-ready,
    // not X).
    logic wr_data_ready;
    logic rst_n;
    int pass_count=0, fail_count=0, total_tests=0;

    wb_port dut (.*);

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    task wb_idle(); wb_cyc_i=0; wb_stb_i=0; wb_we_i=0; wb_adr_i=0; wb_dat_i=0; wb_sel_i=0; endtask

    initial begin
        $dumpfile("wb_port_tb.vcd"); $dumpvars(0, wb_port_tb);
        rst_n=0; req_ready=1; rsp_valid=0; rsp_rdata=0; rsp_aux=0; wr_data_ready=1; wb_idle();
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);

        // Single write
        @(posedge clk); wb_cyc_i=1; wb_stb_i=1; wb_we_i=1;
        wb_adr_i=29'h100; wb_dat_i=32'hDEADBEEF; wb_sel_i={SEL_WIDTH{1'b1}};
        do @(posedge clk); while(wb_stall_o);
        wb_stb_i=0; if(!wb_ack_o) begin repeat(20) begin @(posedge clk); if(wb_ack_o) break; end end
        @(posedge clk); wb_idle();
        check("Single write OK", wb_err_o===1'b0);

        // ACK idle
        wb_idle(); repeat(3) @(posedge clk);
        check("ACK deasserted when idle", wb_ack_o===1'b0);

        // CYC without STB
        @(posedge clk); wb_cyc_i=1; wb_stb_i=0; repeat(3) @(posedge clk);
        check("No ACK when CYC=1 STB=0", wb_ack_o===1'b0);
        wb_idle();

        // Stall
        req_ready=0; @(posedge clk);
        wb_cyc_i=1; wb_stb_i=1; wb_we_i=1; wb_adr_i=29'h300;
        wb_dat_i=32'hCAFEBABE; wb_sel_i={SEL_WIDTH{1'b1}};
        repeat(3) @(posedge clk);
        check("Stall when backend busy", wb_stall_o===1'b1);
        req_ready=1; repeat(5) @(posedge clk); wb_idle();

        // Out-of-order read delivery (HOSTMEM fix, Validation 2026-11-05):
        // accept 2 reads back to back, then deliver their DRAM responses
        // in REVERSED order -- the second read's data arrives first. The
        // host must still see the FIRST read's data acked first, not
        // whichever response showed up first; this is the literal shape
        // of the bug the tag-indexed rd_data_buf fixes (a plain FIFO would
        // deliver the second read's data for the first read's ack).
        wb_idle(); repeat(2) @(posedge clk);
        @(posedge clk); wb_cyc_i=1; wb_stb_i=1; wb_we_i=0; wb_adr_i=29'h500;
        do @(posedge clk); while(wb_stall_o);
        wb_adr_i=29'h504;
        do @(posedge clk); while(wb_stall_o);
        wb_stb_i=0; wb_cyc_i=0;
        // second read's response arrives first -- must not jump the queue
        rsp_valid=1; rsp_aux=4'd1; rsp_rdata=32'hBBBBBBBB;
        @(posedge clk);
        rsp_valid=0;
        check("Out-of-order: early response does not ack yet", wb_ack_o===1'b0);
        repeat(2) @(posedge clk);
        check("Out-of-order: still not acked while first read is outstanding", wb_ack_o===1'b0);
        // first read's response arrives -- must deliver now, with ITS data
        rsp_valid=1; rsp_aux=4'd0; rsp_rdata=32'hAAAAAAAA;
        @(posedge clk);
        rsp_valid=0;
        check("Out-of-order: first read acked first", wb_ack_o===1'b1);
        check($sformatf("Out-of-order: first read's own data (got 0x%08X)", wb_dat_o),
              wb_dat_o===32'hAAAAAAAA);
        @(posedge clk);
        // the buffered second response should deliver right after
        check("Out-of-order: second read acked second", wb_ack_o===1'b1);
        check($sformatf("Out-of-order: second read's own data (got 0x%08X)", wb_dat_o),
              wb_dat_o===32'hBBBBBBBB);
        @(posedge clk); wb_idle();

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
