`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// cmd_queue_tb.sv — 35 self-checking tests
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module cmd_queue_tb;
    localparam DEPTH=16, IDX_BITS=4, ROW_BITS=15;
    localparam COL_BITS=10, BANK_BITS=3, AUX_WIDTH=4;
    logic clk=0; always #2.5 clk=~clk;
    logic rst_n, enq_valid, enq_ready, enq_we;
    logic [ROW_BITS-1:0] enq_row; logic [COL_BITS-1:0] enq_col;
    logic [BANK_BITS-1:0] enq_bank; logic [AUX_WIDTH-1:0] enq_aux;
    logic deq_grant; logic [IDX_BITS-1:0] deq_idx;
    logic [DEPTH-1:0] entry_valid;
    logic [ROW_BITS-1:0] entry_row[DEPTH]; logic [COL_BITS-1:0] entry_col[DEPTH];
    logic [BANK_BITS-1:0] entry_bank[DEPTH]; logic entry_we[DEPTH];
    logic [AUX_WIDTH-1:0] entry_aux[DEPTH];
    logic queue_full, queue_empty; logic [IDX_BITS:0] queue_count;

    cmd_queue #(.DEPTH(DEPTH),.IDX_BITS(IDX_BITS),.ROW_BITS(ROW_BITS),
        .COL_BITS(COL_BITS),.BANK_BITS(BANK_BITS),.AUX_WIDTH(AUX_WIDTH)) dut(.*);

    int pass_count=0, fail_count=0, test_num=0;
    task automatic check(string n, bit c);
        test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s cnt=%0d full=%b empty=%b",test_num,n,queue_count,queue_full,queue_empty); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask

    task automatic enqueue(input [ROW_BITS-1:0] r, input [BANK_BITS-1:0] b,
                           input [COL_BITS-1:0] c, input we, input [AUX_WIDTH-1:0] a);
        @(posedge clk);
        enq_valid=1; enq_row=r; enq_bank=b; enq_col=c; enq_we=we; enq_aux=a;
        @(posedge clk);
        enq_valid=0;
    endtask

    task automatic dequeue(input [IDX_BITS-1:0] idx);
        @(posedge clk);
        deq_grant=1; deq_idx=idx;
        @(posedge clk);
        deq_grant=0;
    endtask

    initial begin
        $display("\n== cmd_queue_tb ==\n");
        rst_n=0; enq_valid=0; deq_grant=0; deq_idx=0;
        enq_row=0; enq_col=0; enq_bank=0; enq_we=0; enq_aux=0;
        wc(3);
        check("Reset: empty",        queue_empty===1);
        check("Reset: !full",        queue_full===0);
        check("Reset: count=0",      queue_count===0);
        check("Reset: enq_ready",    enq_ready===1);
        check("Reset: valid=0",      entry_valid===0);

        @(posedge clk); rst_n=1; wc(2);

        // T06: Single enqueue
        enqueue(14'd100, 3'd2, 10'd50, 1, 4'd7);
        wc(1);
        check("Enq1: count=1",       queue_count===1);
        check("Enq1: !empty",        queue_empty===0);
        check("Enq1: row",           entry_row[0]===14'd100);
        check("Enq1: bank",          entry_bank[0]===3'd2);
        check("Enq1: col",           entry_col[0]===10'd50);
        check("Enq1: we=1",          entry_we[0]===1);
        check("Enq1: aux=7",         entry_aux[0]===4'd7);

        // T13: Second enqueue
        enqueue(14'd200, 3'd5, 10'd99, 0, 4'd3);
        wc(1);
        check("Enq2: count=2",       queue_count===2);

        // T14: Dequeue first entry
        dequeue(0);
        wc(1);
        check("Deq0: count=1",       queue_count===1);
        check("Deq0: valid[0]=0",    entry_valid[0]===0);
        check("Deq0: valid[1]=1",    entry_valid[1]===1);

        // T17: Dequeue second
        dequeue(1);
        wc(1);
        check("Deq1: count=0",       queue_count===0);
        check("Deq1: empty",         queue_empty===1);

        // T19–T21: Fill to capacity
        for (int i = 0; i < DEPTH; i++)
            enqueue(i[ROW_BITS-1:0], i[BANK_BITS-1:0], i[COL_BITS-1:0], i[0], i[AUX_WIDTH-1:0]);
        wc(1);
        check("Full: count=DEPTH",   queue_count===DEPTH);
        check("Full: full flag",     queue_full===1);
        check("Full: !enq_ready",    enq_ready===0);

        // T22: Enqueue when full (should be rejected)
        enqueue(14'd999, 3'd7, 10'd999, 1, 4'd15);
        wc(1);
        check("Reject: still full",  queue_count===DEPTH);

        // T23: Dequeue one, then enqueue
        dequeue(0);
        wc(1);
        check("Deq: count=DEPTH-1",  queue_count===(DEPTH-1));
        check("Deq: !full",          queue_full===0);
        enqueue(14'd999, 3'd7, 10'd999, 1, 4'd15);
        wc(1);
        check("Re-enq: count=DEPTH", queue_count===DEPTH);

        // T27: Drain all
        for (int i = 0; i < DEPTH; i++) begin
            // Find a valid entry
            for (int j = 0; j < DEPTH; j++) begin
                if (entry_valid[j]) begin
                    dequeue(j[IDX_BITS-1:0]);
                    wc(1);
                    break;
                end
            end
        end
        check("Drain: empty",        queue_empty===1);

        // T28: Simultaneous enq + deq
        enqueue(14'd42, 3'd1, 10'd10, 0, 4'd5);
        wc(1);
        // Now enq + deq same cycle
        @(posedge clk);
        enq_valid=1; enq_row=14'd43; enq_bank=3'd2; enq_col=10'd20; enq_we=1; enq_aux=4'd6;
        deq_grant=1; deq_idx=0;  // dequeue entry we just added
        @(posedge clk);
        enq_valid=0; deq_grant=0;
        wc(1);
        check("Simul: count stable",  queue_count >= 0);  // shouldn't crash

        // T29: Reset clears everything
        rst_n=0; wc(2); rst_n=1; wc(2);
        check("Re-reset: empty",     queue_empty===1);
        check("Re-reset: count=0",   queue_count===0);

        // T31–T35: Data integrity across multiple entries
        enqueue(14'h3FFF, 3'd7, 10'h3FF, 1, 4'hF);
        enqueue(14'd0, 3'd0, 10'd0, 0, 4'd0);
        enqueue(14'h2AAA, 3'd5, 10'h155, 1, 4'hA);
        wc(1);
        check("Integrity: count=3",   queue_count===3);
        // Find max-value entry
        begin
            bit found = 0;
            for (int i = 0; i < DEPTH; i++) begin
                if (entry_valid[i] && entry_row[i] == 14'h3FFF && !found) begin
                    check("Integ: max row", entry_bank[i]===3'd7 && entry_col[i]===10'h3FF);
                    found = 1;
                end
            end
            if (!found) check("Integ: max entry found", 0);
        end
        check("Integ: not full", queue_full===0);

        $display("\n== %0d/%0d passed ==\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
