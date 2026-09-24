`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// scheduler_tb.sv — 32 self-checking tests
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module scheduler_tb;
    localparam DEPTH=16,IDX_BITS=4,ROW_BITS=15;
    localparam COL_BITS=10,BANK_BITS=3,NUM_BANKS=8,AUX_WIDTH=4;
    localparam CMD_NOP=0,CMD_ACT=1,CMD_RD=2,CMD_WR=3,CMD_PRE=4,CMD_REF=5;
    logic clk=0; always #2.5 clk=~clk;
    logic rst_n;
    // Queue interface
    logic [DEPTH-1:0] q_valid;
    logic [ROW_BITS-1:0] q_row[DEPTH]; logic [COL_BITS-1:0] q_col[DEPTH];
    logic [BANK_BITS-1:0] q_bank[DEPTH]; logic q_we[DEPTH]; logic [AUX_WIDTH-1:0] q_aux[DEPTH];
    // Bank tracker
    logic [NUM_BANKS-1:0] bank_is_active,bank_act_allowed,bank_rd_allowed,bank_wr_allowed,bank_pre_allowed;
    logic [ROW_BITS-1:0] bank_open_row[NUM_BANKS];
    // Refresh
    logic ref_required,ref_urgent,ref_ack;
    // Outputs
    logic deq_grant; logic [IDX_BITS-1:0] deq_idx;
    logic cmd_valid; logic [3:0] cmd_type;
    logic [ROW_BITS-1:0] cmd_row; logic [COL_BITS-1:0] cmd_col;
    logic [BANK_BITS-1:0] cmd_bank; logic cmd_we; logic [AUX_WIDTH-1:0] cmd_aux;

    scheduler #(.DEPTH(DEPTH),.IDX_BITS(IDX_BITS),.ROW_BITS(ROW_BITS),
        .COL_BITS(COL_BITS),.BANK_BITS(BANK_BITS),.NUM_BANKS(NUM_BANKS),.AUX_WIDTH(AUX_WIDTH)) dut(.*);

    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c);
        test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s cmd=%0d valid=%b",test_num,n,cmd_type,cmd_valid); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask

    task automatic clear_queue();
        q_valid = '0;
        for(int i=0;i<DEPTH;i++) begin q_row[i]=0;q_col[i]=0;q_bank[i]=0;q_we[i]=0;q_aux[i]=0; end
    endtask

    task automatic set_bank_idle();
        bank_is_active='0; bank_act_allowed='1; bank_rd_allowed='0; bank_wr_allowed='0; bank_pre_allowed='0;
        for(int i=0;i<NUM_BANKS;i++) bank_open_row[i]='0;
    endtask

    task automatic set_bank_active(input [2:0] b, input [ROW_BITS-1:0] row);
        bank_is_active[b]=1; bank_act_allowed[b]=0;
        bank_rd_allowed[b]=1; bank_wr_allowed[b]=1; bank_pre_allowed[b]=1;
        bank_open_row[b]=row;
    endtask

    initial begin
        $display("\n== scheduler_tb ==\n");
        rst_n=0; clear_queue(); set_bank_idle(); ref_required=0; ref_urgent=0;
        wc(3);
        check("Reset: !valid",       cmd_valid===0);
        check("Reset: NOP",          cmd_type===CMD_NOP);
        check("Reset: !deq",         deq_grant===0);
        check("Reset: !ref_ack",     ref_ack===0);

        @(posedge clk); rst_n=1; wc(2);

        // T05: Empty queue — NOP
        wc(2);
        check("Empty: NOP",          cmd_valid===0);

        // T06–T08: Row-hit read
        clear_queue(); set_bank_idle(); set_bank_active(3'd0, 14'd100);
        q_valid[0]=1; q_row[0]=14'd100; q_col[0]=10'd50; q_bank[0]=3'd0; q_we[0]=0; q_aux[0]=4'd1;
        wc(2);
        check("RowHit RD: valid",    cmd_valid===1);
        check("RowHit RD: type=RD",  cmd_type===CMD_RD);
        check("RowHit RD: deq",      deq_grant===1);

        // T09–T11: Row-hit write
        clear_queue(); set_bank_idle(); set_bank_active(3'd2, 14'd200);
        q_valid[0]=1; q_row[0]=14'd200; q_col[0]=10'd77; q_bank[0]=3'd2; q_we[0]=1; q_aux[0]=4'd3;
        wc(2);
        check("RowHit WR: valid",    cmd_valid===1);
        check("RowHit WR: type=WR",  cmd_type===CMD_WR);
        check("RowHit WR: bank=2",   cmd_bank===3'd2);

        // T12–T14: Row-miss to idle bank → ACT
        clear_queue(); set_bank_idle();
        q_valid[0]=1; q_row[0]=14'd300; q_bank[0]=3'd4; q_we[0]=0;
        wc(2);
        check("RowMiss idle: ACT",   cmd_type===CMD_ACT);
        check("RowMiss: row=300",    cmd_row===14'd300);
        check("RowMiss: !deq",       deq_grant===0);  // ACT doesn't dequeue

        // T15–T16: Row-miss to active bank → PRE first
        clear_queue(); set_bank_idle(); set_bank_active(3'd1, 14'd50);
        q_valid[0]=1; q_row[0]=14'd999; q_bank[0]=3'd1; q_we[0]=0;
        wc(2);
        check("RowMiss act: PRE",    cmd_type===CMD_PRE);
        check("RowMiss act: bank=1", cmd_bank===3'd1);

        // T17–T18: Urgent refresh preempts
        clear_queue(); set_bank_idle(); set_bank_active(3'd0, 14'd100);
        q_valid[0]=1; q_row[0]=14'd100; q_bank[0]=3'd0; q_we[0]=0;
        ref_urgent=1;
        wc(2);
        check("UrgRef: type=REF",    cmd_type===CMD_REF);
        check("UrgRef: ref_ack",     ref_ack===1);
        ref_urgent=0; wc(2);

        // T19–T20: Normal refresh when idle
        clear_queue(); set_bank_idle();
        ref_required=1; ref_urgent=0;
        wc(2);
        check("NormRef: type=REF",   cmd_type===CMD_REF);
        check("NormRef: ref_ack",    ref_ack===1);
        ref_required=0; wc(2);

        // T21–T23: FR-FCFS priority (row-hit over row-miss)
        clear_queue(); set_bank_idle(); set_bank_active(3'd0, 14'd100);
        bank_rd_allowed=8'hFF; bank_wr_allowed=8'hFF;
        // Entry 0: row-miss (different row)
        q_valid[0]=1; q_row[0]=14'd999; q_bank[0]=3'd0; q_we[0]=0;
        // Entry 1: row-hit
        q_valid[1]=1; q_row[1]=14'd100; q_bank[1]=3'd0; q_we[1]=0;
        wc(2);
        check("FRFCFS: picks hit",   cmd_type===CMD_RD);
        check("FRFCFS: idx=1",       deq_idx===1);
        check("FRFCFS: deq",         deq_grant===1);

        // T24–T25: Multiple banks
        clear_queue(); set_bank_idle();
        set_bank_active(3'd0, 14'd10); set_bank_active(3'd3, 14'd30);
        q_valid[0]=1; q_row[0]=14'd10; q_bank[0]=3'd0; q_we[0]=0;
        q_valid[1]=1; q_row[1]=14'd30; q_bank[1]=3'd3; q_we[1]=1;
        wc(2);
        check("MultiBank: valid",    cmd_valid===1);
        check("MultiBank: first",    deq_idx===0);  // FCFS picks entry 0

        // T26–T27: Timing blocks — bank not ready
        clear_queue(); set_bank_idle(); set_bank_active(3'd5, 14'd500);
        bank_rd_allowed[5]=0; bank_wr_allowed[5]=0;  // timing not yet expired
        q_valid[0]=1; q_row[0]=14'd500; q_bank[0]=3'd5; q_we[0]=0;
        wc(2);
        check("TimingBlk: no CAS",   cmd_type!==CMD_RD && cmd_type!==CMD_WR);
        bank_rd_allowed[5]=1;
        wc(2);
        check("TimingOk: CAS now",   cmd_type===CMD_RD);

        // T28–T29: No deadlock — always produces something or NOP
        clear_queue(); set_bank_idle();
        bank_act_allowed='0;  // everything blocked
        q_valid[0]=1; q_row[0]=14'd1; q_bank[0]=3'd0; q_we[0]=0;
        wc(2);
        check("Blocked: NOP ok",     cmd_valid===0 || cmd_type===CMD_NOP);
        bank_act_allowed='1;

        // T30–T32: Aux passthrough
        clear_queue(); set_bank_idle(); set_bank_active(3'd0, 14'd42);
        q_valid[0]=1; q_row[0]=14'd42; q_col[0]=10'd77; q_bank[0]=3'd0; q_we[0]=1; q_aux[0]=4'hB;
        wc(2);
        check("Aux: passthrough",    cmd_aux===4'hB);
        check("Aux: col",            cmd_col===10'd77);
        check("Aux: row",            cmd_row===14'd42);

        $display("\n== %0d/%0d passed ==\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
