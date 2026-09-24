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

    // Poll for the next issued command instead of hand-counting cycles --
    // a single-entry grant is a genuine one-cycle pulse once recently-
    // granted entries are masked (see Defect 1 fix), so a fixed wc(N)
    // followed by a direct check is fragile against exactly which cycle
    // the pulse lands on.
    task automatic wait_cmd(output logic got, output logic [3:0] captured_type,
                             output logic [BANK_BITS-1:0] captured_bank,
                             output logic captured_deq, output logic [IDX_BITS-1:0] captured_idx,
                             input int max_cyc);
        int cyc;
        got = 0;
        for (cyc = 0; cyc < max_cyc; cyc++) begin
            @(posedge clk);
            if (cmd_valid) begin
                got = 1; captured_type = cmd_type; captured_bank = cmd_bank;
                captured_deq = deq_grant; captured_idx = deq_idx;
                break;
            end
        end
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
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 5);
            check("RowHit RD: valid",    got);
            check("RowHit RD: type=RD",  got && ctype===CMD_RD);
            check("RowHit RD: deq",      got && cdeq===1);
        end

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

        // T17–T18: Urgent refresh preempts (banks already idle -- REF fires
        // immediately. The "active bank forces PRE first" case is its own
        // scenario, covered by RefBlock T35-38 below -- Defect 5 fix).
        clear_queue(); set_bank_idle();
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

        // T21–T23: FR-FCFS priority (row-hit over row-miss). Poll for the
        // FIRST command issued -- with two CAS-ready-or-better candidates,
        // a fixed multi-cycle wait can land after the scheduler has already
        // moved on to the second entry (see Defect 1 fix: a granted entry
        // is masked from re-selection starting the very next cycle, so
        // whichever entry wins first is only observable for one cycle).
        clear_queue(); set_bank_idle(); set_bank_active(3'd0, 14'd100);
        bank_rd_allowed=8'hFF; bank_wr_allowed=8'hFF;
        // Entry 0: row-miss (different row)
        q_valid[0]=1; q_row[0]=14'd999; q_bank[0]=3'd0; q_we[0]=0;
        // Entry 1: row-hit
        q_valid[1]=1; q_row[1]=14'd100; q_bank[1]=3'd0; q_we[1]=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 5);
            check("FRFCFS: picks hit",   got && ctype===CMD_RD);
            check("FRFCFS: idx=1",       got && cidx===1);
            check("FRFCFS: deq",         got && cdeq===1);
        end

        // T24–T25: Multiple banks
        clear_queue(); set_bank_idle();
        set_bank_active(3'd0, 14'd10); set_bank_active(3'd3, 14'd30);
        q_valid[0]=1; q_row[0]=14'd10; q_bank[0]=3'd0; q_we[0]=0;
        q_valid[1]=1; q_row[1]=14'd30; q_bank[1]=3'd3; q_we[1]=1;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 5);
            check("MultiBank: valid",    got);
            check("MultiBank: first",    got && cidx===0);  // FCFS picks entry 0
        end

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

        // T33-T34: Regrant guard -- cmd_queue lags one cycle behind a
        // grant (q_valid stays 1 for one more cycle than the real queue
        // would show), so the scheduler itself must not re-select/re-grant
        // the same entry during that window.
        clear_queue(); set_bank_idle(); set_bank_active(3'd0, 14'd700);
        q_valid[0]=1; q_row[0]=14'd700; q_bank[0]=3'd0; q_we[0]=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 5);
            check("Regrant: first grant", got && cdeq && cidx===0);
        end
        // q_valid[0] intentionally left high here -- simulating cmd_queue
        // not having caught up yet. One more cycle: the just-granted entry
        // must not be immediately re-selected (nothing else is valid, so
        // deq_grant should now read 0).
        @(posedge clk);
        check("Regrant: no re-grant next cycle", !(deq_grant===1'b1 && deq_idx===0));

        // T35-T38: Urgent refresh with an open bank must force-precharge
        // it first, never issue REF while any bank is still active.
        clear_queue(); set_bank_idle(); set_bank_active(3'd3, 14'd800);
        ref_urgent=1;
        wc(2);
        check("RefBlock: PRE not REF while active", cmd_type===CMD_PRE);
        check("RefBlock: PRE targets active bank",  cmd_bank===3'd3);
        set_bank_idle();  // simulate bank_tracker clearing the bank post-PRE
        wc(2);
        check("RefBlock: REF once banks idle",  cmd_type===CMD_REF);
        check("RefBlock: ref_ack",              ref_ack===1);
        ref_urgent=0; wc(2);

        $display("\n== %0d/%0d passed ==\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
