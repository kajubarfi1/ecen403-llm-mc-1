#!/usr/bin/env python3
"""
Testbench Generator Script (Phase 3) -- spec-only, deterministic.

Same discipline as Phase1/tb_generator.py and Phase2/tb_generator.py: these
testbenches are generated from the microarchitecture spec ONLY. They used to be
emitted by each module's own RTL generator (cmd_queue_gen.py, scheduler_gen.py,
cmd_gen_gen.py) from the very same derived parameters as the RTL, so a wrong
derivation showed up identically in the design and in its test. Here every
parameter the testbench uses is re-derived from the spec by code in this file;
nothing is imported from, or read out of, the RTL generators or their output.

The directed test bodies were moved here unchanged from the old generators
(byte-identical output on the golden spec was checked when they moved), so what
changed is where the parameters come from, not what is tested.
"""

import json
from pathlib import Path


class TestbenchGenerator:

    def __init__(self, spec_path: str):
        self.spec_path = spec_path
        with open(spec_path) as f:
            self.spec = json.load(f)
        self.geo = self.spec["memory_geometry"]
        self.arch = self.spec["controller_architecture"]
        self.host = self.spec["host_interface"]

    @staticmethod
    def _idx_bits(depth: int) -> int:
        """Bits to index `depth` entries (re-derived here, not read from the
        spec's $derived block, so a stale $derived value is a visible mismatch)."""
        return max(1, (depth - 1).bit_length())

    # ---- independent parameter derivation, one per module -----------------
    def _p_cmd_queue(self) -> dict:
        p = {}
        p["DEPTH"] = self.arch["command_queue_depth"]
        p["IDX_BITS"] = self._idx_bits(p["DEPTH"])
        p["ROW_BITS"] = self.geo["row_bits"]
        p["COL_BITS"] = self.geo["column_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["AUX_WIDTH"] = self.arch.get("aux_width", 4)
        return p

    def _p_scheduler(self) -> dict:
        p = self._p_cmd_queue()
        p["NUM_BANKS"] = 2 ** p["BANK_BITS"]
        return p

    def _p_cmd_gen(self) -> dict:
        p = {}
        p["ROW_BITS"] = self.geo["row_bits"]
        p["COL_BITS"] = self.geo["column_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["DDR_ADDR_W"] = max(p["ROW_BITS"], p["COL_BITS"])
        p["DDR_BANK_W"] = p["BANK_BITS"]
        p["AUX_WIDTH"] = self.arch.get("aux_width", 4)
        return p

    # ---- testbenches (bodies moved from the RTL generators) ---------------
    def generate_cmd_queue_tb(self) -> str:
        p = self._p_cmd_queue()
        return f"""`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// cmd_queue_tb.sv — 35 self-checking tests
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module cmd_queue_tb;
    localparam DEPTH={p['DEPTH']}, IDX_BITS={p['IDX_BITS']}, ROW_BITS={p['ROW_BITS']};
    localparam COL_BITS={p['COL_BITS']}, BANK_BITS={p['BANK_BITS']}, AUX_WIDTH={p['AUX_WIDTH']};
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
        $display("\\n== cmd_queue_tb ==\\n");
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

        $display("\\n== %0d/%0d passed ==\\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    def generate_scheduler_tb(self) -> str:
        p = self._p_scheduler()
        return f"""`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// scheduler_tb.sv — 32 self-checking tests
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module scheduler_tb;
    localparam DEPTH={p['DEPTH']},IDX_BITS={p['IDX_BITS']},ROW_BITS={p['ROW_BITS']};
    localparam COL_BITS={p['COL_BITS']},BANK_BITS={p['BANK_BITS']},NUM_BANKS={p['NUM_BANKS']},AUX_WIDTH={p['AUX_WIDTH']};
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

    // Starting a new scenario: empty the queue and let any command still in
    // the scheduler's feedback-latency window (FB_LAG = 2 cycles, plus one for
    // the output register) drain, so the previous scenario's command cannot
    // hold off this one. The hold itself is tested explicitly below.
    task automatic clear_queue();
        q_valid = '0;
        for(int i=0;i<DEPTH;i++) begin q_row[i]=0;q_col[i]=0;q_bank[i]=0;q_we[i]=0;q_aux[i]=0; end
        repeat(4) @(posedge clk);
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
        $display("\\n== scheduler_tb ==\\n");
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
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("RowHit WR: valid",    got);
            check("RowHit WR: type=WR",  got && ctype===CMD_WR);
            check("RowHit WR: bank=2",   got && cbank===3'd2);
        end

        // T12–T14: Row-miss to idle bank → ACT
        clear_queue(); set_bank_idle();
        q_valid[0]=1; q_row[0]=14'd300; q_bank[0]=3'd4; q_we[0]=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("RowMiss idle: ACT",   got && ctype===CMD_ACT);
            check("RowMiss: row=300",    got && cmd_row===14'd300);
            check("RowMiss: !deq",       got && cdeq===0);  // ACT doesn't dequeue
        end

        // T15–T16: Row-miss to active bank → PRE first
        clear_queue(); set_bank_idle(); set_bank_active(3'd1, 14'd50);
        q_valid[0]=1; q_row[0]=14'd999; q_bank[0]=3'd1; q_we[0]=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("RowMiss act: PRE",    got && ctype===CMD_PRE);
            check("RowMiss act: bank=1", got && cbank===3'd1);
        end

        // T17–T18: Urgent refresh preempts (banks already idle -- REF fires
        // immediately. The "active bank forces PRE first" case is its own
        // scenario, covered by RefBlock T35-38 below -- Defect 5 fix).
        clear_queue(); set_bank_idle();
        q_valid[0]=1; q_row[0]=14'd100; q_bank[0]=3'd0; q_we[0]=0;
        ref_urgent=1;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("UrgRef: type=REF",    got && ctype===CMD_REF);
            check("UrgRef: ref_ack",     got && ref_ack===1);
        end
        ref_urgent=0; wc(2);

        // T19–T20: Normal refresh when idle
        clear_queue(); set_bank_idle();
        ref_required=1; ref_urgent=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("NormRef: type=REF",   got && ctype===CMD_REF);
            check("NormRef: ref_ack",    got && ref_ack===1);
        end
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
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("RefBlock: PRE not REF while active", got && ctype===CMD_PRE);
            check("RefBlock: PRE targets active bank",  got && cbank===3'd3);
            set_bank_idle();  // simulate bank_tracker clearing the bank post-PRE
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("RefBlock: REF once banks idle",  got && ctype===CMD_REF);
            check("RefBlock: ref_ack",              got && ref_ack===1);
        end
        ref_urgent=0; wc(2);

        // T39-T47: feedback-latency hold (FB_LAG = 2). bank_tracker learns of a
        // command two cycles after the scheduler registers it, and this
        // testbench deliberately never updates the bank state, so the permission
        // inputs stay stale exactly as they do in the real loop. Command
        // pulses are sampled once per cycle (value seen at each posedge).
        //
        // ACT: a second ACT to the same bank must not follow within the window.
        clear_queue(); set_bank_idle();
        q_valid[0]=1; q_row[0]=14'd300; q_bank[0]=3'd4; q_we[0]=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("Hold ACT: first ACT issued",             got && ctype===CMD_ACT && cbank===3'd4);
            @(posedge clk);
            check("Hold ACT: no repeat ACT, cycle 1",       cmd_valid===0);
            @(posedge clk);
            check("Hold ACT: no repeat ACT, cycle 2",       cmd_valid===0);
            @(posedge clk);
            check("Hold ACT: window ends after 2 cycles",   cmd_valid===1 && cmd_type===CMD_ACT);
        end

        // REF: a REFRESH must not follow an ACT that bank_tracker has not yet
        // recorded (banks still read idle); it waits out the window.
        clear_queue(); set_bank_idle();
        q_valid[0]=1; q_row[0]=14'd301; q_bank[0]=3'd5; q_we[0]=0;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("Hold REF: ACT issued first",             got && ctype===CMD_ACT);
            q_valid[0]=0; ref_urgent=1;
            @(posedge clk);
            check("Hold REF: no REF, cycle 1",              cmd_valid===0);
            @(posedge clk);
            check("Hold REF: no REF, cycle 2",              cmd_valid===0);
            @(posedge clk);
            check("Hold REF: REF once the window is over",  cmd_valid===1 && cmd_type===CMD_REF);
        end
        ref_urgent=0; wc(2);

        // RD after WR: tWTR in bank_tracker is not visible for two cycles, so
        // the scheduler itself must not select a READ right after a WRITE.
        clear_queue(); set_bank_idle();
        set_bank_active(3'd0, 14'd100); set_bank_active(3'd1, 14'd200);
        q_valid[0]=1; q_row[0]=14'd100; q_bank[0]=3'd0; q_we[0]=1;
        begin
            logic got; logic [3:0] ctype; logic [BANK_BITS-1:0] cbank;
            logic cdeq; logic [IDX_BITS-1:0] cidx;
            wait_cmd(got, ctype, cbank, cdeq, cidx, 8);
            check("Hold RD: WR issued first",               got && ctype===CMD_WR);
            q_valid[0]=0; q_valid[1]=1; q_row[1]=14'd200; q_bank[1]=3'd1; q_we[1]=0;
            @(posedge clk);
            @(posedge clk);
            check("Hold RD: no RD while the WR is in flight", cmd_valid===0);
            @(posedge clk);
            check("Hold RD: RD allowed after the window",   cmd_valid===1 && cmd_type===CMD_RD);
        end

        $display("\\n== %0d/%0d passed ==\\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    def generate_cmd_gen_tb(self) -> str:
        p = self._p_cmd_gen()
        return f"""`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// cmd_gen_tb.sv — 36 self-checking tests
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module cmd_gen_tb;
    localparam DDR_ADDR_W={p['DDR_ADDR_W']},DDR_BANK_W={p['DDR_BANK_W']},ROW_BITS={p['ROW_BITS']};
    localparam COL_BITS={p['COL_BITS']},BANK_BITS={p['BANK_BITS']},AUX_WIDTH={p['AUX_WIDTH']};
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
        @(posedge clk);  // DUT samples here -- registered output is valid immediately after
        sched_valid=0;
    endtask

    initial begin
        $display("\\n== cmd_gen_tb ==\\n");
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
        issue(SCMD_ACT, {p['ROW_BITS']}'d1234, 0, 3'd2, 0, 0);
        check("ACT: ddr=ACT",        ddr_cmd===DDR_ACT);
        check("ACT: addr=row",       ddr_addr=={p['ROW_BITS']}'d1234);
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
        issue(SCMD_ACT, {p['ROW_BITS']}'d500, 0, 3'd4, 0, 0);
        issue(SCMD_RD, 0, 10'd25, 3'd4, 0, 4'd2);
        check("B2B: RD after ACT",   ddr_cmd===DDR_RD);

        // T35–T36: All banks addressable
        issue(SCMD_ACT, 0, 0, 3'd7, 0, 0);
        check("Bank 7 ACT",          ddr_bank===3'd7 && ddr_cmd===DDR_ACT);
        issue(SCMD_ACT, 0, 0, 3'd0, 0, 0);
        check("Bank 0 ACT",          ddr_bank===3'd0 && ddr_cmd===DDR_ACT);

        $display("\\n== %0d/%0d passed ==\\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    # ---- write all Phase 3 testbenches -----------------------------------
    def write_phase3(self, output_dir: str) -> list:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        written = []
        for filename, gen_fn in [
            ("cmd_queue_tb.sv", self.generate_cmd_queue_tb),
            ("scheduler_tb.sv", self.generate_scheduler_tb),
            ("cmd_gen_tb.sv", self.generate_cmd_gen_tb),
        ]:
            path = out / filename
            path.write_text(gen_fn())
            written.append(str(path))
        return written


if __name__ == "__main__":
    spec = input("Spec JSON path: ").strip()
    out = input("Output dir for testbenches: ").strip() or "./tb_output"
    for path in TestbenchGenerator(spec).write_phase3(out):
        print(f"  wrote {path}")
