#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 SCHEDULER AGENT (Phase 3)                            ║
║  FR-FCFS scheduler with open-page policy.                            ║
║  Generates: scheduler.sv + scheduler_tb.sv + scheduler_manifest.json ║
╚══════════════════════════════════════════════════════════════════════╝
"""
import json, os, sys, math
from pathlib import Path
from datetime import datetime


class SchedulerAgent:
    def __init__(self, spec_path, output_dir="./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        with open(spec_path) as f: self.spec = json.load(f)
        self.geo = self.spec["memory_geometry"]
        self.arch = self.spec["controller_architecture"]
        self.host = self.spec["host_interface"]
        self.dc = self.spec["timing_model"]["$derived_cycles"]
        self.p = self._derive()

    def _derive(self):
        p = {}
        p["DEPTH"]       = self.arch["command_queue_depth"]
        p["IDX_BITS"]    = self.arch["$derived"]["queue_index_bits"]
        p["ROW_BITS"]    = self.geo["row_bits"]
        p["COL_BITS"]    = self.geo["column_bits"]
        p["BANK_BITS"]   = self.geo["bank_bits"]
        p["NUM_BANKS"]   = 2 ** p["BANK_BITS"]
        p["AUX_WIDTH"]   = self.arch.get("aux_width", 4)
        p["POLICY"]      = self.arch["scheduler_policy"]     # fr_fcfs
        p["ROW_POLICY"]  = self.arch["row_policy"]           # open_page
        return p

    def generate_rtl(self):
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        return f"""////////////////////////////////////////////////////////////////////////////////
// Module:    scheduler
// Generated: {ts}
// Agent:     Scheduler Agent (Phase 3)
//
// FR-FCFS (First-Ready First-Come-First-Served) scheduler.
// Open-page policy: row-hit requests prioritized over row-miss.
// Reads cmd_queue entries and bank_tracker permissions.
// Issues one command per cycle to cmd_gen.
////////////////////////////////////////////////////////////////////////////////

module scheduler #(
    parameter DEPTH     = {p['DEPTH']},
    parameter IDX_BITS  = {p['IDX_BITS']},
    parameter ROW_BITS  = {p['ROW_BITS']},
    parameter COL_BITS  = {p['COL_BITS']},
    parameter BANK_BITS = {p['BANK_BITS']},
    parameter NUM_BANKS = {p['NUM_BANKS']},
    parameter AUX_WIDTH = {p['AUX_WIDTH']}
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── From cmd_queue (lookahead) ──
    input  logic [DEPTH-1:0]        q_valid,
    input  logic [ROW_BITS-1:0]     q_row     [DEPTH],
    input  logic [COL_BITS-1:0]     q_col     [DEPTH],
    input  logic [BANK_BITS-1:0]    q_bank    [DEPTH],
    input  logic                    q_we      [DEPTH],
    input  logic [AUX_WIDTH-1:0]    q_aux     [DEPTH],

    // ── From bank_tracker ──
    input  logic [NUM_BANKS-1:0]    bank_is_active,
    input  logic [ROW_BITS-1:0]     bank_open_row [NUM_BANKS],
    input  logic [NUM_BANKS-1:0]    bank_act_allowed,
    input  logic [NUM_BANKS-1:0]    bank_rd_allowed,
    input  logic [NUM_BANKS-1:0]    bank_wr_allowed,
    input  logic [NUM_BANKS-1:0]    bank_pre_allowed,

    // ── From refresh_ctrl ──
    input  logic                    ref_required,
    input  logic                    ref_urgent,
    output logic                    ref_ack,

    // ── Dequeue grant (to cmd_queue) ──
    output logic                    deq_grant,
    output logic [IDX_BITS-1:0]     deq_idx,

    // ── Command output (to cmd_gen) ──
    output logic                    cmd_valid,
    output logic [3:0]              cmd_type,       // ACT/RD/WR/PRE/REF/NOP
    output logic [ROW_BITS-1:0]     cmd_row,
    output logic [COL_BITS-1:0]     cmd_col,
    output logic [BANK_BITS-1:0]    cmd_bank,
    output logic                    cmd_we,
    output logic [AUX_WIDTH-1:0]    cmd_aux
);

    // Command type encoding
    localparam CMD_NOP = 4'd0;
    localparam CMD_ACT = 4'd1;
    localparam CMD_RD  = 4'd2;
    localparam CMD_WR  = 4'd3;
    localparam CMD_PRE = 4'd4;
    localparam CMD_REF = 4'd5;

    // ════════════════════════════════════════════════════
    // Candidate classification
    // ════════════════════════════════════════════════════
    // For each queue entry: is it a row-hit? is it ready for CAS?
    logic [DEPTH-1:0] is_row_hit;
    logic [DEPTH-1:0] is_cas_ready;  // bank active + row hit + timing ok
    logic [DEPTH-1:0] is_act_needed; // bank idle or wrong row

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            logic [BANK_BITS-1:0] b;
            b = q_bank[i];
            is_row_hit[i]   = q_valid[i] && bank_is_active[b] &&
                               (bank_open_row[b] == q_row[i]);
            is_cas_ready[i] = is_row_hit[i] &&
                               (q_we[i] ? bank_wr_allowed[b] : bank_rd_allowed[b]);
            is_act_needed[i] = q_valid[i] && (!bank_is_active[b] ||
                               (bank_open_row[b] != q_row[i]));
        end
    end

    // ════════════════════════════════════════════════════
    // FR-FCFS selection: row-hit CAS > any ACT-needed
    // ════════════════════════════════════════════════════
    logic                    sel_valid;
    logic [IDX_BITS-1:0]     sel_idx;
    logic [3:0]              sel_type;
    logic                    sel_is_ref;

    always_comb begin
        sel_valid  = 1'b0;
        sel_idx    = '0;
        sel_type   = CMD_NOP;
        sel_is_ref = 1'b0;

        // Priority 1: Urgent refresh preempts everything
        if (ref_urgent) begin
            sel_valid  = 1'b1;
            sel_type   = CMD_REF;
            sel_is_ref = 1'b1;
        end
        // Priority 2: Row-hit CAS (first-come = lowest index)
        else begin
            for (int i = 0; i < DEPTH; i++) begin
                if (is_cas_ready[i] && !sel_valid) begin
                    sel_valid = 1'b1;
                    sel_idx   = i[IDX_BITS-1:0];
                    sel_type  = q_we[i] ? CMD_WR : CMD_RD;
                end
            end
            // Priority 3: ACT for row-miss (need PRE first if bank active with wrong row)
            if (!sel_valid) begin
                for (int i = 0; i < DEPTH; i++) begin
                    if (is_act_needed[i] && !sel_valid) begin
                        logic [BANK_BITS-1:0] b;
                        b = q_bank[i];
                        if (bank_is_active[b] && bank_pre_allowed[b]) begin
                            // Need PRE first
                            sel_valid = 1'b1;
                            sel_idx   = i[IDX_BITS-1:0];
                            sel_type  = CMD_PRE;
                        end else if (!bank_is_active[b] && bank_act_allowed[b]) begin
                            // Bank idle, can ACT
                            sel_valid = 1'b1;
                            sel_idx   = i[IDX_BITS-1:0];
                            sel_type  = CMD_ACT;
                        end
                    end
                end
            end
            // Priority 4: Normal refresh (when no other work)
            if (!sel_valid && ref_required) begin
                sel_valid  = 1'b1;
                sel_type   = CMD_REF;
                sel_is_ref = 1'b1;
            end
        end
    end

    // ════════════════════════════════════════════════════
    // Output registration
    // ════════════════════════════════════════════════════
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cmd_valid <= 1'b0;
            cmd_type  <= CMD_NOP;
            cmd_row   <= '0;
            cmd_col   <= '0;
            cmd_bank  <= '0;
            cmd_we    <= 1'b0;
            cmd_aux   <= '0;
            deq_grant <= 1'b0;
            deq_idx   <= '0;
            ref_ack   <= 1'b0;
        end else begin
            cmd_valid <= sel_valid;
            cmd_type  <= sel_type;
            deq_grant <= 1'b0;
            ref_ack   <= 1'b0;

            if (sel_valid) begin
                if (sel_is_ref) begin
                    ref_ack  <= 1'b1;
                    cmd_bank <= '0;
                    cmd_row  <= '0;
                    cmd_col  <= '0;
                    cmd_we   <= 1'b0;
                    cmd_aux  <= '0;
                end else begin
                    cmd_row  <= q_row[sel_idx];
                    cmd_col  <= q_col[sel_idx];
                    cmd_bank <= q_bank[sel_idx];
                    cmd_we   <= q_we[sel_idx];
                    cmd_aux  <= q_aux[sel_idx];
                    // Dequeue only on CAS (RD/WR) — ACT/PRE don't consume entry
                    if (sel_type == CMD_RD || sel_type == CMD_WR) begin
                        deq_grant <= 1'b1;
                        deq_idx   <= sel_idx;
                    end
                end
            end
        end
    end

endmodule
"""

    def generate_tb(self):
        p = self.p
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

        $display("\\n== %0d/%0d passed ==\\n", pass_count, pass_count+fail_count);
        $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    def generate_manifest(self):
        p = self.p
        return {
            "module_name": "scheduler", "file": "scheduler.sv",
            "phase": 3, "agent": "scheduler_agent",
            "dependencies": ["cmd_queue", "bank_tracker", "refresh_ctrl"],
            "spec_version": self.spec.get("schema_version"),
            "parameters": {k: v for k, v in p.items()},
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "queue_lookahead": [
                    {"name": "q_valid", "width": p["DEPTH"], "dir": "input", "source": "cmd_queue.entry_valid"},
                    {"name": "q_row", "width": f"{p['DEPTH']}x{p['ROW_BITS']}", "dir": "input", "source": "cmd_queue.entry_row"},
                    {"name": "q_col", "width": f"{p['DEPTH']}x{p['COL_BITS']}", "dir": "input", "source": "cmd_queue.entry_col"},
                    {"name": "q_bank", "width": f"{p['DEPTH']}x{p['BANK_BITS']}", "dir": "input", "source": "cmd_queue.entry_bank"},
                    {"name": "q_we", "width": f"{p['DEPTH']}x1", "dir": "input", "source": "cmd_queue.entry_we"},
                    {"name": "q_aux", "width": f"{p['DEPTH']}x{p['AUX_WIDTH']}", "dir": "input", "source": "cmd_queue.entry_aux"},
                ],
                "bank_status": [
                    {"name": "bank_is_active", "width": p["NUM_BANKS"], "dir": "input", "source": "bank_tracker.bank_is_active"},
                    {"name": "bank_open_row", "width": f"{p['NUM_BANKS']}x{p['ROW_BITS']}", "dir": "input", "source": "bank_tracker.bank_open_row"},
                    {"name": "bank_act_allowed", "width": p["NUM_BANKS"], "dir": "input", "source": "bank_tracker.bank_act_allowed"},
                    {"name": "bank_rd_allowed", "width": p["NUM_BANKS"], "dir": "input", "source": "bank_tracker.bank_rd_allowed"},
                    {"name": "bank_wr_allowed", "width": p["NUM_BANKS"], "dir": "input", "source": "bank_tracker.bank_wr_allowed"},
                    {"name": "bank_pre_allowed", "width": p["NUM_BANKS"], "dir": "input", "source": "bank_tracker.bank_pre_allowed"},
                ],
                "refresh_if": [
                    {"name": "ref_required", "width": 1, "dir": "input", "source": "refresh_ctrl.ref_required"},
                    {"name": "ref_urgent", "width": 1, "dir": "input", "source": "refresh_ctrl.ref_urgent"},
                    {"name": "ref_ack", "width": 1, "dir": "output"},
                ],
                "cmd_out": [
                    {"name": "cmd_valid", "width": 1, "dir": "output"},
                    {"name": "cmd_type", "width": 4, "dir": "output"},
                    {"name": "cmd_row", "width": p["ROW_BITS"], "dir": "output"},
                    {"name": "cmd_col", "width": p["COL_BITS"], "dir": "output"},
                    {"name": "cmd_bank", "width": p["BANK_BITS"], "dir": "output"},
                    {"name": "cmd_we", "width": 1, "dir": "output"},
                    {"name": "cmd_aux", "width": p["AUX_WIDTH"], "dir": "output"},
                    {"name": "deq_grant", "width": 1, "dir": "output"},
                    {"name": "deq_idx", "width": p["IDX_BITS"], "dir": "output"},
                ],
            },
        }

    def run(self):
        hdr = "=" * 62
        print(f"{hdr}\n  SCHEDULER AGENT\n  Spec: {self.spec_path}\n{hdr}")
        for k, v in self.p.items(): print(f"    {k:20s} = {v}")
        rtl = self.generate_rtl()
        tb = self.generate_tb()
        manifest = self.generate_manifest()
        (self.output_dir / "scheduler.sv").write_text(rtl)
        (self.output_dir / "scheduler_tb.sv").write_text(tb)
        (self.output_dir / "scheduler_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  V scheduler.sv        ({rtl.count(chr(10))} lines)")
        print(f"  V scheduler_tb.sv     ({tb.count(chr(10))} lines)")
        print(f"  V scheduler_manifest.json")
        print(f"\n{hdr}\n  DONE — scheduler\n{hdr}")
        return {"status": "success", "module": "scheduler", "phase": 3,
                "rtl_path": str(self.output_dir / "scheduler.sv"),
                "tb_path": str(self.output_dir / "scheduler_tb.sv"),
                "lines": rtl.count('\n'), "manifest": manifest}

if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output dir: ").strip() or "./output"
    r = SchedulerAgent(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)