#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 SCHEDULER GENERATOR (Phase 3)                            ║
║  FR-FCFS scheduler with open-page policy.                            ║
║  Generates: scheduler.sv + scheduler_tb.sv + scheduler_manifest.json ║
╚══════════════════════════════════════════════════════════════════════╝
"""
import json, os, sys, math
from pathlib import Path
from datetime import datetime

_HERE = os.path.dirname(os.path.abspath(__file__))
_SCRIPTS_DIR = os.path.dirname(_HERE)
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)
from manifest_stamp import stamp


class SchedulerGenerator:
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
        return f"""////////////////////////////////////////////////////////////////////////////////
// Module:    scheduler
// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)
// Generator:     Scheduler Generator (Phase 3)
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

    // JEDEC: REF is only legal once every bank is precharged.
    wire all_banks_idle = ~(|bank_is_active);

    // ════════════════════════════════════════════════════
    // Feedback-latency hold (FB_LAG = 2 cycles)
    // ════════════════════════════════════════════════════
    // A command selected in cycle N is registered at the end of N (cmd_*),
    // cmd_gen registers its fb_* strobes at the end of N+1, and bank_tracker
    // updates its state/counters at the end of N+2. So the permissions this
    // module reads in cycles N+1 and N+2 do not yet reflect that command, and
    // selecting from them re-issues it (ACT to an already-active bank, an
    // ACT inside tRC/tRRD, a REF or RD straight after the PRE/ACT/WR that
    // should have blocked it). Track what was issued in the last two cycles
    // (cmd_* now, d1_* one cycle ago) and hold anything those could change.
    logic                 d1_valid;
    logic [3:0]           d1_type;
    logic [BANK_BITS-1:0] d1_bank;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            d1_valid <= 1'b0;
            d1_type  <= CMD_NOP;
            d1_bank  <= '0;
        end else begin
            d1_valid <= cmd_valid;
            d1_type  <= cmd_type;
            d1_bank  <= cmd_bank;
        end
    end

    logic [NUM_BANKS-1:0] inflight_any;    // any command to this bank in flight
    logic [NUM_BANKS-1:0] inflight_state;  // an ACT or PRE to this bank in flight
    logic                 inflight_ref;    // a REFRESH in flight (all banks)
    logic                 inflight_act;    // an ACT in flight (tRRD / tFAW, any bank)
    logic                 inflight_wr;     // a WRITE in flight (tWTR, any bank)
    always_comb begin
        inflight_any   = '0;
        inflight_state = '0;
        inflight_ref   = 1'b0;
        inflight_act   = 1'b0;
        inflight_wr    = 1'b0;
        if (cmd_valid) begin
            if (cmd_type == CMD_REF) inflight_ref = 1'b1;
            else if (cmd_type != CMD_NOP) begin
                inflight_any[cmd_bank] = 1'b1;
                if (cmd_type == CMD_ACT || cmd_type == CMD_PRE) inflight_state[cmd_bank] = 1'b1;
                if (cmd_type == CMD_ACT) inflight_act = 1'b1;
                if (cmd_type == CMD_WR)  inflight_wr  = 1'b1;
            end
        end
        if (d1_valid) begin
            if (d1_type == CMD_REF) inflight_ref = 1'b1;
            else if (d1_type != CMD_NOP) begin
                inflight_any[d1_bank] = 1'b1;
                if (d1_type == CMD_ACT || d1_type == CMD_PRE) inflight_state[d1_bank] = 1'b1;
                if (d1_type == CMD_ACT) inflight_act = 1'b1;
                if (d1_type == CMD_WR)  inflight_wr  = 1'b1;
            end
        end
    end

    // REF needs every bank idle AND past tRP/tRC/tRFC (bank_act_allowed
    // already folds those counters in), and no ACT/REF still in flight.
    wire ref_ok = all_banks_idle && (&bank_act_allowed) && !inflight_act && !inflight_ref;

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            logic [BANK_BITS-1:0] b;
            logic recently_granted;
            b = q_bank[i];
            // deq_grant/deq_idx are this module's OWN registered outputs
            // from last cycle -- cmd_queue's own q_valid/q_row/... won't
            // reflect the dequeue for (at least) one more cycle after that,
            // so without this guard the same entry gets re-selected and
            // re-granted every cycle until the queue catches up (observed:
            // 19 enqueued, 16 dequeued -- see
            // Frontend2/VALIDATION_INTEGRATION_PLAN.md Defect 1).
            recently_granted = deq_grant && (deq_idx == i[IDX_BITS-1:0]);
            is_row_hit[i]   = q_valid[i] && bank_is_active[b] &&
                               (bank_open_row[b] == q_row[i]);
            is_cas_ready[i] = is_row_hit[i] && !recently_granted &&
                               !inflight_state[b] && !inflight_ref &&
                               (q_we[i] ? bank_wr_allowed[b] : (bank_rd_allowed[b] && !inflight_wr));
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
    // Most commands source row/col/bank/we/aux from the winning queue entry
    // (q_*[sel_idx]). A refresh-driven forced PRE (below) isn't tied to any
    // queue entry -- it only carries a bank -- so this flag picks which
    // source the output-registration stage uses.
    logic                    sel_from_queue;
    logic [BANK_BITS-1:0]    sel_bank;

    always_comb begin
        sel_valid      = 1'b0;
        sel_idx        = '0;
        sel_type       = CMD_NOP;
        sel_is_ref     = 1'b0;
        sel_from_queue = 1'b1;
        sel_bank       = '0;

        // Priority 1: Urgent refresh. JEDEC requires every bank precharged
        // before REF -- if any bank is still open, force-precharge it
        // (lowest-numbered active + precharge-ready bank) instead of
        // issuing REF early; only issue REF once all_banks_idle. If the
        // active bank(s) aren't precharge-ready yet (tRAS/tWR/etc. still
        // counting down), this cycle is a NOP and the next cycle retries --
        // never a raw un-gated REF (see Defect 5 in
        // Frontend2/VALIDATION_INTEGRATION_PLAN.md).
        if (ref_urgent) begin
            if (ref_ok) begin
                sel_valid  = 1'b1;
                sel_type   = CMD_REF;
                sel_is_ref = 1'b1;
            end else begin
                for (int b = 0; b < NUM_BANKS; b++) begin
                    if (bank_is_active[b] && bank_pre_allowed[b] && !inflight_any[b] && !inflight_ref && !sel_valid) begin
                        sel_valid      = 1'b1;
                        sel_type       = CMD_PRE;
                        sel_from_queue = 1'b0;
                        sel_bank       = b[BANK_BITS-1:0];
                    end
                end
            end
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
                        if (bank_is_active[b] && bank_pre_allowed[b] && !inflight_any[b] && !inflight_ref) begin
                            // Need PRE first
                            sel_valid = 1'b1;
                            sel_idx   = i[IDX_BITS-1:0];
                            sel_type  = CMD_PRE;
                        end else if (!bank_is_active[b] && bank_act_allowed[b] && !inflight_any[b] && !inflight_act && !inflight_ref) begin
                            // Bank idle, can ACT
                            sel_valid = 1'b1;
                            sel_idx   = i[IDX_BITS-1:0];
                            sel_type  = CMD_ACT;
                        end
                    end
                end
            end
            // Priority 4: Normal refresh (when no other work) -- same
            // idle-gate / force-precharge-first behavior as urgent refresh.
            if (!sel_valid && ref_required) begin
                if (ref_ok) begin
                    sel_valid  = 1'b1;
                    sel_type   = CMD_REF;
                    sel_is_ref = 1'b1;
                end else begin
                    for (int b = 0; b < NUM_BANKS; b++) begin
                        if (bank_is_active[b] && bank_pre_allowed[b] && !inflight_any[b] && !inflight_ref && !sel_valid) begin
                            sel_valid      = 1'b1;
                            sel_type       = CMD_PRE;
                            sel_from_queue = 1'b0;
                            sel_bank       = b[BANK_BITS-1:0];
                        end
                    end
                end
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
                end else if (!sel_from_queue) begin
                    // Forced precharge ahead of refresh -- bank only, no
                    // backing queue entry, so nothing to dequeue.
                    cmd_bank <= sel_bank;
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

    def generate_manifest(self):
        p = self.p
        return {
            **stamp(self.spec),
            "module_name": "scheduler", "file": "scheduler.sv",
            "phase": 3, "generator": "scheduler_gen",
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
        print(f"{hdr}\n  SCHEDULER GENERATOR\n  Spec: {self.spec_path}\n{hdr}")
        for k, v in self.p.items(): print(f"    {k:20s} = {v}")
        rtl = self.generate_rtl()
        manifest = self.generate_manifest()
        (self.output_dir / "scheduler.sv").write_text(rtl)
        (self.output_dir / "scheduler_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  V scheduler.sv        ({rtl.count(chr(10))} lines)")
        print(f"  V scheduler_manifest.json")
        print(f"\n{hdr}\n  DONE — scheduler\n{hdr}")
        return {"status": "success", "module": "scheduler", "phase": 3,
                "rtl_path": str(self.output_dir / "scheduler.sv"),
                "lines": rtl.count('\n'), "manifest": manifest}

if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output dir: ").strip() or "./output"
    r = SchedulerGenerator(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)