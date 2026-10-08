#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 COMMAND QUEUE GENERATOR (Phase 3)                        ║
║  16-deep request queue between address decoder and scheduler.        ║
║  Generates: cmd_queue.sv + cmd_queue_tb.sv + cmd_queue_manifest.json ║
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


class CmdQueueGenerator:
    def __init__(self, spec_path, output_dir="./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        with open(spec_path) as f:
            self.spec = json.load(f)
        self.geo = self.spec["memory_geometry"]
        self.arch = self.spec["controller_architecture"]
        self.host = self.spec["host_interface"]
        self.p = self._derive()

    def _derive(self):
        p = {}
        p["DEPTH"]      = self.arch["command_queue_depth"]       # 16
        p["IDX_BITS"]   = self.arch["$derived"]["queue_index_bits"]  # 4
        p["ROW_BITS"]   = self.geo["row_bits"]                   # 14
        p["COL_BITS"]   = self.geo["column_bits"]                # 10
        p["BANK_BITS"]  = self.geo["bank_bits"]                  # 3
        p["AUX_WIDTH"]  = self.arch.get("aux_width", 4)         # 4
        p["DATA_WIDTH"] = self.host["data_width_bits"]           # 32
        # Entry width: row + col + bank + we(1) + aux
        p["ENTRY_W"] = p["ROW_BITS"] + p["COL_BITS"] + p["BANK_BITS"] + 1 + p["AUX_WIDTH"]
        return p

    def generate_rtl(self):
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        return f"""////////////////////////////////////////////////////////////////////////////////
// Module:    cmd_queue
// Generated: {ts}
// Generator:     Command Queue Generator (Phase 3)
//
// {p['DEPTH']}-deep command queue. Accepts decoded requests from addr_decoder,
// presents oldest entries to scheduler via lookahead window.
// FIFO with per-entry valid bits, enqueue on push, dequeue on grant.
////////////////////////////////////////////////////////////////////////////////

module cmd_queue #(
    parameter DEPTH     = {p['DEPTH']},
    parameter IDX_BITS  = {p['IDX_BITS']},
    parameter ROW_BITS  = {p['ROW_BITS']},
    parameter COL_BITS  = {p['COL_BITS']},
    parameter BANK_BITS = {p['BANK_BITS']},
    parameter AUX_WIDTH = {p['AUX_WIDTH']}
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── Enqueue interface (from addr_decoder / wb_port) ──
    input  logic                    enq_valid,
    output logic                    enq_ready,
    input  logic [ROW_BITS-1:0]     enq_row,
    input  logic [COL_BITS-1:0]     enq_col,
    input  logic [BANK_BITS-1:0]    enq_bank,
    input  logic                    enq_we,         // 1=write, 0=read
    input  logic [AUX_WIDTH-1:0]    enq_aux,        // tag / transaction ID

    // ── Dequeue interface (from scheduler) ──
    input  logic                    deq_grant,      // scheduler grants this entry
    input  logic [IDX_BITS-1:0]     deq_idx,        // which entry to dequeue

    // ── Lookahead window (to scheduler) ──
    output logic [DEPTH-1:0]        entry_valid,
    output logic [ROW_BITS-1:0]     entry_row   [DEPTH],
    output logic [COL_BITS-1:0]     entry_col   [DEPTH],
    output logic [BANK_BITS-1:0]    entry_bank  [DEPTH],
    output logic                    entry_we    [DEPTH],
    output logic [AUX_WIDTH-1:0]    entry_aux   [DEPTH],

    // ── Status ──
    output logic                    queue_full,
    output logic                    queue_empty,
    output logic [IDX_BITS:0]       queue_count     // 0..DEPTH
);

    // ════════════════════════════════════════════════════
    // Storage
    // ════════════════════════════════════════════════════
    logic [ROW_BITS-1:0]    mem_row   [DEPTH];
    logic [COL_BITS-1:0]    mem_col   [DEPTH];
    logic [BANK_BITS-1:0]   mem_bank  [DEPTH];
    logic                   mem_we    [DEPTH];
    logic [AUX_WIDTH-1:0]   mem_aux   [DEPTH];
    logic [DEPTH-1:0]       mem_valid;

    // Count
    logic [IDX_BITS:0] count;

    assign queue_count = count;
    assign queue_full  = (count == DEPTH);
    assign queue_empty = (count == '0);
    assign enq_ready   = !queue_full;

    // Output lookahead
    always_comb begin
        entry_valid = mem_valid;
        for (int i = 0; i < DEPTH; i++) begin
            entry_row[i]  = mem_row[i];
            entry_col[i]  = mem_col[i];
            entry_bank[i] = mem_bank[i];
            entry_we[i]   = mem_we[i];
            entry_aux[i]  = mem_aux[i];
        end
    end

    // ════════════════════════════════════════════════════
    // Enqueue / Dequeue logic
    // ════════════════════════════════════════════════════
    // Find first free slot for enqueue
    logic [IDX_BITS-1:0] free_slot;
    logic                free_found;

    always_comb begin
        free_slot  = '0;
        free_found = 1'b0;
        for (int i = 0; i < DEPTH; i++) begin
            if (!mem_valid[i] && !free_found) begin
                free_slot  = i[IDX_BITS-1:0];
                free_found = 1'b1;
            end
        end
    end

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem_valid <= '0;
            count     <= '0;
            for (i = 0; i < DEPTH; i++) begin
                mem_row[i]  <= '0;
                mem_col[i]  <= '0;
                mem_bank[i] <= '0;
                mem_we[i]   <= '0;
                mem_aux[i]  <= '0;
            end
        end else begin
            // Dequeue
            if (deq_grant && mem_valid[deq_idx]) begin
                mem_valid[deq_idx] <= 1'b0;
                count <= count - 1'b1;
            end

            // Enqueue
            if (enq_valid && enq_ready && free_found) begin
                mem_row[free_slot]   <= enq_row;
                mem_col[free_slot]   <= enq_col;
                mem_bank[free_slot]  <= enq_bank;
                mem_we[free_slot]    <= enq_we;
                mem_aux[free_slot]   <= enq_aux;
                mem_valid[free_slot] <= 1'b1;
                count <= count + 1'b1;
            end

            // Simultaneous enq + deq: adjust count
            if (enq_valid && enq_ready && free_found && deq_grant && mem_valid[deq_idx])
                count <= count;  // net zero
        end
    end

endmodule
"""

    def generate_manifest(self):
        p = self.p
        return {
            **stamp(self.spec),
            "module_name": "cmd_queue", "file": "cmd_queue.sv",
            "phase": 3, "generator": "cmd_queue_gen",
            "dependencies": ["addr_decoder", "wb_port"],
            "spec_version": self.spec.get("schema_version"),
            "parameters": {k: v for k, v in p.items()},
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "enqueue": [
                    {"name": "enq_valid", "width": 1, "dir": "input", "source": "wb_port.req_valid"},
                    {"name": "enq_ready", "width": 1, "dir": "output"},
                    {"name": "enq_row", "width": p["ROW_BITS"], "dir": "input", "source": "addr_decoder.dec_row"},
                    {"name": "enq_col", "width": p["COL_BITS"], "dir": "input", "source": "addr_decoder.dec_col"},
                    {"name": "enq_bank", "width": p["BANK_BITS"], "dir": "input", "source": "addr_decoder.dec_bank"},
                    {"name": "enq_we", "width": 1, "dir": "input", "source": "wb_port.req_we"},
                    {"name": "enq_aux", "width": p["AUX_WIDTH"], "dir": "input", "source": "wb_port.req_aux"},
                ],
                "dequeue": [
                    {"name": "deq_grant", "width": 1, "dir": "input", "source": "scheduler.deq_grant"},
                    {"name": "deq_idx", "width": p["IDX_BITS"], "dir": "input", "source": "scheduler.deq_idx"},
                ],
                "lookahead": [
                    {"name": "entry_valid", "width": p["DEPTH"], "dir": "output"},
                    {"name": "entry_row", "width": f"{p['DEPTH']}x{p['ROW_BITS']}", "dir": "output"},
                    {"name": "entry_col", "width": f"{p['DEPTH']}x{p['COL_BITS']}", "dir": "output"},
                    {"name": "entry_bank", "width": f"{p['DEPTH']}x{p['BANK_BITS']}", "dir": "output"},
                    {"name": "entry_we", "width": f"{p['DEPTH']}x1", "dir": "output"},
                    {"name": "entry_aux", "width": f"{p['DEPTH']}x{p['AUX_WIDTH']}", "dir": "output"},
                ],
                "status": [
                    {"name": "queue_full", "width": 1, "dir": "output"},
                    {"name": "queue_empty", "width": 1, "dir": "output"},
                    {"name": "queue_count", "width": p["IDX_BITS"]+1, "dir": "output"},
                ],
            },
        }

    def run(self):
        hdr = "=" * 62
        print(f"{hdr}\n  COMMAND QUEUE GENERATOR\n  Spec: {self.spec_path}\n{hdr}")
        errs = []
        if self.p["DEPTH"] < 1: errs.append("DEPTH < 1")
        if errs:
            for e in errs: print(f"  X {e}")
            return {"status": "error", "errors": errs}
        print("  V Valid")
        for k, v in self.p.items(): print(f"    {k:20s} = {v}")

        rtl = self.generate_rtl()
        manifest = self.generate_manifest()

        (self.output_dir / "cmd_queue.sv").write_text(rtl)
        (self.output_dir / "cmd_queue_manifest.json").write_text(json.dumps(manifest, indent=2))

        print(f"  V cmd_queue.sv        ({rtl.count(chr(10))} lines)")
        print(f"  V cmd_queue_manifest.json")
        print(f"\n{hdr}\n  DONE — cmd_queue\n{hdr}")

        return {"status": "success", "module": "cmd_queue", "phase": 3,
                "rtl_path": str(self.output_dir / "cmd_queue.sv"),
                "lines": rtl.count('\n'), "manifest": manifest}


if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output dir (./output): ").strip() or "./output"
    r = CmdQueueGenerator(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)
