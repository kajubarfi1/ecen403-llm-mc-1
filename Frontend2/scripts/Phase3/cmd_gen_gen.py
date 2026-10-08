#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 COMMAND GENERATOR GENERATOR (Phase 3)                    ║
║  Encodes scheduled commands to DDR3 pin-level signals.               ║
║  Generates: cmd_gen.sv + cmd_gen_tb.sv + cmd_gen_manifest.json       ║
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


class CmdGenGenerator:
    def __init__(self, spec_path, output_dir="./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        with open(spec_path) as f: self.spec = json.load(f)
        self.geo = self.spec["memory_geometry"]
        self.arch = self.spec["controller_architecture"]
        self.p = self._derive()

    def _derive(self):
        p = {}
        p["ROW_BITS"]  = self.geo["row_bits"]
        p["COL_BITS"]  = self.geo["column_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["DDR_ADDR_W"] = max(p["ROW_BITS"], p["COL_BITS"])  # 14
        p["DDR_BANK_W"] = p["BANK_BITS"]  # 3
        p["AUX_WIDTH"]  = self.arch.get("aux_width", 4)
        return p

    def generate_rtl(self):
        p = self.p
        return f"""////////////////////////////////////////////////////////////////////////////////
// Module:    cmd_gen
// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)
// Generator:     Command Generator Generator (Phase 3)
//
// Translates scheduler command type → DDR3 pin-level encoding.
// Output: {{CS#, RAS#, CAS#, WE#}} + addr + bank + CKE + reset_n
//
// Command encodings (active-low CS#=0):
//   NOP    = 4'b0111   MRS  = 4'b0000   REF  = 4'b0001
//   PRE    = 4'b0010   ACT  = 4'b0011   WR   = 4'b0100
//   RD     = 4'b0101   ZQCL = 4'b0110   DESL = 4'b1111
////////////////////////////////////////////////////////////////////////////////

module cmd_gen #(
    parameter DDR_ADDR_W = {p['DDR_ADDR_W']},
    parameter DDR_BANK_W = {p['DDR_BANK_W']},
    parameter ROW_BITS   = {p['ROW_BITS']},
    parameter COL_BITS   = {p['COL_BITS']},
    parameter BANK_BITS  = {p['BANK_BITS']},
    parameter AUX_WIDTH  = {p['AUX_WIDTH']}
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── From scheduler ──
    input  logic                    sched_valid,
    input  logic [3:0]              sched_type,     // CMD_ACT/RD/WR/PRE/REF/NOP
    input  logic [ROW_BITS-1:0]     sched_row,
    input  logic [COL_BITS-1:0]     sched_col,
    input  logic [BANK_BITS-1:0]    sched_bank,
    input  logic                    sched_we,
    input  logic [AUX_WIDTH-1:0]    sched_aux,

    // ── DDR3 pin-level outputs ──
    output logic [3:0]              ddr_cmd,        // {{CS#,RAS#,CAS#,WE#}}
    output logic [DDR_ADDR_W-1:0]   ddr_addr,
    output logic [DDR_BANK_W-1:0]   ddr_bank,
    output logic                    ddr_cke,
    output logic                    ddr_reset_n,
    output logic                    ddr_odt,

    // ── Feedback to bank_tracker ──
    output logic                    fb_act_valid,
    output logic [BANK_BITS-1:0]    fb_act_bank,
    output logic [ROW_BITS-1:0]     fb_act_row,
    output logic                    fb_pre_valid,
    output logic [BANK_BITS-1:0]    fb_pre_bank,
    output logic                    fb_pre_all,
    output logic                    fb_rd_valid,
    output logic [BANK_BITS-1:0]    fb_rd_bank,
    output logic                    fb_wr_valid,
    output logic [BANK_BITS-1:0]    fb_wr_bank,
    output logic                    fb_ref_valid,

    // ── Aux passthrough (to data path) ──
    output logic                    cmd_out_valid,
    output logic                    cmd_out_we,
    output logic [AUX_WIDTH-1:0]    cmd_out_aux
);

    // Scheduler command type encoding (must match scheduler)
    localparam SCMD_NOP = 4'd0;
    localparam SCMD_ACT = 4'd1;
    localparam SCMD_RD  = 4'd2;
    localparam SCMD_WR  = 4'd3;
    localparam SCMD_PRE = 4'd4;
    localparam SCMD_REF = 4'd5;

    // DDR3 command encodings {{CS#, RAS#, CAS#, WE#}}
    localparam DDR_NOP  = 4'b0111;
    localparam DDR_MRS  = 4'b0000;
    localparam DDR_REF  = 4'b0001;
    localparam DDR_PRE  = 4'b0010;
    localparam DDR_ACT  = 4'b0011;
    localparam DDR_WR   = 4'b0100;
    localparam DDR_RD   = 4'b0101;
    localparam DDR_DESL = 4'b1111;

    // ════════════════════════════════════════════════════
    // Command encoding
    // ════════════════════════════════════════════════════
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ddr_cmd      <= DDR_NOP;
            ddr_addr     <= '0;
            ddr_bank     <= '0;
            ddr_cke      <= 1'b1;   // CKE high during normal operation
            ddr_reset_n  <= 1'b1;
            ddr_odt      <= 1'b0;
            fb_act_valid <= 1'b0;
            fb_pre_valid <= 1'b0;
            fb_rd_valid  <= 1'b0;
            fb_wr_valid  <= 1'b0;
            fb_ref_valid <= 1'b0;
            fb_pre_all   <= 1'b0;
            fb_act_bank  <= '0;
            fb_act_row   <= '0;
            fb_pre_bank  <= '0;
            fb_rd_bank   <= '0;
            fb_wr_bank   <= '0;
            cmd_out_valid<= 1'b0;
            cmd_out_we   <= 1'b0;
            cmd_out_aux  <= '0;
        end else begin
            // Default: NOP, all feedback deasserted
            ddr_cmd      <= DDR_NOP;
            ddr_addr     <= '0;
            ddr_bank     <= '0;
            ddr_odt      <= 1'b0;
            fb_act_valid <= 1'b0;
            fb_pre_valid <= 1'b0;
            fb_rd_valid  <= 1'b0;
            fb_wr_valid  <= 1'b0;
            fb_ref_valid <= 1'b0;
            fb_pre_all   <= 1'b0;
            cmd_out_valid<= 1'b0;

            if (sched_valid) begin
                case (sched_type)
                    SCMD_ACT: begin
                        ddr_cmd      <= DDR_ACT;
                        ddr_addr     <= sched_row[DDR_ADDR_W-1:0];
                        ddr_bank     <= sched_bank;
                        fb_act_valid <= 1'b1;
                        fb_act_bank  <= sched_bank;
                        fb_act_row   <= sched_row;
                    end
                    SCMD_RD: begin
                        ddr_cmd      <= DDR_RD;
                        // Column address: col in lower bits, A10=0 (no auto-precharge)
                        ddr_addr     <= {{{{DDR_ADDR_W-COL_BITS{{1'b0}}}}, sched_col}};
                        ddr_bank     <= sched_bank;
                        fb_rd_valid  <= 1'b1;
                        fb_rd_bank   <= sched_bank;
                        cmd_out_valid<= 1'b1;
                        cmd_out_we   <= 1'b0;
                        cmd_out_aux  <= sched_aux;
                    end
                    SCMD_WR: begin
                        ddr_cmd      <= DDR_WR;
                        ddr_addr     <= {{{{DDR_ADDR_W-COL_BITS{{1'b0}}}}, sched_col}};
                        ddr_bank     <= sched_bank;
                        ddr_odt      <= 1'b1;  // ODT on for writes
                        fb_wr_valid  <= 1'b1;
                        fb_wr_bank   <= sched_bank;
                        cmd_out_valid<= 1'b1;
                        cmd_out_we   <= 1'b1;
                        cmd_out_aux  <= sched_aux;
                    end
                    SCMD_PRE: begin
                        ddr_cmd      <= DDR_PRE;
                        ddr_addr[10] <= 1'b0;  // A10=0 → single bank precharge
                        ddr_bank     <= sched_bank;
                        fb_pre_valid <= 1'b1;
                        fb_pre_bank  <= sched_bank;
                        fb_pre_all   <= 1'b0;
                    end
                    SCMD_REF: begin
                        ddr_cmd      <= DDR_REF;
                        fb_ref_valid <= 1'b1;
                    end
                    default: begin
                        ddr_cmd <= DDR_NOP;
                    end
                endcase
            end
        end
    end

endmodule
"""

    def generate_manifest(self):
        p = self.p
        return {
            **stamp(self.spec),
            "module_name": "cmd_gen", "file": "cmd_gen.sv",
            "phase": 3, "generator": "cmd_gen_gen",
            "dependencies": ["scheduler", "bank_tracker"],
            "spec_version": self.spec.get("schema_version"),
            "parameters": {k: v for k, v in p.items()},
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "sched_in": [
                    {"name": "sched_valid", "width": 1, "dir": "input", "source": "scheduler.cmd_valid"},
                    {"name": "sched_type", "width": 4, "dir": "input", "source": "scheduler.cmd_type"},
                    {"name": "sched_row", "width": p["ROW_BITS"], "dir": "input", "source": "scheduler.cmd_row"},
                    {"name": "sched_col", "width": p["COL_BITS"], "dir": "input", "source": "scheduler.cmd_col"},
                    {"name": "sched_bank", "width": p["BANK_BITS"], "dir": "input", "source": "scheduler.cmd_bank"},
                    {"name": "sched_we", "width": 1, "dir": "input", "source": "scheduler.cmd_we"},
                    {"name": "sched_aux", "width": p["AUX_WIDTH"], "dir": "input", "source": "scheduler.cmd_aux"},
                ],
                "ddr_out": [
                    {"name": "ddr_cmd", "width": 4, "dir": "output"},
                    {"name": "ddr_addr", "width": p["DDR_ADDR_W"], "dir": "output"},
                    {"name": "ddr_bank", "width": p["DDR_BANK_W"], "dir": "output"},
                    {"name": "ddr_cke", "width": 1, "dir": "output"},
                    {"name": "ddr_reset_n", "width": 1, "dir": "output"},
                    {"name": "ddr_odt", "width": 1, "dir": "output"},
                ],
                "feedback": [
                    {"name": "fb_act_valid", "width": 1, "dir": "output"},
                    {"name": "fb_act_bank", "width": p["BANK_BITS"], "dir": "output"},
                    {"name": "fb_act_row", "width": p["ROW_BITS"], "dir": "output"},
                    {"name": "fb_pre_valid", "width": 1, "dir": "output"},
                    {"name": "fb_pre_bank", "width": p["BANK_BITS"], "dir": "output"},
                    {"name": "fb_pre_all", "width": 1, "dir": "output"},
                    {"name": "fb_rd_valid", "width": 1, "dir": "output"},
                    {"name": "fb_rd_bank", "width": p["BANK_BITS"], "dir": "output"},
                    {"name": "fb_wr_valid", "width": 1, "dir": "output"},
                    {"name": "fb_wr_bank", "width": p["BANK_BITS"], "dir": "output"},
                    {"name": "fb_ref_valid", "width": 1, "dir": "output"},
                ],
                "aux_passthrough": [
                    {"name": "cmd_out_valid", "width": 1, "dir": "output"},
                    {"name": "cmd_out_we", "width": 1, "dir": "output"},
                    {"name": "cmd_out_aux", "width": p["AUX_WIDTH"], "dir": "output"},
                ],
            },
        }

    def run(self):
        hdr = "=" * 62
        print(f"{hdr}\n  COMMAND GENERATOR GENERATOR\n  Spec: {self.spec_path}\n{hdr}")
        for k, v in self.p.items(): print(f"    {k:20s} = {v}")
        rtl = self.generate_rtl()
        manifest = self.generate_manifest()
        (self.output_dir / "cmd_gen.sv").write_text(rtl)
        (self.output_dir / "cmd_gen_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  V cmd_gen.sv          ({rtl.count(chr(10))} lines)")
        print(f"  V cmd_gen_manifest.json")
        print(f"\n{hdr}\n  DONE — cmd_gen\n{hdr}")
        return {"status": "success", "module": "cmd_gen", "phase": 3,
                "rtl_path": str(self.output_dir / "cmd_gen.sv"),
                "lines": rtl.count('\n'), "manifest": manifest}

if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output dir: ").strip() or "./output"
    r = CmdGenGenerator(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)