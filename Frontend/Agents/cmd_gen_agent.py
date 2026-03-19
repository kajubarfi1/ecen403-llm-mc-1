#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 COMMAND GENERATOR AGENT (Phase 3)                    ║
║  Encodes scheduled commands to DDR3 pin-level signals.               ║
║  Generates: cmd_gen.sv + cmd_gen_tb.sv + cmd_gen_manifest.json       ║
╚══════════════════════════════════════════════════════════════════════╝
"""
import json, os, sys, math
from pathlib import Path
from datetime import datetime


class CmdGenAgent:
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
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        return f"""////////////////////////////////////////////////////////////////////////////////
// Module:    cmd_gen
// Generated: {ts}
// Agent:     Command Generator Agent (Phase 3)
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

    def generate_tb(self):
        p = self.p
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
        @(posedge clk);
        sched_valid=0;
        @(posedge clk);  // wait for registered output
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

    def generate_manifest(self):
        p = self.p
        return {
            "module_name": "cmd_gen", "file": "cmd_gen.sv",
            "phase": 3, "agent": "cmd_gen_agent",
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
                    {"name": "fb_rd_valid", "width": 1, "dir": "output"},
                    {"name": "fb_wr_valid", "width": 1, "dir": "output"},
                    {"name": "fb_ref_valid", "width": 1, "dir": "output"},
                ],
            },
        }

    def run(self):
        hdr = "=" * 62
        print(f"{hdr}\n  COMMAND GENERATOR AGENT\n  Spec: {self.spec_path}\n{hdr}")
        for k, v in self.p.items(): print(f"    {k:20s} = {v}")
        rtl = self.generate_rtl()
        tb = self.generate_tb()
        manifest = self.generate_manifest()
        (self.output_dir / "cmd_gen.sv").write_text(rtl)
        (self.output_dir / "cmd_gen_tb.sv").write_text(tb)
        (self.output_dir / "cmd_gen_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  V cmd_gen.sv          ({rtl.count(chr(10))} lines)")
        print(f"  V cmd_gen_tb.sv       ({tb.count(chr(10))} lines)")
        print(f"  V cmd_gen_manifest.json")
        print(f"\n{hdr}\n  DONE — cmd_gen\n{hdr}")
        return {"status": "success", "module": "cmd_gen", "phase": 3,
                "rtl_path": str(self.output_dir / "cmd_gen.sv"),
                "tb_path": str(self.output_dir / "cmd_gen_tb.sv"),
                "lines": rtl.count('\n'), "manifest": manifest}

if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output dir: ").strip() or "./output"
    r = CmdGenAgent(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)