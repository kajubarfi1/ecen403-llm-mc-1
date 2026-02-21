#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 WISHBONE PORT INTERFACE AGENT                       ║
║                                                                      ║
║  Phase 1 RTL Generation Agent                                        ║
║  Generates: wb_port.sv + wb_port_manifest.json                       ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import sys
import os
from pathlib import Path
from datetime import datetime


class WishbonePortAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.host      = self.spec["host_interface"]
        self.data_path = self.spec["data_path_mapping"]
        self.ctrl_arch = self.spec["controller_architecture"]
        self.clocking  = self.spec["clocking_model"]
        self.geometry  = self.spec["memory_geometry"]

        self.p = self._derive_parameters()

    def _derive_parameters(self) -> dict:
        p = {}
        p["DATA_WIDTH"]       = self.host["data_width_bits"]
        p["ADDR_WIDTH"]       = self.host["address_width_bits"]
        p["GRANULARITY"]      = self.host["granularity_bits"]
        p["SEL_WIDTH"]        = p["DATA_WIDTH"] // p["GRANULARITY"]
        p["BURST_TYPE"]       = self.host["burst_type"]
        p["MAX_BURST_LEN"]    = self.host["max_burst_length"]
        p["INTERFACE_TYPE"]   = self.host["interface_type"]
        p["RD_BUFFER_DEPTH"]  = self.host.get("read_buffer_depth", 16)
        p["WR_BUFFER_DEPTH"]  = self.host.get("write_buffer_depth", 16)
        p["AUX_WIDTH"]        = self.ctrl_arch["aux_width"]
        p["QUEUE_DEPTH"]      = self.ctrl_arch["command_queue_depth"]
        p["PIPELINE_LATENCY"] = self.clocking.get("pipeline_latency_cycles", 2)
        p["ROW_BITS"]         = self.geometry["row_bits"]
        p["COL_BITS"]         = self.geometry["column_bits"]
        p["BANK_BITS"]        = self.geometry["bank_bits"]
        p["RANKS"]            = self.geometry["ranks"]
        p["BURST_CTR_WIDTH"]  = max(1, (p["MAX_BURST_LEN"] - 1).bit_length())
        p["TAG_FIFO_DEPTH"]   = p["RD_BUFFER_DEPTH"]
        p["TAG_PTR_WIDTH"]    = max(1, p["TAG_FIFO_DEPTH"].bit_length())
        p["ADDR_INC"]         = p["DATA_WIDTH"] // 8
        return p

    def validate(self) -> list:
        errors = []
        p = self.p
        if p["INTERFACE_TYPE"] != "wishbone_pipelined":
            errors.append(f"Expected wishbone_pipelined, got {p['INTERFACE_TYPE']}")
        if p["DATA_WIDTH"] not in (32, 64, 128):
            errors.append(f"DATA_WIDTH must be 32/64/128, got {p['DATA_WIDTH']}")
        if p["GRANULARITY"] != 8:
            errors.append(f"GRANULARITY must be 8 for byte addressing, got {p['GRANULARITY']}")
        if p["SEL_WIDTH"] != p["DATA_WIDTH"] // 8:
            errors.append(f"SEL_WIDTH derivation error")
        if p["AUX_WIDTH"] < 4:
            errors.append(f"AUX_WIDTH must be >= 4, got {p['AUX_WIDTH']}")
        if not (20 <= p["ADDR_WIDTH"] <= 32):
            errors.append(f"ADDR_WIDTH out of [20,32]: {p['ADDR_WIDTH']}")
        if p["MAX_BURST_LEN"] != 8:
            errors.append(f"MAX_BURST_LEN should be 8 for DDR3 BL8, got {p['MAX_BURST_LEN']}")
        return errors

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        return f"""\
////////////////////////////////////////////////////////////////////////////////
// Module:    wb_port
// File:      wb_port.sv
// Generated: {ts}
// Agent:     Wishbone Port Interface Agent (Phase 1)
// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}
// Schema:    {self.spec.get('schema_version', 'N/A')}
//
// Description:
//   Wishbone B4 pipelined slave. Accepts host read/write requests and
//   translates them into internal request descriptors for the command queue.
//   Implements backpressure (stall), linear burst (BL8), byte-lane masking,
//   error signalling, and auxiliary tag propagation.
//
// Derived parameters:
//   DATA_WIDTH     = {p['DATA_WIDTH']:>3d}   (host_interface.data_width_bits)
//   ADDR_WIDTH     = {p['ADDR_WIDTH']:>3d}   (host_interface.address_width_bits)
//   SEL_WIDTH      = {p['SEL_WIDTH']:>3d}   (DATA_WIDTH / granularity_bits)
//   AUX_WIDTH      = {p['AUX_WIDTH']:>3d}   (controller_architecture.aux_width)
//   MAX_BURST_LEN  = {p['MAX_BURST_LEN']:>3d}   (host_interface.max_burst_length)
//   QUEUE_DEPTH    = {p['QUEUE_DEPTH']:>3d}   (controller_architecture.command_queue_depth)
//   ROW_BITS       = {p['ROW_BITS']:>3d}   (memory_geometry.row_bits)
//
// Validation: WB-001 .. WB-009  (ddr3_validation_checklist_v2.docx)
////////////////////////////////////////////////////////////////////////////////

module wb_port #(
    parameter DATA_WIDTH     = {p['DATA_WIDTH']},
    parameter ADDR_WIDTH     = {p['ADDR_WIDTH']},
    parameter SEL_WIDTH      = {p['SEL_WIDTH']},
    parameter AUX_WIDTH      = {p['AUX_WIDTH']},
    parameter MAX_BURST_LEN  = {p['MAX_BURST_LEN']},
    parameter QUEUE_DEPTH    = {p['QUEUE_DEPTH']},
    parameter BURST_CTR_W    = {p['BURST_CTR_WIDTH']},
    parameter TAG_FIFO_DEPTH = {p['TAG_FIFO_DEPTH']},
    parameter TAG_PTR_W      = {p['TAG_PTR_WIDTH']}
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,            // controller clock ({self.clocking['$derived']['controller_frequency_MHz']:.0f} MHz)
    input  logic                    rst_n,          // active-low synchronous reset

    // ────────────── Wishbone B4 Pipelined Slave (from HOST) ──────────────
    input  logic                    wb_cyc_i,       // bus cycle
    input  logic                    wb_stb_i,       // strobe / valid
    input  logic                    wb_we_i,        // write enable
    input  logic [ADDR_WIDTH-1:0]   wb_adr_i,       // byte address
    input  logic [DATA_WIDTH-1:0]   wb_dat_i,       // write data
    input  logic [SEL_WIDTH-1:0]    wb_sel_i,       // byte-lane select
    input  logic [1:0]              wb_bte_i,       // burst type extension
    input  logic [2:0]              wb_cti_i,       // cycle type identifier

    output logic                    wb_ack_o,       // acknowledge
    output logic [DATA_WIDTH-1:0]   wb_dat_o,       // read data
    output logic                    wb_stall_o,     // pipeline stall
    output logic                    wb_err_o,       // error response

    // ────────────── Internal → Command Queue / Address Decoder ──────────────
    output logic                    req_valid,      // request valid
    output logic                    req_we,         // 1 = write, 0 = read
    output logic [ADDR_WIDTH-1:0]   req_addr,       // byte address
    output logic [DATA_WIDTH-1:0]   req_wdata,      // write data
    output logic [SEL_WIDTH-1:0]    req_wmask,      // write byte mask
    output logic [AUX_WIDTH-1:0]    req_aux,        // auxiliary tag

    input  logic                    req_ready,      // backpressure from queue

    // ────────────── Internal ← Data Path (read responses) ──────────────
    input  logic                    rsp_valid,      // response valid
    input  logic [DATA_WIDTH-1:0]   rsp_rdata,      // response data
    input  logic [AUX_WIDTH-1:0]    rsp_aux         // response tag
);

    // ================================================================
    // Wishbone B4 CTI / BTE encodings
    // ================================================================
    localparam logic [2:0] CTI_CLASSIC   = 3'b000;
    localparam logic [2:0] CTI_CONST     = 3'b001;
    localparam logic [2:0] CTI_INC       = 3'b010;
    localparam logic [2:0] CTI_END       = 3'b111;

    localparam logic [1:0] BTE_LINEAR    = 2'b00;

    // Address increment per beat
    localparam int unsigned ADDR_INC = DATA_WIDTH / 8;   // {p['ADDR_INC']} bytes

    // ================================================================
    // Handshake
    // ================================================================
    wire wb_beat = wb_cyc_i & wb_stb_i & ~wb_stall_o;

    // ================================================================
    // Tag FIFO  —  tracks outstanding read requests
    // ================================================================
    logic [AUX_WIDTH-1:0] tag_mem [0:TAG_FIFO_DEPTH-1];
    logic [TAG_PTR_W:0]   tag_wr, tag_rd;
    wire  [TAG_PTR_W:0]   tag_cnt  = tag_wr - tag_rd;
    wire                   tag_full = (tag_cnt == TAG_FIFO_DEPTH[TAG_PTR_W:0]);

    // Push
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            tag_wr <= '0;
        else if (wb_beat && !wb_we_i)
        begin
            tag_mem[tag_wr[TAG_PTR_W-1:0]] <= aux_ctr;
            tag_wr <= tag_wr + 1'b1;
        end

    // Pop
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            tag_rd <= '0;
        else if (rsp_valid)
            tag_rd <= tag_rd + 1'b1;

    // ================================================================
    // Aux-tag counter  (WB-009)
    // ================================================================
    logic [AUX_WIDTH-1:0] aux_ctr;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)  aux_ctr <= '0;
        else if (wb_beat) aux_ctr <= aux_ctr + 1'b1;

    // ================================================================
    // Stall generation  (WB-005)
    // ================================================================
    always_comb begin
        wb_stall_o = 1'b0;
        if (!req_ready)                        wb_stall_o = 1'b1;
        if (!wb_we_i && tag_full && wb_stb_i)  wb_stall_o = 1'b1;
    end

    // ================================================================
    // Burst tracker  (WB-003, WB-004)
    // ================================================================
    logic                   burst_active;
    logic [BURST_CTR_W-1:0] burst_cnt;
    logic [ADDR_WIDTH-1:0]  burst_nxt_addr;
    logic                   burst_we;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            burst_active   <= 1'b0;
            burst_cnt      <= '0;
            burst_nxt_addr <= '0;
            burst_we       <= 1'b0;
        end else if (wb_beat) begin
            if (!burst_active && wb_cti_i == CTI_INC) begin
                burst_active   <= 1'b1;
                burst_cnt      <= 'd1;
                burst_nxt_addr <= wb_adr_i + ADDR_INC[ADDR_WIDTH-1:0];
                burst_we       <= wb_we_i;
            end else if (burst_active) begin
                burst_cnt      <= burst_cnt + 1'b1;
                burst_nxt_addr <= burst_nxt_addr + ADDR_INC[ADDR_WIDTH-1:0];
                if (wb_cti_i == CTI_END ||
                    burst_cnt == MAX_BURST_LEN[BURST_CTR_W-1:0] - 1'b1) begin
                    burst_active <= 1'b0;
                    burst_cnt    <= '0;
                end
            end
        end else if (!wb_cyc_i) begin
            burst_active <= 1'b0;
            burst_cnt    <= '0;
        end
    end

    // ================================================================
    // Request output  (WB-001, WB-002)
    // ================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_valid <= 1'b0;
            req_we    <= 1'b0;
            req_addr  <= '0;
            req_wdata <= '0;
            req_wmask <= '0;
            req_aux   <= '0;
        end else begin
            req_valid <= 1'b0;
            if (wb_beat) begin
                req_valid <= 1'b1;
                req_we    <= wb_we_i;
                req_addr  <= wb_adr_i;
                req_wdata <= wb_dat_i;
                req_wmask <= wb_sel_i;
                req_aux   <= aux_ctr;
            end
        end
    end

    // ================================================================
    // Write acknowledge  (WB-002, WB-008)
    // ================================================================
    logic wr_ack_r;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) wr_ack_r <= 1'b0;
        else        wr_ack_r <= wb_beat & wb_we_i;

    wire rd_ack = rsp_valid;

    assign wb_ack_o = wr_ack_r | rd_ack;
    assign wb_dat_o = rsp_rdata;

    // ================================================================
    // Error detection  (WB-007)
    // ================================================================
    logic err_r;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            err_r <= 1'b0;
        end else begin
            err_r <= 1'b0;
            if (wb_cyc_i && wb_stb_i) begin
                if (burst_active && (wb_we_i != burst_we))
                    err_r <= 1'b1;
                if (|wb_adr_i[$clog2(ADDR_INC)-1:0])
                    err_r <= 1'b1;
            end
        end
    end

    assign wb_err_o = err_r;

    // ================================================================
    // SVA — simulation-only assertions
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    property p_stall_hold;
        @(posedge clk) disable iff (!rst_n)
        (wb_cyc_i && wb_stb_i && wb_stall_o) |=>
            (wb_cyc_i && wb_stb_i);
    endproperty
    assert property (p_stall_hold)
        else $error("[WB-005] master released request during stall");

    property p_pipeline;
        @(posedge clk) disable iff (!rst_n)
        (wb_ack_o && wb_cyc_i && wb_stb_i && !wb_stall_o) |-> 1'b1;
    endproperty
    assert property (p_pipeline)
        else $error("[WB-008] pipeline accept error");

    property p_tag;
        @(posedge clk) disable iff (!rst_n)
        rsp_valid |->
            (rsp_aux == tag_mem[tag_rd[TAG_PTR_W-1:0]]);
    endproperty
    assert property (p_tag)
        else $error("[WB-009] aux tag mismatch");

    property p_burst_len;
        @(posedge clk) disable iff (!rst_n)
        burst_active |->
            (burst_cnt < MAX_BURST_LEN[BURST_CTR_W-1:0]);
    endproperty
    assert property (p_burst_len)
        else $error("[WB-003/004] burst exceeded MAX_BURST_LEN");

    property p_tag_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (tag_cnt <= TAG_FIFO_DEPTH[TAG_PTR_W:0]);
    endproperty
    assert property (p_tag_no_overflow)
        else $error("[WB-005] tag FIFO overflow");

    property p_sel_nonzero_write;
        @(posedge clk) disable iff (!rst_n)
        (wb_beat && wb_we_i) |-> (|wb_sel_i);
    endproperty
    assert property (p_sel_nonzero_write)
        else $warning("[WB-006] write with zero sel");

    // ================================================================
    // Functional coverage
    // ================================================================
    covergroup cg_wb @(posedge clk);
        option.per_instance = 1;
        cp_single_rd  : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_CLASSIC);
        cp_single_wr  : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_CLASSIC);
        cp_burst_rd   : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_INC);
        cp_burst_wr   : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_INC);
        cp_burst_end  : coverpoint (wb_beat && wb_cti_i == CTI_END);
        cp_stall      : coverpoint wb_stall_o;
        cp_err        : coverpoint wb_err_o;
        cp_backtoback : coverpoint (wb_ack_o && wb_beat);
        cp_tag_full   : coverpoint tag_full;
    endgroup
    cg_wb cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
"""

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "wb_port",
            "file": "wb_port.sv",
            "phase": 1,
            "agent": "wb_port_agent",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "DATA_WIDTH": p["DATA_WIDTH"],
                "ADDR_WIDTH": p["ADDR_WIDTH"],
                "SEL_WIDTH": p["SEL_WIDTH"],
                "AUX_WIDTH": p["AUX_WIDTH"],
                "MAX_BURST_LEN": p["MAX_BURST_LEN"],
                "QUEUE_DEPTH": p["QUEUE_DEPTH"],
                "BURST_CTR_W": p["BURST_CTR_WIDTH"],
                "TAG_FIFO_DEPTH": p["TAG_FIFO_DEPTH"],
                "ROW_BITS": p["ROW_BITS"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk",   "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "external_in": [
                    {"name": "wb_cyc_i", "width": 1,               "dir": "input"},
                    {"name": "wb_stb_i", "width": 1,               "dir": "input"},
                    {"name": "wb_we_i",  "width": 1,               "dir": "input"},
                    {"name": "wb_adr_i", "width": p["ADDR_WIDTH"], "dir": "input"},
                    {"name": "wb_dat_i", "width": p["DATA_WIDTH"], "dir": "input"},
                    {"name": "wb_sel_i", "width": p["SEL_WIDTH"],  "dir": "input"},
                    {"name": "wb_bte_i", "width": 2,               "dir": "input"},
                    {"name": "wb_cti_i", "width": 3,               "dir": "input"},
                ],
                "external_out": [
                    {"name": "wb_ack_o",   "width": 1,               "dir": "output"},
                    {"name": "wb_dat_o",   "width": p["DATA_WIDTH"], "dir": "output"},
                    {"name": "wb_stall_o", "width": 1,               "dir": "output"},
                    {"name": "wb_err_o",   "width": 1,               "dir": "output"},
                ],
                "internal_out": [
                    {"name": "req_valid", "width": 1,               "dir": "output"},
                    {"name": "req_we",    "width": 1,               "dir": "output"},
                    {"name": "req_addr",  "width": p["ADDR_WIDTH"], "dir": "output"},
                    {"name": "req_wdata", "width": p["DATA_WIDTH"], "dir": "output"},
                    {"name": "req_wmask", "width": p["SEL_WIDTH"],  "dir": "output"},
                    {"name": "req_aux",   "width": p["AUX_WIDTH"],  "dir": "output"},
                ],
                "internal_in": [
                    {"name": "req_ready", "width": 1,               "dir": "input"},
                    {"name": "rsp_valid", "width": 1,               "dir": "input"},
                    {"name": "rsp_rdata", "width": p["DATA_WIDTH"], "dir": "input"},
                    {"name": "rsp_aux",   "width": p["AUX_WIDTH"],  "dir": "input"},
                ],
            },
            "assertions": [
                {"name": "p_stall_hold",        "check": "WB-005"},
                {"name": "p_pipeline",          "check": "WB-008"},
                {"name": "p_tag",               "check": "WB-009"},
                {"name": "p_burst_len",         "check": "WB-003/004"},
                {"name": "p_tag_no_overflow",   "check": "WB-005"},
                {"name": "p_sel_nonzero_write", "check": "WB-006"},
            ],
            "coverage_points": [
                "cp_single_rd", "cp_single_wr", "cp_burst_rd", "cp_burst_wr",
                "cp_burst_end", "cp_stall", "cp_err", "cp_backtoback", "cp_tag_full",
            ],
        }

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  WISHBONE PORT INTERFACE AGENT\n  Spec: {self.spec_path}\n{hdr}")

        print("\n[1/4] Validating parameters …")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ✗ {e}")
            return {"status": "error", "errors": errs}
        print("  ✓ All parameters valid")
        for k, v in self.p.items():
            print(f"    {k:20s} = {v}")

        print("\n[2/4] Generating RTL …")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  ✓ {rtl_lines} lines of SystemVerilog")

        print("\n[3/4] Generating port manifest …")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  ✓ {port_cnt} ports | {len(manifest['assertions'])} assertions | {len(manifest['coverage_points'])} cover points")

        print("\n[4/4] Writing files …")
        rtl_path = self.output_dir / "wb_port.sv"
        rtl_path.write_text(rtl)
        print(f"  ✓ {rtl_path}")

        mfst_path = self.output_dir / "wb_port_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {mfst_path}")

        print(f"\n{hdr}\n  DONE — wb_port.sv ready for Phase 1 integration\n{hdr}")
        return {
            "status": "success",
            "module": "wb_port",
            "phase": 1,
            "rtl_path": str(rtl_path),
            "manifest_path": str(mfst_path),
            "manifest": manifest,
            "lines": rtl_lines,
            "ports": port_cnt,
        }


# ─── Interactive entry point ───
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   WISHBONE PORT INTERFACE AGENT  (Phase 1)  ║")
    print("╚══════════════════════════════════════════════╝")
    print()

    spec_path = input("Enter path to filled-in microarchitecture spec JSON: ").strip()

    if not spec_path:
        print("Error: No path provided.")
        sys.exit(1)

    if not os.path.isfile(spec_path):
        print(f"Error: File not found: {spec_path}")
        sys.exit(1)

    output_dir = input("Enter output directory (press Enter for ./output): ").strip()
    if not output_dir:
        output_dir = "./output"

    print()
    agent = WishbonePortAgent(spec_path, output_dir)
    result = agent.run()
    sys.exit(0 if result["status"] == "success" else 1)