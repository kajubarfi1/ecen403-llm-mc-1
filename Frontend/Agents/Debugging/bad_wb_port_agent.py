#!/usr/bin/env python3
"""
BAD WB_PORT AGENT — for testing validation retry loop.

Attempt 1: Wrong ADDR_WIDTH (16), missing wb_stall_o, no burst support, wrong SEL_WIDTH (2)
Attempt 2: Fixes ADDR_WIDTH and SEL_WIDTH, still missing burst support
Attempt 3+: Delegates to real agent → passes
"""

import json
import os
import sys
from pathlib import Path


class WishbonePortAgent:

    def __init__(self, spec_path: str, output_dir: str):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.attempt_file = self.output_dir / ".wb_port_attempt"
        if self.attempt_file.exists():
            self.attempt = int(self.attempt_file.read_text().strip()) + 1
        else:
            self.attempt = 1
        self.attempt_file.write_text(str(self.attempt))

    def run(self) -> dict:
        print(f"\n{'=' * 62}")
        print(f"  WB_PORT AGENT (BAD — attempt {self.attempt})")
        print(f"{'=' * 62}")

        if self.attempt >= 3:
            print(f"  ✓ Delegating to real agent (attempt {self.attempt})")
            import importlib.util
            real_path = Path(__file__).parent / "wb_port_agent.py"
            if not real_path.exists():
                for p in [Path(__file__).parent.parent / "wb_port_agent.py",
                           Path(__file__).parent / "Agents" / "Phase_1_Agents" / "wb_port_agent.py"]:
                    if p.exists():
                        real_path = p
                        break
            spec = importlib.util.spec_from_file_location("real_wb_port", str(real_path))
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            return mod.WishbonePortAgent(self.spec_path, str(self.output_dir)).run()

        host = self.spec["host_interface"]
        correct_aw = host["address_width_bits"]  # 29
        correct_dw = host["data_width_bits"]      # 32
        correct_sel = correct_dw // 8             # 4

        if self.attempt == 1:
            addr_w = 16          # WRONG: should be 29
            sel_w = 2            # WRONG: should be 4
            include_stall = False  # MISSING
            include_burst = False  # MISSING
            print(f"  ⚠ INJECTING FAULTS: wrong ADDR_WIDTH (16), wrong SEL (2), no stall, no burst")
        elif self.attempt == 2:
            addr_w = correct_aw  # FIXED
            sel_w = correct_sel  # FIXED
            include_stall = True # FIXED
            include_burst = False  # STILL MISSING
            print(f"  ⚠ INJECTING FAULTS: no burst support (partial fix)")

        sv = []
        L = sv.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module: wb_port (attempt {self.attempt})")
        L(f"// Wishbone B4 pipelined slave")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"module wb_port (")
        L(f"    input  logic                    clk,            // controller clock (200 MHz)")
        L(f"    input  logic                    rst_n,")
        L(f"    // ────────────── Wishbone B4 Pipelined Slave ──────────────")
        L(f"    input  logic                    wb_cyc_i,")
        L(f"    input  logic                    wb_stb_i,")
        L(f"    input  logic                    wb_we_i,")
        L(f"    input  logic [{addr_w-1}:0]            wb_adr_i,")
        L(f"    input  logic [{correct_dw-1}:0]            wb_dat_i,")
        L(f"    input  logic [{sel_w-1}:0]             wb_sel_i,")
        L(f"    output logic                    wb_ack_o,")
        L(f"    output logic [{correct_dw-1}:0]            wb_dat_o,")
        if include_stall:
            L(f"    output logic                    wb_stall_o,     // pipeline stall")
        L(f"    output logic                    wb_err_o,")
        L(f"    // ────────────── Internal Request Interface ──────────────")
        L(f"    output logic                    req_valid,")
        L(f"    output logic                    req_we,")
        L(f"    output logic [{addr_w-1}:0]            req_addr,")
        L(f"    output logic [{correct_dw-1}:0]            req_wdata,")
        L(f"    output logic [{sel_w-1}:0]             req_sel,")
        L(f"    input  logic                    req_ready,")
        L(f"    input  logic                    resp_valid,")
        L(f"    input  logic [{correct_dw-1}:0]            resp_rdata")
        L(f");")
        L(f"")
        L(f"    parameter ADDR_WIDTH = {addr_w};")
        L(f"    parameter DATA_WIDTH = {correct_dw};")
        L(f"    parameter SEL_WIDTH  = {sel_w};")
        L(f"    parameter AUX_WIDTH  = 4;")
        L(f"")
        L(f"    // Simple pass-through (no pipeline, no burst)")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            wb_ack_o  <= 1'b0;")
        L(f"            wb_dat_o  <= '0;")
        L(f"            wb_err_o  <= 1'b0;")
        if include_stall:
            L(f"            wb_stall_o <= 1'b0;")
        L(f"            req_valid <= 1'b0;")
        L(f"        end else begin")
        L(f"            wb_ack_o <= wb_cyc_i & wb_stb_i & req_ready;")
        L(f"            req_valid <= wb_cyc_i & wb_stb_i;")
        L(f"            req_we    <= wb_we_i;")
        L(f"            req_addr  <= wb_adr_i;")
        L(f"            req_wdata <= wb_dat_i;")
        L(f"            req_sel   <= wb_sel_i;")
        L(f"            wb_dat_o  <= resp_rdata;")
        if include_stall:
            L(f"            wb_stall_o <= ~req_ready;")
        L(f"        end")
        L(f"    end")
        L(f"")

        if include_stall:
            L(f"    // Stall assertion")
            L(f"    property p_pipeline;")
            L(f"        @(posedge clk) disable iff (!rst_n)")
            L(f"        wb_stall_o |-> !wb_ack_o;")
            L(f"    endproperty")
            L(f"    assert property (p_pipeline)")
            L(f"        else $error(\"stall/ack conflict\");")
            L(f"")

        L(f"    // ACK assertion")
        L(f"    property p_ack_gated;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        wb_ack_o |-> wb_cyc_i;")
        L(f"    endproperty")
        L(f"    assert property (p_ack_gated)")
        L(f"        else $error(\"ACK without CYC\");")
        L(f"")
        L(f"endmodule")

        sv_text = "\n".join(sv)
        sv_path = self.output_dir / "wb_port.sv"
        sv_path.write_text(sv_text)
        print(f"  ✓ {sv_path} ({len(sv)} lines)")

        manifest = {
            "module_name": "wb_port",
            "file": "wb_port.sv",
            "phase": 1,
            "parameters": {"ADDR_WIDTH": addr_w, "DATA_WIDTH": correct_dw, "SEL_WIDTH": sel_w},
            "ports": {"clock_reset": [
                {"name": "clk", "dir": "input", "width": 1},
                {"name": "rst_n", "dir": "input", "width": 1},
            ], "outputs": []},
            "assertions": [],
            "dependencies": [],
        }
        manifest_path = self.output_dir / "wb_port_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2))

        return {"status": "success", "module": "wb_port",
                "manifest": manifest, "rtl_path": str(sv_path)}
