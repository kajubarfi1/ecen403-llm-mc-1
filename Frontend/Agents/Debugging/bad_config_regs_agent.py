#!/usr/bin/env python3
"""
BAD CONFIG_REGS AGENT — for testing validation retry loop.

Attempt 1: Wrong reset values, missing cfg_tFAW_nCK and cfg_tCCD_nCK ports, wrong data width (16)
Attempt 2: Fixes reset values and data width, still missing cfg_tCCD_nCK
Attempt 3+: Delegates to real agent → passes
"""

import json
import os
import sys
from pathlib import Path


class ConfigRegsAgent:

    def __init__(self, spec_path: str, output_dir: str):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.attempt_file = self.output_dir / ".config_regs_attempt"
        if self.attempt_file.exists():
            self.attempt = int(self.attempt_file.read_text().strip()) + 1
        else:
            self.attempt = 1
        self.attempt_file.write_text(str(self.attempt))

    def run(self) -> dict:
        print(f"\n{'=' * 62}")
        print(f"  CONFIG_REGS AGENT (BAD — attempt {self.attempt})")
        print(f"{'=' * 62}")

        if self.attempt >= 3:
            print(f"  ✓ Delegating to real agent (attempt {self.attempt})")
            # Import and run the real agent
            # We need to get the real module without hitting our own file
            import importlib.util
            real_path = Path(__file__).parent / "config_regs_agent.py"
            if not real_path.exists():
                # Try parent dirs
                for p in [Path(__file__).parent.parent / "config_regs_agent.py",
                           Path(__file__).parent / "Agents" / "Phase_1_Agents" / "config_regs_agent.py"]:
                    if p.exists():
                        real_path = p
                        break
            spec = importlib.util.spec_from_file_location("real_config_regs", str(real_path))
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            return mod.ConfigRegsAgent(self.spec_path, str(self.output_dir)).run()

        csr_map = self.spec["csr_register_map"]
        regs = csr_map.get("registers", csr_map if isinstance(csr_map, list) else [])

        # Decide what to break
        if self.attempt == 1:
            data_width = 16  # WRONG: should be 32
            include_tFAW = False  # MISSING
            include_tCCD = False  # MISSING
            wrong_reset_values = True
            print(f"  ⚠ INJECTING FAULTS: wrong data width (16), missing cfg_tFAW/tCCD, wrong reset values")
        elif self.attempt == 2:
            data_width = 32  # FIXED
            include_tFAW = True  # FIXED
            include_tCCD = False  # STILL MISSING
            wrong_reset_values = False  # FIXED
            print(f"  ⚠ INJECTING FAULTS: missing cfg_tCCD_nCK (partial fix)")

        sv = []
        L = sv.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module: config_regs (attempt {self.attempt})")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"module config_regs (")
        L(f"    input  logic clk,")
        L(f"    input  logic rst_n,")
        L(f"    // CSR bus")
        L(f"    input  logic                    csr_wr,")
        L(f"    input  logic                    csr_rd,")
        L(f"    input  logic [7:0]              csr_addr,")
        L(f"    input  logic [{data_width-1}:0]             csr_wdata,")
        L(f"    output logic [{data_width-1}:0]             csr_rdata,")
        L(f"    output logic                    csr_ready,")
        L(f"    output logic                    csr_error,")
        L(f"    // Timing outputs")
        L(f"    output logic [7:0]  cfg_tRCD_nCK,")
        L(f"    output logic [7:0]  cfg_tRP_nCK,")
        L(f"    output logic [7:0]  cfg_tRAS_nCK,")
        L(f"    output logic [7:0]  cfg_tRC_nCK,")
        L(f"    output logic [7:0]  cfg_tRRD_nCK,")
        L(f"    output logic [7:0]  cfg_tWTR_nCK,")
        if include_tFAW:
            L(f"    output logic [7:0]  cfg_tFAW_nCK,")
        L(f"    output logic [7:0]  cfg_tRFC_nCK,")
        L(f"    output logic [7:0]  cfg_tWR_nCK,")
        L(f"    output logic [7:0]  cfg_tRTP_nCK,")
        L(f"    output logic [7:0]  cfg_CL_nCK,")
        L(f"    output logic [7:0]  cfg_CWL_nCK,")
        if include_tCCD:
            L(f"    output logic [7:0]  cfg_tCCD_nCK,")
        L(f"    output logic [23:0] cfg_tREFI_nCK,")
        L(f"    // Control outputs")
        L(f"    output logic        cfg_force_refresh,")
        L(f"    output logic [3:0]  cfg_max_postpone,")
        L(f"    output logic [3:0]  cfg_urgent_threshold,")
        L(f"    output logic        cfg_ref_priority")
        L(f");")
        L(f"")
        L(f"    parameter CSR_ADDR_W = 8;")
        L(f"    parameter CSR_DATA_W = {data_width};")
        L(f"")

        # Register declarations with reset values
        for reg in regs:
            name = reg["name"].lower()
            offset_raw = reg["offset"]
            offset_int = int(offset_raw, 16) if isinstance(offset_raw, str) else offset_raw

            rv_raw = reg.get("reset_value", 0)
            if isinstance(rv_raw, str):
                rv_int = int(rv_raw, 16)
            else:
                rv_int = rv_raw

            if wrong_reset_values and rv_int != 0:
                rv_int = 0xDEADBEEF  # WRONG

            L(f"    logic [{data_width-1}:0] reg_{name};  // @ 0x{offset_int:02X}")

        L(f"")
        L(f"    // Address decode — read")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        for reg in regs:
            name = reg["name"].lower()
            rv_raw = reg.get("reset_value", 0)
            if isinstance(rv_raw, str):
                rv_int = int(rv_raw, 16)
            else:
                rv_int = rv_raw
            if wrong_reset_values and rv_int != 0:
                rv_int = 0xDEADBEEF
            L(f"            reg_{name} <= {data_width}'h{rv_int:08X};")
        L(f"        end else if (csr_wr) begin")
        L(f"            case (csr_addr)")
        for reg in regs:
            name = reg["name"].lower()
            offset_raw = reg["offset"]
            offset_int = int(offset_raw, 16) if isinstance(offset_raw, str) else offset_raw
            access = reg["access"]
            if access == "RW":
                L(f"                8'h{offset_int:02X}: reg_{name} <= csr_wdata;")
            elif access == "RW1C":
                L(f"                8'h{offset_int:02X}: reg_{name} <= reg_{name} & ~csr_wdata; // RW1C write-1-to-clear")
        L(f"                default: ;")
        L(f"            endcase")
        L(f"        end")
        L(f"    end")
        L(f"")

        L(f"    // Read mux")
        L(f"    always_comb begin")
        L(f"        csr_rdata = '0;")
        L(f"        csr_error = 1'b0;")
        L(f"        case (csr_addr)")
        for reg in regs:
            name = reg["name"].lower()
            offset_raw = reg["offset"]
            offset_int = int(offset_raw, 16) if isinstance(offset_raw, str) else offset_raw
            L(f"            8'h{offset_int:02X}: csr_rdata = reg_{name};")
        L(f"            default: begin csr_rdata = {data_width}'hDEAD_DEAD; csr_error = 1'b1; end")
        L(f"        endcase")
        L(f"    end")
        L(f"")
        L(f"    assign csr_ready = 1'b1;")
        L(f"")

        # Timing output assignments (RO access type)
        L(f"    // Timing outputs from registers")
        L(f"    assign cfg_tRCD_nCK = reg_timing_0[7:0];")
        L(f"    assign cfg_tRP_nCK  = reg_timing_0[15:8];")
        L(f"    assign cfg_tRAS_nCK = reg_timing_0[23:16];")
        L(f"    assign cfg_tRC_nCK  = reg_timing_0[31:24];")
        L(f"    assign cfg_tRRD_nCK = reg_timing_1[7:0];")
        L(f"    assign cfg_tWTR_nCK = reg_timing_1[15:8];")
        if include_tFAW:
            L(f"    assign cfg_tFAW_nCK = reg_timing_1[23:16];")
        L(f"    assign cfg_tRFC_nCK = reg_timing_1[31:24];")
        L(f"    assign cfg_tWR_nCK  = reg_timing_2[7:0];")
        L(f"    assign cfg_tRTP_nCK = reg_timing_2[15:8];")
        L(f"    assign cfg_CL_nCK   = reg_timing_2[23:16];")
        L(f"    assign cfg_CWL_nCK  = reg_timing_2[31:24];")
        if include_tCCD:
            L(f"    assign cfg_tCCD_nCK = reg_timing_3[7:0];")
        L(f"    assign cfg_tREFI_nCK = reg_timing_3[23:0];")
        L(f"")
        L(f"endmodule")

        sv_text = "\n".join(sv)
        sv_path = self.output_dir / "config_regs.sv"
        sv_path.write_text(sv_text)
        print(f"  ✓ {sv_path} ({len(sv)} lines)")

        manifest = {
            "module_name": "config_regs",
            "file": "config_regs.sv",
            "phase": 1,
            "parameters": {"CSR_ADDR_W": 8, "CSR_DATA_W": data_width},
            "ports": {"clock_reset": [
                {"name": "clk", "dir": "input", "width": 1},
                {"name": "rst_n", "dir": "input", "width": 1},
            ], "outputs": []},
            "assertions": [],
            "dependencies": [],
        }
        manifest_path = self.output_dir / "config_regs_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2))

        return {"status": "success", "module": "config_regs",
                "manifest": manifest, "rtl_path": str(sv_path)}
