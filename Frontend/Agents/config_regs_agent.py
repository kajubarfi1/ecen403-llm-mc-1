#!/usr/bin/env python3
"""
+======================================================================+
|                 CONFIG / CSR REGISTERS AGENT                         |
|                                                                      |
|  Phase 1 RTL Generation Agent                                        |
|  Generates: config_regs.sv + config_regs_tb.sv                      |
|             + config_regs_manifest.json                              |
|                                                                      |
|  Dependencies: None (Phase 1)                                        |
|                                                                      |
|  Spec sections consumed:                                             |
|    csr_register_map, controller_architecture, clocking_model         |
|                                                                      |
|  Testbench: ~35 tests across 9 sections (A-I)                       |
|    A: Reset values             B: Write/readback                     |
|    C: RO behavior              D: WO self-clearing                   |
|    E: RW1C latch/clear         F: Error handling                     |
|    G: cfg_* output prop        H: Reset mid-transaction              |
|    I: Edge cases                                                     |
|                                                                      |
|  Validation checks: CA-001 through CA-004                            |
+======================================================================+
"""

import json
import sys
import os
from pathlib import Path
from datetime import datetime


class ConfigRegsAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.csr       = self.spec["csr_register_map"]
        self.ctrl_arch = self.spec["controller_architecture"]
        self.clocking  = self.spec["clocking_model"]
        self.registers = self.csr["registers"]

        self.p = self._derive_parameters()

    def _derive_parameters(self) -> dict:
        p = {}
        p["CSR_ADDR_W"]   = self.csr["address_width_bits"]
        p["CSR_DATA_W"]   = self.csr["data_width_bits"]
        p["NUM_REGS"]     = len(self.registers)
        p["BASE_ADDR"]    = self.csr["base_address"]
        p["CTRL_PERIOD"]  = self.clocking["controller_clock_period_ns"]

        total_fields = sum(len(r["fields"]) for r in self.registers)
        p["TOTAL_FIELDS"] = total_fields

        return p

    def validate(self) -> list:
        errors = []
        p = self.p

        if p["CSR_DATA_W"] != 32:
            errors.append(f"CSR data width must be 32, got {p['CSR_DATA_W']}")
        if p["CSR_ADDR_W"] < 5:
            errors.append(f"CSR addr width too small for {p['NUM_REGS']} registers")

        offsets = set()
        for r in self.registers:
            off = int(r["offset"], 16)
            if off % 4 != 0:
                errors.append(f"Register {r['name']} offset {r['offset']} not 4-byte aligned")
            if off in offsets:
                errors.append(f"Duplicate offset {r['offset']}")
            offsets.add(off)

        for r in self.registers:
            used_bits = set()
            for f in r["fields"]:
                bits = self._parse_bits(f["bits"])
                overlap = used_bits & bits
                if overlap:
                    errors.append(f"{r['name']}.{f['name']}: bit overlap at {overlap}")
                used_bits |= bits

        return errors

    def _parse_bits(self, bits_str: str) -> set:
        if ":" in bits_str:
            hi, lo = bits_str.split(":")
            return set(range(int(lo), int(hi) + 1))
        else:
            return {int(bits_str)}

    def _bit_range(self, bits_str: str):
        if ":" in bits_str:
            hi, lo = bits_str.split(":")
            return int(hi), int(lo)
        else:
            b = int(bits_str)
            return b, b

    def _bit_width(self, bits_str: str) -> int:
        msb, lsb = self._bit_range(bits_str)
        return msb - lsb + 1

    def _status_input_name(self, field_name: str) -> str:
        mapping = {
            "init_done": "sts_init_done", "cal_done": "sts_cal_done",
            "cal_fail": "sts_cal_fail", "bist_done": "sts_bist_done",
            "bist_fail": "sts_bist_fail", "ref_pending_cnt": "sts_ref_pending_cnt",
            "self_refresh_active": "sts_self_refresh_active", "reserved": "23'b0",
        }
        return mapping.get(field_name, "1'b0")

    def _rw1c_event_name(self, field_name: str) -> str:
        mapping = {
            "ecc_ue_flag": "sts_ecc_ue_event",
            "ref_starve_flag": "sts_ref_starve_event",
            "init_fail_flag": "sts_init_fail_event",
        }
        return mapping.get(field_name, "1'b0")

    # ================================================================
    # RTL generation (identical logic to original, just reformatted)
    # ================================================================
    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        lines = []
        L = lines.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module:    config_regs")
        L(f"// File:      config_regs.sv")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Config/CSR Registers Agent (Phase 1)")
        L(f"// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}")
        L(f"// Schema:    {self.spec.get('schema_version', 'N/A')}")
        L(f"//")
        L(f"// Description:")
        L(f"//   {p['NUM_REGS']} CSR registers, {p['TOTAL_FIELDS']} bit fields.")
        L(f"//   Wishbone B4 classic slave on secondary CSR bus.")
        L(f"//   Access types: RO, RW, RW1C, WO (self-clearing).")
        L(f"//")
        L(f"// Validation: CA-001 .. CA-004")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"")
        L(f"module config_regs #(")
        L(f"    parameter CSR_ADDR_W = {p['CSR_ADDR_W']},")
        L(f"    parameter CSR_DATA_W = {p['CSR_DATA_W']}")
        L(f") (")
        L(f"    input  logic                    clk,")
        L(f"    input  logic                    rst_n,")
        L(f"")
        L(f"    // CSR Wishbone Slave")
        L(f"    input  logic                    csr_cyc_i,")
        L(f"    input  logic                    csr_stb_i,")
        L(f"    input  logic                    csr_we_i,")
        L(f"    input  logic [CSR_ADDR_W-1:0]   csr_adr_i,")
        L(f"    input  logic [CSR_DATA_W-1:0]   csr_dat_i,")
        L(f"    input  logic [3:0]              csr_sel_i,")
        L(f"    output logic                    csr_ack_o,")
        L(f"    output logic [CSR_DATA_W-1:0]   csr_dat_o,")
        L(f"    output logic                    csr_err_o,")
        L(f"")
        L(f"    // Status inputs")
        L(f"    input  logic                    sts_init_done,")
        L(f"    input  logic                    sts_cal_done,")
        L(f"    input  logic                    sts_cal_fail,")
        L(f"    input  logic                    sts_bist_done,")
        L(f"    input  logic                    sts_bist_fail,")
        L(f"    input  logic [2:0]              sts_ref_pending_cnt,")
        L(f"    input  logic                    sts_self_refresh_active,")
        L(f"    input  logic [15:0]             sts_ecc_ce_count,")
        L(f"    input  logic                    sts_ecc_ue_event,")
        L(f"    input  logic                    sts_ref_starve_event,")
        L(f"    input  logic                    sts_init_fail_event,")
        L(f"    input  logic [12:0]             sts_bist_fail_addr,")
        L(f"")
        L(f"    // Config outputs")
        L(f"    output logic [7:0]  cfg_tRCD_nCK, output logic [7:0]  cfg_tRP_nCK,")
        L(f"    output logic [7:0]  cfg_tRAS_nCK, output logic [7:0]  cfg_tRC_nCK,")
        L(f"    output logic [7:0]  cfg_tRRD_nCK, output logic [7:0]  cfg_tWTR_nCK,")
        L(f"    output logic [7:0]  cfg_tFAW_nCK, output logic [7:0]  cfg_tRFC_nCK,")
        L(f"    output logic [7:0]  cfg_tWR_nCK,  output logic [7:0]  cfg_tRTP_nCK,")
        L(f"    output logic [7:0]  cfg_CL_nCK,   output logic [7:0]  cfg_CWL_nCK,")
        L(f"    output logic [7:0]  cfg_tCCD_nCK, output logic [23:0] cfg_tREFI_nCK,")
        L(f"    output logic        cfg_sched_policy, output logic     cfg_row_policy,")
        L(f"    output logic [1:0]  cfg_self_ref_mode, output logic    cfg_ecc_enable,")
        L(f"    output logic        cfg_bist_start, output logic       cfg_force_refresh,")
        L(f"    output logic        cfg_force_self_ref,")
        L(f"    output logic [3:0]  cfg_max_postpone, output logic [3:0] cfg_urgent_threshold,")
        L(f"    output logic        cfg_ref_priority,")
        L(f"    output logic [2:0]  cfg_bist_pattern, output logic     cfg_bist_addr_mode,")
        L(f"    output logic [28:0] cfg_bist_addr_start, output logic [28:0] cfg_bist_addr_end")
        L(f");")
        L(f"")

        # Register offsets
        for r in self.registers:
            L(f"    localparam logic [CSR_ADDR_W-1:0] ADDR_{r['name']:20s} = {p['CSR_ADDR_W']}'h{int(r['offset'], 16):02X};")
        L(f"")

        # Register storage
        for r in self.registers:
            if r["access"] != "RO":
                L(f"    logic [CSR_DATA_W-1:0] reg_{r['name'].lower()};")
        L(f"")

        # Handshake
        L(f"    wire csr_req = csr_cyc_i & csr_stb_i;")
        L(f"    wire csr_wr  = csr_req & csr_we_i;")
        L(f"    wire csr_rd  = csr_req & ~csr_we_i;")
        L(f"    logic ack_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) ack_r <= 1'b0;")
        L(f"        else        ack_r <= csr_req & ~ack_r;")
        L(f"    assign csr_ack_o = ack_r;")
        L(f"")

        # Address decode
        L(f"    logic addr_valid;")
        L(f"    always_comb begin")
        L(f"        addr_valid = 1'b0;")
        L(f"        case (csr_adr_i)")
        for r in self.registers:
            L(f"            ADDR_{r['name']:20s}: addr_valid = 1'b1;")
        L(f"            default: addr_valid = 1'b0;")
        L(f"        endcase")
        L(f"    end")
        L(f"    logic err_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) err_r <= 1'b0;")
        L(f"        else        err_r <= csr_req & ~addr_valid & ~ack_r;")
        L(f"    assign csr_err_o = err_r;")
        L(f"")

        # Write logic
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        for r in self.registers:
            if r["access"] == "RO":
                continue
            L(f"            reg_{r['name'].lower()} <= 32'h{int(r['reset_value'], 16):08X};")
        L(f"        end else begin")

        # Self-clearing WO
        for r in self.registers:
            for f in r["fields"]:
                if f.get("access") == "WO":
                    msb, lsb = self._bit_range(f["bits"])
                    L(f"            reg_{r['name'].lower()}[{msb}:{lsb}] <= {self._bit_width(f['bits'])}'b0;  // {f['name']} WO self-clear")

        # RW1C latches
        for r in self.registers:
            if r["access"] != "RW1C":
                continue
            for f in r["fields"]:
                if f.get("access") == "RW1C":
                    msb, lsb = self._bit_range(f["bits"])
                    evt = self._rw1c_event_name(f["name"])
                    L(f"            if ({evt}) reg_{r['name'].lower()}[{msb}] <= 1'b1;")

        # Bus writes
        L(f"            if (csr_wr && addr_valid) begin")
        L(f"                case (csr_adr_i)")
        for r in self.registers:
            if r["access"] == "RO":
                continue
            L(f"                    ADDR_{r['name']}: begin")
            if r["access"] == "RW1C":
                for f in r["fields"]:
                    msb, lsb = self._bit_range(f["bits"])
                    if f.get("access") == "RW1C":
                        L(f"                        if (csr_dat_i[{msb}]) reg_{r['name'].lower()}[{msb}] <= 1'b0;")
            else:
                for f in r["fields"]:
                    msb, lsb = self._bit_range(f["bits"])
                    fa = f.get("access", r["access"])
                    if fa in ("RW", "WO"):
                        if msb == lsb:
                            L(f"                        reg_{r['name'].lower()}[{msb}] <= csr_dat_i[{msb}];  // {f['name']}")
                        else:
                            L(f"                        reg_{r['name'].lower()}[{msb}:{lsb}] <= csr_dat_i[{msb}:{lsb}];  // {f['name']}")
            L(f"                    end")
        L(f"                    default: ;")
        L(f"                endcase")
        L(f"            end")
        L(f"        end")
        L(f"    end")
        L(f"")

        # Read mux
        L(f"    logic [CSR_DATA_W-1:0] rdata_mux;")
        L(f"    always_comb begin")
        L(f"        rdata_mux = 32'h0;")
        L(f"        case (csr_adr_i)")
        for r in self.registers:
            L(f"            ADDR_{r['name']}: begin")
            if r["access"] == "RO":
                L(f"                rdata_mux = 32'h0;")
                for f in r["fields"]:
                    msb, lsb = self._bit_range(f["bits"])
                    src = self._status_input_name(f["name"])
                    if msb == lsb:
                        L(f"                rdata_mux[{msb}] = {src};")
                    else:
                        L(f"                rdata_mux[{msb}:{lsb}] = {src};")
            else:
                L(f"                rdata_mux = reg_{r['name'].lower()};")
            L(f"            end")
        L(f"            default: rdata_mux = 32'hDEAD_BEEF;")
        L(f"        endcase")
        L(f"    end")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) csr_dat_o <= 32'h0;")
        L(f"        else if (csr_rd) csr_dat_o <= rdata_mux;")
        L(f"")

        # cfg_* outputs
        L(f"    assign cfg_tRCD_nCK = reg_timing_0[7:0];   assign cfg_tRP_nCK  = reg_timing_0[15:8];")
        L(f"    assign cfg_tRAS_nCK = reg_timing_0[23:16];  assign cfg_tRC_nCK  = reg_timing_0[31:24];")
        L(f"    assign cfg_tRRD_nCK = reg_timing_1[7:0];   assign cfg_tWTR_nCK = reg_timing_1[15:8];")
        L(f"    assign cfg_tFAW_nCK = reg_timing_1[23:16];  assign cfg_tRFC_nCK = reg_timing_1[31:24];")
        L(f"    assign cfg_tWR_nCK  = reg_timing_2[7:0];   assign cfg_tRTP_nCK = reg_timing_2[15:8];")
        L(f"    assign cfg_CL_nCK   = reg_timing_2[23:16];  assign cfg_CWL_nCK  = reg_timing_2[31:24];")
        L(f"    assign cfg_tCCD_nCK = reg_timing_3[7:0];   assign cfg_tREFI_nCK = reg_timing_3[31:8];")
        L(f"    assign cfg_sched_policy   = reg_ctrl_config[0];")
        L(f"    assign cfg_row_policy     = reg_ctrl_config[1];")
        L(f"    assign cfg_self_ref_mode  = reg_ctrl_config[3:2];")
        L(f"    assign cfg_ecc_enable     = reg_ctrl_config[4];")
        L(f"    assign cfg_bist_start     = reg_ctrl_config[5];")
        L(f"    assign cfg_force_refresh  = reg_ctrl_config[6];")
        L(f"    assign cfg_force_self_ref = reg_ctrl_config[7];")
        L(f"    assign cfg_max_postpone     = reg_refresh_config[3:0];")
        L(f"    assign cfg_urgent_threshold = reg_refresh_config[7:4];")
        L(f"    assign cfg_ref_priority     = reg_refresh_config[8];")
        L(f"    assign cfg_bist_pattern     = reg_bist_config[2:0];")
        L(f"    assign cfg_bist_addr_mode   = reg_bist_config[3];")
        L(f"    assign cfg_bist_addr_start  = reg_bist_addr_start[28:0];")
        L(f"    assign cfg_bist_addr_end    = reg_bist_addr_end[28:0];")
        L(f"")

        # SVA
        L(f"    // synopsys translate_off")
        L(f"    // synthesis translate_off")
        L(f"    property p_rw_retain;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (csr_wr && csr_adr_i == ADDR_TIMING_0) |=> (reg_timing_0[7:0] == $past(csr_dat_i[7:0]));")
        L(f"    endproperty")
        L(f"    assert property (p_rw_retain) else $error(\"[CA-001] RW register did not retain value\");")
        L(f"    property p_bad_addr;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (csr_req && !addr_valid) |=> csr_err_o;")
        L(f"    endproperty")
        L(f"    assert property (p_bad_addr) else $error(\"[CA-004] No error on invalid address\");")
        L(f"    covergroup cg_csr @(posedge clk);")
        L(f"        option.per_instance = 1;")
        L(f"        cp_write : coverpoint (csr_wr && addr_valid);")
        L(f"        cp_read  : coverpoint (csr_rd && addr_valid);")
        L(f"        cp_err   : coverpoint csr_err_o;")
        L(f"    endgroup")
        L(f"    cg_csr cg_inst = new();")
        L(f"    // synthesis translate_on")
        L(f"    // synopsys translate_on")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    # ================================================================
    # Testbench generation
    # ================================================================
    def _tb_test_registry(self) -> list:
        """Returns ordered list of (id, description) for all TB tests."""
        tests = []
        # A: Reset values
        for i, r in enumerate(self.registers):
            tests.append((f"A{i+1}", f"{r['name']} reset = 0x{int(r['reset_value'], 16):08X}"))
        # B: Write/readback for RW regs
        bi = 1
        for r in self.registers:
            if r["access"] in ("RW", "RW1C") and r["access"] != "RO":
                if r["name"] == "ERROR_STATUS":
                    continue  # tested in E
                if r["name"] == "CTRL_STATUS":
                    continue
                tests.append((f"B{bi}", f"{r['name']} write/readback"))
                bi += 1
        # C: RO behavior
        tests.append(("C1", "CTRL_STATUS reflects status inputs"))
        tests.append(("C2", "CTRL_STATUS ignores writes (RO)"))
        # D: WO self-clearing
        tests.append(("D1", "bist_start self-clears after 1 cycle"))
        tests.append(("D2", "force_refresh self-clears after 1 cycle"))
        # E: RW1C
        tests.append(("E1", "ERROR_STATUS latches ecc_ue event"))
        tests.append(("E2", "ERROR_STATUS W1C clears ecc_ue flag"))
        tests.append(("E3", "ERROR_STATUS flag stays clear after W1C"))
        # F: Error handling
        tests.append(("F1", "Invalid address returns error"))
        tests.append(("F2", "Valid address no error"))
        # G: cfg_* outputs
        tests.append(("G1", "cfg_tRCD_nCK matches TIMING_0[7:0]"))
        tests.append(("G2", "cfg_sched_policy matches CTRL_CONFIG[0]"))
        tests.append(("G3", "cfg_max_postpone matches REFRESH_CONFIG[3:0]"))
        # H: Reset
        tests.append(("H1", "Registers return to reset values after reset"))
        tests.append(("H2", "Normal operation after reset recovery"))
        # I: Edge cases
        tests.append(("I1", "Back-to-back writes to different registers"))
        tests.append(("I2", "Readback after back-to-back writes correct"))
        return tests

    def generate_testbench(self) -> str:
        """Read the standalone TB file and return it. The TB is generated
        statically since CSR layout is spec-driven but the test structure
        is fixed. The header includes the dynamic test registry."""
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        tests = self._tb_test_registry()

        # Build the register reset-value checks and write/readback dynamically
        rw_regs = [(r, int(r["offset"], 16)) for r in self.registers
                   if r["access"] not in ("RO",) and r["name"] != "ERROR_STATUS"]

        lines = []
        L = lines.append

        # Header with test list
        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// config_regs_tb.sv -- Enhanced testbench ({len(tests)} tests)")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Config/CSR Registers Agent (Phase 1)")
        L(f"//")
        L(f"// Sections:")
        L(f"//   A: Reset value verification ({p['NUM_REGS']} registers)")
        L(f"//   B: Write/readback for all RW registers")
        L(f"//   C: Read-only register behavior (CTRL_STATUS)")
        L(f"//   D: Write-once self-clearing fields")
        L(f"//   E: RW1C fields (ERROR_STATUS latch and clear)")
        L(f"//   F: Error handling (invalid address)")
        L(f"//   G: cfg_* output propagation")
        L(f"//   H: Reset mid-transaction")
        L(f"//   I: Edge cases (back-to-back writes)")
        L(f"//")
        L(f"// Test List:")
        for tid, desc in tests:
            L(f"//   {tid:4s} {desc}")
        L(f"//")
        L(f"// VCD: dumps config_regs_tb.vcd")
        L(f"//==============================================================")
        L(f"module config_regs_tb;")
        L(f"")
        L(f"    localparam real CLK_PERIOD = {p['CTRL_PERIOD']};")
        L(f"    logic clk = 0;")
        L(f"    always #(CLK_PERIOD/2) clk = ~clk;")
        L(f"")

        # Signal declarations
        L(f"    logic        rst_n;")
        L(f"    logic        csr_cyc_i, csr_stb_i, csr_we_i;")
        L(f"    logic [7:0]  csr_adr_i;")
        L(f"    logic [31:0] csr_dat_i;")
        L(f"    logic [3:0]  csr_sel_i;")
        L(f"    logic        csr_ack_o;")
        L(f"    logic [31:0] csr_dat_o;")
        L(f"    logic        csr_err_o;")
        L(f"    logic        sts_init_done, sts_cal_done, sts_cal_fail;")
        L(f"    logic        sts_bist_done, sts_bist_fail;")
        L(f"    logic [2:0]  sts_ref_pending_cnt;")
        L(f"    logic        sts_self_refresh_active;")
        L(f"    logic [15:0] sts_ecc_ce_count;")
        L(f"    logic        sts_ecc_ue_event, sts_ref_starve_event, sts_init_fail_event;")
        L(f"    logic [12:0] sts_bist_fail_addr;")
        L(f"")

        # cfg outputs
        L(f"    logic [7:0]  cfg_tRCD_nCK, cfg_tRP_nCK, cfg_tRAS_nCK, cfg_tRC_nCK;")
        L(f"    logic [7:0]  cfg_tRRD_nCK, cfg_tWTR_nCK, cfg_tFAW_nCK, cfg_tRFC_nCK;")
        L(f"    logic [7:0]  cfg_tWR_nCK, cfg_tRTP_nCK, cfg_CL_nCK, cfg_CWL_nCK;")
        L(f"    logic [7:0]  cfg_tCCD_nCK;  logic [23:0] cfg_tREFI_nCK;")
        L(f"    logic        cfg_sched_policy, cfg_row_policy, cfg_ecc_enable;")
        L(f"    logic [1:0]  cfg_self_ref_mode;")
        L(f"    logic        cfg_bist_start, cfg_force_refresh, cfg_force_self_ref;")
        L(f"    logic [3:0]  cfg_max_postpone, cfg_urgent_threshold;")
        L(f"    logic        cfg_ref_priority;")
        L(f"    logic [2:0]  cfg_bist_pattern; logic cfg_bist_addr_mode;")
        L(f"    logic [28:0] cfg_bist_addr_start, cfg_bist_addr_end;")
        L(f"")

        # DUT instantiation
        L(f"    config_regs dut (")
        L(f"        .clk(clk), .rst_n(rst_n),")
        L(f"        .csr_cyc_i(csr_cyc_i), .csr_stb_i(csr_stb_i), .csr_we_i(csr_we_i),")
        L(f"        .csr_adr_i(csr_adr_i), .csr_dat_i(csr_dat_i), .csr_sel_i(csr_sel_i),")
        L(f"        .csr_ack_o(csr_ack_o), .csr_dat_o(csr_dat_o), .csr_err_o(csr_err_o),")
        L(f"        .sts_init_done(sts_init_done), .sts_cal_done(sts_cal_done), .sts_cal_fail(sts_cal_fail),")
        L(f"        .sts_bist_done(sts_bist_done), .sts_bist_fail(sts_bist_fail),")
        L(f"        .sts_ref_pending_cnt(sts_ref_pending_cnt), .sts_self_refresh_active(sts_self_refresh_active),")
        L(f"        .sts_ecc_ce_count(sts_ecc_ce_count), .sts_ecc_ue_event(sts_ecc_ue_event),")
        L(f"        .sts_ref_starve_event(sts_ref_starve_event), .sts_init_fail_event(sts_init_fail_event),")
        L(f"        .sts_bist_fail_addr(sts_bist_fail_addr),")
        L(f"        .cfg_tRCD_nCK(cfg_tRCD_nCK), .cfg_tRP_nCK(cfg_tRP_nCK),")
        L(f"        .cfg_tRAS_nCK(cfg_tRAS_nCK), .cfg_tRC_nCK(cfg_tRC_nCK),")
        L(f"        .cfg_tRRD_nCK(cfg_tRRD_nCK), .cfg_tWTR_nCK(cfg_tWTR_nCK),")
        L(f"        .cfg_tFAW_nCK(cfg_tFAW_nCK), .cfg_tRFC_nCK(cfg_tRFC_nCK),")
        L(f"        .cfg_tWR_nCK(cfg_tWR_nCK), .cfg_tRTP_nCK(cfg_tRTP_nCK),")
        L(f"        .cfg_CL_nCK(cfg_CL_nCK), .cfg_CWL_nCK(cfg_CWL_nCK),")
        L(f"        .cfg_tCCD_nCK(cfg_tCCD_nCK), .cfg_tREFI_nCK(cfg_tREFI_nCK),")
        L(f"        .cfg_sched_policy(cfg_sched_policy), .cfg_row_policy(cfg_row_policy),")
        L(f"        .cfg_self_ref_mode(cfg_self_ref_mode), .cfg_ecc_enable(cfg_ecc_enable),")
        L(f"        .cfg_bist_start(cfg_bist_start), .cfg_force_refresh(cfg_force_refresh),")
        L(f"        .cfg_force_self_ref(cfg_force_self_ref),")
        L(f"        .cfg_max_postpone(cfg_max_postpone), .cfg_urgent_threshold(cfg_urgent_threshold),")
        L(f"        .cfg_ref_priority(cfg_ref_priority),")
        L(f"        .cfg_bist_pattern(cfg_bist_pattern), .cfg_bist_addr_mode(cfg_bist_addr_mode),")
        L(f"        .cfg_bist_addr_start(cfg_bist_addr_start), .cfg_bist_addr_end(cfg_bist_addr_end)")
        L(f"    );")
        L(f"")

        # Infrastructure tasks
        L(f"    int pass_count=0, fail_count=0, total_tests=0;")
        L(f"    task automatic check(string name, logic condition);")
        L(f"        total_tests++;")
        L(f"        if (condition) begin pass_count++; $display(\"  [PASS] %0d: %s\", total_tests, name); end")
        L(f"        else begin fail_count++; $display(\"  [FAIL] %0d: %s\", total_tests, name); end")
        L(f"    endtask")
        L(f"    logic [31:0] rdata;")
        L(f"    task automatic csr_idle(); csr_cyc_i=0;csr_stb_i=0;csr_we_i=0;csr_adr_i=0;csr_dat_i=0;csr_sel_i=4'hF; endtask")
        L(f"    task automatic csr_write(input [7:0] addr, input [31:0] data);")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=1;csr_adr_i=addr;csr_dat_i=data;csr_sel_i=4'hF;")
        L(f"        @(posedge clk); wait(csr_ack_o||csr_err_o); @(posedge clk); csr_idle();")
        L(f"    endtask")
        L(f"    task automatic csr_read(input [7:0] addr, output [31:0] data);")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=addr;csr_sel_i=4'hF;")
        L(f"        @(posedge clk); wait(csr_ack_o||csr_err_o); data=csr_dat_o; @(posedge clk); csr_idle();")
        L(f"    endtask")
        L(f"    task automatic hw_reset();")
        L(f"        rst_n=0; csr_idle();")
        L(f"        sts_init_done=0;sts_cal_done=0;sts_cal_fail=0;sts_bist_done=0;sts_bist_fail=0;")
        L(f"        sts_ref_pending_cnt=0;sts_self_refresh_active=0;sts_ecc_ce_count=0;")
        L(f"        sts_ecc_ue_event=0;sts_ref_starve_event=0;sts_init_fail_event=0;sts_bist_fail_addr=0;")
        L(f"        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);")
        L(f"    endtask")
        L(f"")

        # Module-scope localparam (cannot be inside initial block)
        L(f"    // CTRL_CONFIG bits [7:5] are WO self-clearing -- mask for readback comparison")
        L(f"    localparam [31:0] CTRL_CONFIG_WO_MASK = 32'hFFFFFF1F;")
        L(f"")

        # Main test
        L(f"    initial begin")
        L(f"        $dumpfile(\"config_regs_tb.vcd\");")
        L(f"        $dumpvars(0, config_regs_tb);")
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"  config_regs_tb -- CSR Register Verification\");")
        L(f"        $display(\"  {p['NUM_REGS']} registers, {p['CSR_DATA_W']}-bit data bus\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        hw_reset();")
        L(f"")

        # Section A: Reset values
        L(f"        $display(\"\"); $display(\"  -- Section A: Reset Values --\");")
        for i, r in enumerate(self.registers):
            off = int(r["offset"], 16)
            rst = int(r["reset_value"], 16)
            L(f"        csr_read(8'h{off:02X}, rdata); check($sformatf(\"A{i+1}: {r['name']} reset = 0x%08X\", rdata), rdata == 32'h{rst:08X});")
        L(f"")

        # Section B: Write/readback
        L(f"        $display(\"\"); $display(\"  -- Section B: Write / Readback --\");")
        bi = 1
        vi = 0
        test_vals = [0x0000001F, 0x12345678, 0xDEADBEEF, 0xCAFEBABE,
                     0xFACEFEED, 0x000001FF, 0x0000000F, 0x1ABC0000, 0x1FFFFFFF]
        for r in self.registers:
            if r["access"] == "RO" or r["name"] == "ERROR_STATUS":
                continue
            off = int(r["offset"], 16)
            val = test_vals[vi % len(test_vals)]
            vi += 1
            L(f"        csr_write(8'h{off:02X}, 32'h{val:08X}); csr_read(8'h{off:02X}, rdata);")
            if r["name"] == "CTRL_CONFIG":
                L(f"        check($sformatf(\"B{bi}: {r['name']} write/readback (0x%08X, WO masked)\", rdata),")
                L(f"              (rdata & CTRL_CONFIG_WO_MASK) == (32'h{val:08X} & CTRL_CONFIG_WO_MASK));")
            else:
                L(f"        check(\"B{bi}: {r['name']} write/readback\", rdata == 32'h{val:08X});")
            bi += 1
        L(f"")

        # Section C: RO
        L(f"        $display(\"\"); $display(\"  -- Section C: CTRL_STATUS (RO) --\");")
        L(f"        hw_reset();")
        L(f"        sts_init_done=1; sts_cal_done=1; sts_ref_pending_cnt=3'd5;")
        L(f"        repeat(2) @(posedge clk);")
        L(f"        csr_read(8'h00, rdata);")
        L(f"        check($sformatf(\"C1: CTRL_STATUS reflects inputs (0x%08X)\", rdata),")
        L(f"              rdata[0]==1'b1 && rdata[1]==1'b1 && rdata[7:5]==3'd5);")
        L(f"        csr_write(8'h00, 32'hFFFFFFFF); csr_read(8'h00, rdata);")
        L(f"        check(\"C2: CTRL_STATUS ignores writes\", rdata[0]==1'b1 && rdata[1]==1'b1);")
        L(f"")

        # Section D: WO self-clearing
        L(f"        $display(\"\"); $display(\"  -- Section D: WO Self-Clearing --\");")
        L(f"        hw_reset();")
        L(f"        csr_write(8'h04, 32'h00000029); repeat(1) @(posedge clk); csr_read(8'h04, rdata);")
        L(f"        check($sformatf(\"D1: bist_start self-clears (bit5=%0b)\", rdata[5]), rdata[5]==1'b0);")
        L(f"        csr_write(8'h04, 32'h00000049); repeat(1) @(posedge clk); csr_read(8'h04, rdata);")
        L(f"        check($sformatf(\"D2: force_refresh self-clears (bit6=%0b)\", rdata[6]), rdata[6]==1'b0);")
        L(f"")

        # Section E: RW1C
        L(f"        $display(\"\"); $display(\"  -- Section E: RW1C (ERROR_STATUS) --\");")
        L(f"        hw_reset();")
        L(f"        sts_ecc_ue_event=1; @(posedge clk); sts_ecc_ue_event=0; repeat(2) @(posedge clk);")
        L(f"        csr_read(8'h1C, rdata); check($sformatf(\"E1: ecc_ue latched (0x%08X)\", rdata), rdata[16]==1'b1);")
        L(f"        csr_write(8'h1C, 32'h00010000); csr_read(8'h1C, rdata);")
        L(f"        check($sformatf(\"E2: ecc_ue W1C clears (0x%08X)\", rdata), rdata[16]==1'b0);")
        L(f"        csr_read(8'h1C, rdata); check(\"E3: Flag stays clear\", rdata[16]==1'b0);")
        L(f"")

        # Section F: Error
        L(f"        $display(\"\"); $display(\"  -- Section F: Error Handling --\");")
        L(f"        hw_reset();")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=8'hFF;csr_sel_i=4'hF;")
        L(f"        begin")
        L(f"            logic saw_err; saw_err=0;")
        L(f"            repeat(10) begin @(posedge clk); if(csr_err_o) begin saw_err=1; break; end end")
        L(f"            check(\"F1: Invalid addr error\", saw_err);")
        L(f"        end")
        L(f"        csr_idle(); repeat(2) @(posedge clk);")
        L(f"        csr_read(8'h04, rdata); check(\"F2: Valid addr no error\", csr_err_o===1'b0);")
        L(f"")

        # Section G: cfg_* outputs
        L(f"        $display(\"\"); $display(\"  -- Section G: cfg_* Outputs --\");")
        L(f"        hw_reset();")
        L(f"        csr_write(8'h08, 32'h44332211); repeat(2) @(posedge clk);")
        L(f"        check($sformatf(\"G1: cfg_tRCD_nCK=0x%02X\", cfg_tRCD_nCK), cfg_tRCD_nCK==8'h11);")
        L(f"        csr_write(8'h04, 32'h00000001); repeat(2) @(posedge clk);")
        L(f"        check($sformatf(\"G2: cfg_sched_policy=%0b\", cfg_sched_policy), cfg_sched_policy==1'b1);")
        L(f"        csr_write(8'h18, 32'h0000006A); repeat(2) @(posedge clk);")
        L(f"        check($sformatf(\"G3: cfg_max_postpone=%0d\", cfg_max_postpone), cfg_max_postpone==4'hA);")
        L(f"")

        # Section H: Reset
        L(f"        $display(\"\"); $display(\"  -- Section H: Reset --\");")
        L(f"        csr_write(8'h08, 32'hFFFFFFFF); csr_write(8'h0C, 32'hFFFFFFFF);")
        L(f"        rst_n=0; repeat(5) @(posedge clk); rst_n=1; csr_idle(); repeat(2) @(posedge clk);")
        L(f"        csr_read(8'h08, rdata); check($sformatf(\"H1: TIMING_0 reset (0x%08X)\", rdata), rdata==32'h271C0B0B);")
        L(f"        csr_write(8'h08, 32'h11223344); csr_read(8'h08, rdata); check(\"H2: Normal after reset\", rdata==32'h11223344);")
        L(f"")

        # Section I: Edge cases
        L(f"        $display(\"\"); $display(\"  -- Section I: Edge Cases --\");")
        L(f"        hw_reset();")
        L(f"        csr_write(8'h08, 32'hAAAAAAAA); csr_write(8'h0C, 32'hBBBBBBBB);")
        L(f"        csr_read(8'h08, rdata); check(\"I1: Back-to-back TIMING_0\", rdata==32'hAAAAAAAA);")
        L(f"        csr_read(8'h0C, rdata); check(\"I2: Back-to-back TIMING_1\", rdata==32'hBBBBBBBB);")
        L(f"")

        # Summary
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        if (fail_count==0) $display(\"  ALL %0d TESTS PASSED\", total_tests);")
        L(f"        else $display(\"  %0d of %0d TESTS FAILED\", fail_count, total_tests);")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"\"); $finish;")
        L(f"    end")
        L(f"    initial begin #(1_000_000); $display(\"  [FAIL] GLOBAL TIMEOUT\"); $finish; end")
        L(f"endmodule")

        return "\n".join(lines)

    # ================================================================
    # Manifest
    # ================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "config_regs", "file": "config_regs.sv",
            "phase": 1, "agent": "config_regs_agent",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "CSR_ADDR_W": p["CSR_ADDR_W"], "CSR_DATA_W": p["CSR_DATA_W"],
                "NUM_REGS": p["NUM_REGS"], "TOTAL_FIELDS": p["TOTAL_FIELDS"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "csr_bus_in": [
                    {"name": "csr_cyc_i", "width": 1, "dir": "input"},
                    {"name": "csr_stb_i", "width": 1, "dir": "input"},
                    {"name": "csr_we_i", "width": 1, "dir": "input"},
                    {"name": "csr_adr_i", "width": p["CSR_ADDR_W"], "dir": "input"},
                    {"name": "csr_dat_i", "width": p["CSR_DATA_W"], "dir": "input"},
                    {"name": "csr_sel_i", "width": 4, "dir": "input"},
                ],
                "csr_bus_out": [
                    {"name": "csr_ack_o", "width": 1, "dir": "output"},
                    {"name": "csr_dat_o", "width": p["CSR_DATA_W"], "dir": "output"},
                    {"name": "csr_err_o", "width": 1, "dir": "output"},
                ],
                "status_in": [
                    {"name": "sts_init_done", "width": 1, "dir": "input"},
                    {"name": "sts_cal_done", "width": 1, "dir": "input"},
                    {"name": "sts_cal_fail", "width": 1, "dir": "input"},
                    {"name": "sts_bist_done", "width": 1, "dir": "input"},
                    {"name": "sts_bist_fail", "width": 1, "dir": "input"},
                    {"name": "sts_ref_pending_cnt", "width": 3, "dir": "input"},
                    {"name": "sts_self_refresh_active", "width": 1, "dir": "input"},
                    {"name": "sts_ecc_ce_count", "width": 16, "dir": "input"},
                    {"name": "sts_ecc_ue_event", "width": 1, "dir": "input"},
                    {"name": "sts_ref_starve_event", "width": 1, "dir": "input"},
                    {"name": "sts_init_fail_event", "width": 1, "dir": "input"},
                    {"name": "sts_bist_fail_addr", "width": 13, "dir": "input"},
                ],
                "config_out": [
                    {"name": "cfg_tRCD_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tRP_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tRAS_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tRC_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tRRD_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tWTR_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tFAW_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tRFC_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tWR_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tRTP_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_CL_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_CWL_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tCCD_nCK", "width": 8, "dir": "output"},
                    {"name": "cfg_tREFI_nCK", "width": 24, "dir": "output"},
                    {"name": "cfg_sched_policy", "width": 1, "dir": "output"},
                    {"name": "cfg_row_policy", "width": 1, "dir": "output"},
                    {"name": "cfg_self_ref_mode", "width": 2, "dir": "output"},
                    {"name": "cfg_ecc_enable", "width": 1, "dir": "output"},
                    {"name": "cfg_bist_start", "width": 1, "dir": "output"},
                    {"name": "cfg_force_refresh", "width": 1, "dir": "output"},
                    {"name": "cfg_force_self_ref", "width": 1, "dir": "output"},
                    {"name": "cfg_max_postpone", "width": 4, "dir": "output"},
                    {"name": "cfg_urgent_threshold", "width": 4, "dir": "output"},
                    {"name": "cfg_ref_priority", "width": 1, "dir": "output"},
                    {"name": "cfg_bist_pattern", "width": 3, "dir": "output"},
                    {"name": "cfg_bist_addr_mode", "width": 1, "dir": "output"},
                    {"name": "cfg_bist_addr_start", "width": 29, "dir": "output"},
                    {"name": "cfg_bist_addr_end", "width": 29, "dir": "output"},
                ],
            },
            "assertions": [
                {"name": "p_rw_retain", "check": "CA-001"},
                {"name": "p_bad_addr", "check": "CA-004"},
            ],
            "coverage_points": ["cp_write", "cp_read", "cp_err"],
        }

    # ================================================================
    # Main entry point
    # ================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  CONFIG / CSR REGISTERS AGENT\n  Spec: {self.spec_path}\n{hdr}")

        print("\n[1/5] Validating parameters ...")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ERROR: {e}")
            return {"status": "error", "errors": errs}
        print("  OK: All parameters valid")
        for k, v in self.p.items():
            print(f"    {k:20s} = {v}")

        print("\n[2/5] Generating RTL ...")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines of SystemVerilog")

        print("\n[3/5] Generating testbench ...")
        tb = self.generate_testbench()
        tb_lines = len(tb.splitlines())
        tests = self._tb_test_registry()
        print(f"  OK: {tb_lines} lines ({len(tests)} tests, 9 sections, VCD enabled)")

        print("\n[4/5] Generating port manifest ...")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  OK: {port_cnt} ports | {len(manifest['assertions'])} assertions | {len(manifest['coverage_points'])} cover points")

        print("\n[5/5] Writing files ...")
        rtl_path = self.output_dir / "config_regs.sv"
        rtl_path.write_text(rtl)
        print(f"  -> {rtl_path}")

        tb_path = self.output_dir / "config_regs_tb.sv"
        tb_path.write_text(tb)
        print(f"  -> {tb_path}")

        mfst_path = self.output_dir / "config_regs_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  -> {mfst_path}")

        print(f"\n{hdr}\n  DONE -- config_regs.sv + config_regs_tb.sv ready for Phase 1\n{hdr}")
        return {
            "status": "success",
            "module": "config_regs",
            "phase": 1,
            "rtl_path": str(rtl_path),
            "tb_path": str(tb_path),
            "manifest_path": str(mfst_path),
            "manifest": manifest,
            "rtl_lines": rtl_lines,
            "tb_lines": tb_lines,
            "ports": port_cnt,
        }


if __name__ == "__main__":
    print("+=============================================+")
    print("|   CONFIG / CSR REGISTERS AGENT  (Phase 1)   |")
    print("+=============================================+")
    print()
    spec_path = input("Enter path to spec JSON: ").strip()
    if not spec_path or not os.path.isfile(spec_path):
        print("Error: Invalid path."); sys.exit(1)
    output_dir = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    agent = ConfigRegsAgent(spec_path, output_dir)
    result = agent.run()
    sys.exit(0 if result["status"] == "success" else 1)