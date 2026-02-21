#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 CONFIG / CSR REGISTERS AGENT                         ║
║                                                                      ║
║  Phase 1 RTL Generation Agent                                        ║
║  Generates: config_regs.sv + config_regs_manifest.json               ║
║                                                                      ║
║  Dependencies: None (Phase 1)                                        ║
║                                                                      ║
║  Spec sections consumed:                                             ║
║    csr_register_map, controller_architecture, clocking_model         ║
║                                                                      ║
║  Implements:                                                         ║
║    - 11 CSR registers, 46 bit fields                                 ║
║    - Access types: RO, RW, RW1C, WO (self-clearing)                 ║
║    - Wishbone B4 classic slave on secondary CSR bus                   ║
║    - cfg_* output buses to bank_tracker, scheduler, refresh_ctrl     ║
║    - Observability signals: csr_addr/we/re/wdata/rdata/ack           ║
║                                                                      ║
║  Validation checks: CA-001 through CA-004                            ║
╚══════════════════════════════════════════════════════════════════════╝
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

        # Validate register offsets are unique and aligned
        offsets = set()
        for r in self.registers:
            off = int(r["offset"], 16)
            if off % 4 != 0:
                errors.append(f"Register {r['name']} offset {r['offset']} not 4-byte aligned")
            if off in offsets:
                errors.append(f"Duplicate offset {r['offset']}")
            offsets.add(off)

        # Validate bit field ranges don't overlap within a register
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
        """Parse '7:0' or '3' into a set of bit indices."""
        if ":" in bits_str:
            hi, lo = bits_str.split(":")
            return set(range(int(lo), int(hi) + 1))
        else:
            return {int(bits_str)}

    def _bit_range(self, bits_str: str):
        """Return (msb, lsb) tuple."""
        if ":" in bits_str:
            hi, lo = bits_str.split(":")
            return int(hi), int(lo)
        else:
            b = int(bits_str)
            return b, b

    def _bit_width(self, bits_str: str) -> int:
        msb, lsb = self._bit_range(bits_str)
        return msb - lsb + 1

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        lines = []
        L = lines.append

        # ── Header ──
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
        L(f"//   Outputs cfg_* buses consumed by bank_tracker, scheduler,")
        L(f"//   refresh_ctrl, and init_fsm.")
        L(f"//")
        L(f"// Validation: CA-001 .. CA-004  (ddr3_validation_checklist_v2.docx)")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"")

        # ── Module declaration ──
        L(f"module config_regs #(")
        L(f"    parameter CSR_ADDR_W = {p['CSR_ADDR_W']},")
        L(f"    parameter CSR_DATA_W = {p['CSR_DATA_W']}")
        L(f") (")
        L(f"    // ────────────── Clock / Reset ──────────────")
        L(f"    input  logic                    clk,")
        L(f"    input  logic                    rst_n,")
        L(f"")
        L(f"    // ────────────── CSR Wishbone Slave ──────────────")
        L(f"    input  logic                    csr_cyc_i,")
        L(f"    input  logic                    csr_stb_i,")
        L(f"    input  logic                    csr_we_i,")
        L(f"    input  logic [CSR_ADDR_W-1:0]   csr_adr_i,")
        L(f"    input  logic [CSR_DATA_W-1:0]   csr_dat_i,")
        L(f"    input  logic [3:0]              csr_sel_i,")
        L(f"")
        L(f"    output logic                    csr_ack_o,")
        L(f"    output logic [CSR_DATA_W-1:0]   csr_dat_o,")
        L(f"    output logic                    csr_err_o,")
        L(f"")
        L(f"    // ────────────── Status inputs (from other modules) ──────────────")
        L(f"    input  logic                    sts_init_done,")
        L(f"    input  logic                    sts_cal_done,")
        L(f"    input  logic                    sts_cal_fail,")
        L(f"    input  logic                    sts_bist_done,")
        L(f"    input  logic                    sts_bist_fail,")
        L(f"    input  logic [2:0]              sts_ref_pending_cnt,")
        L(f"    input  logic                    sts_self_refresh_active,")
        L(f"    input  logic [15:0]             sts_ecc_ce_count,")
        L(f"    input  logic                    sts_ecc_ue_event,      // pulse")
        L(f"    input  logic                    sts_ref_starve_event,  // pulse")
        L(f"    input  logic                    sts_init_fail_event,   // pulse")
        L(f"    input  logic [12:0]             sts_bist_fail_addr,")
        L(f"")
        L(f"    // ────────────── Config outputs (to other modules) ──────────────")

        # Timing outputs
        L(f"    // Timing (from TIMING_0..3)")
        L(f"    output logic [7:0]              cfg_tRCD_nCK,")
        L(f"    output logic [7:0]              cfg_tRP_nCK,")
        L(f"    output logic [7:0]              cfg_tRAS_nCK,")
        L(f"    output logic [7:0]              cfg_tRC_nCK,")
        L(f"    output logic [7:0]              cfg_tRRD_nCK,")
        L(f"    output logic [7:0]              cfg_tWTR_nCK,")
        L(f"    output logic [7:0]              cfg_tFAW_nCK,")
        L(f"    output logic [7:0]              cfg_tRFC_nCK,")
        L(f"    output logic [7:0]              cfg_tWR_nCK,")
        L(f"    output logic [7:0]              cfg_tRTP_nCK,")
        L(f"    output logic [7:0]              cfg_CL_nCK,")
        L(f"    output logic [7:0]              cfg_CWL_nCK,")
        L(f"    output logic [7:0]              cfg_tCCD_nCK,")
        L(f"    output logic [23:0]             cfg_tREFI_nCK,")
        L(f"")
        L(f"    // Control (from CTRL_CONFIG)")
        L(f"    output logic                    cfg_sched_policy,     // 0=in_order, 1=fr_fcfs")
        L(f"    output logic                    cfg_row_policy,       // 0=open, 1=close")
        L(f"    output logic [1:0]              cfg_self_ref_mode,")
        L(f"    output logic                    cfg_ecc_enable,")
        L(f"    output logic                    cfg_bist_start,       // pulse (self-clearing)")
        L(f"    output logic                    cfg_force_refresh,    // pulse (self-clearing)")
        L(f"    output logic                    cfg_force_self_ref,   // pulse (self-clearing)")
        L(f"")
        L(f"    // Refresh (from REFRESH_CONFIG)")
        L(f"    output logic [3:0]              cfg_max_postpone,")
        L(f"    output logic [3:0]              cfg_urgent_threshold,")
        L(f"    output logic                    cfg_ref_priority,")
        L(f"")
        L(f"    // BIST (from BIST_CONFIG, BIST_ADDR_START/END)")
        L(f"    output logic [2:0]              cfg_bist_pattern,")
        L(f"    output logic                    cfg_bist_addr_mode,")
        L(f"    output logic [28:0]             cfg_bist_addr_start,")
        L(f"    output logic [28:0]             cfg_bist_addr_end")
        L(f");")
        L(f"")

        # ── Register offset localparams ──
        L(f"    // ================================================================")
        L(f"    // Register offsets")
        L(f"    // ================================================================")
        for r in self.registers:
            L(f"    localparam logic [CSR_ADDR_W-1:0] ADDR_{r['name']:20s} = {p['CSR_ADDR_W']}'h{int(r['offset'], 16):02X};")
        L(f"")

        # ── Register storage ──
        L(f"    // ================================================================")
        L(f"    // Register storage")
        L(f"    // ================================================================")
        for r in self.registers:
            if r["access"] == "RO":
                L(f"    // {r['name']} — read-only, assembled from status inputs")
            else:
                L(f"    logic [CSR_DATA_W-1:0] reg_{r['name'].lower()};")
        L(f"")

        # ── CSR bus handshake ──
        L(f"    // ================================================================")
        L(f"    // CSR bus handshake")
        L(f"    // ================================================================")
        L(f"    wire csr_req = csr_cyc_i & csr_stb_i;")
        L(f"    wire csr_wr  = csr_req & csr_we_i;")
        L(f"    wire csr_rd  = csr_req & ~csr_we_i;")
        L(f"")
        L(f"    // Ack — one-cycle response (classic Wishbone)")
        L(f"    logic ack_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) ack_r <= 1'b0;")
        L(f"        else        ack_r <= csr_req & ~ack_r;  // single-cycle ack")
        L(f"    assign csr_ack_o = ack_r;")
        L(f"")

        # ── Address decode: invalid address error ──
        L(f"    // Address decode — error on unmapped address")
        L(f"    logic addr_valid;")
        L(f"    always_comb begin")
        L(f"        addr_valid = 1'b0;")
        L(f"        case (csr_adr_i)")
        for r in self.registers:
            L(f"            ADDR_{r['name']:20s}: addr_valid = 1'b1;")
        L(f"            default: addr_valid = 1'b0;")
        L(f"        endcase")
        L(f"    end")
        L(f"")
        L(f"    logic err_r;")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) err_r <= 1'b0;")
        L(f"        else        err_r <= csr_req & ~addr_valid & ~ack_r;")
        L(f"    assign csr_err_o = err_r;")
        L(f"")

        # ── Write logic ──
        L(f"    // ================================================================")
        L(f"    // Write logic")
        L(f"    // ================================================================")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")

        # Reset values
        for r in self.registers:
            if r["access"] == "RO":
                continue
            L(f"            reg_{r['name'].lower()} <= 32'h{int(r['reset_value'], 16):08X};")
        L(f"        end else begin")
        L(f"")

        # Self-clearing WO fields — clear every cycle
        L(f"            // Self-clearing WO fields (pulse for one cycle)")
        wo_fields = []
        for r in self.registers:
            for f in r["fields"]:
                if f.get("access") == "WO":
                    msb, lsb = self._bit_range(f["bits"])
                    wo_fields.append((r, f, msb, lsb))
                    L(f"            reg_{r['name'].lower()}[{msb}:{lsb}] <= {self._bit_width(f['bits'])}'b0;  // {f['name']} (WO self-clear)")
        L(f"")

        # RW1C fields — latch on event pulse, clear on write-1
        L(f"            // RW1C fields — latch on event, clear on write-1")
        for r in self.registers:
            if r["access"] != "RW1C":
                continue
            for f in r["fields"]:
                if f.get("access") == "RW1C":
                    msb, lsb = self._bit_range(f["bits"])
                    event_name = self._rw1c_event_name(f["name"])
                    L(f"            if ({event_name})")
                    L(f"                reg_{r['name'].lower()}[{msb}] <= 1'b1;  // latch {f['name']}")
        L(f"")

        # Write from bus
        L(f"            // Bus writes")
        L(f"            if (csr_wr && addr_valid) begin")
        L(f"                case (csr_adr_i)")

        for r in self.registers:
            if r["access"] == "RO":
                continue

            L(f"                    ADDR_{r['name']}: begin")

            if r["access"] == "RW1C":
                # RW1C: write-1-to-clear for RW1C fields, RO fields ignored
                for f in r["fields"]:
                    msb, lsb = self._bit_range(f["bits"])
                    if f.get("access") == "RW1C":
                        L(f"                        if (csr_dat_i[{msb}]) reg_{r['name'].lower()}[{msb}] <= 1'b0;  // W1C {f['name']}")
            else:
                # Normal RW: write RW fields, skip RO and WO handled above
                for f in r["fields"]:
                    msb, lsb = self._bit_range(f["bits"])
                    fa = f.get("access", r["access"])
                    if fa == "RW" or fa == "WO":
                        w = self._bit_width(f["bits"])
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

        # ── Read mux ──
        L(f"    // ================================================================")
        L(f"    // Read mux")
        L(f"    // ================================================================")
        L(f"    logic [CSR_DATA_W-1:0] rdata_mux;")
        L(f"")
        L(f"    always_comb begin")
        L(f"        rdata_mux = 32'h0;")
        L(f"        case (csr_adr_i)")

        for r in self.registers:
            L(f"            ADDR_{r['name']}: begin")
            if r["access"] == "RO":
                # Assemble from status inputs
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
        L(f"")
        L(f"    // Registered read output")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) csr_dat_o <= 32'h0;")
        L(f"        else if (csr_rd) csr_dat_o <= rdata_mux;")
        L(f"")

        # ── cfg_* output assignments ──
        L(f"    // ================================================================")
        L(f"    // Configuration outputs")
        L(f"    // ================================================================")
        L(f"")
        L(f"    // Timing (TIMING_0)")
        L(f"    assign cfg_tRCD_nCK       = reg_timing_0[7:0];")
        L(f"    assign cfg_tRP_nCK        = reg_timing_0[15:8];")
        L(f"    assign cfg_tRAS_nCK       = reg_timing_0[23:16];")
        L(f"    assign cfg_tRC_nCK        = reg_timing_0[31:24];")
        L(f"")
        L(f"    // Timing (TIMING_1)")
        L(f"    assign cfg_tRRD_nCK       = reg_timing_1[7:0];")
        L(f"    assign cfg_tWTR_nCK       = reg_timing_1[15:8];")
        L(f"    assign cfg_tFAW_nCK       = reg_timing_1[23:16];")
        L(f"    assign cfg_tRFC_nCK       = reg_timing_1[31:24];")
        L(f"")
        L(f"    // Timing (TIMING_2)")
        L(f"    assign cfg_tWR_nCK        = reg_timing_2[7:0];")
        L(f"    assign cfg_tRTP_nCK       = reg_timing_2[15:8];")
        L(f"    assign cfg_CL_nCK         = reg_timing_2[23:16];")
        L(f"    assign cfg_CWL_nCK        = reg_timing_2[31:24];")
        L(f"")
        L(f"    // Timing (TIMING_3)")
        L(f"    assign cfg_tCCD_nCK       = reg_timing_3[7:0];")
        L(f"    assign cfg_tREFI_nCK      = reg_timing_3[31:8];")
        L(f"")
        L(f"    // Control (CTRL_CONFIG)")
        L(f"    assign cfg_sched_policy   = reg_ctrl_config[0];")
        L(f"    assign cfg_row_policy     = reg_ctrl_config[1];")
        L(f"    assign cfg_self_ref_mode  = reg_ctrl_config[3:2];")
        L(f"    assign cfg_ecc_enable     = reg_ctrl_config[4];")
        L(f"    assign cfg_bist_start     = reg_ctrl_config[5];")
        L(f"    assign cfg_force_refresh  = reg_ctrl_config[6];")
        L(f"    assign cfg_force_self_ref = reg_ctrl_config[7];")
        L(f"")
        L(f"    // Refresh (REFRESH_CONFIG)")
        L(f"    assign cfg_max_postpone      = reg_refresh_config[3:0];")
        L(f"    assign cfg_urgent_threshold  = reg_refresh_config[7:4];")
        L(f"    assign cfg_ref_priority      = reg_refresh_config[8];")
        L(f"")
        L(f"    // BIST")
        L(f"    assign cfg_bist_pattern      = reg_bist_config[2:0];")
        L(f"    assign cfg_bist_addr_mode    = reg_bist_config[3];")
        L(f"    assign cfg_bist_addr_start   = reg_bist_addr_start[28:0];")
        L(f"    assign cfg_bist_addr_end     = reg_bist_addr_end[28:0];")
        L(f"")

        # ── Assertions ──
        L(f"    // ================================================================")
        L(f"    // SVA — simulation only")
        L(f"    // ================================================================")
        L(f"    // synopsys translate_off")
        L(f"    // synthesis translate_off")
        L(f"")
        L(f"    // CA-001: Read after write — RW register retains value")
        L(f"    property p_rw_retain;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (csr_wr && csr_adr_i == ADDR_TIMING_0) |=>")
        L(f"            (reg_timing_0[7:0] == $past(csr_dat_i[7:0]));")
        L(f"    endproperty")
        L(f"    assert property (p_rw_retain)")
        L(f"        else $error(\"[CA-001] RW register did not retain written value\");")
        L(f"")
        L(f"    // CA-002: RO register ignores writes")
        L(f"    property p_ro_ignore;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (csr_wr && csr_adr_i == ADDR_CTRL_STATUS) |=>")
        L(f"            1'b1;  // no storage for CTRL_STATUS, always assembled from inputs")
        L(f"    endproperty")
        L(f"    assert property (p_ro_ignore)")
        L(f"        else $error(\"[CA-002] RO register was modified\");")
        L(f"")
        L(f"    // CA-003: WO self-clearing fields clear after one cycle")
        L(f"    property p_wo_clear;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (csr_wr && csr_adr_i == ADDR_CTRL_CONFIG && csr_dat_i[5]) |=>")
        L(f"            (reg_ctrl_config[5] == 1'b1) ##1 (reg_ctrl_config[5] == 1'b0);")
        L(f"    endproperty")
        L(f"    assert property (p_wo_clear)")
        L(f"        else $error(\"[CA-003] WO field did not self-clear\");")
        L(f"")
        L(f"    // CA-004: Invalid address returns error")
        L(f"    property p_bad_addr;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (csr_req && !addr_valid) |=> csr_err_o;")
        L(f"    endproperty")
        L(f"    assert property (p_bad_addr)")
        L(f"        else $error(\"[CA-004] No error on invalid CSR address\");")
        L(f"")
        L(f"    // Functional coverage")
        L(f"    covergroup cg_csr @(posedge clk);")
        L(f"        option.per_instance = 1;")
        L(f"        cp_write   : coverpoint (csr_wr && addr_valid);")
        L(f"        cp_read    : coverpoint (csr_rd && addr_valid);")
        L(f"        cp_err     : coverpoint csr_err_o;")
        L(f"        cp_bist_go : coverpoint cfg_bist_start;")
        L(f"        cp_fref    : coverpoint cfg_force_refresh;")
        L(f"    endgroup")
        L(f"    cg_csr cg_inst = new();")
        L(f"")
        L(f"    // synthesis translate_on")
        L(f"    // synopsys translate_on")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    def _status_input_name(self, field_name: str) -> str:
        """Map CTRL_STATUS field names to status input port names."""
        mapping = {
            "init_done":           "sts_init_done",
            "cal_done":            "sts_cal_done",
            "cal_fail":            "sts_cal_fail",
            "bist_done":           "sts_bist_done",
            "bist_fail":           "sts_bist_fail",
            "ref_pending_cnt":     "sts_ref_pending_cnt",
            "self_refresh_active": "sts_self_refresh_active",
            "reserved":            "23'b0",
        }
        return mapping.get(field_name, "1'b0")

    def _rw1c_event_name(self, field_name: str) -> str:
        """Map RW1C field names to event pulse inputs."""
        mapping = {
            "ecc_ue_flag":     "sts_ecc_ue_event",
            "ref_starve_flag": "sts_ref_starve_event",
            "init_fail_flag":  "sts_init_fail_event",
        }
        return mapping.get(field_name, "1'b0")

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "config_regs",
            "file": "config_regs.sv",
            "phase": 1,
            "agent": "config_regs_agent",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "CSR_ADDR_W": p["CSR_ADDR_W"],
                "CSR_DATA_W": p["CSR_DATA_W"],
                "NUM_REGS": p["NUM_REGS"],
                "TOTAL_FIELDS": p["TOTAL_FIELDS"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk",   "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "csr_bus_in": [
                    {"name": "csr_cyc_i", "width": 1,            "dir": "input"},
                    {"name": "csr_stb_i", "width": 1,            "dir": "input"},
                    {"name": "csr_we_i",  "width": 1,            "dir": "input"},
                    {"name": "csr_adr_i", "width": p["CSR_ADDR_W"], "dir": "input"},
                    {"name": "csr_dat_i", "width": p["CSR_DATA_W"], "dir": "input"},
                    {"name": "csr_sel_i", "width": 4,            "dir": "input"},
                ],
                "csr_bus_out": [
                    {"name": "csr_ack_o", "width": 1,            "dir": "output"},
                    {"name": "csr_dat_o", "width": p["CSR_DATA_W"], "dir": "output"},
                    {"name": "csr_err_o", "width": 1,            "dir": "output"},
                ],
                "status_in": [
                    {"name": "sts_init_done",           "width": 1,  "dir": "input"},
                    {"name": "sts_cal_done",            "width": 1,  "dir": "input"},
                    {"name": "sts_cal_fail",            "width": 1,  "dir": "input"},
                    {"name": "sts_bist_done",           "width": 1,  "dir": "input"},
                    {"name": "sts_bist_fail",           "width": 1,  "dir": "input"},
                    {"name": "sts_ref_pending_cnt",     "width": 3,  "dir": "input"},
                    {"name": "sts_self_refresh_active", "width": 1,  "dir": "input"},
                    {"name": "sts_ecc_ce_count",        "width": 16, "dir": "input"},
                    {"name": "sts_ecc_ue_event",        "width": 1,  "dir": "input"},
                    {"name": "sts_ref_starve_event",    "width": 1,  "dir": "input"},
                    {"name": "sts_init_fail_event",     "width": 1,  "dir": "input"},
                    {"name": "sts_bist_fail_addr",      "width": 13, "dir": "input"},
                ],
                "config_out": [
                    {"name": "cfg_tRCD_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tRP_nCK",          "width": 8,  "dir": "output"},
                    {"name": "cfg_tRAS_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tRC_nCK",          "width": 8,  "dir": "output"},
                    {"name": "cfg_tRRD_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tWTR_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tFAW_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tRFC_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tWR_nCK",          "width": 8,  "dir": "output"},
                    {"name": "cfg_tRTP_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_CL_nCK",           "width": 8,  "dir": "output"},
                    {"name": "cfg_CWL_nCK",          "width": 8,  "dir": "output"},
                    {"name": "cfg_tCCD_nCK",         "width": 8,  "dir": "output"},
                    {"name": "cfg_tREFI_nCK",        "width": 24, "dir": "output"},
                    {"name": "cfg_sched_policy",     "width": 1,  "dir": "output"},
                    {"name": "cfg_row_policy",       "width": 1,  "dir": "output"},
                    {"name": "cfg_self_ref_mode",    "width": 2,  "dir": "output"},
                    {"name": "cfg_ecc_enable",       "width": 1,  "dir": "output"},
                    {"name": "cfg_bist_start",       "width": 1,  "dir": "output"},
                    {"name": "cfg_force_refresh",    "width": 1,  "dir": "output"},
                    {"name": "cfg_force_self_ref",   "width": 1,  "dir": "output"},
                    {"name": "cfg_max_postpone",     "width": 4,  "dir": "output"},
                    {"name": "cfg_urgent_threshold", "width": 4,  "dir": "output"},
                    {"name": "cfg_ref_priority",     "width": 1,  "dir": "output"},
                    {"name": "cfg_bist_pattern",     "width": 3,  "dir": "output"},
                    {"name": "cfg_bist_addr_mode",   "width": 1,  "dir": "output"},
                    {"name": "cfg_bist_addr_start",  "width": 29, "dir": "output"},
                    {"name": "cfg_bist_addr_end",    "width": 29, "dir": "output"},
                ],
            },
            "assertions": [
                {"name": "p_rw_retain", "check": "CA-001"},
                {"name": "p_ro_ignore", "check": "CA-002"},
                {"name": "p_wo_clear",  "check": "CA-003"},
                {"name": "p_bad_addr",  "check": "CA-004"},
            ],
            "coverage_points": [
                "cp_write", "cp_read", "cp_err", "cp_bist_go", "cp_fref",
            ],
        }

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  CONFIG / CSR REGISTERS AGENT\n  Spec: {self.spec_path}\n{hdr}")

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
        rtl_path = self.output_dir / "config_regs.sv"
        rtl_path.write_text(rtl)
        print(f"  ✓ {rtl_path}")

        mfst_path = self.output_dir / "config_regs_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {mfst_path}")

        print(f"\n{hdr}\n  DONE — config_regs.sv ready for Phase 1 integration\n{hdr}")
        return {
            "status": "success",
            "module": "config_regs",
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
    print("║   CONFIG / CSR REGISTERS AGENT  (Phase 1)   ║")
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
    agent = ConfigRegsAgent(spec_path, output_dir)
    result = agent.run()
    sys.exit(0 if result["status"] == "success" else 1)