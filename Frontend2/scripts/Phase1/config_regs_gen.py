#!/usr/bin/env python3
"""
CONFIG / CSR REGISTERS -- RTL Generation Script (Phase 1, deterministic)

Replaces the LLM-driven Frontend/Agents/config_regs_agent.py. That agent's
own docstring called this the "HARD NAMING CONTRACT" strategy: every
register name, offset, reset value, bit field, and cfg_* output assignment
was already being computed in Python and handed to the LLM as literal,
copy-verbatim text -- the LLM's only real job was assembling those fixed
pieces into one file plus deciding comment/SVA style. That means there was
nothing left for a model to decide; this script does the assembly directly.

Scope note (inherited from the original, not introduced here): the cfg_*
output assignments and the special-cased registers (CTRL_STATUS, CTRL_CONFIG,
ERROR_STATUS) are specific to this project's golden CSR layout (TIMING_0..3,
CTRL_CONFIG, REFRESH_CONFIG, BIST_*), the same way the original LLM prompt
hardcoded them. Generalizing to an arbitrary CSR map is a separate task
(see the schema-coverage audit in the project roadmap), not a determinism
gap -- the LLM version was exactly as spec-locked as this one.
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Optional

_HERE = os.path.dirname(os.path.abspath(__file__))
_SCRIPTS_DIR = os.path.dirname(_HERE)
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)
from manifest_stamp import stamp


class ConfigRegsGenerator:

    def __init__(self, spec_path: str, output_dir: str = "./output",
                 retry_instructions: Optional[dict] = None):
        # retry_instructions accepted for pipeline call-signature compatibility
        # only. A deterministic generator produces the same output for the
        # same spec every time, so there is nothing to "retry" -- see
        # Frontend2/IMPLEMENTATION_PLAN.md on why the old retry loop doesn't
        # apply to script-converted modules.
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.csr = self.spec["csr_register_map"]
        self.ctrl_arch = self.spec["controller_architecture"]
        self.clocking = self.spec["clocking_model"]
        self.registers = self.csr["registers"]

        self.p = self._derive_parameters()

    # ================================================================
    # Parameter derivation (unchanged from the original agent)
    # ================================================================
    def _derive_parameters(self) -> dict:
        p = {}
        p["CSR_ADDR_W"] = self.csr["address_width_bits"]
        p["CSR_DATA_W"] = self.csr["data_width_bits"]
        p["NUM_REGS"] = len(self.registers)
        p["BASE_ADDR"] = self.csr["base_address"]
        p["CTRL_PERIOD"] = self.clocking["controller_clock_period_ns"]

        total_fields = sum(len(r["fields"]) for r in self.registers)
        p["TOTAL_FIELDS"] = total_fields

        p["REG_TABLE"] = []
        for r in self.registers:
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            rst = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
            fields = []
            covered_bits = set()
            reserved_bits = set()
            for f in r["fields"]:
                fa = f.get("access", r["access"])
                fields.append({
                    "name": f["name"], "bits": f["bits"],
                    "access": fa, "description": f.get("description", ""),
                })
                fbits = self._parse_bits(f["bits"])
                covered_bits |= fbits
                # Every register in this spec already declares its unused
                # positions as an explicit field literally named "reserved"
                # -- treat those (and any gap bits not covered by ANY
                # field, belt-and-suspenders) as non-writable. Writes to
                # them must not be stored (see Defect 8,
                # Frontend2/VALIDATION_INTEGRATION_PLAN.md: this masking
                # did not exist at all in this generator, a regression
                # against an earlier version that had it).
                if f["name"].strip().lower() == "reserved":
                    reserved_bits |= fbits
            reserved_bits |= {bit for bit in range(32) if bit not in covered_bits}
            reserved_mask = 0
            for bit in reserved_bits:
                reserved_mask |= (1 << bit)
            p["REG_TABLE"].append({
                "name": r["name"], "offset": off, "offset_hex": f"0x{off:02X}",
                "reset_value": rst, "reset_hex": f"0x{rst:08X}",
                "access": r["access"], "fields": fields,
                "reserved_mask": reserved_mask,
            })
        return p

    # ================================================================
    # Validation (unchanged -- catches spec errors before generating)
    # ================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["CSR_DATA_W"] != 32:
            errors.append(f"CSR data width must be 32, got {p['CSR_DATA_W']}")
        if p["CSR_ADDR_W"] < 5:
            errors.append(f"CSR addr width too small for {p['NUM_REGS']} registers")

        offsets = set()
        for r in self.registers:
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
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
        return {int(bits_str)}

    # ================================================================
    # RTL generation -- deterministic assembly, no LLM
    # ================================================================
    def generate_rtl(self) -> str:
        p = self.p
        aw, dw = p["CSR_ADDR_W"], p["CSR_DATA_W"]
        reg_by_name = {rt["name"]: rt for rt in p["REG_TABLE"]}

        lines = []
        L = lines.append

        # -- Module header (fixed port contract) --
        L(f"""module config_regs #(
    parameter CSR_ADDR_W = {aw},
    parameter CSR_DATA_W = {dw}
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // CSR Wishbone Slave
    input  logic                    csr_cyc_i,
    input  logic                    csr_stb_i,
    input  logic                    csr_we_i,
    input  logic [CSR_ADDR_W-1:0]   csr_adr_i,
    input  logic [CSR_DATA_W-1:0]   csr_dat_i,
    input  logic [3:0]              csr_sel_i,
    output logic                    csr_ack_o,
    output logic [CSR_DATA_W-1:0]   csr_dat_o,
    output logic                    csr_err_o,

    // Status inputs
    input  logic                    sts_init_done,
    input  logic                    sts_cal_done,
    input  logic                    sts_cal_fail,
    input  logic                    sts_bist_done,
    input  logic                    sts_bist_fail,
    input  logic [2:0]              sts_ref_pending_cnt,
    input  logic                    sts_self_refresh_active,
    input  logic [15:0]             sts_ecc_ce_count,
    input  logic                    sts_ecc_ue_event,
    input  logic                    sts_ref_starve_event,
    input  logic                    sts_init_fail_event,
    input  logic [12:0]             sts_bist_fail_addr,

    // Config outputs
    output logic [7:0]  cfg_tRCD_nCK, output logic [7:0]  cfg_tRP_nCK,
    output logic [7:0]  cfg_tRAS_nCK, output logic [7:0]  cfg_tRC_nCK,
    output logic [7:0]  cfg_tRRD_nCK, output logic [7:0]  cfg_tWTR_nCK,
    output logic [7:0]  cfg_tFAW_nCK, output logic [7:0]  cfg_tRFC_nCK,
    output logic [7:0]  cfg_tWR_nCK,  output logic [7:0]  cfg_tRTP_nCK,
    output logic [7:0]  cfg_CL_nCK,   output logic [7:0]  cfg_CWL_nCK,
    output logic [7:0]  cfg_tCCD_nCK, output logic [23:0] cfg_tREFI_nCK,
    output logic        cfg_sched_policy, output logic     cfg_row_policy,
    output logic [1:0]  cfg_self_ref_mode, output logic    cfg_ecc_enable,
    output logic        cfg_bist_start, output logic       cfg_force_refresh,
    output logic        cfg_force_self_ref,
    output logic [3:0]  cfg_max_postpone, output logic [3:0] cfg_urgent_threshold,
    output logic        cfg_ref_priority,
    output logic [2:0]  cfg_bist_pattern, output logic     cfg_bist_addr_mode,
    output logic [28:0] cfg_bist_addr_start, output logic [28:0] cfg_bist_addr_end
);""")

        # -- Register address localparams --
        L("\n    // Register address map")
        for rt in p["REG_TABLE"]:
            L(f"    localparam [CSR_ADDR_W-1:0] ADDR_{rt['name']} = {aw}'h{rt['offset']:02X};")

        # -- Bus decode + addr_valid --
        L("\n    // Bus request decode")
        L("    wire csr_req = csr_cyc_i & csr_stb_i;")
        L("    wire csr_wr  = csr_req & csr_we_i;")
        L("    wire csr_rd  = csr_req & ~csr_we_i;")
        addr_terms = " ||\n        ".join(f"(csr_adr_i == ADDR_{rt['name']})" for rt in p["REG_TABLE"])
        L(f"    wire addr_valid =\n        {addr_terms};")

        # -- Handshake (verbatim mandated pattern) --
        L("""
    // ACK generation (internal register + continuous assign)
    logic ack_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ack_r <= 1'b0;
        else        ack_r <= csr_req & ~ack_r;
    assign csr_ack_o = ack_r;

    // Error generation (internal register + continuous assign)
    logic err_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) err_r <= 1'b0;
        else        err_r <= csr_req & ~addr_valid & ~ack_r;
    assign csr_err_o = err_r;""")

        # -- Register storage + write logic --
        L("\n    // Register storage")
        plain_rw = [rt for rt in p["REG_TABLE"]
                    if rt["name"] not in ("CTRL_STATUS", "CTRL_CONFIG", "ERROR_STATUS")]
        for rt in plain_rw:
            reg = f"reg_{rt['name'].lower()}"
            rmask = rt["reserved_mask"]
            L(f"    logic [31:0] {reg};")
            L(f"    always_ff @(posedge clk or negedge rst_n)")
            L(f"        if (!rst_n) {reg} <= 32'h{rt['reset_value']:08X};")
            if rmask:
                keep_mask = rmask & 0xFFFFFFFF
                take_mask = (~rmask) & 0xFFFFFFFF
                L(f"        else if (csr_wr && addr_valid && csr_adr_i == ADDR_{rt['name']})")
                L(f"            {reg} <= (csr_dat_i & 32'h{take_mask:08X}) | ({reg} & 32'h{keep_mask:08X});  // reserved bits pinned")
            else:
                L(f"        else if (csr_wr && addr_valid && csr_adr_i == ADDR_{rt['name']}) {reg} <= csr_dat_i;")
            L("")

        # CTRL_CONFIG: plain RW, but bits 5/6/7 (bist_start, force_refresh,
        # force_self_ref) self-clear one cycle after being set, regardless
        # of source (see WRITE-ONCE SELF-CLEARING FIELDS in the original
        # HARD NAMING CONTRACT).
        cc = reg_by_name["CTRL_CONFIG"]
        cc_rmask = cc["reserved_mask"]
        cc_keep = cc_rmask & 0xFFFFFFFF
        cc_take = (~cc_rmask) & 0xFFFFFFFF
        L(f"    logic [31:0] reg_ctrl_config;")
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) reg_ctrl_config <= 32'h{cc['reset_value']:08X};")
        if cc_rmask:
            L(f"        else if (csr_wr && addr_valid && csr_adr_i == ADDR_CTRL_CONFIG)")
            L(f"            reg_ctrl_config <= (csr_dat_i & 32'h{cc_take:08X}) | (reg_ctrl_config & 32'h{cc_keep:08X});  // reserved bits pinned")
        else:
            L(f"        else if (csr_wr && addr_valid && csr_adr_i == ADDR_CTRL_CONFIG) reg_ctrl_config <= csr_dat_i;")
        L(f"        else begin")
        L(f"            reg_ctrl_config[5] <= 1'b0;  // bist_start self-clear")
        L(f"            reg_ctrl_config[6] <= 1'b0;  // force_refresh self-clear")
        L(f"            reg_ctrl_config[7] <= 1'b0;  // force_self_ref self-clear")
        L(f"        end")
        L(f"    end")
        L("")

        # ERROR_STATUS: RW1C flags latch on event, clear on write-1;
        # ecc_ce_count/bist_fail_addr are live read-through of status inputs.
        L("    // ERROR_STATUS (RW1C flags; count/addr fields are live status passthrough)")
        for flag, event, bit in [
            ("ecc_ue_flag_r", "sts_ecc_ue_event", 16),
            ("ref_starve_flag_r", "sts_ref_starve_event", 17),
            ("init_fail_flag_r", "sts_init_fail_event", 18),
        ]:
            L(f"    logic {flag};")
            L(f"    always_ff @(posedge clk or negedge rst_n)")
            L(f"        if (!rst_n) {flag} <= 1'b0;")
            L(f"        else if ({event}) {flag} <= 1'b1;")
            L(f"        else if (csr_wr && addr_valid && csr_adr_i == ADDR_ERROR_STATUS && csr_dat_i[{bit}]) {flag} <= 1'b0;")
        L("")

        # -- Read data mux --
        L("    // Read data mux")
        L("    logic [31:0] rdata_mux;")
        L("    always_comb begin")
        L("        case (csr_adr_i)")
        L("            ADDR_CTRL_STATUS: rdata_mux = {23'b0, sts_self_refresh_active, "
          "sts_ref_pending_cnt, sts_bist_fail, sts_bist_done, sts_cal_fail, sts_cal_done, sts_init_done};")
        L("            ADDR_CTRL_CONFIG: rdata_mux = reg_ctrl_config;")
        for rt in plain_rw:
            if rt["name"] == "CTRL_STATUS":
                continue
            L(f"            ADDR_{rt['name']}: rdata_mux = reg_{rt['name'].lower()};")
        L("            ADDR_ERROR_STATUS: rdata_mux = {sts_bist_fail_addr, "
          "init_fail_flag_r, ref_starve_flag_r, ecc_ue_flag_r, sts_ecc_ce_count};")
        L("            default: rdata_mux = 32'h0;")
        L("        endcase")
        L("    end")

        # -- csr_dat_o latch (verbatim mandated pattern) --
        L("""
    // Read data output (latch on csr_rd, hold value)
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) csr_dat_o <= 32'h0;
        else if (csr_rd) csr_dat_o <= rdata_mux;""")

        # -- cfg_* output assignments (fixed layout, matches the golden CSR map) --
        L("""
    // Config outputs
    assign cfg_tRCD_nCK         = reg_timing_0[7:0];
    assign cfg_tRP_nCK          = reg_timing_0[15:8];
    assign cfg_tRAS_nCK         = reg_timing_0[23:16];
    assign cfg_tRC_nCK          = reg_timing_0[31:24];
    assign cfg_tRRD_nCK         = reg_timing_1[7:0];
    assign cfg_tWTR_nCK         = reg_timing_1[15:8];
    assign cfg_tFAW_nCK         = reg_timing_1[23:16];
    assign cfg_tRFC_nCK         = reg_timing_1[31:24];
    assign cfg_tWR_nCK          = reg_timing_2[7:0];
    assign cfg_tRTP_nCK         = reg_timing_2[15:8];
    assign cfg_CL_nCK           = reg_timing_2[23:16];
    assign cfg_CWL_nCK          = reg_timing_2[31:24];
    assign cfg_tCCD_nCK         = reg_timing_3[7:0];
    assign cfg_tREFI_nCK        = reg_timing_3[31:8];
    assign cfg_sched_policy     = reg_ctrl_config[0];
    assign cfg_row_policy       = reg_ctrl_config[1];
    assign cfg_self_ref_mode    = reg_ctrl_config[3:2];
    assign cfg_ecc_enable       = reg_ctrl_config[4];
    assign cfg_bist_start       = reg_ctrl_config[5];
    assign cfg_force_refresh    = reg_ctrl_config[6];
    assign cfg_force_self_ref   = reg_ctrl_config[7];
    assign cfg_max_postpone     = reg_refresh_config[3:0];
    assign cfg_urgent_threshold = reg_refresh_config[7:4];
    assign cfg_ref_priority     = reg_refresh_config[8];
    assign cfg_bist_pattern     = reg_bist_config[2:0];
    assign cfg_bist_addr_mode   = reg_bist_config[3];
    assign cfg_bist_addr_start  = reg_bist_addr_start[28:0];
    assign cfg_bist_addr_end    = reg_bist_addr_end[28:0];""")

        # -- SVA (translate_off-guarded) --
        L("""
    // synopsys translate_off
    property p_rw_retain;
        @(posedge clk) disable iff (!rst_n)
        (csr_wr && addr_valid && csr_adr_i == ADDR_TIMING_0) |=> (reg_timing_0 == $past(csr_dat_i));
    endproperty
    assert property (p_rw_retain);

    property p_bad_addr;
        @(posedge clk) disable iff (!rst_n)
        (csr_req && !addr_valid) |=> csr_err_o;
    endproperty
    assert property (p_bad_addr);
    // synopsys translate_on""")

        L("\nendmodule\n")
        return "\n".join(lines)

    # ================================================================
    # Testbench generation -- unchanged from the original (already
    # deterministic; kept here so this generator is drop-in complete).
    # ================================================================
    def _tb_test_registry(self) -> list:
        tests = []
        for i, r in enumerate(self.registers):
            rv = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
            tests.append((f"A{i+1}", f"{r['name']} reset = 0x{rv:08X}"))
        bi = 1
        for r in self.registers:
            if r["access"] in ("RW", "RW1C") and r["name"] not in ("ERROR_STATUS", "CTRL_STATUS"):
                tests.append((f"B{bi}", f"{r['name']} write/readback"))
                bi += 1
        tests += [
            ("C1", "CTRL_STATUS reflects status inputs"), ("C2", "CTRL_STATUS ignores writes (RO)"),
            ("D1", "bist_start self-clears after 1 cycle"), ("D2", "force_refresh self-clears after 1 cycle"),
            ("E1", "ERROR_STATUS latches ecc_ue event"), ("E2", "ERROR_STATUS W1C clears ecc_ue flag"),
            ("E3", "ERROR_STATUS flag stays clear after W1C"),
            ("F1", "Invalid address returns error"), ("F2", "Valid address no error"),
            ("G1", "cfg_tRCD_nCK matches TIMING_0[7:0]"), ("G2", "cfg_sched_policy matches CTRL_CONFIG[0]"),
            ("G3", "cfg_max_postpone matches REFRESH_CONFIG[3:0]"),
            ("H1", "Registers return to reset values after reset"), ("H2", "Normal operation after reset recovery"),
            ("I1", "Back-to-back writes to different registers"), ("I2", "Readback after back-to-back writes correct"),
        ]
        return tests

    def generate_testbench(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        tests = self._tb_test_registry()

        lines = []
        L = lines.append
        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// config_regs_tb.sv -- Enhanced testbench ({len(tests)} tests)")
        L(f"// Generated: {ts}")
        L(f"// Generator: config_regs_gen.py (Phase 1, deterministic script)")
        L(f"//==============================================================")
        L(f"module config_regs_tb;")
        L(f"")
        L(f"    localparam real CLK_PERIOD = {p['CTRL_PERIOD']};")
        L(f"    logic clk = 0;")
        L(f"    always #(CLK_PERIOD/2) clk = ~clk;")
        L(f"")
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
        L(f"    int pass_count=0, fail_count=0, total_tests=0;")
        L(f"    task automatic check(string name, logic condition);")
        L(f"        total_tests++;")
        L(f'        if (condition) begin pass_count++; $display("  [PASS] %0d: %s", total_tests, name); end')
        L(f'        else begin fail_count++; $display("  [FAIL] %0d: %s", total_tests, name); end')
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
        L(f"    localparam [31:0] CTRL_CONFIG_WO_MASK = 32'hFFFFFF1F;")
        L(f"")
        L(f"    initial begin")
        L(f'        $dumpfile("config_regs_tb.vcd");')
        L(f"        $dumpvars(0, config_regs_tb);")
        L(f'        $display("");')
        L(f'        $display("==========================================================");')
        L(f'        $display("  config_regs_tb -- CSR Register Verification");')
        L(f'        $display("  {p["NUM_REGS"]} registers, {p["CSR_DATA_W"]}-bit data bus");')
        L(f'        $display("==========================================================");')
        L(f"        hw_reset();")
        L(f"")
        L(f'        $display(""); $display("  -- Section A: Reset Values --");')
        for i, r in enumerate(self.registers):
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            rst = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
            L(f'        csr_read(8\'h{off:02X}, rdata); check($sformatf("A{i+1}: {r["name"]} reset = 0x%08X", rdata), rdata == 32\'h{rst:08X});')
        L(f"")
        L(f'        $display(""); $display("  -- Section B: Write / Readback --");')
        bi = 1
        vi = 0
        test_vals = [0x0000001F, 0x12345678, 0xDEADBEEF, 0xCAFEBABE,
                     0xFACEFEED, 0x000001FF, 0x0000000F, 0x1ABC0000, 0x1FFFFFFF]
        for r in self.registers:
            if r["access"] == "RO" or r["name"] == "ERROR_STATUS":
                continue
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            val = test_vals[vi % len(test_vals)]
            vi += 1
            L(f"        csr_write(8'h{off:02X}, 32'h{val:08X}); csr_read(8'h{off:02X}, rdata);")
            if r["name"] == "CTRL_CONFIG":
                L(f'        check($sformatf("B{bi}: {r["name"]} write/readback (0x%08X, WO masked)", rdata),')
                L(f"              (rdata & CTRL_CONFIG_WO_MASK) == (32'h{val:08X} & CTRL_CONFIG_WO_MASK));")
            else:
                L(f'        check("B{bi}: {r["name"]} write/readback", rdata == 32\'h{val:08X});')
            bi += 1
        L(f"")
        L(f'        $display(""); $display("  -- Section C: CTRL_STATUS (RO) --");')
        L(f"        hw_reset();")
        L(f"        sts_init_done=1; sts_cal_done=1; sts_ref_pending_cnt=3'd5;")
        L(f"        repeat(2) @(posedge clk);")
        L(f"        csr_read(8'h00, rdata);")
        L(f'        check($sformatf("C1: CTRL_STATUS reflects inputs (0x%08X)", rdata),')
        L(f"              rdata[0]==1'b1 && rdata[1]==1'b1 && rdata[7:5]==3'd5);")
        L(f"        csr_write(8'h00, 32'hFFFFFFFF); csr_read(8'h00, rdata);")
        L(f'        check("C2: CTRL_STATUS ignores writes", rdata[0]==1\'b1 && rdata[1]==1\'b1);')
        L(f"")
        L(f'        $display(""); $display("  -- Section D: WO Self-Clearing --");')
        L(f"        hw_reset();")
        L(f"        csr_write(8'h04, 32'h00000029); repeat(1) @(posedge clk); csr_read(8'h04, rdata);")
        L(f'        check($sformatf("D1: bist_start self-clears (bit5=%0b)", rdata[5]), rdata[5]==1\'b0);')
        L(f"        csr_write(8'h04, 32'h00000049); repeat(1) @(posedge clk); csr_read(8'h04, rdata);")
        L(f'        check($sformatf("D2: force_refresh self-clears (bit6=%0b)", rdata[6]), rdata[6]==1\'b0);')
        L(f"")
        L(f'        $display(""); $display("  -- Section E: RW1C (ERROR_STATUS) --");')
        L(f"        hw_reset();")
        L(f"        sts_ecc_ue_event=1; @(posedge clk); sts_ecc_ue_event=0; repeat(2) @(posedge clk);")
        L(f'        csr_read(8\'h1C, rdata); check($sformatf("E1: ecc_ue latched (0x%08X)", rdata), rdata[16]==1\'b1);')
        L(f"        csr_write(8'h1C, 32'h00010000); csr_read(8'h1C, rdata);")
        L(f'        check($sformatf("E2: ecc_ue W1C clears (0x%08X)", rdata), rdata[16]==1\'b0);')
        L(f'        csr_read(8\'h1C, rdata); check("E3: Flag stays clear", rdata[16]==1\'b0);')
        L(f"")
        L(f'        $display(""); $display("  -- Section F: Error Handling --");')
        L(f"        hw_reset();")
        L(f"        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=8'hFF;csr_sel_i=4'hF;")
        L(f"        begin")
        L(f"            logic saw_err; saw_err=0;")
        L(f"            repeat(10) begin @(posedge clk); if(csr_err_o) begin saw_err=1; break; end end")
        L(f'            check("F1: Invalid addr error", saw_err);')
        L(f"        end")
        L(f"        csr_idle(); repeat(2) @(posedge clk);")
        L(f'        csr_read(8\'h04, rdata); check("F2: Valid addr no error", csr_err_o===1\'b0);')
        L(f"")
        L(f'        $display(""); $display("  -- Section G: cfg_* Outputs --");')
        L(f"        hw_reset();")
        L(f"        csr_write(8'h08, 32'h44332211); repeat(2) @(posedge clk);")
        L(f'        check($sformatf("G1: cfg_tRCD_nCK=0x%02X", cfg_tRCD_nCK), cfg_tRCD_nCK==8\'h11);')
        L(f"        csr_write(8'h04, 32'h00000001); repeat(2) @(posedge clk);")
        L(f'        check($sformatf("G2: cfg_sched_policy=%0b", cfg_sched_policy), cfg_sched_policy==1\'b1);')
        L(f"        csr_write(8'h18, 32'h0000006A); repeat(2) @(posedge clk);")
        L(f'        check($sformatf("G3: cfg_max_postpone=%0d", cfg_max_postpone), cfg_max_postpone==4\'hA);')
        L(f"")
        L(f'        $display(""); $display("  -- Section H: Reset --");')
        L(f"        csr_write(8'h08, 32'hFFFFFFFF); csr_write(8'h0C, 32'hFFFFFFFF);")
        L(f"        rst_n=0; repeat(5) @(posedge clk); rst_n=1; csr_idle(); repeat(2) @(posedge clk);")
        L(f'        csr_read(8\'h08, rdata); check($sformatf("H1: TIMING_0 reset (0x%08X)", rdata), rdata==32\'h271C0B0B);')
        L(f'        csr_write(8\'h08, 32\'h11223344); csr_read(8\'h08, rdata); check("H2: Normal after reset", rdata==32\'h11223344);')
        L(f"")
        L(f'        $display(""); $display("  -- Section I: Edge Cases --");')
        L(f"        hw_reset();")
        L(f"        csr_write(8'h08, 32'hAAAAAAAA); csr_write(8'h0C, 32'hBBBBBBBB);")
        L(f'        csr_read(8\'h08, rdata); check("I1: Back-to-back TIMING_0", rdata==32\'hAAAAAAAA);')
        L(f'        csr_read(8\'h0C, rdata); check("I2: Back-to-back TIMING_1", rdata==32\'hBBBBBBBB);')
        L(f"")
        L(f'        $display(""); $display("  -- Section J: Reserved Bits Pinned on Write --");')
        L(f"        hw_reset();")
        ji = 1
        for rt in p["REG_TABLE"]:
            rmask = rt["reserved_mask"]
            if rmask == 0 or rt["access"] not in ("RW", "RW1C") or rt["name"] == "ERROR_STATUS":
                continue
            off = rt["offset"]
            rst = rt["reset_value"]
            L(f"        csr_write(8'h{off:02X}, 32'hFFFFFFFF); csr_read(8'h{off:02X}, rdata);")
            L(f'        check($sformatf("J{ji}: {rt["name"]} reserved bits pinned (0x%08X)", rdata),')
            L(f"              (rdata & 32'h{rmask:08X}) == (32'h{rst:08X} & 32'h{rmask:08X}));")
            ji += 1
        L(f"")
        L(f'        $display("");')
        L(f'        $display("==========================================================");')
        L(f'        if (fail_count==0) $display("  ALL %0d TESTS PASSED", total_tests);')
        L(f'        else $display("  %0d of %0d TESTS FAILED", fail_count, total_tests);')
        L(f'        $display("==========================================================");')
        L(f'        $display(""); $finish;')
        L(f"    end")
        L(f'    initial begin #(1_000_000); $display("  [FAIL] GLOBAL TIMEOUT"); $finish; end')
        L(f"endmodule")
        return "\n".join(lines)

    # ================================================================
    # Manifest -- unchanged from the original
    # ================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            **stamp(self.spec),
            "module_name": "config_regs", "file": "config_regs.sv",
            "phase": 1, "agent": "config_regs_gen",
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
                    {"name": "sts_init_done", "width": 1, "dir": "input",
                     "source": "init_fsm.init_done"},
                    {"name": "sts_cal_done", "width": 1, "dir": "input",
                     "source": "calibration.cal_done"},
                    {"name": "sts_cal_fail", "width": 1, "dir": "input",
                     "source": "calibration.cal_fail"},
                    {"name": "sts_bist_done", "width": 1, "dir": "input"},
                    {"name": "sts_bist_fail", "width": 1, "dir": "input"},
                    {"name": "sts_ref_pending_cnt", "width": 3, "dir": "input",
                     "source": "refresh_ctrl.ref_pending_cnt"},
                    {"name": "sts_self_refresh_active", "width": 1, "dir": "input"},
                    {"name": "sts_ecc_ce_count", "width": 16, "dir": "input"},
                    {"name": "sts_ecc_ue_event", "width": 1, "dir": "input"},
                    {"name": "sts_ref_starve_event", "width": 1, "dir": "input",
                     "source": "refresh_ctrl.ref_starve_flag"},
                    {"name": "sts_init_fail_event", "width": 1, "dir": "input",
                     "source": "init_fsm.init_fail"},
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
        errs = self.validate()
        if errs:
            return {"status": "error", "errors": errs}

        rtl = self.generate_rtl()
        tb = self.generate_testbench()
        manifest = self.generate_manifest()

        rtl_path = self.output_dir / "config_regs.sv"
        tb_path = self.output_dir / "config_regs_tb.sv"
        mfst_path = self.output_dir / "config_regs_manifest.json"
        rtl_path.write_text(rtl)
        tb_path.write_text(tb)
        mfst_path.write_text(json.dumps(manifest, indent=2))

        return {
            "status": "success", "module": "config_regs", "phase": 1,
            "rtl_path": str(rtl_path), "tb_path": str(tb_path),
            "manifest_path": str(mfst_path), "manifest": manifest,
            "rtl_lines": len(rtl.splitlines()), "tb_lines": len(tb.splitlines()),
        }


if __name__ == "__main__":
    print("+=============================================+")
    print("|   CONFIG / CSR REGISTERS -- RTL Gen Script  |")
    print("|   Deterministic (no LLM)                    |")
    print("+=============================================+")
    print()
    spec_path = input("Enter path to spec JSON: ").strip()
    if not spec_path or not os.path.isfile(spec_path):
        print("Error: Invalid path.")
        sys.exit(1)
    output_dir = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    result = ConfigRegsGenerator(spec_path, output_dir).run()
    if result["status"] == "success":
        print(f"  wrote {result['rtl_path']} ({result['rtl_lines']} lines)")
        print(f"  wrote {result['tb_path']} ({result['tb_lines']} lines)")
        print(f"  wrote {result['manifest_path']}")
    else:
        print(f"  ERROR: {result['errors']}")
    sys.exit(0 if result["status"] == "success" else 1)
