#!/usr/bin/env python3
"""
+======================================================================+
|             CONFIG / CSR REGISTERS AGENT  (LLM-driven)               |
|                                                                      |
|  Phase 1 RTL Generation Agent -- Claude-powered                      |
|  Generates: config_regs.sv + config_regs_tb.sv                      |
|             + config_regs_manifest.json                              |
|                                                                      |
|  Drop-in replacement for the deterministic template-based agent.     |
|  - Same constructor signature (+ optional retry_instructions)        |
|  - Same run() return shape                                           |
|  - Same output filenames                                             |
|  - Testbench generation is DETERMINISTIC (kept from original)        |
|  - Manifest is deterministic (same port contract)                    |
|                                                                      |
|  Determinism strategy (hybrid):                                      |
|    - Register names, offsets, reset values, access types, field      |
|      bit ranges, cfg_* output mappings are derived in Python and     |
|      embedded as HARD NAMING CONTRACT in the LLM prompt.             |
|    - LLM gets freedom over coding style, always_ff/comb structure,   |
|      comments, SVA assertion style, coverage, etc.                   |
|    - Temperature: 0.7 cold start, 0.3 on retry.                     |
|                                                                      |
|  Dependencies: anthropic (pip install anthropic)                     |
|                                                                      |
|  Spec sections consumed:                                             |
|    csr_register_map, controller_architecture, clocking_model         |
|                                                                      |
|  Validation checks this must pass: V-RTL-10 .. V-RTL-15, V-JED-10   |
+======================================================================+
"""

from __future__ import annotations

import json
import os
import re
import time
import sys
from pathlib import Path
from datetime import datetime
from typing import Optional


class ConfigRegsAgent:

    # ================================================================
    # Construction
    # ================================================================
    def __init__(
        self,
        spec_path: str,
        output_dir: str = "./output",
        retry_instructions: Optional[dict] = None,
        model: Optional[str] = None,
        temperature: float = 0.7,
        max_attempts: int = 3,
    ):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.csr       = self.spec["csr_register_map"]
        self.ctrl_arch = self.spec["controller_architecture"]
        self.clocking  = self.spec["clocking_model"]
        self.registers = self.csr["registers"]

        self.retry_instructions = retry_instructions
        self.model = model or os.environ.get("CLAUDE_MODEL", "claude-sonnet-4-5")
        self.temperature = temperature
        self.max_attempts = max_attempts

        self.p = self._derive_parameters()

    # ================================================================
    # Parameter derivation (deterministic, from spec)
    # ================================================================
    def _derive_parameters(self) -> dict:
        p = {}
        p["CSR_ADDR_W"]   = self.csr["address_width_bits"]
        p["CSR_DATA_W"]   = self.csr["data_width_bits"]
        p["NUM_REGS"]     = len(self.registers)
        p["BASE_ADDR"]    = self.csr["base_address"]
        p["CTRL_PERIOD"]  = self.clocking["controller_clock_period_ns"]

        total_fields = sum(len(r["fields"]) for r in self.registers)
        p["TOTAL_FIELDS"] = total_fields

        # Pre-compute register table for prompt
        p["REG_TABLE"] = []
        for r in self.registers:
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            rst = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
            fields = []
            for f in r["fields"]:
                fa = f.get("access", r["access"])
                fields.append({
                    "name": f["name"],
                    "bits": f["bits"],
                    "access": fa,
                    "description": f.get("description", ""),
                })
            p["REG_TABLE"].append({
                "name": r["name"],
                "offset": off,
                "offset_hex": f"0x{off:02X}",
                "reset_value": rst,
                "reset_hex": f"0x{rst:08X}",
                "access": r["access"],
                "fields": fields,
            })

        return p

    # ================================================================
    # Validation (same as original — catches spec errors early)
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

    # ================================================================
    # Status input / RW1C event name mappings (deterministic)
    # ================================================================
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
    # HARD NAMING CONTRACT — everything the validator regex-matches
    # ================================================================
    def _validator_contract(self) -> str:
        p = self.p
        lines = []
        L = lines.append

        L("=" * 72)
        L("HARD NAMING CONTRACT — MANDATORY VERBATIM STRINGS")
        L("The downstream validator uses regex / substring matching on the")
        L("generated .sv file. If ANY of these names, values, or patterns")
        L("are missing or renamed, validation WILL fail.")
        L("=" * 72)
        L("")

        # Module declaration
        L("MODULE NAME: config_regs")
        L(f"PARAMETERS:  CSR_ADDR_W = {p['CSR_ADDR_W']}, CSR_DATA_W = {p['CSR_DATA_W']}")
        L("  These MUST appear as: parameter CSR_ADDR_W = N, parameter CSR_DATA_W = N")
        L("  in the #(...) parameter block of the module header.")
        L("")

        # Register address localparams
        L("REGISTER ADDRESS LOCALPARAMS (must appear exactly as shown):")
        for rt in p["REG_TABLE"]:
            L(f"  localparam ... ADDR_{rt['name']:20s} = {p['CSR_ADDR_W']}'h{rt['offset']:02X};")
        L("")

        # Reset values
        L("REGISTER RESET VALUES (must appear in reset block as hex literals):")
        for rt in p["REG_TABLE"]:
            if rt["access"] != "RO":
                L(f"  reg_{rt['name'].lower()} <= 32'h{rt['reset_value']:08X};")
        L("")

        # Access types
        L("ACCESS TYPES PER REGISTER:")
        for rt in p["REG_TABLE"]:
            L(f"  {rt['name']:20s}  offset={rt['offset_hex']}  access={rt['access']}  reset={rt['reset_hex']}")
            for f in rt["fields"]:
                L(f"    field: {f['name']:25s}  bits=[{f['bits']}]  access={f['access']}")
        L("")

        # RO register — CTRL_STATUS
        L("READ-ONLY REGISTER: CTRL_STATUS (offset 0x00)")
        L("  This register reads live status inputs, NOT a stored register.")
        L("  Fields map to status input ports:")
        L("    init_done            -> sts_init_done")
        L("    cal_done             -> sts_cal_done")
        L("    cal_fail             -> sts_cal_fail")
        L("    bist_done            -> sts_bist_done")
        L("    bist_fail            -> sts_bist_fail")
        L("    ref_pending_cnt[2:0] -> sts_ref_pending_cnt")
        L("    self_refresh_active  -> sts_self_refresh_active")
        L("    reserved[31:8]       -> 23'b0 (hard-wired zero)")
        L("  Writes to CTRL_STATUS must be IGNORED.")
        L("")

        # RW1C register — ERROR_STATUS
        L("RW1C REGISTER: ERROR_STATUS (offset 0x1C)")
        L("  Fields latch on event pulse, clear on write-1:")
        L("    ecc_ue_flag    [16]  <- sts_ecc_ue_event     (W1C)")
        L("    ref_starve_flag[17]  <- sts_ref_starve_event  (W1C)")
        L("    init_fail_flag [18]  <- sts_init_fail_event   (W1C)")
        L("    ecc_ce_count [15:0]  <- sts_ecc_ce_count      (RO)")
        L("    bist_fail_addr[31:19]<- sts_bist_fail_addr    (RO)")
        L("")

        # WO self-clearing fields
        L("WRITE-ONCE SELF-CLEARING FIELDS (in CTRL_CONFIG @ 0x04):")
        L("  bist_start     [5]   — WO, must self-clear to 0 one cycle after write")
        L("  force_refresh  [6]   — WO, must self-clear to 0 one cycle after write")
        L("  force_self_ref [7]   — WO, must self-clear to 0 one cycle after write")
        L("")

        # cfg_* output assignments
        L("CFG OUTPUT PORT ASSIGNMENTS (must appear as assign statements):")
        L("  assign cfg_tRCD_nCK         = reg_timing_0[7:0];")
        L("  assign cfg_tRP_nCK          = reg_timing_0[15:8];")
        L("  assign cfg_tRAS_nCK         = reg_timing_0[23:16];")
        L("  assign cfg_tRC_nCK          = reg_timing_0[31:24];")
        L("  assign cfg_tRRD_nCK         = reg_timing_1[7:0];")
        L("  assign cfg_tWTR_nCK         = reg_timing_1[15:8];")
        L("  assign cfg_tFAW_nCK         = reg_timing_1[23:16];")
        L("  assign cfg_tRFC_nCK         = reg_timing_1[31:24];")
        L("  assign cfg_tWR_nCK          = reg_timing_2[7:0];")
        L("  assign cfg_tRTP_nCK         = reg_timing_2[15:8];")
        L("  assign cfg_CL_nCK           = reg_timing_2[23:16];")
        L("  assign cfg_CWL_nCK          = reg_timing_2[31:24];")
        L("  assign cfg_tCCD_nCK         = reg_timing_3[7:0];")
        L("  assign cfg_tREFI_nCK        = reg_timing_3[31:8];")
        L("  assign cfg_sched_policy     = reg_ctrl_config[0];")
        L("  assign cfg_row_policy       = reg_ctrl_config[1];")
        L("  assign cfg_self_ref_mode    = reg_ctrl_config[3:2];")
        L("  assign cfg_ecc_enable       = reg_ctrl_config[4];")
        L("  assign cfg_bist_start       = reg_ctrl_config[5];")
        L("  assign cfg_force_refresh    = reg_ctrl_config[6];")
        L("  assign cfg_force_self_ref   = reg_ctrl_config[7];")
        L("  assign cfg_max_postpone     = reg_refresh_config[3:0];")
        L("  assign cfg_urgent_threshold = reg_refresh_config[7:4];")
        L("  assign cfg_ref_priority     = reg_refresh_config[8];")
        L("  assign cfg_bist_pattern     = reg_bist_config[2:0];")
        L("  assign cfg_bist_addr_mode   = reg_bist_config[3];")
        L("  assign cfg_bist_addr_start  = reg_bist_addr_start[28:0];")
        L("  assign cfg_bist_addr_end    = reg_bist_addr_end[28:0];")
        L("")

        # Mandatory handshake code
        L("=" * 72)
        L("MANDATORY WISHBONE HANDSHAKE — COPY THIS CODE VERBATIM")
        L("=" * 72)
        L("The testbench relies on the EXACT timing of this handshake pattern.")
        L("Using a different implementation (e.g. directly registering csr_ack_o")
        L("instead of using an internal ack_r with continuous assign) will cause")
        L("ALL read tests to fail due to Xcelium event scheduling differences.")
        L("")
        L("You MUST use these EXACT signal definitions and handshake blocks:")
        L("")
        L("  // --- Bus request decode (use 'wire', not 'logic' with assign) ---")
        L("  wire csr_req = csr_cyc_i & csr_stb_i;")
        L("  wire csr_wr  = csr_req & csr_we_i;")
        L("  wire csr_rd  = csr_req & ~csr_we_i;")
        L("")
        L("  // --- ACK generation (internal register + continuous assign) ---")
        L("  logic ack_r;")
        L("  always_ff @(posedge clk or negedge rst_n)")
        L("      if (!rst_n) ack_r <= 1'b0;")
        L("      else        ack_r <= csr_req & ~ack_r;")
        L("  assign csr_ack_o = ack_r;")
        L("")
        L("  // --- Error generation (internal register + continuous assign) ---")
        L("  logic err_r;")
        L("  always_ff @(posedge clk or negedge rst_n)")
        L("      if (!rst_n) err_r <= 1'b0;")
        L("      else        err_r <= csr_req & ~addr_valid & ~ack_r;")
        L("  assign csr_err_o = err_r;")
        L("")
        L("  // --- Read data output (latch on csr_rd, hold value) ---")
        L("  always_ff @(posedge clk or negedge rst_n)")
        L("      if (!rst_n) csr_dat_o <= 32'h0;")
        L("      else if (csr_rd) csr_dat_o <= rdata_mux;")
        L("")
        L("CRITICAL RULES FOR THE HANDSHAKE:")
        L("  1. csr_ack_o MUST be driven by 'assign csr_ack_o = ack_r;'")
        L("     Do NOT use 'csr_ack_o <=' in any always_ff block.")
        L("  2. csr_err_o MUST be driven by 'assign csr_err_o = err_r;'")
        L("     Do NOT use 'csr_err_o <=' in any always_ff block.")
        L("  3. csr_dat_o MUST latch on 'csr_rd' (no addr_valid gate).")
        L("     Do NOT add an 'else' clause that clears csr_dat_o to 0.")
        L("  4. ack_r feedback MUST use '~ack_r', NOT '~csr_ack_o'.")
        L("  5. The read data mux MUST be named 'rdata_mux' (not 'rd_data',")
        L("     'read_data', etc.) — the sanity checker looks for this name.")
        L("  6. Write logic MUST gate on 'csr_wr && addr_valid'.")
        L("  7. Do NOT put ack, err, and dat_o in the same always_ff block.")
        L("     Each gets its own always_ff as shown above.")
        L("")

        # SVA
        L("SVA ASSERTIONS (must include at minimum):")
        L("  p_rw_retain  — after writing TIMING_0, the value is retained next cycle")
        L("  p_bad_addr   — invalid address request produces csr_err_o")
        L("  Wrap assertions in // synopsys translate_off / // synopsys translate_on")
        L("")

        return "\n".join(lines)

    # ================================================================
    # Required ports (full module header — LLM must not alter)
    # ================================================================
    def _required_ports(self) -> str:
        p = self.p
        return f"""MANDATORY MODULE HEADER — copy this EXACTLY as the module declaration.
Do NOT rename, reorder, add, or remove any port. Do NOT drop the #(parameter ...) block.

module config_regs #(
    parameter CSR_ADDR_W = {p['CSR_ADDR_W']},
    parameter CSR_DATA_W = {p['CSR_DATA_W']}
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
);"""

    # ================================================================
    # LLM prompt for RTL generation
    # ================================================================
    def _build_prompt(self) -> str:
        p = self.p
        contract = self._validator_contract()
        ports = self._required_ports()

        retry_section = ""
        if self.retry_instructions:
            fails = self.retry_instructions.get("validation_failures", [])
            if fails:
                retry_section = (
                    "\n\n" + "=" * 72 + "\n"
                    "RETRY — YOUR PREVIOUS OUTPUT FAILED THESE CHECKS:\n"
                    + "=" * 72 + "\n"
                )
                for chk in fails:
                    retry_section += (
                        f"  [{chk.get('id','?')}] {chk.get('name','?')}\n"
                        f"    expected: {chk.get('expected','?')}\n"
                        f"    actual:   {chk.get('actual','?')}\n"
                    )
                retry_section += "\nFix these specific issues. Do NOT change anything that was passing.\n"

        prompt = f"""You are a senior digital design engineer. Generate a COMPLETE, synthesizable
SystemVerilog file for a CSR (Control/Status Register) block for a DDR3-1600
memory controller.

The module implements {p['NUM_REGS']} memory-mapped registers on a Wishbone B4
classic slave interface. It provides configuration outputs (cfg_*) to the rest
of the controller and reads live status inputs (sts_*).

{contract}

{ports}

CRITICAL RULES:
1. Output the COMPLETE file from `module config_regs` to `endmodule`.
2. Wrap in ```systemverilog ... ``` fences.
3. Every name, offset, reset value, and bit slice listed in the HARD NAMING
   CONTRACT must appear VERBATIM in the output. The validator uses substring
   and regex matching — even a 1-character difference fails.
4. Register storage names MUST be reg_<lowercase_name> (e.g., reg_timing_0).
5. The parameter block #(parameter CSR_ADDR_W = ..., parameter CSR_DATA_W = ...)
   MUST be present. Do NOT drop it.
6. cfg_* output assignments MUST use the exact register bit slices shown.
7. Include SVA assertions p_rw_retain and p_bad_addr wrapped in translate_off.
8. Must compile cleanly with Cadence xrun -sysv.
9. No prose before or after — just the SystemVerilog in a code fence.
{retry_section}"""

        return prompt

    # ================================================================
    # LLM API call (Anthropic, with exponential backoff)
    # ================================================================
    def _call_llm(self, prompt: str) -> str:
        try:
            from anthropic import Anthropic
        except ImportError:
            raise RuntimeError("pip install anthropic  (required for LLM-driven agent)")

        client = Anthropic()
        last_err = None

        for attempt in range(1, self.max_attempts + 1):
            try:
                resp = client.messages.create(
                    model=self.model,
                    max_tokens=8192,
                    temperature=self.temperature,
                    messages=[{"role": "user", "content": prompt}],
                )
                return resp.content[0].text
            except Exception as e:
                last_err = e
                wait = min(2 ** attempt, 30)
                print(f"  ! LLM call attempt {attempt} failed: {e}")
                print(f"    Retrying in {wait}s ...")
                time.sleep(wait)

        raise RuntimeError(f"LLM call failed after {self.max_attempts} attempts: {last_err}")

    # ================================================================
    # Extract SystemVerilog from markdown code fence
    # ================================================================
    @staticmethod
    def _extract_sv(text: str) -> str:
        for tag in ("systemverilog", "verilog", "sv", ""):
            pat = rf"```{tag}\s*\n(.*?)```" if tag else r"```\s*\n(.*?)```"
            m = re.search(pat, text, re.DOTALL)
            if m:
                return m.group(1).strip() + "\n"
        return text.strip() + "\n"

    # ================================================================
    # Sanity checks (catch LLM mistakes before writing to disk)
    # ================================================================
    def _sv_sanity_check(self, rtl: str) -> Optional[str]:
        """Returns an error string if the RTL has obvious problems, else None."""
        if "module config_regs" not in rtl:
            return "Missing `module config_regs` declaration."

        if "#(" not in rtl:
            return (
                "Missing #(parameter ...) block. The module MUST have "
                "#(parameter CSR_ADDR_W = ..., parameter CSR_DATA_W = ...) "
                "before the port list."
            )

        if f"CSR_DATA_W" not in rtl or f"CSR_ADDR_W" not in rtl:
            return "Missing CSR_DATA_W or CSR_ADDR_W parameter."

        # Check all register address localparams are present
        for rt in self.p["REG_TABLE"]:
            addr_name = f"ADDR_{rt['name']}"
            if addr_name not in rtl:
                return f"Missing localparam {addr_name} for register {rt['name']}."

        # Check all non-RO register storage names
        for rt in self.p["REG_TABLE"]:
            if rt["access"] != "RO":
                reg_name = f"reg_{rt['name'].lower()}"
                if reg_name not in rtl:
                    return f"Missing register storage {reg_name}."

        # Check reset values for non-RO registers
        for rt in self.p["REG_TABLE"]:
            if rt["access"] != "RO" and rt["reset_value"] != 0:
                hex_val = f"{rt['reset_value']:08X}"
                if hex_val.lower() not in rtl.lower() and hex_val.upper() not in rtl.upper():
                    return f"Missing reset value 0x{hex_val} for {rt['name']}."

        # Check key cfg_* outputs
        for cfg_name in ["cfg_tRCD_nCK", "cfg_sched_policy", "cfg_max_postpone",
                         "cfg_bist_start", "cfg_bist_addr_start"]:
            if cfg_name not in rtl:
                return f"Missing cfg_* output assignment for {cfg_name}."

        # Check SVA assertions
        if "p_rw_retain" not in rtl:
            return "Missing SVA assertion p_rw_retain."
        if "p_bad_addr" not in rtl:
            return "Missing SVA assertion p_bad_addr."

        # Check error output
        if "csr_err_o" not in rtl:
            return "Missing csr_err_o error output."

        # Check ack output
        if "csr_ack_o" not in rtl:
            return "Missing csr_ack_o acknowledge output."

        # ── Handshake pattern guards ──
        # The deterministic TB requires a specific ack/err/dat_o pattern.
        # LLM-generated alternatives are logically equivalent but cause
        # Xcelium scheduling mismatches that make ALL reads return 0.

        # GUARD 1: ack must use internal ack_r + continuous assign
        if "assign csr_ack_o" not in rtl:
            return (
                "HANDSHAKE BUG: csr_ack_o must be driven by "
                "'assign csr_ack_o = ack_r;' (continuous assign from internal "
                "register). Do NOT use 'csr_ack_o <=' in any always_ff block. "
                "See the MANDATORY WISHBONE HANDSHAKE section in the contract."
            )

        # GUARD 2: must have ack_r internal register
        if "ack_r" not in rtl:
            return (
                "HANDSHAKE BUG: Missing internal 'ack_r' register. "
                "The ack pattern must be: logic ack_r; always_ff: ack_r <= ...; "
                "assign csr_ack_o = ack_r;"
            )

        # GUARD 3: reject direct registered ack (the pattern that breaks)
        if re.search(r"csr_ack_o\s*<=", rtl):
            return (
                "HANDSHAKE BUG: Found 'csr_ack_o <=' (direct NBA on output). "
                "This causes reads to return 0x00000000 due to Xcelium scheduling. "
                "Use 'ack_r <=' internally and 'assign csr_ack_o = ack_r;' instead."
            )

        # GUARD 4: reject direct registered err
        if re.search(r"csr_err_o\s*<=", rtl):
            return (
                "HANDSHAKE BUG: Found 'csr_err_o <=' (direct NBA on output). "
                "Use 'err_r <=' internally and 'assign csr_err_o = err_r;' instead."
            )

        # GUARD 5: read mux must be named rdata_mux
        if "rdata_mux" not in rtl:
            return (
                "HANDSHAKE BUG: Read data mux must be named 'rdata_mux'. "
                "Found a different name (rd_data, read_data, etc). "
                "Use: always_comb begin rdata_mux = ...; and "
                "else if (csr_rd) csr_dat_o <= rdata_mux;"
            )

        # GUARD 6: csr_dat_o must NOT have an else clause clearing to 0
        # Pattern: "else" followed by "csr_dat_o" followed by "<= 32'h0" on nearby lines
        if re.search(r"else\s+(begin\s+)?csr_dat_o\s*<=\s*32'h0", rtl):
            return (
                "HANDSHAKE BUG: csr_dat_o must HOLD its value between reads. "
                "Found an 'else csr_dat_o <= 32'h0' clause that clears the "
                "output every non-read cycle. Remove the else clause."
            )

        return None

    # ================================================================
    # Testbench generation — DETERMINISTIC (kept from original agent)
    # ================================================================
    def _tb_test_registry(self) -> list:
        """Returns ordered list of (id, description) for all TB tests."""
        tests = []
        for i, r in enumerate(self.registers):
            tests.append((f"A{i+1}", f"{r['name']} reset = 0x{int(r['reset_value'], 16) if isinstance(r['reset_value'], str) else r['reset_value']:08X}"))
        bi = 1
        for r in self.registers:
            if r["access"] in ("RW", "RW1C") and r["access"] != "RO":
                if r["name"] in ("ERROR_STATUS", "CTRL_STATUS"):
                    continue
                tests.append((f"B{bi}", f"{r['name']} write/readback"))
                bi += 1
        tests.append(("C1", "CTRL_STATUS reflects status inputs"))
        tests.append(("C2", "CTRL_STATUS ignores writes (RO)"))
        tests.append(("D1", "bist_start self-clears after 1 cycle"))
        tests.append(("D2", "force_refresh self-clears after 1 cycle"))
        tests.append(("E1", "ERROR_STATUS latches ecc_ue event"))
        tests.append(("E2", "ERROR_STATUS W1C clears ecc_ue flag"))
        tests.append(("E3", "ERROR_STATUS flag stays clear after W1C"))
        tests.append(("F1", "Invalid address returns error"))
        tests.append(("F2", "Valid address no error"))
        tests.append(("G1", "cfg_tRCD_nCK matches TIMING_0[7:0]"))
        tests.append(("G2", "cfg_sched_policy matches CTRL_CONFIG[0]"))
        tests.append(("G3", "cfg_max_postpone matches REFRESH_CONFIG[3:0]"))
        tests.append(("H1", "Registers return to reset values after reset"))
        tests.append(("H2", "Normal operation after reset recovery"))
        tests.append(("I1", "Back-to-back writes to different registers"))
        tests.append(("I2", "Readback after back-to-back writes correct"))
        return tests

    def generate_testbench(self) -> str:
        """Deterministic testbench generation — identical to the original
        template-based agent. No LLM involved."""
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        tests = self._tb_test_registry()

        lines = []
        L = lines.append

        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// config_regs_tb.sv -- Enhanced testbench ({len(tests)} tests)")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Config/CSR Registers Agent (Phase 1, LLM-driven)")
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
        L(f"    localparam [31:0] CTRL_CONFIG_WO_MASK = 32'hFFFFFF1F;")
        L(f"")
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
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
            rst = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
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
            off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
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
    # Manifest (deterministic — same port contract as original)
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
        print(f"{hdr}\n  CONFIG / CSR REGISTERS AGENT (LLM-driven)\n  Spec: {self.spec_path}\n  Model: {self.model}\n{hdr}")

        print("\n[1/5] Validating parameters ...")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ERROR: {e}")
            return {"status": "error", "errors": errs}
        print("  OK: All parameters valid")
        for k, v in self.p.items():
            if k != "REG_TABLE":
                print(f"    {k:20s} = {v}")

        print("\n[2/5] Generating RTL via LLM ...")
        prompt = self._build_prompt()
        rtl = ""
        local_attempts = 3
        for local_try in range(1, local_attempts + 1):
            rtl_text = self._call_llm(prompt)
            rtl = self._extract_sv(rtl_text)
            err = self._sv_sanity_check(rtl)
            if err is None:
                break
            print(f"  ! Local sanity check failed (try {local_try}/{local_attempts}): {err}")
            prompt = (
                self._build_prompt()
                + "\n\nYOUR LAST OUTPUT FAILED A LOCAL SYNTAX SANITY CHECK:\n"
                + f"  {err}\n"
                + "Regenerate the file fixing this specific issue."
            )
        else:
            print(f"  ! WARNING: sanity check still failing after {local_attempts} tries. "
                  f"Writing anyway; xrun will likely fail.")
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines of SystemVerilog")

        print("\n[3/5] Generating testbench (deterministic) ...")
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
    print("|   LLM-driven (Claude API)                   |")
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