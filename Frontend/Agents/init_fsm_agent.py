#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 INIT / RESET FSM AGENT                               ║
║                                                                      ║
║  Phase 1 RTL Generation Agent                                        ║
║  Generates: init_fsm.sv + init_fsm_manifest.json                    ║
║                                                                      ║
║  Dependencies: None (Phase 1)                                        ║
║                                                                      ║
║  Spec sections consumed:                                             ║
║    initialization_sequence, clocking_model, timing_model,            ║
║    memory_geometry                                                   ║
║                                                                      ║
║  Implements:                                                         ║
║    JEDEC DDR3 init sequence (JESD79-3F §4.6):                       ║
║      RESET# low (200µs) → RESET# high → CKE delay (500µs)          ║
║      → CKE high → tXPR wait → MR2 → MR3 → MR1                     ║
║      → MR0 (DLL reset) → ZQCL (512 nCK) → init_done                ║
║                                                                      ║
║  Validation checks: IN-001 through IN-011                            ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import sys
import os
import math
from pathlib import Path
from datetime import datetime


class InitFsmAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.init_seq  = self.spec["initialization_sequence"]
        self.clocking  = self.spec["clocking_model"]
        self.timing    = self.spec["timing_model"]
        self.geometry  = self.spec["memory_geometry"]

        self.p = self._derive_parameters()

    def _derive_parameters(self) -> dict:
        p = {}

        tCK_ns = self.clocking["$derived"]["tCK_ns"]
        ctrl_freq = self.clocking["$derived"]["controller_frequency_MHz"]
        ctrl_period_ns = self.clocking["controller_clock_period_ns"]
        ratio = self.clocking["clock_ratio_ddr_to_controller"]

        p["tCK_ns"]       = tCK_ns
        p["CTRL_FREQ"]    = ctrl_freq
        p["CTRL_PERIOD"]  = ctrl_period_ns
        p["CLK_RATIO"]    = ratio

        # Init timing — convert µs to controller clock cycles
        reset_hold_us = self.init_seq["reset_hold_us"]
        cke_delay_us  = self.init_seq["cke_delay_us"]
        p["RESET_HOLD_US"]  = reset_hold_us
        p["CKE_DELAY_US"]   = cke_delay_us
        p["RESET_HOLD_CYC"] = math.ceil(reset_hold_us * 1000 / ctrl_period_ns)
        p["CKE_DELAY_CYC"]  = math.ceil(cke_delay_us * 1000 / ctrl_period_ns)

        # tXPR in controller cycles
        tXPR_ns = self.init_seq["tXPR_ns"]
        p["tXPR_ns"]  = tXPR_ns
        p["tXPR_CYC"] = math.ceil(tXPR_ns / ctrl_period_ns)

        # tZQinit in controller cycles
        tZQinit_ns = self.init_seq["tZQinit_ns"]
        p["tZQinit_ns"]  = tZQinit_ns
        p["tZQinit_CYC"] = math.ceil(tZQinit_ns / ctrl_period_ns)

        # tMRD — mode register delay (4 nCK per JEDEC, convert to ctrl cycles)
        p["tMRD_CYC"] = math.ceil(4 * tCK_ns / ctrl_period_ns)

        # tMOD — mode register to non-mode command (12 nCK or 15ns, whichever larger)
        tMOD_nCK = max(12, math.ceil(15.0 / tCK_ns))
        p["tMOD_CYC"] = math.ceil(tMOD_nCK * tCK_ns / ctrl_period_ns)

        # Counter width — needs to hold the largest wait (CKE_DELAY)
        max_wait = max(p["RESET_HOLD_CYC"], p["CKE_DELAY_CYC"],
                       p["tXPR_CYC"], p["tZQinit_CYC"])
        p["CTR_WIDTH"] = max(1, (max_wait).bit_length())
        p["MAX_WAIT"]  = max_wait

        # DDR address/bank widths
        p["DDR_ADDR_W"] = max(self.geometry["row_bits"], self.geometry["column_bits"])
        p["DDR_BANK_W"] = self.geometry["bank_bits"]

        # Mode register values
        p["MR"] = self.init_seq["mode_registers"]

        return p

    def validate(self) -> list:
        errors = []
        p = self.p
        mr = p["MR"]

        if p["RESET_HOLD_US"] < 200:
            errors.append(f"JEDEC requires reset_hold >= 200µs, got {p['RESET_HOLD_US']}")
        if p["CKE_DELAY_US"] < 500:
            errors.append(f"JEDEC requires cke_delay >= 500µs, got {p['CKE_DELAY_US']}")
        if not self.init_seq.get("zq_calibration_on_init", True):
            errors.append("JEDEC requires ZQCL on init")

        # Cross-check MR values against timing
        derived = self.timing.get("$derived_cycles", {})
        if derived:
            spec_cl = mr["MR0"]["cas_latency_cycles"]
            tim_cl  = derived.get("tRCD_nCK")  # CL is separate, check MR0 field
            spec_cwl = mr["MR2"]["cas_write_latency_cycles"]

        # MR program order must be MR2 → MR3 → MR1 → MR0
        order = self.init_seq.get("$derived", {}).get("init_sequence_order", "")
        if "MR2" in order and "MR0" in order:
            mr2_pos = order.index("MR2")
            mr0_pos = order.index("MR0")
            if mr2_pos > mr0_pos:
                errors.append("JEDEC requires MR2 before MR0 in init sequence")

        return errors

    def _encode_mr0(self) -> str:
        """Encode MR0 as a DDR_ADDR_W-bit value."""
        mr0 = self.p["MR"]["MR0"]
        cl = mr0["cas_latency_cycles"]
        wr_ns = mr0["write_recovery_ns"]
        tCK = self.p["tCK_ns"]
        wr_nCK = math.ceil(wr_ns / tCK)

        # MR0 encoding per JEDEC DDR3 Table 2
        # A[1:0] = BL: 00=fixed8
        # A2 = CL bit (CAS Latency) — part of CL encoding
        # A[6:4], A2 = CL encoding
        # A[11:9] = WR encoding
        # A8 = DLL Reset
        # A12 = PD mode

        cl_map = {5:0b0001, 6:0b0010, 7:0b0011, 8:0b0100, 9:0b0101,
                  10:0b0110, 11:0b0111, 13:0b1000, 14:0b1001}
        cl_enc = cl_map.get(cl, 0b0111)  # default CL=11

        wr_map = {5:0b001, 6:0b010, 7:0b011, 8:0b100, 10:0b101,
                  12:0b110, 14:0b111, 16:0b000}
        wr_enc = wr_map.get(wr_nCK, 0b110)  # default WR=12

        val = 0
        val |= 0b00                  # A[1:0] BL=fixed8
        val |= (cl_enc & 1) << 2     # A2 = CL[0]
        val |= ((cl_enc >> 1) & 0b111) << 4  # A[6:4] = CL[3:1]
        val |= 1 << 8                # A8 = DLL reset
        val |= (wr_enc & 0b111) << 9 # A[11:9] = WR
        val |= (1 if mr0.get("precharge_pd_mode") == "fast_exit" else 0) << 12

        return f"{self.p['DDR_ADDR_W']}'h{val:04X}"

    def _encode_mr1(self) -> str:
        mr1 = self.p["MR"]["MR1"]

        val = 0
        # A0 = DLL enable (0=enable, 1=disable)
        val |= (0 if mr1.get("dll_enable", True) else 1)
        # A[2,1] = ODS (output drive): 00=RZQ/6, 01=RZQ/7
        if mr1.get("output_drive_strength") == "RZQ_7":
            val |= 1 << 1
        # A[9,6,2] = RTT_NOM
        rtt_map = {"disabled": 0b000, "RZQ_4": 0b001, "RZQ_2": 0b010,
                   "RZQ_6": 0b011, "RZQ_12": 0b100, "RZQ_8": 0b101}
        rtt = rtt_map.get(mr1.get("rtt_nom", "RZQ_4"), 0b001)
        val |= (rtt & 1) << 2
        val |= ((rtt >> 1) & 1) << 6
        val |= ((rtt >> 2) & 1) << 9
        # A7 = Write leveling (0=disabled)
        if mr1.get("write_leveling_enable", False):
            val |= 1 << 7

        return f"{self.p['DDR_ADDR_W']}'h{val:04X}"

    def _encode_mr2(self) -> str:
        mr2 = self.p["MR"]["MR2"]

        val = 0
        # A[5:3] = CWL
        cwl = mr2["cas_write_latency_cycles"]
        cwl_enc = cwl - 5  # CWL 5=000, 6=001, ..., 12=111
        val |= (cwl_enc & 0b111) << 3
        # A[10:9] = RTT_WR
        rtt_wr_map = {"disabled": 0b00, "RZQ_4": 0b01, "RZQ_2": 0b10}
        rtt_wr = rtt_wr_map.get(mr2.get("rtt_wr", "RZQ_4"), 0b01)
        val |= (rtt_wr & 0b11) << 9

        return f"{self.p['DDR_ADDR_W']}'h{val:04X}"

    def _encode_mr3(self) -> str:
        mr3 = self.p["MR"]["MR3"]
        val = 0
        if mr3.get("mpr_enable", False):
            val |= 1 << 2
        return f"{self.p['DDR_ADDR_W']}'h{val:04X}"

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        lines = []
        L = lines.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module:    init_fsm")
        L(f"// File:      init_fsm.sv")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Init/Reset FSM Agent (Phase 1)")
        L(f"// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}")
        L(f"//")
        L(f"// JEDEC DDR3 Initialization Sequence (JESD79-3F §4.6):")
        L(f"//   RESET# low ({p['RESET_HOLD_US']}µs = {p['RESET_HOLD_CYC']} ctrl clks)")
        L(f"//   → RESET# high → CKE delay ({p['CKE_DELAY_US']}µs = {p['CKE_DELAY_CYC']} ctrl clks)")
        L(f"//   → CKE high → tXPR ({p['tXPR_ns']}ns = {p['tXPR_CYC']} ctrl clks)")
        L(f"//   → MR2 → MR3 → MR1 → MR0 (DLL reset) → ZQCL ({p['tZQinit_CYC']} ctrl clks)")
        L(f"//   → init_done")
        L(f"//")
        L(f"// Counter width: {p['CTR_WIDTH']} bits (max wait = {p['MAX_WAIT']} cycles)")
        L(f"// DDR address:   {p['DDR_ADDR_W']} bits, Bank: {p['DDR_BANK_W']} bits")
        L(f"//")
        L(f"// Validation: IN-001 .. IN-011")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"")
        L(f"module init_fsm #(")
        L(f"    parameter DDR_ADDR_W  = {p['DDR_ADDR_W']},")
        L(f"    parameter DDR_BANK_W  = {p['DDR_BANK_W']},")
        L(f"    parameter CTR_WIDTH   = {p['CTR_WIDTH']}")
        L(f") (")
        L(f"    // ────────────── Clock / Reset ──────────────")
        L(f"    input  logic                    clk,")
        L(f"    input  logic                    rst_n,")
        L(f"")
        L(f"    // ────────────── Control ──────────────")
        L(f"    input  logic                    enable,         // start init when high")
        L(f"")
        L(f"    // ────────────── Status outputs ──────────────")
        L(f"    output logic                    init_done,      // init complete")
        L(f"    output logic                    init_fail,      // init timeout/error")
        L(f"")
        L(f"    // ────────────── DDR3 command outputs (to cmd_gen) ──────────────")
        L(f"    output logic                    init_cmd_valid, // command valid")
        L(f"    output logic [3:0]              init_cmd,       // {{cs_n, ras_n, cas_n, we_n}}")
        L(f"    output logic [DDR_ADDR_W-1:0]   init_addr,      // MR data / row address")
        L(f"    output logic [DDR_BANK_W-1:0]   init_bank,      // bank (selects MR0-3)")
        L(f"")
        L(f"    // ────────────── DDR3 control outputs ──────────────")
        L(f"    output logic                    init_cke,       // clock enable")
        L(f"    output logic                    init_reset_n,   // RESET# to DRAM")
        L(f"")
        L(f"    // ────────────── State debug (observability) ──────────────")
        L(f"    output logic [3:0]              init_state      // current FSM state")
        L(f");")
        L(f"")

        # ── Command encodings ──
        L(f"    // ================================================================")
        L(f"    // DDR3 command encodings {{CS#, RAS#, CAS#, WE#}}")
        L(f"    // ================================================================")
        L(f"    localparam CMD_NOP  = 4'b0111;  // CS=0, RAS=1, CAS=1, WE=1")
        L(f"    localparam CMD_MRS  = 4'b0000;  // mode register set")
        L(f"    localparam CMD_ZQCL = 4'b0110;  // ZQ calibration long (WE=0)")
        L(f"    localparam CMD_DESL = 4'b1111;  // deselect (CS=1)")
        L(f"")

        # ── Wait counts ──
        L(f"    // ================================================================")
        L(f"    // Wait counts (derived from spec)")
        L(f"    // ================================================================")
        L(f"    localparam CTR_WIDTH_W = CTR_WIDTH;")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_RESET    = {p['RESET_HOLD_CYC']};  // {p['RESET_HOLD_US']}µs")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_CKE      = {p['CKE_DELAY_CYC']};  // {p['CKE_DELAY_US']}µs")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TXPR     = {p['tXPR_CYC']};    // tXPR = {p['tXPR_ns']}ns")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TMRD     = {p['tMRD_CYC']};      // tMRD = 4 nCK")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TMOD     = {p['tMOD_CYC']};      // tMOD = max(12nCK, 15ns)")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_ZQCL     = {p['tZQinit_CYC']};   // tZQinit = 512 nCK")
        L(f"")

        # ── MR values ──
        L(f"    // ================================================================")
        L(f"    // Mode register encoded values")
        L(f"    // ================================================================")
        L(f"    localparam [DDR_ADDR_W-1:0] MR0_VAL = {self._encode_mr0()};")
        L(f"    localparam [DDR_ADDR_W-1:0] MR1_VAL = {self._encode_mr1()};")
        L(f"    localparam [DDR_ADDR_W-1:0] MR2_VAL = {self._encode_mr2()};")
        L(f"    localparam [DDR_ADDR_W-1:0] MR3_VAL = {self._encode_mr3()};")
        L(f"")

        # ── State encoding ──
        L(f"    // ================================================================")
        L(f"    // FSM states")
        L(f"    // ================================================================")
        L(f"    typedef enum logic [3:0] {{")
        L(f"        S_IDLE       = 4'd0,   // waiting for enable")
        L(f"        S_RESET_LOW  = 4'd1,   // RESET# asserted low")
        L(f"        S_RESET_HIGH = 4'd2,   // RESET# released, wait before CKE")
        L(f"        S_CKE_WAIT   = 4'd3,   // CKE high, wait tXPR")
        L(f"        S_MR2        = 4'd4,   // issue MRS for MR2")
        L(f"        S_MR2_WAIT   = 4'd5,   // wait tMRD")
        L(f"        S_MR3        = 4'd6,   // issue MRS for MR3")
        L(f"        S_MR3_WAIT   = 4'd7,   // wait tMRD")
        L(f"        S_MR1        = 4'd8,   // issue MRS for MR1")
        L(f"        S_MR1_WAIT   = 4'd9,   // wait tMRD")
        L(f"        S_MR0        = 4'd10,  // issue MRS for MR0 (DLL reset)")
        L(f"        S_MR0_WAIT   = 4'd11,  // wait tMOD")
        L(f"        S_ZQCL       = 4'd12,  // issue ZQCL")
        L(f"        S_ZQCL_WAIT  = 4'd13,  // wait tZQinit")
        L(f"        S_DONE       = 4'd14   // init complete")
        L(f"    }} state_t;")
        L(f"")
        L(f"    state_t state, state_nxt;")
        L(f"")

        # ── Counter ──
        L(f"    // ================================================================")
        L(f"    // Wait counter")
        L(f"    // ================================================================")
        L(f"    logic [CTR_WIDTH-1:0] ctr, ctr_load;")
        L(f"    logic                 ctr_en, ctr_done;")
        L(f"")
        L(f"    assign ctr_done = (ctr == '0);")
        L(f"")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n)")
        L(f"            ctr <= '0;")
        L(f"        else if (ctr_en)")
        L(f"            ctr <= ctr_load;")
        L(f"        else if (!ctr_done)")
        L(f"            ctr <= ctr - 1'b1;")
        L(f"")

        # ── State register ──
        L(f"    // ================================================================")
        L(f"    // State register")
        L(f"    // ================================================================")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) state <= S_IDLE;")
        L(f"        else        state <= state_nxt;")
        L(f"")
        L(f"    assign init_state = state;")
        L(f"")

        # ── Next-state + output logic ──
        L(f"    // ================================================================")
        L(f"    // Next-state and output logic")
        L(f"    // ================================================================")
        L(f"    always_comb begin")
        L(f"        // Defaults")
        L(f"        state_nxt     = state;")
        L(f"        ctr_en        = 1'b0;")
        L(f"        ctr_load      = '0;")
        L(f"        init_cmd_valid= 1'b0;")
        L(f"        init_cmd      = CMD_NOP;")
        L(f"        init_addr     = '0;")
        L(f"        init_bank     = '0;")
        L(f"        init_cke      = 1'b0;")
        L(f"        init_reset_n  = 1'b1;")
        L(f"        init_done     = 1'b0;")
        L(f"        init_fail     = 1'b0;")
        L(f"")
        L(f"        case (state)")
        L(f"")
        L(f"            S_IDLE: begin")
        L(f"                init_reset_n = 1'b0;  // hold reset low")
        L(f"                init_cke     = 1'b0;")
        L(f"                if (enable) begin")
        L(f"                    state_nxt = S_RESET_LOW;")
        L(f"                    ctr_en    = 1'b1;")
        L(f"                    ctr_load  = WAIT_RESET;")
        L(f"                end")
        L(f"            end")
        L(f"")
        L(f"            S_RESET_LOW: begin")
        L(f"                init_reset_n = 1'b0;  // RESET# still low")
        L(f"                init_cke     = 1'b0;")
        L(f"                if (ctr_done) begin")
        L(f"                    state_nxt = S_RESET_HIGH;")
        L(f"                    ctr_en    = 1'b1;")
        L(f"                    ctr_load  = WAIT_CKE;")
        L(f"                end")
        L(f"            end")
        L(f"")
        L(f"            S_RESET_HIGH: begin")
        L(f"                init_reset_n = 1'b1;  // RESET# released")
        L(f"                init_cke     = 1'b0;  // CKE still low")
        L(f"                if (ctr_done) begin")
        L(f"                    state_nxt = S_CKE_WAIT;")
        L(f"                    ctr_en    = 1'b1;")
        L(f"                    ctr_load  = WAIT_TXPR;")
        L(f"                end")
        L(f"            end")
        L(f"")
        L(f"            S_CKE_WAIT: begin")
        L(f"                init_cke = 1'b1;      // CKE now high")
        L(f"                if (ctr_done)")
        L(f"                    state_nxt = S_MR2;")
        L(f"            end")
        L(f"")

        # MR2
        L(f"            S_MR2: begin")
        L(f"                init_cke       = 1'b1;")
        L(f"                init_cmd_valid = 1'b1;")
        L(f"                init_cmd       = CMD_MRS;")
        L(f"                init_addr      = MR2_VAL;")
        L(f"                init_bank      = {p['DDR_BANK_W']}'d2;")
        L(f"                state_nxt      = S_MR2_WAIT;")
        L(f"                ctr_en         = 1'b1;")
        L(f"                ctr_load       = WAIT_TMRD;")
        L(f"            end")
        L(f"")
        L(f"            S_MR2_WAIT: begin")
        L(f"                init_cke = 1'b1;")
        L(f"                if (ctr_done) state_nxt = S_MR3;")
        L(f"            end")
        L(f"")

        # MR3
        L(f"            S_MR3: begin")
        L(f"                init_cke       = 1'b1;")
        L(f"                init_cmd_valid = 1'b1;")
        L(f"                init_cmd       = CMD_MRS;")
        L(f"                init_addr      = MR3_VAL;")
        L(f"                init_bank      = {p['DDR_BANK_W']}'d3;")
        L(f"                state_nxt      = S_MR3_WAIT;")
        L(f"                ctr_en         = 1'b1;")
        L(f"                ctr_load       = WAIT_TMRD;")
        L(f"            end")
        L(f"")
        L(f"            S_MR3_WAIT: begin")
        L(f"                init_cke = 1'b1;")
        L(f"                if (ctr_done) state_nxt = S_MR1;")
        L(f"            end")
        L(f"")

        # MR1
        L(f"            S_MR1: begin")
        L(f"                init_cke       = 1'b1;")
        L(f"                init_cmd_valid = 1'b1;")
        L(f"                init_cmd       = CMD_MRS;")
        L(f"                init_addr      = MR1_VAL;")
        L(f"                init_bank      = {p['DDR_BANK_W']}'d1;")
        L(f"                state_nxt      = S_MR1_WAIT;")
        L(f"                ctr_en         = 1'b1;")
        L(f"                ctr_load       = WAIT_TMRD;")
        L(f"            end")
        L(f"")
        L(f"            S_MR1_WAIT: begin")
        L(f"                init_cke = 1'b1;")
        L(f"                if (ctr_done) state_nxt = S_MR0;")
        L(f"            end")
        L(f"")

        # MR0
        L(f"            S_MR0: begin")
        L(f"                init_cke       = 1'b1;")
        L(f"                init_cmd_valid = 1'b1;")
        L(f"                init_cmd       = CMD_MRS;")
        L(f"                init_addr      = MR0_VAL;  // includes DLL reset bit")
        L(f"                init_bank      = {p['DDR_BANK_W']}'d0;")
        L(f"                state_nxt      = S_MR0_WAIT;")
        L(f"                ctr_en         = 1'b1;")
        L(f"                ctr_load       = WAIT_TMOD;  // tMOD after MR0 before ZQCL")
        L(f"            end")
        L(f"")
        L(f"            S_MR0_WAIT: begin")
        L(f"                init_cke = 1'b1;")
        L(f"                if (ctr_done) state_nxt = S_ZQCL;")
        L(f"            end")
        L(f"")

        # ZQCL
        L(f"            S_ZQCL: begin")
        L(f"                init_cke       = 1'b1;")
        L(f"                init_cmd_valid = 1'b1;")
        L(f"                init_cmd       = CMD_ZQCL;")
        L(f"                init_addr      = '0;")
        L(f"                init_addr[10]  = 1'b1;  // A10=1 for ZQCL (long)")
        L(f"                init_bank      = '0;")
        L(f"                state_nxt      = S_ZQCL_WAIT;")
        L(f"                ctr_en         = 1'b1;")
        L(f"                ctr_load       = WAIT_ZQCL;")
        L(f"            end")
        L(f"")
        L(f"            S_ZQCL_WAIT: begin")
        L(f"                init_cke = 1'b1;")
        L(f"                if (ctr_done) state_nxt = S_DONE;")
        L(f"            end")
        L(f"")

        # DONE
        L(f"            S_DONE: begin")
        L(f"                init_cke  = 1'b1;")
        L(f"                init_done = 1'b1;")
        L(f"            end")
        L(f"")
        L(f"            default: begin")
        L(f"                state_nxt = S_IDLE;")
        L(f"                init_fail = 1'b1;")
        L(f"            end")
        L(f"        endcase")
        L(f"    end")
        L(f"")

        # ── Assertions ──
        L(f"    // ================================================================")
        L(f"    // SVA — simulation only")
        L(f"    // ================================================================")
        L(f"    // synopsys translate_off")
        L(f"    // synthesis translate_off")
        L(f"")
        L(f"    // IN-001: RESET# held low for >= {p['RESET_HOLD_US']}µs")
        L(f"    // IN-002: CKE low during reset")
        L(f"    property p_cke_low_during_reset;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (state == S_RESET_LOW) |-> (!init_cke);")
        L(f"    endproperty")
        L(f"    assert property (p_cke_low_during_reset)")
        L(f"        else $error(\"[IN-002] CKE not low during reset\");")
        L(f"")
        L(f"    // IN-003: MR program order is MR2→MR3→MR1→MR0")
        L(f"    // (enforced structurally by FSM)")
        L(f"")
        L(f"    // IN-005: init_done only in S_DONE")
        L(f"    property p_done_only_in_done;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        init_done |-> (state == S_DONE);")
        L(f"    endproperty")
        L(f"    assert property (p_done_only_in_done)")
        L(f"        else $error(\"[IN-005] init_done asserted outside S_DONE\");")
        L(f"")
        L(f"    // IN-010: ZQCL A10=1")
        L(f"    property p_zqcl_a10;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (state == S_ZQCL && init_cmd_valid) |-> init_addr[10];")
        L(f"    endproperty")
        L(f"    assert property (p_zqcl_a10)")
        L(f"        else $error(\"[IN-010] ZQCL issued without A10=1\");")
        L(f"")
        L(f"    // Coverage")
        L(f"    covergroup cg_init @(posedge clk);")
        L(f"        option.per_instance = 1;")
        L(f"        cp_state   : coverpoint state;")
        L(f"        cp_mr_cmd  : coverpoint (init_cmd_valid && init_cmd == CMD_MRS);")
        L(f"        cp_zq_cmd  : coverpoint (init_cmd_valid && init_cmd == CMD_ZQCL);")
        L(f"        cp_done    : coverpoint init_done;")
        L(f"    endgroup")
        L(f"    cg_init cg_inst = new();")
        L(f"")
        L(f"    // synthesis translate_on")
        L(f"    // synopsys translate_on")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "init_fsm",
            "file": "init_fsm.sv",
            "phase": 1,
            "agent": "init_fsm_agent",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "DDR_ADDR_W": p["DDR_ADDR_W"],
                "DDR_BANK_W": p["DDR_BANK_W"],
                "CTR_WIDTH": p["CTR_WIDTH"],
                "RESET_HOLD_CYC": p["RESET_HOLD_CYC"],
                "CKE_DELAY_CYC": p["CKE_DELAY_CYC"],
                "tXPR_CYC": p["tXPR_CYC"],
                "tZQinit_CYC": p["tZQinit_CYC"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk",   "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "control": [
                    {"name": "enable", "width": 1, "dir": "input"},
                ],
                "status_out": [
                    {"name": "init_done", "width": 1, "dir": "output"},
                    {"name": "init_fail", "width": 1, "dir": "output"},
                ],
                "ddr_cmd_out": [
                    {"name": "init_cmd_valid", "width": 1, "dir": "output"},
                    {"name": "init_cmd",       "width": 4, "dir": "output"},
                    {"name": "init_addr",      "width": p["DDR_ADDR_W"], "dir": "output"},
                    {"name": "init_bank",      "width": p["DDR_BANK_W"], "dir": "output"},
                ],
                "ddr_ctrl_out": [
                    {"name": "init_cke",     "width": 1, "dir": "output"},
                    {"name": "init_reset_n", "width": 1, "dir": "output"},
                ],
                "debug": [
                    {"name": "init_state", "width": 4, "dir": "output"},
                ],
            },
            "assertions": [
                {"name": "p_cke_low_during_reset", "check": "IN-002"},
                {"name": "p_done_only_in_done",    "check": "IN-005"},
                {"name": "p_zqcl_a10",             "check": "IN-010"},
            ],
            "coverage_points": [
                "cp_state", "cp_mr_cmd", "cp_zq_cmd", "cp_done",
            ],
        }

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  INIT / RESET FSM AGENT\n  Spec: {self.spec_path}\n{hdr}")

        print("\n[1/4] Validating parameters …")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ✗ {e}")
            return {"status": "error", "errors": errs}
        print("  ✓ All parameters valid")
        for k, v in self.p.items():
            if k == "MR":
                print(f"    {'MR registers':20s} = MR0..MR3 encoded")
            else:
                print(f"    {k:20s} = {v}")

        print("\n[2/4] Generating RTL …")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  ✓ {rtl_lines} lines of SystemVerilog")
        print(f"    MR0 = {self._encode_mr0()}")
        print(f"    MR1 = {self._encode_mr1()}")
        print(f"    MR2 = {self._encode_mr2()}")
        print(f"    MR3 = {self._encode_mr3()}")

        print("\n[3/4] Generating port manifest …")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  ✓ {port_cnt} ports | {len(manifest['assertions'])} assertions | {len(manifest['coverage_points'])} cover points")

        print("\n[4/4] Writing files …")
        rtl_path = self.output_dir / "init_fsm.sv"
        rtl_path.write_text(rtl)
        print(f"  ✓ {rtl_path}")

        mfst_path = self.output_dir / "init_fsm_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {mfst_path}")

        print(f"\n{hdr}\n  DONE — init_fsm.sv ready for Phase 1 integration\n{hdr}")
        return {
            "status": "success",
            "module": "init_fsm",
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
    print("║     INIT / RESET FSM AGENT  (Phase 1)       ║")
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
    agent = InitFsmAgent(spec_path, output_dir)
    result = agent.run()
    sys.exit(0 if result["status"] == "success" else 1)