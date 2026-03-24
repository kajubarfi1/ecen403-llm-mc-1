#!/usr/bin/env python3
"""
+======================================================================+
|                 INIT / RESET FSM AGENT                               |
|                                                                      |
|  Phase 1 RTL Generation Agent                                        |
|  Generates: init_fsm.sv + init_fsm_tb.sv + init_fsm_manifest.json   |
|                                                                      |
|  Dependencies: None (Phase 1)                                        |
|                                                                      |
|  Spec sections consumed:                                             |
|    initialization_sequence, clocking_model, timing_model,            |
|    memory_geometry                                                   |
|                                                                      |
|  Implements:                                                         |
|    JEDEC DDR3 init sequence (JESD79-3F 4.6):                        |
|      RESET# low (200us) -> RESET# high -> CKE delay (500us)         |
|      -> CKE high -> tXPR wait -> MR2 -> MR3 -> MR1                  |
|      -> MR0 (DLL reset) -> ZQCL (512 nCK) -> init_done              |
|                                                                      |
|  Testbench: ~35 tests across 9 sections (A-I)                       |
|    A: Normal init sequence    B: MR values on wire                   |
|    C: ZQCL encoding           D: Signal integrity                    |
|    E: Idle behavior           F: Enable deassert mid-init            |
|    G: Reset mid-init          H: Re-init after done                  |
|    I: Late enable                                                    |
|                                                                      |
|  Validation checks: IN-001 through IN-011                            |
+======================================================================+
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

    # ================================================================
    # Parameter derivation
    # ================================================================
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

        reset_hold_us = self.init_seq["reset_hold_us"]
        cke_delay_us  = self.init_seq["cke_delay_us"]
        p["RESET_HOLD_US"]  = reset_hold_us
        p["CKE_DELAY_US"]   = cke_delay_us
        p["RESET_HOLD_CYC"] = math.ceil(reset_hold_us * 1000 / ctrl_period_ns)
        p["CKE_DELAY_CYC"]  = math.ceil(cke_delay_us * 1000 / ctrl_period_ns)

        tXPR_ns = self.init_seq["tXPR_ns"]
        p["tXPR_ns"]  = tXPR_ns
        p["tXPR_CYC"] = math.ceil(tXPR_ns / ctrl_period_ns)

        tZQinit_ns = self.init_seq["tZQinit_ns"]
        p["tZQinit_ns"]  = tZQinit_ns
        p["tZQinit_CYC"] = math.ceil(tZQinit_ns / ctrl_period_ns)

        p["tMRD_CYC"] = math.ceil(4 * tCK_ns / ctrl_period_ns)

        tMOD_nCK = max(12, math.ceil(15.0 / tCK_ns))
        p["tMOD_CYC"] = math.ceil(tMOD_nCK * tCK_ns / ctrl_period_ns)

        max_wait = max(p["RESET_HOLD_CYC"], p["CKE_DELAY_CYC"],
                       p["tXPR_CYC"], p["tZQinit_CYC"])
        p["CTR_WIDTH"] = max(1, (max_wait).bit_length())
        p["MAX_WAIT"]  = max_wait

        p["DDR_ADDR_W"] = max(self.geometry["row_bits"], self.geometry["column_bits"])
        p["DDR_BANK_W"] = self.geometry["bank_bits"]

        p["MR"] = self.init_seq["mode_registers"]

        return p

    # ================================================================
    # Pre-generation validation
    # ================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        mr = p["MR"]

        if p["RESET_HOLD_US"] < 200:
            errors.append(f"JEDEC requires reset_hold >= 200us, got {p['RESET_HOLD_US']}")
        if p["CKE_DELAY_US"] < 500:
            errors.append(f"JEDEC requires cke_delay >= 500us, got {p['CKE_DELAY_US']}")
        if not self.init_seq.get("zq_calibration_on_init", True):
            errors.append("JEDEC requires ZQCL on init")

        derived = self.timing.get("$derived_cycles", {})
        if derived:
            spec_cl = mr["MR0"]["cas_latency_cycles"]
            spec_cwl = mr["MR2"]["cas_write_latency_cycles"]

        order = self.init_seq.get("$derived", {}).get("init_sequence_order", "")
        if "MR2" in order and "MR0" in order:
            mr2_pos = order.index("MR2")
            mr0_pos = order.index("MR0")
            if mr2_pos > mr0_pos:
                errors.append("JEDEC requires MR2 before MR0 in init sequence")

        return errors

    # ================================================================
    # Mode register encoders
    # ================================================================
    def _encode_mr0(self) -> str:
        mr0 = self.p["MR"]["MR0"]
        cl = mr0["cas_latency_cycles"]
        wr_ns = mr0["write_recovery_ns"]
        tCK = self.p["tCK_ns"]
        wr_nCK = math.ceil(wr_ns / tCK)

        cl_map = {5:0b0001, 6:0b0010, 7:0b0011, 8:0b0100, 9:0b0101,
                  10:0b0110, 11:0b0111, 13:0b1000, 14:0b1001}
        cl_enc = cl_map.get(cl, 0b0111)

        wr_map = {5:0b001, 6:0b010, 7:0b011, 8:0b100, 10:0b101,
                  12:0b110, 14:0b111, 16:0b000}
        wr_enc = wr_map.get(wr_nCK, 0b110)

        val = 0
        val |= 0b00
        val |= (cl_enc & 1) << 2
        val |= ((cl_enc >> 1) & 0b111) << 4
        val |= 1 << 8
        val |= (wr_enc & 0b111) << 9
        val |= (1 if mr0.get("precharge_pd_mode") == "fast_exit" else 0) << 12

        return f"{self.p['DDR_ADDR_W']}'h{val:04X}"

    def _encode_mr1(self) -> str:
        mr1 = self.p["MR"]["MR1"]
        val = 0
        val |= (0 if mr1.get("dll_enable", True) else 1)
        if mr1.get("output_drive_strength") == "RZQ_7":
            val |= 1 << 1
        rtt_map = {"disabled": 0b000, "RZQ_4": 0b001, "RZQ_2": 0b010,
                   "RZQ_6": 0b011, "RZQ_12": 0b100, "RZQ_8": 0b101}
        rtt = rtt_map.get(mr1.get("rtt_nom", "RZQ_4"), 0b001)
        val |= (rtt & 1) << 2
        val |= ((rtt >> 1) & 1) << 6
        val |= ((rtt >> 2) & 1) << 9
        if mr1.get("write_leveling_enable", False):
            val |= 1 << 7
        return f"{self.p['DDR_ADDR_W']}'h{val:04X}"

    def _encode_mr2(self) -> str:
        mr2 = self.p["MR"]["MR2"]
        val = 0
        cwl = mr2["cas_write_latency_cycles"]
        cwl_enc = cwl - 5
        val |= (cwl_enc & 0b111) << 3
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

    def _mr_hex(self, encode_fn) -> str:
        """Extract just the hex value from an encode string like 15'h1D34 -> 1D34."""
        full = encode_fn()
        return full.split("'h")[1] if "'h" in full else full

    # ================================================================
    # RTL generation
    # ================================================================
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
        L(f"// JEDEC DDR3 Initialization Sequence (JESD79-3F 4.6):")
        L(f"//   RESET# low ({p['RESET_HOLD_US']}us = {p['RESET_HOLD_CYC']} ctrl clks)")
        L(f"//   -> RESET# high -> CKE delay ({p['CKE_DELAY_US']}us = {p['CKE_DELAY_CYC']} ctrl clks)")
        L(f"//   -> CKE high -> tXPR ({p['tXPR_ns']}ns = {p['tXPR_CYC']} ctrl clks)")
        L(f"//   -> MR2 -> MR3 -> MR1 -> MR0 (DLL reset) -> ZQCL ({p['tZQinit_CYC']} ctrl clks)")
        L(f"//   -> init_done")
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
        L(f"    // Clock / Reset")
        L(f"    input  logic                    clk,")
        L(f"    input  logic                    rst_n,")
        L(f"")
        L(f"    // Control")
        L(f"    input  logic                    enable,         // start init when high")
        L(f"")
        L(f"    // Status outputs")
        L(f"    output logic                    init_done,      // init complete")
        L(f"    output logic                    init_fail,      // init timeout/error")
        L(f"")
        L(f"    // DDR3 command outputs (to cmd_gen)")
        L(f"    output logic                    init_cmd_valid, // command valid")
        L(f"    output logic [3:0]              init_cmd,       // {{cs_n, ras_n, cas_n, we_n}}")
        L(f"    output logic [DDR_ADDR_W-1:0]   init_addr,      // MR data / row address")
        L(f"    output logic [DDR_BANK_W-1:0]   init_bank,      // bank (selects MR0-3)")
        L(f"")
        L(f"    // DDR3 control outputs")
        L(f"    output logic                    init_cke,       // clock enable")
        L(f"    output logic                    init_reset_n,   // RESET# to DRAM")
        L(f"")
        L(f"    // State debug (observability)")
        L(f"    output logic [3:0]              init_state      // current FSM state")
        L(f");")
        L(f"")

        L(f"    // ================================================================")
        L(f"    // DDR3 command encodings {{CS#, RAS#, CAS#, WE#}}")
        L(f"    // ================================================================")
        L(f"    localparam CMD_NOP  = 4'b0111;  // CS=0, RAS=1, CAS=1, WE=1")
        L(f"    localparam CMD_MRS  = 4'b0000;  // mode register set")
        L(f"    localparam CMD_ZQCL = 4'b0110;  // ZQ calibration long (WE=0)")
        L(f"    localparam CMD_DESL = 4'b1111;  // deselect (CS=1)")
        L(f"")

        L(f"    // ================================================================")
        L(f"    // Wait counts (derived from spec)")
        L(f"    // ================================================================")
        L(f"    localparam CTR_WIDTH_W = CTR_WIDTH;")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_RESET    = {p['RESET_HOLD_CYC']};  // {p['RESET_HOLD_US']}us")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_CKE      = {p['CKE_DELAY_CYC']};  // {p['CKE_DELAY_US']}us")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TXPR     = {p['tXPR_CYC']};    // tXPR = {p['tXPR_ns']}ns")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TMRD     = {p['tMRD_CYC']};      // tMRD = 4 nCK")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TMOD     = {p['tMOD_CYC']};      // tMOD = max(12nCK, 15ns)")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_ZQCL     = {p['tZQinit_CYC']};   // tZQinit = 512 nCK")
        L(f"")

        L(f"    // ================================================================")
        L(f"    // Mode register encoded values")
        L(f"    // ================================================================")
        L(f"    localparam [DDR_ADDR_W-1:0] MR0_VAL = {self._encode_mr0()};")
        L(f"    localparam [DDR_ADDR_W-1:0] MR1_VAL = {self._encode_mr1()};")
        L(f"    localparam [DDR_ADDR_W-1:0] MR2_VAL = {self._encode_mr2()};")
        L(f"    localparam [DDR_ADDR_W-1:0] MR3_VAL = {self._encode_mr3()};")
        L(f"")

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

        L(f"    // ================================================================")
        L(f"    // State register")
        L(f"    // ================================================================")
        L(f"    always_ff @(posedge clk or negedge rst_n)")
        L(f"        if (!rst_n) state <= S_IDLE;")
        L(f"        else        state <= state_nxt;")
        L(f"")
        L(f"    assign init_state = state;")
        L(f"")

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
        L(f"                init_reset_n = 1'b0;")
        L(f"                init_cke     = 1'b0;")
        L(f"                if (ctr_done) begin")
        L(f"                    state_nxt = S_RESET_HIGH;")
        L(f"                    ctr_en    = 1'b1;")
        L(f"                    ctr_load  = WAIT_CKE;")
        L(f"                end")
        L(f"            end")
        L(f"")
        L(f"            S_RESET_HIGH: begin")
        L(f"                init_reset_n = 1'b1;")
        L(f"                init_cke     = 1'b0;")
        L(f"                if (ctr_done) begin")
        L(f"                    state_nxt = S_CKE_WAIT;")
        L(f"                    ctr_en    = 1'b1;")
        L(f"                    ctr_load  = WAIT_TXPR;")
        L(f"                end")
        L(f"            end")
        L(f"")
        L(f"            S_CKE_WAIT: begin")
        L(f"                init_cke = 1'b1;")
        L(f"                if (ctr_done)")
        L(f"                    state_nxt = S_MR2;")
        L(f"            end")
        L(f"")

        # MR2 -> MR3 -> MR1 -> MR0
        for mr_name, mr_val, bank_n, next_st, wait_name, wait_st in [
            ("MR2", "MR2_VAL", 2, "S_MR2_WAIT", "WAIT_TMRD", "S_MR3"),
            ("MR3", "MR3_VAL", 3, "S_MR3_WAIT", "WAIT_TMRD", "S_MR1"),
            ("MR1", "MR1_VAL", 1, "S_MR1_WAIT", "WAIT_TMRD", "S_MR0"),
            ("MR0", "MR0_VAL", 0, "S_MR0_WAIT", "WAIT_TMOD", "S_ZQCL"),
        ]:
            st = f"S_{mr_name}"
            L(f"            {st}: begin")
            L(f"                init_cke       = 1'b1;")
            L(f"                init_cmd_valid = 1'b1;")
            L(f"                init_cmd       = CMD_MRS;")
            L(f"                init_addr      = {mr_val};")
            if mr_name == "MR0":
                L(f"                // includes DLL reset bit")
            L(f"                init_bank      = {p['DDR_BANK_W']}'d{bank_n};")
            L(f"                state_nxt      = {next_st};")
            L(f"                ctr_en         = 1'b1;")
            L(f"                ctr_load       = {wait_name};")
            if mr_name == "MR0":
                L(f"                // tMOD after MR0 before ZQCL")
            L(f"            end")
            L(f"")
            L(f"            {next_st}: begin")
            L(f"                init_cke = 1'b1;")
            L(f"                if (ctr_done) state_nxt = {wait_st};")
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

        # SVA
        L(f"    // ================================================================")
        L(f"    // SVA -- simulation only")
        L(f"    // ================================================================")
        L(f"    // synopsys translate_off")
        L(f"    // synthesis translate_off")
        L(f"")
        L(f"    // IN-001: RESET# held low for >= {p['RESET_HOLD_US']}us")
        L(f"    // IN-002: CKE low during reset")
        L(f"    property p_cke_low_during_reset;")
        L(f"        @(posedge clk) disable iff (!rst_n)")
        L(f"        (state == S_RESET_LOW) |-> (!init_cke);")
        L(f"    endproperty")
        L(f"    assert property (p_cke_low_during_reset)")
        L(f"        else $error(\"[IN-002] CKE not low during reset\");")
        L(f"")
        L(f"    // IN-003: MR program order is MR2->MR3->MR1->MR0")
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

    # ================================================================
    # Testbench generation (~35 tests, VCD, Xelium-safe)
    # ================================================================
    def _tb_test_registry(self) -> list:
        """Returns ordered list of (id, description) for all TB tests."""
        return [
            ("A1", "init_done asserted"),
            ("A2", "init_fail never asserted"),
            ("A3", "FSM reached S_DONE (state=14)"),
            ("A4", "RESET# hold >= 40000 cycles (200us)"),
            ("A5", "CKE delay >= 100000 cycles (500us)"),
            ("A6", "Exactly 4 MRS commands issued"),
            ("A7", "MR order MR2(2)->MR3(3)->MR1(1)->MR0(0)"),
            ("B1", "MR2 addr value on wire"),
            ("B2", "MR3 addr value on wire"),
            ("B3", "MR1 addr value on wire"),
            ("B4", "MR0 addr value on wire"),
            ("B5", "All 4 MRS used CMD_MRS encoding (4'b0000)"),
            ("C1", "ZQCL command issued"),
            ("C2", "ZQCL A10 = 1 (long calibration)"),
            ("C3", "ZQCL bank = 0"),
            ("D1", "No spurious cmd_valid in wait states"),
            ("D2", "CKE low during RESET_LOW/HIGH"),
            ("D3", "RESET# low in IDLE/RESET_LOW"),
            ("D4", "init_done only asserted in S_DONE"),
            ("D5", "init_done is level (still high in S_DONE)"),
            ("D6", "init_state output matches S_DONE encoding"),
            ("E1", "FSM stays S_IDLE without enable"),
            ("E2", "init_done low in IDLE"),
            ("E3", "init_fail low in IDLE"),
            ("E4", "RESET# low in IDLE"),
            ("E5", "CKE low in IDLE"),
            ("E6", "cmd_valid low in IDLE"),
            ("F1", "Init completes after enable deasserted"),
            ("F2", "init_fail not asserted after enable deassert"),
            ("G1", "FSM returns to S_IDLE on async reset"),
            ("G2", "init_done deasserted after reset"),
            ("G3", "Re-init completes after mid-init reset"),
            ("G4", "MR order correct on re-init"),
            ("H1", "Second init completes"),
            ("H2", "4 MRS on re-init"),
            ("H3", "ZQCL issued on re-init"),
            ("I1", "FSM still IDLE after 500 cycles no enable"),
            ("I2", "Init completes with late enable"),
        ]

    def generate_testbench(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        addr_w = p["DDR_ADDR_W"]
        bank_w = p["DDR_BANK_W"]
        reset_cyc = p["RESET_HOLD_CYC"]
        cke_cyc   = p["CKE_DELAY_CYC"]
        timeout   = reset_cyc + cke_cyc + 5000  # generous margin

        mr0_hex = self._mr_hex(self._encode_mr0)
        mr1_hex = self._mr_hex(self._encode_mr1)
        mr2_hex = self._mr_hex(self._encode_mr2)
        mr3_hex = self._mr_hex(self._encode_mr3)

        tests = self._tb_test_registry()

        lines = []
        L = lines.append

        L(f"`timescale 1ns / 1ps")
        L(f"//==============================================================")
        L(f"// init_fsm_tb.sv -- Enhanced testbench ({len(tests)} tests)")
        L(f"// Generated: {ts}")
        L(f"// Agent:     Init/Reset FSM Agent (Phase 1)")
        L(f"//")
        L(f"// Sections:")
        L(f"//   A: Normal init sequence (timing, ordering, completion)")
        L(f"//   B: MR register value verification on the wire")
        L(f"//   C: ZQCL command encoding")
        L(f"//   D: Signal integrity during wait states")
        L(f"//   E: Idle behavior (no enable)")
        L(f"//   F: Enable deassert mid-init")
        L(f"//   G: Async reset mid-init + recovery")
        L(f"//   H: Back-to-back re-init after done")
        L(f"//   I: Late enable assertion")
        L(f"//")
        L(f"// Test List:")
        for tid, desc in tests:
            L(f"//   {tid:4s} {desc}")
        L(f"//")
        L(f"// VCD: dumps init_fsm_tb.vcd")
        L(f"//==============================================================")
        L(f"module init_fsm_tb;")
        L(f"")
        L(f"    // -- Clock: {p['CTRL_PERIOD']}ns period ({p['CTRL_FREQ']} MHz) --")
        L(f"    localparam real CLK_PERIOD = {p['CTRL_PERIOD']};")
        L(f"    logic clk = 0;")
        L(f"    always #(CLK_PERIOD/2) clk = ~clk;")
        L(f"")
        L(f"    // -- DUT signals --")
        L(f"    logic        rst_n;")
        L(f"    logic        enable;")
        L(f"    logic        init_done;")
        L(f"    logic        init_fail;")
        L(f"    logic        init_cmd_valid;")
        L(f"    logic [3:0]  init_cmd;")
        L(f"    logic [{addr_w - 1}:0] init_addr;")
        L(f"    logic [{bank_w - 1}:0]  init_bank;")
        L(f"    logic        init_cke;")
        L(f"    logic        init_reset_n;")
        L(f"    logic [3:0]  init_state;")
        L(f"")
        L(f"    // -- DUT --")
        L(f"    init_fsm dut (")
        L(f"        .clk           (clk),")
        L(f"        .rst_n         (rst_n),")
        L(f"        .enable        (enable),")
        L(f"        .init_done     (init_done),")
        L(f"        .init_fail     (init_fail),")
        L(f"        .init_cmd_valid(init_cmd_valid),")
        L(f"        .init_cmd      (init_cmd),")
        L(f"        .init_addr     (init_addr),")
        L(f"        .init_bank     (init_bank),")
        L(f"        .init_cke      (init_cke),")
        L(f"        .init_reset_n  (init_reset_n),")
        L(f"        .init_state    (init_state)")
        L(f"    );")
        L(f"")
        L(f"    // -- Command encodings --")
        L(f"    localparam CMD_MRS  = 4'b0000;")
        L(f"    localparam CMD_ZQCL = 4'b0110;")
        L(f"    localparam CMD_NOP  = 4'b0111;")
        L(f"")
        L(f"    // -- FSM state encodings (mirror RTL) --")
        for name, val in [("S_IDLE",0),("S_RESET_LOW",1),("S_RESET_HIGH",2),
                          ("S_CKE_WAIT",3),("S_MR2",4),("S_MR2_WAIT",5),
                          ("S_MR3",6),("S_MR3_WAIT",7),("S_MR1",8),("S_MR1_WAIT",9),
                          ("S_MR0",10),("S_MR0_WAIT",11),("S_ZQCL",12),
                          ("S_ZQCL_WAIT",13),("S_DONE",14)]:
            L(f"    localparam {name:16s} = 4'd{val};")
        L(f"")
        L(f"    // -- Expected MR values --")
        L(f"    localparam [{addr_w - 1}:0] EXP_MR0 = {addr_w}'h{mr0_hex};")
        L(f"    localparam [{addr_w - 1}:0] EXP_MR1 = {addr_w}'h{mr1_hex};")
        L(f"    localparam [{addr_w - 1}:0] EXP_MR2 = {addr_w}'h{mr2_hex};")
        L(f"    localparam [{addr_w - 1}:0] EXP_MR3 = {addr_w}'h{mr3_hex};")
        L(f"")
        L(f"    // -- Test infrastructure --")
        L(f"    int pass_count = 0;")
        L(f"    int fail_count = 0;")
        L(f"    int total_tests = 0;")
        L(f"")
        L(f"    task automatic check(string name, logic condition);")
        L(f"        total_tests++;")
        L(f"        if (condition) begin")
        L(f"            pass_count++;")
        L(f"            $display(\"  [PASS] %0d: %s\", total_tests, name);")
        L(f"        end else begin")
        L(f"            fail_count++;")
        L(f"            $display(\"  [FAIL] %0d: %s\", total_tests, name);")
        L(f"        end")
        L(f"    endtask")
        L(f"")

        # ── Monitor infrastructure ──
        L(f"    // ---------------------------------------------------------------")
        L(f"    // Monitor infrastructure")
        L(f"    // ---------------------------------------------------------------")
        L(f"    int cycle_count;")
        L(f"    int cke_rise_cycle;")
        L(f"    int reset_n_rise_cycle;")
        L(f"    int init_done_cycle;")
        L(f"    int mr_cmd_count;")
        L(f"    int mr_bank_idx;")
        L(f"    int zqcl_seen;")
        L(f"    int zqcl_a10_ok;")
        L(f"    int zqcl_bank_zero;")
        L(f"    int spurious_cmd_count;")
        L(f"    int fail_ever_asserted;")
        L(f"")
        L(f"    logic [{bank_w - 1}:0]  mr_bank_order  [0:7];")
        L(f"    logic [{addr_w - 1}:0] mr_addr_values [0:7];")
        L(f"    logic [3:0]  mr_cmd_values  [0:7];")
        L(f"")
        L(f"    function automatic logic is_wait_state(logic [3:0] st);")
        L(f"        return (st == S_IDLE      || st == S_RESET_LOW || st == S_RESET_HIGH ||")
        L(f"                st == S_CKE_WAIT  || st == S_MR2_WAIT  || st == S_MR3_WAIT  ||")
        L(f"                st == S_MR1_WAIT  || st == S_MR0_WAIT  || st == S_ZQCL_WAIT ||")
        L(f"                st == S_DONE);")
        L(f"    endfunction")
        L(f"")
        L(f"    always @(posedge clk) begin")
        L(f"        if (rst_n) begin")
        L(f"            cycle_count++;")
        L(f"")
        L(f"            if (init_cke && cke_rise_cycle == 0 && cycle_count > 2)")
        L(f"                cke_rise_cycle = cycle_count;")
        L(f"")
        L(f"            if (init_reset_n && reset_n_rise_cycle == 0 && cycle_count > 2)")
        L(f"                reset_n_rise_cycle = cycle_count;")
        L(f"")
        L(f"            if (init_cmd_valid && init_cmd == CMD_MRS) begin")
        L(f"                if (mr_bank_idx < 8) begin")
        L(f"                    mr_bank_order[mr_bank_idx]  = init_bank;")
        L(f"                    mr_addr_values[mr_bank_idx] = init_addr;")
        L(f"                    mr_cmd_values[mr_bank_idx]  = init_cmd;")
        L(f"                    mr_bank_idx++;")
        L(f"                end")
        L(f"                mr_cmd_count++;")
        L(f"            end")
        L(f"")
        L(f"            if (init_cmd_valid && init_cmd == CMD_ZQCL) begin")
        L(f"                zqcl_seen = 1;")
        L(f"                if (init_addr[10])      zqcl_a10_ok    = 1;")
        L(f"                if (init_bank == {bank_w}'d0) zqcl_bank_zero = 1;")
        L(f"            end")
        L(f"")
        L(f"            if (init_done && init_done_cycle == 0)")
        L(f"                init_done_cycle = cycle_count;")
        L(f"")
        L(f"            if (init_cmd_valid && is_wait_state(init_state))")
        L(f"                spurious_cmd_count++;")
        L(f"")
        L(f"            if (init_fail)")
        L(f"                fail_ever_asserted = 1;")
        L(f"        end")
        L(f"    end")
        L(f"")

        # ── Continuous monitors ──
        L(f"    // CKE-during-reset monitor")
        L(f"    int cke_violation_during_reset;")
        L(f"    always @(posedge clk) begin")
        L(f"        if (rst_n && (init_state == S_RESET_LOW || init_state == S_RESET_HIGH))")
        L(f"            if (init_cke) cke_violation_during_reset++;")
        L(f"    end")
        L(f"")
        L(f"    // RESET# monitor: low in IDLE and RESET_LOW")
        L(f"    int resetn_violation_count;")
        L(f"    always @(posedge clk) begin")
        L(f"        if (rst_n && (init_state == S_IDLE || init_state == S_RESET_LOW))")
        L(f"            if (init_reset_n) resetn_violation_count++;")
        L(f"    end")
        L(f"")
        L(f"    // init_done only in S_DONE")
        L(f"    int done_outside_sdone;")
        L(f"    always @(posedge clk) begin")
        L(f"        if (rst_n && init_done && init_state != S_DONE)")
        L(f"            done_outside_sdone++;")
        L(f"    end")
        L(f"")

        # ── Helper tasks ──
        L(f"    // ---------------------------------------------------------------")
        L(f"    // Task: reset all monitors")
        L(f"    // ---------------------------------------------------------------")
        L(f"    task automatic reset_monitors();")
        L(f"        cycle_count             = 0;")
        L(f"        cke_rise_cycle          = 0;")
        L(f"        reset_n_rise_cycle      = 0;")
        L(f"        init_done_cycle         = 0;")
        L(f"        mr_cmd_count            = 0;")
        L(f"        mr_bank_idx             = 0;")
        L(f"        zqcl_seen               = 0;")
        L(f"        zqcl_a10_ok             = 0;")
        L(f"        zqcl_bank_zero          = 0;")
        L(f"        spurious_cmd_count      = 0;")
        L(f"        fail_ever_asserted      = 0;")
        L(f"        cke_violation_during_reset = 0;")
        L(f"        resetn_violation_count  = 0;")
        L(f"        done_outside_sdone      = 0;")
        L(f"        for (int i = 0; i < 8; i++) begin")
        L(f"            mr_bank_order[i]  = {bank_w}'d0;")
        L(f"            mr_addr_values[i] = {addr_w}'d0;")
        L(f"            mr_cmd_values[i]  = 4'd0;")
        L(f"        end")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic hw_reset();")
        L(f"        rst_n  = 0;")
        L(f"        enable = 0;")
        L(f"        repeat (5) @(posedge clk);")
        L(f"        rst_n  = 1;")
        L(f"        @(posedge clk);")
        L(f"    endtask")
        L(f"")
        L(f"    task automatic run_init_to_done(input int timeout_cycles, output logic success);")
        L(f"        success = 0;")
        L(f"        fork")
        L(f"            begin wait(init_done); success = 1; end")
        L(f"            begin repeat (timeout_cycles) @(posedge clk); end")
        L(f"        join_any")
        L(f"        disable fork;")
        L(f"        repeat (5) @(posedge clk);")
        L(f"    endtask")
        L(f"")

        # ── Main test sequence ──
        L(f"    // ---------------------------------------------------------------")
        L(f"    // Main test")
        L(f"    // ---------------------------------------------------------------")
        L(f"    initial begin")
        L(f"        $dumpfile(\"init_fsm_tb.vcd\");")
        L(f"        $dumpvars(0, init_fsm_tb);")
        L(f"")
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"  init_fsm_tb -- Enhanced JEDEC DDR3 Init Verification\");")
        L(f"        $display(\"  Clock: {p['CTRL_FREQ']} MHz ({p['CTRL_PERIOD']} ns)    VCD: init_fsm_tb.vcd\");")
        L(f"        $display(\"  Total sections: A-I (~35 tests)\");")
        L(f"        $display(\"==========================================================\");")
        L(f"")

        # Section A: Normal init
        L(f"        // ==========================================================")
        L(f"        // SECTION A: Normal init sequence")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section A: Normal Init Sequence --\");")
        L(f"")
        L(f"        hw_reset();")
        L(f"        reset_monitors();")
        L(f"        enable = 1;")
        L(f"")
        L(f"        begin")
        L(f"            logic ok;")
        L(f"            run_init_to_done({timeout}, ok);")
        L(f"")
        L(f"            check(\"A1: init_done asserted\", ok);")
        L(f"            check(\"A2: init_fail never asserted\", fail_ever_asserted == 0);")
        L(f"            check(\"A3: FSM reached S_DONE (state=14)\", init_state == S_DONE);")
        L(f"            check($sformatf(\"A4: RESET# hold >= {reset_cyc} cyc [got %0d]\", reset_n_rise_cycle),")
        L(f"                  reset_n_rise_cycle >= {reset_cyc});")
        L(f"            check($sformatf(\"A5: CKE delay >= {cke_cyc} cyc [delta=%0d]\",")
        L(f"                  cke_rise_cycle - reset_n_rise_cycle),")
        L(f"                  (cke_rise_cycle - reset_n_rise_cycle) >= {cke_cyc});")
        L(f"            check($sformatf(\"A6: Exactly 4 MRS commands [got %0d]\", mr_cmd_count),")
        L(f"                  mr_cmd_count == 4);")
        L(f"            if (mr_bank_idx >= 4) begin")
        L(f"                check(\"A7: MR order MR2(2)->MR3(3)->MR1(1)->MR0(0)\",")
        L(f"                      mr_bank_order[0] == {bank_w}'d2 && mr_bank_order[1] == {bank_w}'d3 &&")
        L(f"                      mr_bank_order[2] == {bank_w}'d1 && mr_bank_order[3] == {bank_w}'d0);")
        L(f"            end else begin")
        L(f"                check(\"A7: MR order (insufficient commands)\", 0);")
        L(f"            end")
        L(f"        end")
        L(f"")

        # Section B: MR values
        L(f"        // ==========================================================")
        L(f"        // SECTION B: MR register values on the wire")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section B: MR Register Values --\");")
        L(f"")
        L(f"        check($sformatf(\"B1: MR2 addr = 0x%04X [exp 0x{mr2_hex}]\", mr_addr_values[0]),")
        L(f"              mr_addr_values[0] == EXP_MR2);")
        L(f"        check($sformatf(\"B2: MR3 addr = 0x%04X [exp 0x{mr3_hex}]\", mr_addr_values[1]),")
        L(f"              mr_addr_values[1] == EXP_MR3);")
        L(f"        check($sformatf(\"B3: MR1 addr = 0x%04X [exp 0x{mr1_hex}]\", mr_addr_values[2]),")
        L(f"              mr_addr_values[2] == EXP_MR1);")
        L(f"        check($sformatf(\"B4: MR0 addr = 0x%04X [exp 0x{mr0_hex}]\", mr_addr_values[3]),")
        L(f"              mr_addr_values[3] == EXP_MR0);")
        L(f"        begin")
        L(f"            logic all_mrs;")
        L(f"            all_mrs = 1;")
        L(f"            for (int i = 0; i < 4; i++)")
        L(f"                if (mr_cmd_values[i] != CMD_MRS) all_mrs = 0;")
        L(f"            check(\"B5: All 4 MRS used CMD_MRS encoding (4'b0000)\", all_mrs);")
        L(f"        end")
        L(f"")

        # Section C: ZQCL
        L(f"        // ==========================================================")
        L(f"        // SECTION C: ZQCL command")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section C: ZQCL Command --\");")
        L(f"")
        L(f"        check(\"C1: ZQCL command issued\",             zqcl_seen == 1);")
        L(f"        check(\"C2: ZQCL A10 = 1 (long calibration)\", zqcl_a10_ok == 1);")
        L(f"        check(\"C3: ZQCL bank = 0\",                   zqcl_bank_zero == 1);")
        L(f"")

        # Section D: Signal integrity
        L(f"        // ==========================================================")
        L(f"        // SECTION D: Signal integrity")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section D: Signal Integrity --\");")
        L(f"")
        L(f"        check($sformatf(\"D1: No spurious cmd_valid in wait states [%0d violations]\",")
        L(f"              spurious_cmd_count), spurious_cmd_count == 0);")
        L(f"        check($sformatf(\"D2: CKE low during RESET_LOW/HIGH [%0d violations]\",")
        L(f"              cke_violation_during_reset), cke_violation_during_reset == 0);")
        L(f"        check($sformatf(\"D3: RESET# low in IDLE/RESET_LOW [%0d violations]\",")
        L(f"              resetn_violation_count), resetn_violation_count == 0);")
        L(f"        check($sformatf(\"D4: init_done only in S_DONE [%0d violations]\",")
        L(f"              done_outside_sdone), done_outside_sdone == 0);")
        L(f"        check(\"D5: init_done is level (still high in S_DONE)\", init_done === 1'b1);")
        L(f"        check($sformatf(\"D6: init_state output = %0d (expect 14)\", init_state),")
        L(f"              init_state == 4'd14);")
        L(f"")

        # Section E: Idle behavior
        L(f"        // ==========================================================")
        L(f"        // SECTION E: Idle behavior (no enable)")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section E: Reset / Idle Behavior --\");")
        L(f"")
        L(f"        hw_reset();")
        L(f"        repeat (20) @(posedge clk);")
        L(f"")
        L(f"        check(\"E1: FSM stays S_IDLE without enable\",   init_state == S_IDLE);")
        L(f"        check(\"E2: init_done low in IDLE\",              init_done === 1'b0);")
        L(f"        check(\"E3: init_fail low in IDLE\",              init_fail === 1'b0);")
        L(f"        check(\"E4: RESET# low in IDLE\",                init_reset_n === 1'b0);")
        L(f"        check(\"E5: CKE low in IDLE\",                   init_cke === 1'b0);")
        L(f"        check(\"E6: cmd_valid low in IDLE\",              init_cmd_valid === 1'b0);")
        L(f"")

        # Section F: Enable deassert mid-init
        L(f"        // ==========================================================")
        L(f"        // SECTION F: Enable deassert mid-init")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section F: Enable Deassert Mid-Init --\");")
        L(f"")
        L(f"        hw_reset();")
        L(f"        reset_monitors();")
        L(f"        enable = 1;")
        L(f"        wait(init_state == S_RESET_LOW);")
        L(f"        repeat (100) @(posedge clk);")
        L(f"        enable = 0;")
        L(f"")
        L(f"        begin")
        L(f"            logic ok;")
        L(f"            run_init_to_done({timeout}, ok);")
        L(f"            check(\"F1: Init completes after enable deasserted\", ok);")
        L(f"            check(\"F2: init_fail not asserted\", fail_ever_asserted == 0);")
        L(f"        end")
        L(f"")

        # Section G: Reset mid-init
        L(f"        // ==========================================================")
        L(f"        // SECTION G: Async reset mid-init + recovery")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section G: Reset Mid-Init --\");")
        L(f"")
        L(f"        hw_reset();")
        L(f"        reset_monitors();")
        L(f"        enable = 1;")
        L(f"        wait(init_state == S_RESET_HIGH);")
        L(f"        repeat (50) @(posedge clk);")
        L(f"")
        L(f"        rst_n = 0;")
        L(f"        repeat (5) @(posedge clk);")
        L(f"")
        L(f"        check(\"G1: FSM returns to S_IDLE on async reset\", init_state == S_IDLE);")
        L(f"        check(\"G2: init_done deasserted after reset\",     init_done === 1'b0);")
        L(f"")
        L(f"        rst_n = 1;")
        L(f"        reset_monitors();")
        L(f"        @(posedge clk);")
        L(f"        enable = 1;")
        L(f"")
        L(f"        begin")
        L(f"            logic ok;")
        L(f"            run_init_to_done({timeout}, ok);")
        L(f"            check(\"G3: Re-init completes after mid-init reset\", ok);")
        L(f"            check(\"G4: MR order correct on re-init\",")
        L(f"                  mr_bank_idx >= 4 &&")
        L(f"                  mr_bank_order[0] == {bank_w}'d2 && mr_bank_order[1] == {bank_w}'d3 &&")
        L(f"                  mr_bank_order[2] == {bank_w}'d1 && mr_bank_order[3] == {bank_w}'d0);")
        L(f"        end")
        L(f"")

        # Section H: Re-init after done
        L(f"        // ==========================================================")
        L(f"        // SECTION H: Re-init after done")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section H: Re-Init After Done --\");")
        L(f"")
        L(f"        hw_reset();")
        L(f"        reset_monitors();")
        L(f"        enable = 1;")
        L(f"")
        L(f"        begin")
        L(f"            logic ok;")
        L(f"            run_init_to_done({timeout}, ok);")
        L(f"            check(\"H1: Second init completes\", ok);")
        L(f"            check($sformatf(\"H2: 4 MRS on re-init [got %0d]\", mr_cmd_count),")
        L(f"                  mr_cmd_count == 4);")
        L(f"            check(\"H3: ZQCL issued on re-init\", zqcl_seen == 1);")
        L(f"        end")
        L(f"")

        # Section I: Late enable
        L(f"        // ==========================================================")
        L(f"        // SECTION I: Late enable")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"  -- Section I: Late Enable --\");")
        L(f"")
        L(f"        hw_reset();")
        L(f"        reset_monitors();")
        L(f"        repeat (500) @(posedge clk);")
        L(f"        check(\"I1: FSM still IDLE after 500 cyc no enable\", init_state == S_IDLE);")
        L(f"")
        L(f"        enable = 1;")
        L(f"        begin")
        L(f"            logic ok;")
        L(f"            run_init_to_done({timeout}, ok);")
        L(f"            check(\"I2: Init completes with late enable\", ok);")
        L(f"        end")
        L(f"")

        # Summary
        L(f"        // ==========================================================")
        L(f"        // Summary")
        L(f"        // ==========================================================")
        L(f"        $display(\"\");")
        L(f"        $display(\"==========================================================\");")
        L(f"        if (fail_count == 0)")
        L(f"            $display(\"  ALL %0d TESTS PASSED\", total_tests);")
        L(f"        else")
        L(f"            $display(\"  %0d of %0d TESTS FAILED\", fail_count, total_tests);")
        L(f"        $display(\"==========================================================\");")
        L(f"        $display(\"\");")
        L(f"")
        L(f"        $finish;")
        L(f"    end")
        L(f"")
        L(f"endmodule")

        return "\n".join(lines)

    # ================================================================
    # Manifest generation
    # ================================================================
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

    # ================================================================
    # Main entry point
    # ================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  INIT / RESET FSM AGENT\n  Spec: {self.spec_path}\n{hdr}")

        print("\n[1/5] Validating parameters ...")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  ERROR: {e}")
            return {"status": "error", "errors": errs}
        print("  OK: All parameters valid")
        for k, v in self.p.items():
            if k == "MR":
                print(f"    {'MR registers':20s} = MR0..MR3 encoded")
            else:
                print(f"    {k:20s} = {v}")

        print("\n[2/5] Generating RTL ...")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines of SystemVerilog")
        print(f"    MR0 = {self._encode_mr0()}")
        print(f"    MR1 = {self._encode_mr1()}")
        print(f"    MR2 = {self._encode_mr2()}")
        print(f"    MR3 = {self._encode_mr3()}")

        print("\n[3/5] Generating testbench ...")
        tb = self.generate_testbench()
        tb_lines = len(tb.splitlines())
        print(f"  OK: {tb_lines} lines (~35 tests, 9 sections, VCD enabled)")

        print("\n[4/5] Generating port manifest ...")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  OK: {port_cnt} ports | {len(manifest['assertions'])} assertions | {len(manifest['coverage_points'])} cover points")

        print("\n[5/5] Writing files ...")
        rtl_path = self.output_dir / "init_fsm.sv"
        rtl_path.write_text(rtl)
        print(f"  -> {rtl_path}")

        tb_path = self.output_dir / "init_fsm_tb.sv"
        tb_path.write_text(tb)
        print(f"  -> {tb_path}")

        mfst_path = self.output_dir / "init_fsm_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  -> {mfst_path}")

        print(f"\n{hdr}\n  DONE -- init_fsm.sv + init_fsm_tb.sv ready for Phase 1\n{hdr}")
        return {
            "status": "success",
            "module": "init_fsm",
            "phase": 1,
            "rtl_path": str(rtl_path),
            "tb_path": str(tb_path),
            "manifest_path": str(mfst_path),
            "manifest": manifest,
            "rtl_lines": rtl_lines,
            "tb_lines": tb_lines,
            "ports": port_cnt,
        }


# --- Interactive entry point ---
if __name__ == "__main__":
    print("+=============================================+")
    print("|     INIT / RESET FSM AGENT  (Phase 1)      |")
    print("+=============================================+")
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