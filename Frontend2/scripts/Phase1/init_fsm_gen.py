#!/usr/bin/env python3
"""
INIT / RESET FSM -- RTL Generation Script (Phase 1, deterministic)

Replaces the LLM-driven Frontend/Agents/init_fsm_agent.py. That agent's own
"HARD NAMING CONTRACT" already fully specified the FSM as data before ever
calling the model: every wait-count localparam, every MR register hex value,
and the complete 11-state enum with fixed numeric encodings (down to
"S_DONE = 4'd14 is REQUIRED, do not renumber it") were handed to the LLM as
literal, non-negotiable text. There was no design decision left for a model
to make -- this script builds the FSM directly from the same derived values.

Testbench generation is NOT part of this script. In the old agent, init_fsm
generated its own testbench via a second LLM call (kept once-generated,
reused across regenerations). In this architecture, testbench generation is
its own separate, spec-only stage (see Phase1/tb_generator.py) -- it isn't
bundled into the RTL generator, LLM or otherwise.
"""

import json
import math
import os
import sys
from pathlib import Path
from typing import Optional

_HERE = os.path.dirname(os.path.abspath(__file__))
_SCRIPTS_DIR = os.path.dirname(_HERE)
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)
from manifest_stamp import stamp


class InitFsmGenerator:

    def __init__(self, spec_path: str, output_dir: str = "./output",
                 retry_instructions: Optional[dict] = None):
        # retry_instructions accepted for pipeline call-signature compatibility
        # only -- a deterministic generator has nothing to retry against.
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.init_seq = self.spec["initialization_sequence"]
        self.clocking = self.spec["clocking_model"]
        self.geometry = self.spec["memory_geometry"]

        self.p = self._derive_parameters()

    # ================================================================
    # Parameter derivation (unchanged from the original agent)
    # ================================================================
    def _derive_parameters(self) -> dict:
        p = {}
        tCK_ns = self.clocking["$derived"]["tCK_ns"]
        ctrl_period_ns = self.clocking["controller_clock_period_ns"]

        reset_us = self.init_seq["reset_hold_us"]
        cke_us = self.init_seq["cke_delay_us"]
        tXPR_ns = self.init_seq["tXPR_ns"]
        tZQ_ns = self.init_seq["tZQinit_ns"]

        p["WAIT_RESET"] = math.ceil(reset_us * 1000 / ctrl_period_ns)
        p["WAIT_CKE"] = math.ceil(cke_us * 1000 / ctrl_period_ns)
        p["WAIT_TXPR"] = math.ceil(tXPR_ns / ctrl_period_ns)
        p["WAIT_ZQCL"] = math.ceil(tZQ_ns / ctrl_period_ns)

        max_wait = max(p["WAIT_RESET"], p["WAIT_CKE"], p["WAIT_TXPR"], p["WAIT_ZQCL"])
        p["CTR_WIDTH"] = max(1, max_wait.bit_length())
        p["DDR_ADDR_W"] = max(self.geometry["row_bits"], self.geometry["column_bits"])
        p["DDR_BANK_W"] = self.geometry["bank_bits"]

        p["MR0_HEX"] = self._encode_mr0()
        p["MR1_HEX"] = self._encode_mr1()
        p["MR2_HEX"] = self._encode_mr2()
        p["MR3_HEX"] = self._encode_mr3()

        zqcl_val = (1 << 10)
        hex_width = (p["DDR_ADDR_W"] + 3) // 4
        p["ZQCL_ADDR_HEX"] = f"{zqcl_val:0{hex_width}X}"
        return p

    def _encode_mr0(self) -> str:
        mr0 = self.init_seq["mode_registers"]["MR0"]
        cl = mr0["cas_latency_cycles"]
        wr_nCK = math.ceil(mr0["write_recovery_ns"] / self.clocking["$derived"]["tCK_ns"])
        cl_map = {5: 0b0001, 6: 0b0010, 7: 0b0011, 8: 0b0100, 9: 0b0101,
                  10: 0b0110, 11: 0b0111, 13: 0b1000, 14: 0b1001}
        wr_map = {5: 0b001, 6: 0b010, 7: 0b011, 8: 0b100, 10: 0b101,
                  12: 0b110, 14: 0b111, 16: 0b000}
        cl_enc = cl_map.get(cl, 0b0111)
        wr_enc = wr_map.get(wr_nCK, 0b110)
        val = 0
        val |= (cl_enc & 1) << 2
        val |= ((cl_enc >> 1) & 0b111) << 4
        val |= 1 << 8
        val |= (wr_enc & 0b111) << 9
        val |= (1 if mr0.get("precharge_pd_mode") == "fast_exit" else 0) << 12
        return f"{val:04X}"

    def _encode_mr1(self) -> str:
        mr1 = self.init_seq["mode_registers"]["MR1"]
        val = 0
        val |= (0 if mr1.get("dll_enable", True) else 1)
        if mr1.get("output_drive_strength") == "RZQ_7":
            val |= 1 << 1
        rtt_map = {"disabled": 0, "RZQ_4": 1, "RZQ_2": 2, "RZQ_6": 3, "RZQ_12": 4, "RZQ_8": 5}
        rtt = rtt_map.get(mr1.get("rtt_nom", "RZQ_4"), 1)
        val |= (rtt & 1) << 2
        val |= ((rtt >> 1) & 1) << 6
        val |= ((rtt >> 2) & 1) << 9
        if mr1.get("write_leveling_enable", False):
            val |= 1 << 7
        return f"{val:04X}"

    def _encode_mr2(self) -> str:
        mr2 = self.init_seq["mode_registers"]["MR2"]
        cwl_enc = mr2["cas_write_latency_cycles"] - 5
        rtt_wr_map = {"disabled": 0, "RZQ_4": 1, "RZQ_2": 2}
        rtt_wr = rtt_wr_map.get(mr2.get("rtt_wr", "RZQ_4"), 1)
        val = ((cwl_enc & 0b111) << 3) | ((rtt_wr & 0b11) << 9)
        return f"{val:04X}"

    def _encode_mr3(self) -> str:
        mr3 = self.init_seq["mode_registers"]["MR3"]
        val = (1 << 2) if mr3.get("mpr_enable", False) else 0
        return f"{val:04X}"

    # ================================================================
    # RTL generation -- direct FSM construction, no LLM
    # ================================================================
    def generate_rtl(self) -> str:
        p = self.p
        aw, bw = p["DDR_ADDR_W"], p["DDR_BANK_W"]

        return f"""module init_fsm #(
    parameter int DDR_ADDR_W = {aw},
    parameter int DDR_BANK_W = {bw},
    parameter int CTR_WIDTH  = {p['CTR_WIDTH']}
) (
    input  logic                    clk,
    input  logic                    rst_n,            // active-low async reset
    input  logic                    enable,           // start init when high
    output logic                    init_done,
    output logic                    init_fail,
    output logic                    init_cmd_valid,
    output logic [3:0]              init_cmd,         // {{cs_n, ras_n, cas_n, we_n}}
    output logic [DDR_ADDR_W-1:0]   init_addr,        // MR data / row address
    output logic [DDR_BANK_W-1:0]   init_bank,        // MR select for MRS commands
    output logic                    init_cke,
    output logic                    init_reset_n,
    output logic [3:0]              init_state        // for debug
);

    localparam WAIT_RESET = {p['WAIT_RESET']};
    localparam WAIT_CKE   = {p['WAIT_CKE']};
    localparam WAIT_TXPR  = {p['WAIT_TXPR']};
    localparam WAIT_ZQCL  = {p['WAIT_ZQCL']};

    localparam [DDR_ADDR_W-1:0] MR0_VAL   = {aw}'h{p['MR0_HEX']};
    localparam [DDR_ADDR_W-1:0] MR1_VAL   = {aw}'h{p['MR1_HEX']};
    localparam [DDR_ADDR_W-1:0] MR2_VAL   = {aw}'h{p['MR2_HEX']};
    localparam [DDR_ADDR_W-1:0] MR3_VAL   = {aw}'h{p['MR3_HEX']};
    localparam [DDR_ADDR_W-1:0] ZQCL_ADDR = {aw}'h{p['ZQCL_ADDR_HEX']};  // A10=1, long calibration

    localparam logic [3:0] CMD_MRS  = 4'b0000;
    localparam logic [3:0] CMD_ZQCL = 4'b0110;  // ZQCL
    localparam logic [3:0] CMD_NOP  = 4'b0111;

    typedef enum logic [3:0] {{
        S_IDLE       = 4'd0,   // before enable; init_reset_n=0, init_cke=0
        S_RESET_LOW  = 4'd1,   // RESET# low for WAIT_RESET cycles
        S_RESET_HIGH = 4'd2,   // RESET# high, CKE low, for WAIT_CKE cycles
        S_TXPR_WAIT  = 4'd3,   // CKE high, wait WAIT_TXPR cycles
        S_MR2        = 4'd4,
        S_MR3        = 4'd5,
        S_MR1        = 4'd6,
        S_MR0        = 4'd7,
        S_ZQCL       = 4'd8,
        S_ZQCL_WAIT  = 4'd9,   // wait WAIT_ZQCL cycles
        S_DONE       = 4'd14  // init_done asserted ONLY here
    }} state_t;

    state_t state, next_state;
    logic [CTR_WIDTH-1:0] wait_cnt;

    // State register
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= S_IDLE;
        else        state <= next_state;

    // Wait counter: resets to 0 on every state change, counts cycles spent
    // in the current state (0 .. WAIT_N-1 -- WAIT_N cycles total).
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) wait_cnt <= '0;
        else if (state != next_state) wait_cnt <= '0;
        else wait_cnt <= wait_cnt + 1'b1;

    // Next-state logic
    always_comb begin
        next_state = state;
        case (state)
            S_IDLE:       next_state = enable ? S_RESET_LOW : S_IDLE;
            S_RESET_LOW:  next_state = (wait_cnt == WAIT_RESET-1) ? S_RESET_HIGH : S_RESET_LOW;
            S_RESET_HIGH: next_state = (wait_cnt == WAIT_CKE-1)   ? S_TXPR_WAIT  : S_RESET_HIGH;
            S_TXPR_WAIT:  next_state = (wait_cnt == WAIT_TXPR-1)  ? S_MR2        : S_TXPR_WAIT;
            S_MR2:        next_state = S_MR3;
            S_MR3:        next_state = S_MR1;
            S_MR1:        next_state = S_MR0;
            S_MR0:        next_state = S_ZQCL;
            S_ZQCL:       next_state = S_ZQCL_WAIT;
            S_ZQCL_WAIT:  next_state = (wait_cnt == WAIT_ZQCL-1)  ? S_DONE : S_ZQCL_WAIT;
            S_DONE:       next_state = S_DONE;
            default:      next_state = S_IDLE;
        endcase
    end

    // Combinational command outputs -- high ONLY in the 5 command states,
    // never registered (registering would bleed one cycle into the next
    // wait state).
    always_comb begin
        init_cmd_valid = 1'b0;
        init_cmd  = CMD_NOP;
        init_addr = '0;
        init_bank = '0;
        case (state)
            S_MR2:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR2_VAL;   init_bank = 2; end
            S_MR3:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR3_VAL;   init_bank = 3; end
            S_MR1:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR1_VAL;   init_bank = 1; end
            S_MR0:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR0_VAL;   init_bank = 0; end
            S_ZQCL: begin init_cmd_valid = 1'b1; init_cmd = CMD_ZQCL; init_addr = ZQCL_ADDR; init_bank = '0; end
            default: ;
        endcase
    end

    assign init_reset_n = !(state == S_IDLE || state == S_RESET_LOW);
    assign init_cke     = !(state == S_IDLE || state == S_RESET_LOW || state == S_RESET_HIGH);
    assign init_done    = (state == S_DONE);
    assign init_fail    = 1'b0;
    assign init_state   = state;

endmodule
"""

    # ================================================================
    # Manifest (unchanged shape from the original)
    # ================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            **stamp(self.spec),
            "module_name": "init_fsm",
            "file": "init_fsm.sv",
            "phase": 1,
            "generator": "init_fsm_gen",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "parameters": {
                "DDR_ADDR_W": p["DDR_ADDR_W"],
                "DDR_BANK_W": p["DDR_BANK_W"],
                "CTR_WIDTH": p["CTR_WIDTH"],
                "WAIT_RESET": p["WAIT_RESET"],
                "WAIT_CKE": p["WAIT_CKE"],
                "WAIT_TXPR": p["WAIT_TXPR"],
                "WAIT_ZQCL": p["WAIT_ZQCL"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "control": [{"name": "enable", "width": 1, "dir": "input"}],
                "status_out": [
                    {"name": "init_done", "width": 1, "dir": "output"},
                    {"name": "init_fail", "width": 1, "dir": "output"},
                ],
                "ddr_cmd_out": [
                    {"name": "init_cmd_valid", "width": 1, "dir": "output"},
                    {"name": "init_cmd", "width": 4, "dir": "output"},
                    {"name": "init_addr", "width": p["DDR_ADDR_W"], "dir": "output"},
                    {"name": "init_bank", "width": p["DDR_BANK_W"], "dir": "output"},
                ],
                "ddr_ctrl_out": [
                    {"name": "init_cke", "width": 1, "dir": "output"},
                    {"name": "init_reset_n", "width": 1, "dir": "output"},
                ],
                "debug": [{"name": "init_state", "width": 4, "dir": "output"}],
            },
            "assertions": [
                {"name": "p_cke_low_during_reset", "check": "IN-002"},
                {"name": "p_done_only_in_done", "check": "IN-005"},
                {"name": "p_zqcl_a10", "check": "IN-010"},
            ],
            "coverage_points": ["cp_state", "cp_mr_cmd", "cp_zq_cmd", "cp_done"],
        }

    # ================================================================
    # Main entry point
    # ================================================================
    def run(self) -> dict:
        rtl = self.generate_rtl()
        manifest = self.generate_manifest()

        rtl_path = self.output_dir / "init_fsm.sv"
        mfst_path = self.output_dir / "init_fsm_manifest.json"
        rtl_path.write_text(rtl)
        mfst_path.write_text(json.dumps(manifest, indent=2))

        return {
            "status": "success", "module": "init_fsm", "phase": 1,
            "rtl_path": str(rtl_path), "manifest_path": str(mfst_path),
            "manifest": manifest, "rtl_lines": len(rtl.splitlines()),
        }


if __name__ == "__main__":
    print("+=============================================+")
    print("|   INIT / RESET FSM -- RTL Gen Script        |")
    print("|   Deterministic (no LLM)                    |")
    print("+=============================================+")
    print()
    spec_path = input("Enter path to spec JSON: ").strip()
    if not spec_path or not os.path.isfile(spec_path):
        print("Error: Invalid path.")
        sys.exit(1)
    output_dir = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    result = InitFsmGenerator(spec_path, output_dir).run()
    if result["status"] == "success":
        print(f"  wrote {result['rtl_path']} ({result['rtl_lines']} lines)")
        print(f"  wrote {result['manifest_path']}")
    sys.exit(0 if result["status"] == "success" else 1)
