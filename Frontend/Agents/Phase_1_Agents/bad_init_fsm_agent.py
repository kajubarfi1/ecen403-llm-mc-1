#!/usr/bin/env python3
"""
BAD INIT FSM AGENT — for testing the validation retry loop.

Attempt 1: Wrong reset wait, wrong MR0, missing ZQCL
Attempt 2: Fixes reset wait, still wrong MR0
Attempt 3: Fixes everything → passes

Drop this in Phase_1_Agents/ and the pipeline will import it
instead of the real init_fsm_agent.
"""

import json
import os
import math
from pathlib import Path


class InitFsmAgent:

    def __init__(self, spec_path: str, output_dir: str):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        # Track attempt via a file on disk
        self.attempt_file = self.output_dir / ".init_fsm_attempt"
        if self.attempt_file.exists():
            self.attempt = int(self.attempt_file.read_text().strip()) + 1
        else:
            self.attempt = 1
        self.attempt_file.write_text(str(self.attempt))

    def run(self) -> dict:
        print(f"\n{'=' * 62}")
        print(f"  INIT FSM AGENT (BAD — attempt {self.attempt})")
        print(f"{'=' * 62}")

        cl = self.spec["clocking_model"]
        init = self.spec["initialization_sequence"]
        geo = self.spec["memory_geometry"]
        ctrl_period = cl["controller_clock_period_ns"]

        # Correct values
        correct_reset = math.ceil(init["reset_hold_us"] * 1000 / ctrl_period)  # 40000
        correct_cke = math.ceil(init["cke_delay_us"] * 1000 / ctrl_period)     # 100000
        correct_txpr = math.ceil(init["tXPR_ns"] / ctrl_period)                # 34
        correct_zqcl = math.ceil(init["tZQinit_ns"] / ctrl_period)             # 128
        ddr_addr_w = max(geo["row_bits"], geo["column_bits"])                   # 15

        # ── Inject faults based on attempt ──
        if self.attempt == 1:
            # ATTEMPT 1: Multiple failures
            wait_reset = 100          # WRONG: should be 40000
            mr0_val = "15'hFFFF"      # WRONG: should be 15'h1D34
            mr_order = "MR0 MR1 MR2 MR3"  # WRONG order
            include_zqcl = False      # MISSING
            print(f"  ⚠ INJECTING FAULTS: wrong reset, wrong MR0, wrong MR order, no ZQCL")
        elif self.attempt == 2:
            # ATTEMPT 2: Partial fix — reset fixed, MR0 still wrong
            wait_reset = correct_reset  # FIXED
            mr0_val = "15'hDEAD"        # STILL WRONG
            mr_order = "MR2 MR3 MR1 MR0"  # FIXED
            include_zqcl = True          # FIXED
            print(f"  ⚠ INJECTING FAULTS: wrong MR0 encoding (partial fix)")
        else:
            # ATTEMPT 3+: All correct
            wait_reset = correct_reset
            mr0_val = "15'h1D34"
            mr_order = "MR2 MR3 MR1 MR0"
            include_zqcl = True
            print(f"  ✓ Generating correct code (attempt {self.attempt})")

        # Generate the SV
        sv_lines = []
        L = sv_lines.append

        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"// Module: init_fsm (attempt {self.attempt})")
        L(f"////////////////////////////////////////////////////////////////////////////////")
        L(f"module init_fsm (")
        L(f"    // Clock / Reset")
        L(f"    input  logic clk,")
        L(f"    input  logic rst_n,")
        L(f"    // Outputs")
        L(f"    output logic                    init_done,")
        L(f"    output logic                    init_fail,")
        L(f"    output logic                    init_cmd_valid,")
        L(f"    output logic [3:0]              init_cmd,")
        L(f"    output logic [{ddr_addr_w-1}:0]             init_addr,")
        L(f"    output logic [2:0]              init_bank,")
        L(f"    output logic                    init_cke,")
        L(f"    output logic                    init_reset_n,")
        L(f"    output logic [3:0]              init_state")
        L(f");")
        L(f"")
        L(f"    parameter DDR_ADDR_W  = {ddr_addr_w};")
        L(f"    parameter DDR_BANK_W  = 3;")
        L(f"    parameter CTR_WIDTH   = 17;")
        L(f"")
        L(f"    localparam CMD_NOP  = 4'b0111;")
        L(f"    localparam CMD_MRS  = 4'b0000;")
        if include_zqcl:
            L(f"    localparam CMD_ZQCL = 4'b0110;")
        L(f"    localparam CMD_DESL = 4'b1111;")
        L(f"")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_RESET    = {wait_reset};  // 200µs")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_CKE      = {correct_cke};  // 500µs")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TXPR     = {correct_txpr};")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TMRD     = 1;")
        L(f"    localparam [CTR_WIDTH-1:0] WAIT_TMOD     = 3;")
        if include_zqcl:
            L(f"    localparam [CTR_WIDTH-1:0] WAIT_ZQCL     = {correct_zqcl};")
        L(f"")
        L(f"    localparam [{ddr_addr_w-1}:0] MR0_VAL = {mr0_val};")
        L(f"    localparam [{ddr_addr_w-1}:0] MR1_VAL = 15'h0004;")
        L(f"    localparam [{ddr_addr_w-1}:0] MR2_VAL = 15'h0218;")
        L(f"    localparam [{ddr_addr_w-1}:0] MR3_VAL = 15'h0000;")
        L(f"")

        # State enum — order determines V-JED-01 check
        if self.attempt == 1:
            # Wrong order
            L(f"    typedef enum logic [3:0] {{")
            L(f"        S_RESET, S_CKE, S_TXPR,")
            L(f"        S_MR0, S_MR1, S_MR2, S_MR3,")  # WRONG ORDER
            L(f"        S_DONE")
            L(f"    }} state_t;")
        else:
            # Correct JEDEC order
            L(f"    typedef enum logic [3:0] {{")
            L(f"        S_RESET, S_CKE, S_TXPR,")
            L(f"        S_MR2, S_MR3, S_MR1, S_MR0,")  # CORRECT
            if include_zqcl:
                L(f"        S_ZQCL,")
            L(f"        S_DONE")
            L(f"    }} state_t;")

        L(f"")
        L(f"    state_t state, next_state;")
        L(f"    logic [CTR_WIDTH-1:0] ctr;")
        L(f"    logic ctr_done;")
        L(f"    logic [CTR_WIDTH-1:0] ctr_load;")
        L(f"")

        # Sequential block
        L(f"    always_ff @(posedge clk or negedge rst_n) begin")
        L(f"        if (!rst_n) begin")
        L(f"            state     <= S_RESET;")
        L(f"            ctr       <= '0;")
        L(f"            init_done  = 1'b0;")
        L(f"            init_fail  = 1'b0;")
        L(f"            init_cke   = 1'b0;")
        L(f"            init_reset_n = 1'b0;")
        L(f"            init_cmd_valid = 1'b0;")
        L(f"            init_cmd   = CMD_NOP;")
        L(f"            init_addr  = '0;")
        L(f"            init_bank  = '0;")
        L(f"        end else begin")
        L(f"            if (ctr != '0)")
        L(f"                ctr <= ctr - 1;")
        L(f"            else")
        L(f"                state <= next_state;")
        L(f"        end")
        L(f"    end")
        L(f"")

        # Combinational next-state
        L(f"    always_comb begin")
        L(f"        next_state = state;")
        L(f"        ctr_load   = '0;")
        L(f"        case (state)")
        L(f"            S_RESET: begin")
        L(f"                ctr_load  = WAIT_RESET;")
        L(f"                next_state = S_CKE;")
        L(f"            end")
        L(f"            S_CKE: begin")
        L(f"                ctr_load  = WAIT_CKE;")
        L(f"                next_state = S_TXPR;")
        L(f"            end")
        L(f"            S_TXPR: begin")
        L(f"                ctr_load  = WAIT_TXPR;")

        if self.attempt == 1:
            L(f"                next_state = S_MR0;")
        else:
            L(f"                next_state = S_MR2;")

        L(f"            end")

        if self.attempt == 1:
            for mr in ["MR0", "MR1", "MR2", "MR3"]:
                next_st = {"MR0": "S_MR1", "MR1": "S_MR2", "MR2": "S_MR3", "MR3": "S_DONE"}[mr]
                L(f"            S_{mr}: begin")
                L(f"                ctr_load  = WAIT_TMRD;")
                L(f"                next_state = {next_st};")
                L(f"            end")
        else:
            for mr, next_st in [("MR2", "S_MR3"), ("MR3", "S_MR1"), ("MR1", "S_MR0"), ("MR0", "S_ZQCL" if include_zqcl else "S_DONE")]:
                L(f"            S_{mr}: begin")
                L(f"                ctr_load  = WAIT_TMRD;")
                L(f"                next_state = {next_st};")
                L(f"            end")

        if include_zqcl:
            L(f"            S_ZQCL: begin")
            L(f"                ctr_load  = WAIT_ZQCL;")
            L(f"                next_state = S_DONE;")
            L(f"            end")

        L(f"            S_DONE: begin")
        L(f"                init_done = 1'b1;")
        L(f"            end")
        L(f"            default: next_state = S_RESET;")
        L(f"        endcase")
        L(f"    end")
        L(f"")
        L(f"    assign init_state = state;")
        L(f"")
        L(f"endmodule")

        sv_text = "\n".join(sv_lines)
        sv_path = self.output_dir / "init_fsm.sv"
        sv_path.write_text(sv_text)
        print(f"  ✓ {sv_path} ({len(sv_lines)} lines)")

        # Manifest (same structure as real agent)
        manifest = {
            "module_name": "init_fsm",
            "file": "init_fsm.sv",
            "phase": 1,
            "parameters": {
                "DDR_ADDR_W": ddr_addr_w,
                "DDR_BANK_W": 3,
                "CTR_WIDTH": 17,
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "dir": "input", "width": 1},
                    {"name": "rst_n", "dir": "input", "width": 1},
                ],
                "outputs": [
                    {"name": "init_done", "dir": "output", "width": 1},
                    {"name": "init_fail", "dir": "output", "width": 1},
                    {"name": "init_cmd_valid", "dir": "output", "width": 1},
                    {"name": "init_cmd", "dir": "output", "width": 4},
                    {"name": "init_addr", "dir": "output", "width": ddr_addr_w},
                    {"name": "init_bank", "dir": "output", "width": 3},
                    {"name": "init_cke", "dir": "output", "width": 1},
                    {"name": "init_reset_n", "dir": "output", "width": 1},
                    {"name": "init_state", "dir": "output", "width": 4},
                ],
            },
            "assertions": [],
            "dependencies": [],
        }
        manifest_path = self.output_dir / "init_fsm_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2))

        return {
            "status": "success",
            "module": "init_fsm",
            "manifest": manifest,
            "rtl_path": str(sv_path),
        }
