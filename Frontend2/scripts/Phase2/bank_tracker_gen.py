#!/usr/bin/env python3
"""
BANK TRACKER -- RTL Generation Script (Phase 2, deterministic)

Replaces the LLM-driven Frontend/Agents/bank_tracker_agent.py. The most
structurally complex Phase 2 block (8 per-bank state machines, shared
timing counters, a tFAW window), but its own "HARD NAMING CONTRACT" plus
"BEHAVIORAL REQUIREMENTS" sections already pinned down exact reset values,
exact per-command register updates, and exact combinational permission
formulas -- the "you choose the implementation" language only mattered
because an LLM needed room to phrase a state machine; a script just needs
one correct implementation of the same spec. This is that implementation.
"""

import json
import os
import sys
from pathlib import Path
from typing import Optional


class BankTrackerGenerator:

    def __init__(self, spec_path: str, output_dir: str = "./output",
                 retry_instructions: Optional[dict] = None):
        # retry_instructions accepted for pipeline call-signature compatibility
        # only -- a deterministic generator has nothing to retry against.
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geo = self.spec["memory_geometry"]
        self.ca = self.spec["controller_architecture"]
        self.tm = self.spec["timing_model"]
        self.dc = self.tm["$derived_cycles"]
        self.p = self._derive()

    # ==================================================================
    # Parameter derivation (unchanged from the original agent)
    # ==================================================================
    def _derive(self) -> dict:
        p = {}
        p["ROW_BITS"] = self.geo["row_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["NUM_BANKS"] = 2 ** p["BANK_BITS"]

        timing_params = [
            "tRCD_nCK", "tRP_nCK", "tRAS_nCK", "tRC_nCK",
            "tRRD_nCK", "tFAW_nCK", "tWTR_nCK", "tWR_nCK",
            "tRTP_nCK", "tCCD_nCK", "tRFC_nCK",
        ]
        for tp in timing_params:
            p[tp] = self.dc[tp]

        max_val = max(p[tp] for tp in timing_params)
        p["CTR_WIDTH"] = max(1, max_val.bit_length())

        p["FAW_DEPTH"] = 4
        p["TREFI_nCK"] = self.dc["tREFI_nCK"]
        return p

    # ==================================================================
    # Validation (unchanged)
    # ==================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["NUM_BANKS"] != 8:
            errors.append(f"Expected 8 banks for DDR3, got {p['NUM_BANKS']}")
        if p["tRCD_nCK"] < 1:
            errors.append(f"tRCD must be >= 1, got {p['tRCD_nCK']}")
        return errors

    # ==================================================================
    # RTL generation -- direct construction of the one implementation
    # that satisfies the contract's behavioral requirements. No LLM.
    # ==================================================================
    def generate_rtl(self) -> str:
        p = self.p
        nb, bb, rb, cw = p["NUM_BANKS"], p["BANK_BITS"], p["ROW_BITS"], p["CTR_WIDTH"]

        return f"""// bank_tracker.sv -- 8 independent per-bank state machines, DDR3 bank
// timing constraints (tRCD/tRP/tRAS/tRC/tWTR/tWR/tRTP per bank; tRRD/tCCD/
// tRFC shared), tFAW 4-ACT rolling window, combinational permission vectors.
module bank_tracker #(
    parameter NUM_BANKS  = {nb},
    parameter BANK_BITS  = {bb},
    parameter ROW_BITS   = {rb},
    parameter CTR_WIDTH  = {cw}
) (
    input  logic                       clk,
    input  logic                       rst_n,

    input  logic                       cmd_act_valid,
    input  logic [BANK_BITS-1:0]       cmd_act_bank,
    input  logic [ROW_BITS-1:0]        cmd_act_row,
    input  logic                       cmd_pre_valid,
    input  logic [BANK_BITS-1:0]       cmd_pre_bank,
    input  logic                       cmd_pre_all,
    input  logic                       cmd_rd_valid,
    input  logic [BANK_BITS-1:0]       cmd_rd_bank,
    input  logic                       cmd_wr_valid,
    input  logic [BANK_BITS-1:0]       cmd_wr_bank,
    input  logic                       cmd_ref_valid,

    input  logic [7:0]                 cfg_tRCD_nCK,
    input  logic [7:0]                 cfg_tRP_nCK,
    input  logic [7:0]                 cfg_tRAS_nCK,
    input  logic [7:0]                 cfg_tRC_nCK,
    input  logic [7:0]                 cfg_tRRD_nCK,
    input  logic [7:0]                 cfg_tFAW_nCK,
    input  logic [7:0]                 cfg_tWTR_nCK,
    input  logic [7:0]                 cfg_tWR_nCK,
    input  logic [7:0]                 cfg_tRTP_nCK,
    input  logic [7:0]                 cfg_tCCD_nCK,
    input  logic [7:0]                 cfg_tRFC_nCK,

    output logic [NUM_BANKS-1:0]       bank_is_active,
    output logic [ROW_BITS-1:0]        bank_open_row [NUM_BANKS],
    output logic [NUM_BANKS-1:0]       bank_act_allowed,
    output logic [NUM_BANKS-1:0]       bank_rd_allowed,
    output logic [NUM_BANKS-1:0]       bank_wr_allowed,
    output logic [NUM_BANKS-1:0]       bank_pre_allowed,
    output logic                       all_banks_idle,
    output logic                       faw_allows_act
);

    typedef enum logic [1:0] {{
        BANK_IDLE   = 2'd0,
        BANK_ACTIVE = 2'd1
    }} bank_state_t;

    bank_state_t          bk_state [NUM_BANKS];
    logic [ROW_BITS-1:0]  bk_row   [NUM_BANKS];

    // Per-bank timing counters (required names -- validator checks these).
    logic [CTR_WIDTH-1:0] ctr_rcd [NUM_BANKS];
    logic [CTR_WIDTH-1:0] ctr_rp  [NUM_BANKS];
    logic [CTR_WIDTH-1:0] ctr_ras [NUM_BANKS];
    logic [CTR_WIDTH-1:0] ctr_rc  [NUM_BANKS];
    logic [CTR_WIDTH-1:0] ctr_wtr [NUM_BANKS];
    logic [CTR_WIDTH-1:0] ctr_wr  [NUM_BANKS];
    logic [CTR_WIDTH-1:0] ctr_rtp [NUM_BANKS];

    // Global timing counters (shared across banks -- required names).
    logic [CTR_WIDTH-1:0] ctr_rrd;
    logic [CTR_WIDTH-1:0] ctr_ccd;
    logic [CTR_WIDTH-1:0] ctr_rfc;

    // Per-bank state/row/counter updates. Command priority per bank:
    // REF (forces every bank idle) > ACT > PRE. Each counter loads on its
    // triggering command, else decrements while non-zero; a load always
    // overrides that cycle's decrement.
    genvar gi;
    generate
        for (gi = 0; gi < NUM_BANKS; gi++) begin : g_bank
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    bk_state[gi] <= BANK_IDLE;
                    bk_row[gi]   <= '0;
                    ctr_rcd[gi]  <= '0;
                    ctr_rp[gi]   <= '0;
                    ctr_ras[gi]  <= '0;
                    ctr_rc[gi]   <= '0;
                    ctr_wtr[gi]  <= '0;
                    ctr_wr[gi]   <= '0;
                    ctr_rtp[gi]  <= '0;
                end else begin
                    // State + open row
                    if (cmd_ref_valid)
                        bk_state[gi] <= BANK_IDLE;
                    else if (cmd_act_valid && cmd_act_bank == gi[BANK_BITS-1:0])
                        bk_state[gi] <= BANK_ACTIVE;
                    else if (cmd_pre_valid && (cmd_pre_all || cmd_pre_bank == gi[BANK_BITS-1:0]))
                        bk_state[gi] <= BANK_IDLE;

                    if (cmd_act_valid && cmd_act_bank == gi[BANK_BITS-1:0])
                        bk_row[gi] <= cmd_act_row;

                    // tRCD / tRAS / tRC load on ACT to this bank
                    if (cmd_act_valid && cmd_act_bank == gi[BANK_BITS-1:0])
                        ctr_rcd[gi] <= cfg_tRCD_nCK[CTR_WIDTH-1:0];
                    else if (ctr_rcd[gi] != 0)
                        ctr_rcd[gi] <= ctr_rcd[gi] - 1'b1;

                    if (cmd_act_valid && cmd_act_bank == gi[BANK_BITS-1:0])
                        ctr_ras[gi] <= cfg_tRAS_nCK[CTR_WIDTH-1:0];
                    else if (ctr_ras[gi] != 0)
                        ctr_ras[gi] <= ctr_ras[gi] - 1'b1;

                    if (cmd_act_valid && cmd_act_bank == gi[BANK_BITS-1:0])
                        ctr_rc[gi] <= cfg_tRC_nCK[CTR_WIDTH-1:0];
                    else if (ctr_rc[gi] != 0)
                        ctr_rc[gi] <= ctr_rc[gi] - 1'b1;

                    // tRP loads on PRE to this bank (or PRE-all)
                    if (cmd_pre_valid && (cmd_pre_all || cmd_pre_bank == gi[BANK_BITS-1:0]))
                        ctr_rp[gi] <= cfg_tRP_nCK[CTR_WIDTH-1:0];
                    else if (ctr_rp[gi] != 0)
                        ctr_rp[gi] <= ctr_rp[gi] - 1'b1;

                    // tWTR / tWR load on WR to this bank
                    if (cmd_wr_valid && cmd_wr_bank == gi[BANK_BITS-1:0])
                        ctr_wtr[gi] <= cfg_tWTR_nCK[CTR_WIDTH-1:0];
                    else if (ctr_wtr[gi] != 0)
                        ctr_wtr[gi] <= ctr_wtr[gi] - 1'b1;

                    if (cmd_wr_valid && cmd_wr_bank == gi[BANK_BITS-1:0])
                        ctr_wr[gi] <= cfg_tWR_nCK[CTR_WIDTH-1:0];
                    else if (ctr_wr[gi] != 0)
                        ctr_wr[gi] <= ctr_wr[gi] - 1'b1;

                    // tRTP loads on RD to this bank
                    if (cmd_rd_valid && cmd_rd_bank == gi[BANK_BITS-1:0])
                        ctr_rtp[gi] <= cfg_tRTP_nCK[CTR_WIDTH-1:0];
                    else if (ctr_rtp[gi] != 0)
                        ctr_rtp[gi] <= ctr_rtp[gi] - 1'b1;
                end
            end
        end
    endgenerate

    // Global counters: tRRD on any ACT, tCCD on any RD or WR, tRFC on REF.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctr_rrd <= '0;
            ctr_ccd <= '0;
            ctr_rfc <= '0;
        end else begin
            if (cmd_act_valid)
                ctr_rrd <= cfg_tRRD_nCK[CTR_WIDTH-1:0];
            else if (ctr_rrd != 0)
                ctr_rrd <= ctr_rrd - 1'b1;

            if (cmd_rd_valid || cmd_wr_valid)
                ctr_ccd <= cfg_tCCD_nCK[CTR_WIDTH-1:0];
            else if (ctr_ccd != 0)
                ctr_ccd <= ctr_ccd - 1'b1;

            if (cmd_ref_valid)
                ctr_rfc <= cfg_tRFC_nCK[CTR_WIDTH-1:0];
            else if (ctr_rfc != 0)
                ctr_rfc <= ctr_rfc - 1'b1;
        end
    end

    // tFAW: 4-slot rolling window. Every cycle each non-zero slot
    // decrements; on ACT the next slot (round-robin) is loaded with
    // cfg_tFAW_nCK -- written after the decrement loop so the load wins
    // on the cycle it lands. faw_allows_act is high iff at least one slot
    // is currently at 0 (fewer than 4 ACTs pending in the window).
    localparam int FAW_DEPTH = {p['FAW_DEPTH']};
    logic [CTR_WIDTH-1:0] faw_pipe [FAW_DEPTH];
    logic [1:0]           faw_wptr;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int k = 0; k < FAW_DEPTH; k++) faw_pipe[k] <= '0;
            faw_wptr <= '0;
        end else begin
            for (int k = 0; k < FAW_DEPTH; k++)
                if (faw_pipe[k] != 0) faw_pipe[k] <= faw_pipe[k] - 1'b1;
            if (cmd_act_valid) begin
                faw_pipe[faw_wptr] <= cfg_tFAW_nCK[CTR_WIDTH-1:0];
                faw_wptr <= faw_wptr + 1'b1;
            end
        end
    end

    assign faw_allows_act = (faw_pipe[0] == 0) || (faw_pipe[1] == 0)
                          || (faw_pipe[2] == 0) || (faw_pipe[3] == 0);

    // Combinational permission vectors -- per-bank formulas from the spec,
    // driven with blocking assignment inside always_comb (never NBA).
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            bank_is_active[b]   = (bk_state[b] == BANK_ACTIVE);
            bank_open_row[b]    = bk_row[b];
            bank_act_allowed[b] = (bk_state[b] == BANK_IDLE)
                                && (ctr_rc[b]  == 0)
                                && (ctr_rp[b]  == 0)
                                && (ctr_rrd    == 0)
                                && (ctr_rfc    == 0)
                                && faw_allows_act;
            bank_rd_allowed[b]  = (bk_state[b] == BANK_ACTIVE)
                                && (ctr_rcd[b] == 0)
                                && (ctr_ccd    == 0)
                                && (ctr_rfc    == 0);
            bank_wr_allowed[b]  = (bk_state[b] == BANK_ACTIVE)
                                && (ctr_rcd[b] == 0)
                                && (ctr_ccd    == 0)
                                && (ctr_rfc    == 0);
            bank_pre_allowed[b] = (bk_state[b] == BANK_ACTIVE)
                                && (ctr_ras[b] == 0)
                                && (ctr_rtp[b] == 0)
                                && (ctr_wr[b]  == 0)
                                && (ctr_wtr[b] == 0)
                                && (ctr_rfc    == 0);
        end
    end

    assign all_banks_idle = ~(|bank_is_active);

endmodule
"""

    # ==================================================================
    # Manifest (unchanged from the original)
    # ==================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "bank_tracker", "file": "bank_tracker.sv",
            "phase": 2, "generator": "bank_tracker_gen",
            "dependencies": ["config_regs"],
            "parameters": {
                "NUM_BANKS": p["NUM_BANKS"], "BANK_BITS": p["BANK_BITS"],
                "ROW_BITS": p["ROW_BITS"], "CTR_WIDTH": p["CTR_WIDTH"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "cmd_feedback": [
                    {"name": "cmd_act_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_act_bank", "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_act_row", "width": p["ROW_BITS"], "dir": "input"},
                    {"name": "cmd_pre_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_pre_bank", "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_pre_all", "width": 1, "dir": "input"},
                    {"name": "cmd_rd_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_rd_bank", "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_wr_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_wr_bank", "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_ref_valid", "width": 1, "dir": "input"},
                ],
                "config_in": [
                    {"name": f"cfg_{n}_nCK", "width": 8, "dir": "input",
                     "source": f"config_regs.cfg_{n}_nCK"}
                    for n in ["tRCD", "tRP", "tRAS", "tRC", "tRRD", "tFAW",
                              "tWTR", "tWR", "tRTP", "tCCD", "tRFC"]
                ],
                "status_out": [
                    {"name": "bank_is_active", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_open_row", "width": f"{p['NUM_BANKS']}x{p['ROW_BITS']}", "dir": "output"},
                    {"name": "bank_act_allowed", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_rd_allowed", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_wr_allowed", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_pre_allowed", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "all_banks_idle", "width": 1, "dir": "output"},
                    {"name": "faw_allows_act", "width": 1, "dir": "output"},
                ],
            },
        }

    # ==================================================================
    # Main entry point
    # ==================================================================
    def run(self) -> dict:
        errs = self.validate()
        if errs:
            return {"status": "error", "errors": errs}

        rtl = self.generate_rtl()
        manifest = self.generate_manifest()

        sv_path = self.output_dir / "bank_tracker.sv"
        mf_path = self.output_dir / "bank_tracker_manifest.json"
        sv_path.write_text(rtl)
        mf_path.write_text(json.dumps(manifest, indent=2))

        return {
            "status": "success", "module": "bank_tracker", "phase": 2,
            "lines": len(rtl.splitlines()), "manifest": manifest,
            "rtl_path": str(sv_path), "manifest_path": str(mf_path),
        }


if __name__ == "__main__":
    print("+==============================================+")
    print("|   BANK TRACKER -- RTL Gen Script             |")
    print("|   Deterministic (no LLM)                     |")
    print("+==============================================+\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'")
        sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = BankTrackerGenerator(spec, out).run()
    if r["status"] == "success":
        print(f"  wrote {r['rtl_path']} ({r['lines']} lines)")
        print(f"  wrote {r['manifest_path']}")
    else:
        print(f"  ERROR: {r['errors']}")
    sys.exit(0 if r["status"] == "success" else 1)
