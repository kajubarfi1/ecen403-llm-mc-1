#!/usr/bin/env python3
"""
REFRESH CONTROLLER -- RTL Generation Script (Phase 2, deterministic)

Replaces the LLM-driven Frontend/Agents/refresh_ctrl_agent.py. That agent's
own "HARD NAMING CONTRACT" already specified four required code blocks
(REFI counter, postpone counter, output assignments, starvation detect)
labeled "copy this block verbatim" -- the LLM's job was assembling fixed
blocks around a fixed port list, same pattern as config_regs and init_fsm.
This script does the assembly directly; the four blocks below are those
verbatim blocks unchanged.
"""

import json
import os
import sys
from pathlib import Path
from typing import Optional


class RefreshCtrlGenerator:

    def __init__(self, spec_path: str, output_dir: str = "./output",
                 retry_instructions: Optional[dict] = None):
        # retry_instructions accepted for pipeline call-signature compatibility
        # only -- a deterministic generator has nothing to retry against.
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.ca = self.spec["controller_architecture"]
        self.dc = self.spec["timing_model"]["$derived_cycles"]
        self.rp = self.ca["refresh_policy"]
        self.p = self._derive()

    # ==================================================================
    # Parameter derivation (unchanged from the original agent)
    # ==================================================================
    def _derive(self) -> dict:
        p = {}
        p["tREFI_nCK"] = self.dc["tREFI_nCK"]
        p["tRFC_nCK"] = self.dc["tRFC_nCK"]
        p["MAX_POSTPONE"] = self.rp["max_postpone_count"]
        p["URGENT_THRESH"] = self.rp["urgent_threshold"]
        p["REFRESH_PRIORITY"] = self.rp["refresh_priority"]
        p["REFI_CTR_W"] = max(1, p["tREFI_nCK"].bit_length())
        p["POST_CTR_W"] = max(1, p["MAX_POSTPONE"].bit_length())
        return p

    # ==================================================================
    # Validation (unchanged)
    # ==================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["tREFI_nCK"] < 1:
            errors.append(f"tREFI must be > 0, got {p['tREFI_nCK']}")
        if p["URGENT_THRESH"] > p["MAX_POSTPONE"]:
            errors.append(f"urgent_threshold ({p['URGENT_THRESH']}) > max_postpone ({p['MAX_POSTPONE']})")
        return errors

    # ==================================================================
    # RTL generation -- direct assembly of the mandated blocks, no LLM
    # ==================================================================
    def generate_rtl(self) -> str:
        p = self.p
        return f"""// refresh_ctrl.sv -- tREFI interval counter, postpone tracking,
// urgent-threshold escalation, refresh starvation detection.
module refresh_ctrl #(
    parameter REFI_CTR_W = {p['REFI_CTR_W']},
    parameter POST_CTR_W = {p['POST_CTR_W']}
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    init_done,
    input  logic                    cfg_force_refresh,
    input  logic [23:0]             cfg_tREFI_nCK,
    input  logic [3:0]              cfg_max_postpone,
    input  logic [3:0]              cfg_urgent_threshold,
    input  logic                    cfg_ref_priority,
    output logic                    ref_required,
    output logic                    ref_urgent,
    input  logic                    ref_ack,
    output logic [2:0]              ref_pending_cnt,
    output logic                    ref_starve_flag
);

    // tREFI interval counter -- counts down from cfg_tREFI_nCK; init_done
    // gates all activity (held quiescent before init completes).
    logic [REFI_CTR_W-1:0] refi_ctr;
    logic                  refi_tick;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            refi_ctr  <= '0;
            refi_tick <= 1'b0;
        end else if (!init_done) begin
            refi_ctr  <= '0;
            refi_tick <= 1'b0;
        end else begin
            refi_tick <= 1'b0;
            if (refi_ctr == '0) begin
                refi_ctr  <= cfg_tREFI_nCK[REFI_CTR_W-1:0];
                refi_tick <= 1'b1;
            end else begin
                refi_ctr <= refi_ctr - 1'b1;
            end
        end
    end

    // Postpone counter -- running count of un-acked (owed) refreshes.
    // Saturates at cfg_max_postpone; simultaneous tick+ack cancels out.
    logic [POST_CTR_W-1:0] postpone_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            postpone_cnt <= '0;
        end else if (!init_done) begin
            postpone_cnt <= '0;
        end else begin
            case ({{(refi_tick | cfg_force_refresh), ref_ack}})
                2'b10: if (postpone_cnt < cfg_max_postpone)
                           postpone_cnt <= postpone_cnt + 1'b1;
                2'b01: if (|postpone_cnt)
                           postpone_cnt <= postpone_cnt - 1'b1;
                default: ; // 2'b00 idle, 2'b11 cancel
            endcase
        end
    end

    // ref_required/ref_urgent/ref_pending_cnt are combinational functions
    // of postpone_cnt -- urgent escalation compares against
    // cfg_urgent_threshold when the controller is in priority-preempt mode.
    assign ref_required    = (|postpone_cnt) & init_done;
    assign ref_urgent      = ref_required
                           & (postpone_cnt >= cfg_urgent_threshold)
                           & cfg_ref_priority;
    assign ref_pending_cnt = postpone_cnt[2:0];

    // Starvation detect -- registered 1-cycle pulse when a tick arrives
    // while already saturated at cfg_max_postpone.
    logic starve_detect;
    assign starve_detect = refi_tick
                         & (postpone_cnt >= cfg_max_postpone)
                         & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

endmodule
"""

    # ==================================================================
    # Manifest (unchanged from the original)
    # ==================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "refresh_ctrl", "file": "refresh_ctrl.sv",
            "phase": 2, "generator": "refresh_ctrl_gen",
            "dependencies": ["config_regs"],
            "parameters": {
                "REFI_CTR_W": p["REFI_CTR_W"], "POST_CTR_W": p["POST_CTR_W"],
                "tREFI_nCK": p["tREFI_nCK"], "tRFC_nCK": p["tRFC_nCK"],
                "MAX_POSTPONE": p["MAX_POSTPONE"], "URGENT_THRESH": p["URGENT_THRESH"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "control": [
                    {"name": "init_done", "width": 1, "dir": "input",
                     "source": "init_fsm.init_done"},
                    {"name": "cfg_force_refresh", "width": 1, "dir": "input",
                     "source": "config_regs.cfg_force_refresh"},
                ],
                "config_in": [
                    {"name": "cfg_tREFI_nCK", "width": 24, "dir": "input",
                     "source": "config_regs.cfg_tREFI_nCK"},
                    {"name": "cfg_max_postpone", "width": 4, "dir": "input",
                     "source": "config_regs.cfg_max_postpone"},
                    {"name": "cfg_urgent_threshold", "width": 4, "dir": "input",
                     "source": "config_regs.cfg_urgent_threshold"},
                    {"name": "cfg_ref_priority", "width": 1, "dir": "input",
                     "source": "config_regs.cfg_ref_priority"},
                ],
                "scheduler_if": [
                    {"name": "ref_required", "width": 1, "dir": "output"},
                    {"name": "ref_urgent", "width": 1, "dir": "output"},
                    {"name": "ref_ack", "width": 1, "dir": "input"},
                ],
                "status_out": [
                    {"name": "ref_pending_cnt", "width": 3, "dir": "output"},
                    {"name": "ref_starve_flag", "width": 1, "dir": "output"},
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

        sv_path = self.output_dir / "refresh_ctrl.sv"
        mf_path = self.output_dir / "refresh_ctrl_manifest.json"
        sv_path.write_text(rtl)
        mf_path.write_text(json.dumps(manifest, indent=2))

        return {
            "status": "success", "module": "refresh_ctrl", "phase": 2,
            "lines": len(rtl.splitlines()), "manifest": manifest,
            "rtl_path": str(sv_path), "manifest_path": str(mf_path),
        }


if __name__ == "__main__":
    print("+==============================================+")
    print("|   REFRESH CONTROLLER -- RTL Gen Script       |")
    print("|   Deterministic (no LLM)                     |")
    print("+==============================================+\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'")
        sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = RefreshCtrlGenerator(spec, out).run()
    if r["status"] == "success":
        print(f"  wrote {r['rtl_path']} ({r['lines']} lines)")
        print(f"  wrote {r['manifest_path']}")
    else:
        print(f"  ERROR: {r['errors']}")
    sys.exit(0 if r["status"] == "success" else 1)
