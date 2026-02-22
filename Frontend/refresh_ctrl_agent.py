#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 REFRESH CONTROLLER AGENT                             ║
║  Phase 2 — Depends on: Config Registers (config_regs)                ║
║  Generates: refresh_ctrl.sv + refresh_ctrl_manifest.json             ║
║                                                                      ║
║  tREFI interval counter, postpone tracking (max 8),                  ║
║  urgent threshold, refresh starvation detection.                     ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json, sys, os, math
from pathlib import Path
from datetime import datetime


class RefreshCtrlAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.ca = self.spec["controller_architecture"]
        self.dc = self.spec["timing_model"]["$derived_cycles"]
        self.rp = self.ca["refresh_policy"]
        self.p  = self._derive()

    def _derive(self) -> dict:
        p = {}
        p["tREFI_nCK"]       = self.dc["tREFI_nCK"]      # 6240
        p["tRFC_nCK"]        = self.dc["tRFC_nCK"]        # 128
        p["MAX_POSTPONE"]    = self.rp["max_postpone_count"]  # 8
        p["URGENT_THRESH"]   = self.rp["urgent_threshold"]    # 6
        p["REFRESH_PRIORITY"]= self.rp["refresh_priority"]    # urgent_preempt

        # Counter widths
        p["REFI_CTR_W"] = max(1, p["tREFI_nCK"].bit_length())  # 13 bits
        p["POST_CTR_W"] = max(1, (p["MAX_POSTPONE"]).bit_length())  # 4 bits

        return p

    def validate(self) -> list:
        errors = []
        p = self.p
        if p["tREFI_nCK"] < 1:
            errors.append(f"tREFI must be > 0, got {p['tREFI_nCK']}")
        if p["URGENT_THRESH"] > p["MAX_POSTPONE"]:
            errors.append(f"urgent_threshold ({p['URGENT_THRESH']}) > max_postpone ({p['MAX_POSTPONE']})")
        return errors

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        return f"""\
////////////////////////////////////////////////////////////////////////////////
// Module:    refresh_ctrl
// File:      refresh_ctrl.sv
// Generated: {ts}
// Agent:     Refresh Controller Agent (Phase 2)
// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}
//
// Description:
//   tREFI interval counter ({p['tREFI_nCK']} nCK = {p['tREFI_nCK']*1.25/1000:.1f}µs).
//   Tracks postponed refresh count (max {p['MAX_POSTPONE']}).
//   Asserts ref_urgent when postponed >= {p['URGENT_THRESH']}.
//   Signals ref_starve when postponed > {p['MAX_POSTPONE']}.
//   Supports CSR force_refresh.
//
// Dependency: Config Registers (cfg_tREFI_nCK, cfg_max_postpone, etc.)
// Validation: RF-001 .. RF-006
////////////////////////////////////////////////////////////////////////////////

module refresh_ctrl #(
    parameter REFI_CTR_W = {p['REFI_CTR_W']},
    parameter POST_CTR_W = {p['POST_CTR_W']}
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,
    input  logic                    rst_n,

    // ────────────── Control ──────────────
    input  logic                    init_done,          // don't refresh until init complete
    input  logic                    cfg_force_refresh,  // CSR force refresh (pulse)

    // ────────────── Config inputs (from config_regs) ──────────────
    input  logic [23:0]             cfg_tREFI_nCK,
    input  logic [3:0]              cfg_max_postpone,
    input  logic [3:0]              cfg_urgent_threshold,
    input  logic                    cfg_ref_priority,   // 1 = urgent_preempt

    // ────────────── Scheduler interface ──────────────
    output logic                    ref_required,       // refresh needed (normal)
    output logic                    ref_urgent,         // urgent — preempt scheduler
    input  logic                    ref_ack,            // scheduler completed refresh

    // ────────────── Status ──────────────
    output logic [2:0]              ref_pending_cnt,    // current postpone count (to CSR)
    output logic                    ref_starve_flag     // starvation event pulse
);

    // ================================================================
    // tREFI interval counter
    // ================================================================
    logic [REFI_CTR_W-1:0] refi_ctr;
    logic                  refi_tick;  // fires every tREFI

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

    // ================================================================
    // Postpone counter
    // ================================================================
    // Increments on refi_tick (refresh due but not yet issued)
    // Decrements on ref_ack (refresh completed)
    // Force refresh acts as an additional refi_tick
    // ================================================================
    logic [POST_CTR_W-1:0] postpone_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            postpone_cnt <= '0;
        end else if (!init_done) begin
            postpone_cnt <= '0;
        end else begin
            case ({{(refi_tick | cfg_force_refresh), ref_ack}})
                2'b10: begin   // refresh due, not acked
                    if (postpone_cnt < cfg_max_postpone)
                        postpone_cnt <= postpone_cnt + 1'b1;
                end
                2'b01: begin   // acked, no new refresh due
                    if (|postpone_cnt)
                        postpone_cnt <= postpone_cnt - 1'b1;
                end
                2'b11: begin   // simultaneous — net zero
                    // no change
                end
                default: ;     // 2'b00 — idle
            endcase
        end
    end

    // ================================================================
    // Outputs
    // ================================================================

    // Refresh required when postpone count > 0
    assign ref_required   = (|postpone_cnt) & init_done;

    // Urgent when count >= threshold AND priority mode is urgent_preempt
    assign ref_urgent     = ref_required
                          & (postpone_cnt >= cfg_urgent_threshold)
                          & cfg_ref_priority;

    // Pending count for CTRL_STATUS CSR (3-bit view)
    assign ref_pending_cnt = postpone_cnt[2:0];

    // Starvation: postpone count hit max and another tick arrived
    logic starve_detect;
    assign starve_detect = refi_tick & (postpone_cnt >= cfg_max_postpone) & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // RF-001: postpone never exceeds max_postpone
    property p_no_overflow;
        @(posedge clk) disable iff (!rst_n || !init_done)
        1'b1 |-> (postpone_cnt <= cfg_max_postpone);
    endproperty
    assert property (p_no_overflow)
        else $error("[RF-001] postpone count exceeded max");

    // RF-002: ref_urgent only when count >= threshold
    property p_urgent_thresh;
        @(posedge clk) disable iff (!rst_n)
        ref_urgent |-> (postpone_cnt >= cfg_urgent_threshold);
    endproperty
    assert property (p_urgent_thresh)
        else $error("[RF-002] ref_urgent with count below threshold");

    // RF-004: no refresh before init_done
    property p_no_early_ref;
        @(posedge clk) disable iff (!rst_n)
        (!init_done) |-> (!ref_required);
    endproperty
    assert property (p_no_early_ref)
        else $error("[RF-004] refresh requested before init_done");

    // Coverage
    covergroup cg_ref @(posedge clk);
        option.per_instance = 1;
        cp_tick    : coverpoint refi_tick;
        cp_ack     : coverpoint ref_ack;
        cp_urgent  : coverpoint ref_urgent;
        cp_starve  : coverpoint ref_starve_flag;
        cp_force   : coverpoint cfg_force_refresh;
        cp_pending : coverpoint postpone_cnt {{ bins low = {{[0:3]}}; bins high = {{[4:8]}}; }}
    endgroup
    cg_ref cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
"""

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "refresh_ctrl", "file": "refresh_ctrl.sv",
            "phase": 2, "agent": "refresh_ctrl_agent",
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
                    {"name": "init_done", "width": 1, "dir": "input", "source": "init_fsm.init_done"},
                    {"name": "cfg_force_refresh", "width": 1, "dir": "input", "source": "config_regs.cfg_force_refresh"},
                ],
                "config_in": [
                    {"name": "cfg_tREFI_nCK", "width": 24, "dir": "input", "source": "config_regs.cfg_tREFI_nCK"},
                    {"name": "cfg_max_postpone", "width": 4, "dir": "input", "source": "config_regs.cfg_max_postpone"},
                    {"name": "cfg_urgent_threshold", "width": 4, "dir": "input", "source": "config_regs.cfg_urgent_threshold"},
                    {"name": "cfg_ref_priority", "width": 1, "dir": "input", "source": "config_regs.cfg_ref_priority"},
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

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  REFRESH CONTROLLER AGENT\n  Spec: {self.spec_path}\n{hdr}")
        print("\n[1/4] Validating …")
        errs = self.validate()
        if errs:
            for e in errs: print(f"  ✗ {e}")
            return {"status": "error", "errors": errs}
        print("  ✓ Valid")
        for k,v in self.p.items(): print(f"    {k:20s} = {v}")
        print("\n[2/4] Generating RTL …")
        rtl = self.generate_rtl()
        print(f"  ✓ {len(rtl.splitlines())} lines")
        print("\n[3/4] Manifest …")
        manifest = self.generate_manifest()
        print(f"  ✓ {sum(len(v) for v in manifest['ports'].values())} ports")
        print("\n[4/4] Writing …")
        (self.output_dir / "refresh_ctrl.sv").write_text(rtl)
        (self.output_dir / "refresh_ctrl_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {self.output_dir}/refresh_ctrl.sv")
        print(f"  ✓ {self.output_dir}/refresh_ctrl_manifest.json")
        print(f"\n{hdr}\n  DONE — refresh_ctrl.sv\n{hdr}")
        return {"status": "success", "module": "refresh_ctrl", "phase": 2,
                "lines": len(rtl.splitlines()), "manifest": manifest}


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   REFRESH CONTROLLER AGENT  (Phase 2)       ║")
    print("╚══════════════════════════════════════════════╝\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'"); sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = RefreshCtrlAgent(spec, out).run()
    sys.exit(0 if r["status"]=="success" else 1)
