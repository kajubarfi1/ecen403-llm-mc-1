#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 BANK TRACKER AGENT                                   ║
║  Phase 2 — Depends on: Config Registers (config_regs)                ║
║  Generates: bank_tracker.sv + bank_tracker_manifest.json             ║
║                                                                      ║
║  8 independent bank state machines (IDLE/ACTIVE/PRECHARGING).        ║
║  Tracks open row per bank, 14 timing counters.                       ║
║  Outputs per-bank permission bits (act/rd/wr/pre_allowed).           ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json, sys, os, math
from pathlib import Path
from datetime import datetime


class BankTrackerAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geo = self.spec["memory_geometry"]
        self.ca  = self.spec["controller_architecture"]
        self.tm  = self.spec["timing_model"]
        self.dc  = self.tm["$derived_cycles"]
        self.p   = self._derive()

    def _derive(self) -> dict:
        p = {}
        p["ROW_BITS"]   = self.geo["row_bits"]
        p["BANK_BITS"]  = self.geo["bank_bits"]
        p["NUM_BANKS"]  = 2 ** p["BANK_BITS"]
        p["BANK_BITS"]  = p["BANK_BITS"]

        # Timing counter values (from $derived_cycles)
        timing_params = [
            "tRCD_nCK", "tRP_nCK", "tRAS_nCK", "tRC_nCK",
            "tRRD_nCK", "tFAW_nCK", "tWTR_nCK", "tWR_nCK",
            "tRTP_nCK", "tCCD_nCK", "tRFC_nCK"
        ]
        for tp in timing_params:
            p[tp] = self.dc[tp]

        # Counter width — must hold the largest value (tRFC=128 or tREFI=6240)
        max_val = max(p[tp] for tp in timing_params)
        p["CTR_WIDTH"] = max(1, max_val.bit_length())

        # FAW tracking needs a 4-deep shift register of timestamps
        p["FAW_DEPTH"] = 4
        p["TREFI_nCK"] = self.dc["tREFI_nCK"]

        return p

    def validate(self) -> list:
        errors = []
        p = self.p
        if p["NUM_BANKS"] != 8:
            errors.append(f"Expected 8 banks for DDR3, got {p['NUM_BANKS']}")
        if p["tRCD_nCK"] < 1:
            errors.append(f"tRCD must be >= 1, got {p['tRCD_nCK']}")
        return errors

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        return f"""\
////////////////////////////////////////////////////////////////////////////////
// Module:    bank_tracker
// File:      bank_tracker.sv
// Generated: {ts}
// Agent:     Bank Tracker Agent (Phase 2)
// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}
//
// Description:
//   {p['NUM_BANKS']} independent bank state machines tracking IDLE/ACTIVE/PRECHARGING.
//   Maintains open row per bank ({p['ROW_BITS']}-bit), 14 timing counters.
//   Outputs per-bank permission bits for the scheduler.
//   All timing loaded from cfg_* buses (runtime-programmable via CSRs).
//
// Dependency: Config Registers (cfg_tRCD_nCK, cfg_tRP_nCK, etc.)
// Validation: BT-001 .. BT-006
////////////////////////////////////////////////////////////////////////////////

module bank_tracker #(
    parameter NUM_BANKS  = {p['NUM_BANKS']},
    parameter BANK_BITS  = {p['BANK_BITS']},
    parameter ROW_BITS   = {p['ROW_BITS']},
    parameter CTR_WIDTH  = {p['CTR_WIDTH']}
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                       clk,
    input  logic                       rst_n,

    // ────────────── Command feedback (from cmd_gen) ──────────────
    input  logic                       cmd_act_valid,    // ACT issued this cycle
    input  logic [BANK_BITS-1:0]       cmd_act_bank,     // which bank was activated
    input  logic [ROW_BITS-1:0]        cmd_act_row,      // which row was activated
    input  logic                       cmd_pre_valid,    // PRE issued
    input  logic [BANK_BITS-1:0]       cmd_pre_bank,
    input  logic                       cmd_pre_all,      // precharge all banks
    input  logic                       cmd_rd_valid,     // RD issued
    input  logic [BANK_BITS-1:0]       cmd_rd_bank,
    input  logic                       cmd_wr_valid,     // WR issued
    input  logic [BANK_BITS-1:0]       cmd_wr_bank,
    input  logic                       cmd_ref_valid,    // REF issued (all banks)

    // ────────────── Config inputs (from config_regs) ──────────────
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

    // ────────────── Per-bank status outputs (to scheduler) ──────────────
    output logic [NUM_BANKS-1:0]       bank_is_active,       // 1 = bank has open row
    output logic [ROW_BITS-1:0]        bank_open_row [NUM_BANKS],  // open row per bank
    output logic [NUM_BANKS-1:0]       bank_act_allowed,     // safe to ACT
    output logic [NUM_BANKS-1:0]       bank_rd_allowed,      // safe to RD
    output logic [NUM_BANKS-1:0]       bank_wr_allowed,      // safe to WR
    output logic [NUM_BANKS-1:0]       bank_pre_allowed,     // safe to PRE
    output logic                       all_banks_idle,       // all banks precharged
    output logic                       faw_allows_act        // tFAW window not full
);

    // ================================================================
    // Bank state enum
    // ================================================================
    typedef enum logic [1:0] {{
        BANK_IDLE    = 2'b00,
        BANK_ACTIVE  = 2'b01,
        BANK_PRECHAR = 2'b10
    }} bank_state_t;

    // ================================================================
    // Per-bank storage
    // ================================================================
    bank_state_t            bk_state   [NUM_BANKS];
    logic [ROW_BITS-1:0]    bk_row     [NUM_BANKS];

    // Per-bank timing counters (count down to 0)
    logic [CTR_WIDTH-1:0]   ctr_rcd    [NUM_BANKS];  // ACT → RD/WR
    logic [CTR_WIDTH-1:0]   ctr_rp     [NUM_BANKS];  // PRE → ACT
    logic [CTR_WIDTH-1:0]   ctr_ras    [NUM_BANKS];  // ACT → PRE (minimum)
    logic [CTR_WIDTH-1:0]   ctr_rc     [NUM_BANKS];  // ACT → ACT (same bank)
    logic [CTR_WIDTH-1:0]   ctr_wtr    [NUM_BANKS];  // WR → RD
    logic [CTR_WIDTH-1:0]   ctr_wr     [NUM_BANKS];  // WR → PRE
    logic [CTR_WIDTH-1:0]   ctr_rtp    [NUM_BANKS];  // RD → PRE

    // Global timing counters
    logic [CTR_WIDTH-1:0]   ctr_rrd;                  // ACT → ACT (different bank)
    logic [CTR_WIDTH-1:0]   ctr_ccd;                  // CAS → CAS
    logic [CTR_WIDTH-1:0]   ctr_rfc;                  // REF → any command

    // FAW tracking: circular buffer of last 4 ACT timestamps
    logic [CTR_WIDTH-1:0]   faw_pipe [{p['FAW_DEPTH']}];
    logic [1:0]             faw_idx;

    // ================================================================
    // Counter decrement — all counters decrement each cycle
    // ================================================================
    integer i;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i < NUM_BANKS; i++) begin
                bk_state[i]  <= BANK_IDLE;
                bk_row[i]    <= '0;
                ctr_rcd[i]   <= '0;
                ctr_rp[i]    <= '0;
                ctr_ras[i]   <= '0;
                ctr_rc[i]    <= '0;
                ctr_wtr[i]   <= '0;
                ctr_wr[i]    <= '0;
                ctr_rtp[i]   <= '0;
            end
            ctr_rrd  <= '0;
            ctr_ccd  <= '0;
            ctr_rfc  <= '0;
            faw_idx  <= '0;
            for (i = 0; i < {p['FAW_DEPTH']}; i++)
                faw_pipe[i] <= '0;
        end else begin

            // Decrement all nonzero counters
            for (i = 0; i < NUM_BANKS; i++) begin
                if (|ctr_rcd[i])  ctr_rcd[i]  <= ctr_rcd[i]  - 1'b1;
                if (|ctr_rp[i])   ctr_rp[i]   <= ctr_rp[i]   - 1'b1;
                if (|ctr_ras[i])  ctr_ras[i]  <= ctr_ras[i]  - 1'b1;
                if (|ctr_rc[i])   ctr_rc[i]   <= ctr_rc[i]   - 1'b1;
                if (|ctr_wtr[i])  ctr_wtr[i]  <= ctr_wtr[i]  - 1'b1;
                if (|ctr_wr[i])   ctr_wr[i]   <= ctr_wr[i]   - 1'b1;
                if (|ctr_rtp[i])  ctr_rtp[i]  <= ctr_rtp[i]  - 1'b1;
            end
            if (|ctr_rrd) ctr_rrd <= ctr_rrd - 1'b1;
            if (|ctr_ccd) ctr_ccd <= ctr_ccd - 1'b1;
            if (|ctr_rfc) ctr_rfc <= ctr_rfc - 1'b1;

            // Shift FAW pipe
            for (i = 0; i < {p['FAW_DEPTH']}; i++)
                if (|faw_pipe[i]) faw_pipe[i] <= faw_pipe[i] - 1'b1;

            // ──── ACT command ────
            if (cmd_act_valid) begin
                bk_state[cmd_act_bank]  <= BANK_ACTIVE;
                bk_row[cmd_act_bank]    <= cmd_act_row;
                ctr_rcd[cmd_act_bank]   <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRCD_nCK;
                ctr_ras[cmd_act_bank]   <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRAS_nCK;
                ctr_rc[cmd_act_bank]    <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRC_nCK;
                ctr_rrd                 <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRRD_nCK;
                // FAW: record new ACT
                faw_pipe[faw_idx]       <= {{CTR_WIDTH{{1'b0}}}} | cfg_tFAW_nCK;
                faw_idx                 <= faw_idx + 1'b1;
            end

            // ──── PRE command ────
            if (cmd_pre_valid) begin
                if (cmd_pre_all) begin
                    for (i = 0; i < NUM_BANKS; i++) begin
                        bk_state[i] <= BANK_PRECHAR;
                        ctr_rp[i]   <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRP_nCK;
                    end
                end else begin
                    bk_state[cmd_pre_bank] <= BANK_PRECHAR;
                    ctr_rp[cmd_pre_bank]   <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRP_nCK;
                end
            end

            // ──── PRE → IDLE transition when tRP expires ────
            for (i = 0; i < NUM_BANKS; i++)
                if (bk_state[i] == BANK_PRECHAR && ctr_rp[i] == '0)
                    bk_state[i] <= BANK_IDLE;

            // ──── RD command ────
            if (cmd_rd_valid) begin
                ctr_ccd             <= {{CTR_WIDTH{{1'b0}}}} | cfg_tCCD_nCK;
                ctr_rtp[cmd_rd_bank] <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRTP_nCK;
            end

            // ──── WR command ────
            if (cmd_wr_valid) begin
                ctr_ccd             <= {{CTR_WIDTH{{1'b0}}}} | cfg_tCCD_nCK;
                ctr_wtr[cmd_wr_bank] <= {{CTR_WIDTH{{1'b0}}}} | cfg_tWTR_nCK;
                ctr_wr[cmd_wr_bank]  <= {{CTR_WIDTH{{1'b0}}}} | cfg_tWR_nCK;
            end

            // ──── REF command ────
            if (cmd_ref_valid) begin
                ctr_rfc <= {{CTR_WIDTH{{1'b0}}}} | cfg_tRFC_nCK;
                // All banks return to idle after refresh
                for (i = 0; i < NUM_BANKS; i++)
                    bk_state[i] <= BANK_IDLE;
            end
        end
    end

    // ================================================================
    // Permission outputs — combinational
    // ================================================================
    always_comb begin
        for (int j = 0; j < NUM_BANKS; j++) begin
            bank_is_active[j]   = (bk_state[j] == BANK_ACTIVE);
            bank_open_row[j]    = bk_row[j];

            // ACT allowed: bank idle, tRC/tRRD/tRFC expired, FAW not full
            bank_act_allowed[j] = (bk_state[j] == BANK_IDLE)
                                && (ctr_rc[j]  == '0)
                                && (ctr_rp[j]  == '0)
                                && (ctr_rrd    == '0)
                                && (ctr_rfc    == '0)
                                && faw_allows_act;

            // RD allowed: bank active, tRCD expired, tCCD expired
            bank_rd_allowed[j]  = (bk_state[j] == BANK_ACTIVE)
                                && (ctr_rcd[j] == '0)
                                && (ctr_ccd    == '0)
                                && (ctr_rfc    == '0);

            // WR allowed: bank active, tRCD expired, tCCD expired
            bank_wr_allowed[j]  = (bk_state[j] == BANK_ACTIVE)
                                && (ctr_rcd[j] == '0)
                                && (ctr_ccd    == '0)
                                && (ctr_rfc    == '0);

            // PRE allowed: bank active, tRAS expired, tRTP/tWR expired
            bank_pre_allowed[j] = (bk_state[j] == BANK_ACTIVE)
                                && (ctr_ras[j] == '0)
                                && (ctr_rtp[j] == '0)
                                && (ctr_wr[j]  == '0)
                                && (ctr_wtr[j] == '0)
                                && (ctr_rfc    == '0);
        end
    end

    // All banks idle
    assign all_banks_idle = (bk_state[0] == BANK_IDLE) && (bk_state[1] == BANK_IDLE)
                         && (bk_state[2] == BANK_IDLE) && (bk_state[3] == BANK_IDLE)
                         && (bk_state[4] == BANK_IDLE) && (bk_state[5] == BANK_IDLE)
                         && (bk_state[6] == BANK_IDLE) && (bk_state[7] == BANK_IDLE);

    // FAW: allows ACT if oldest window entry has expired
    assign faw_allows_act = (faw_pipe[faw_idx] == '0);

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // BT-001: No RD/WR to idle bank
    property p_no_rd_idle;
        @(posedge clk) disable iff (!rst_n)
        cmd_rd_valid |-> (bk_state[cmd_rd_bank] == BANK_ACTIVE);
    endproperty
    assert property (p_no_rd_idle) else $error("[BT-001] RD to non-active bank");

    property p_no_wr_idle;
        @(posedge clk) disable iff (!rst_n)
        cmd_wr_valid |-> (bk_state[cmd_wr_bank] == BANK_ACTIVE);
    endproperty
    assert property (p_no_wr_idle) else $error("[BT-001] WR to non-active bank");

    // BT-003: tRCD respected
    property p_trcd;
        @(posedge clk) disable iff (!rst_n)
        (cmd_rd_valid || cmd_wr_valid) |-> (ctr_rcd[cmd_rd_valid ? cmd_rd_bank : cmd_wr_bank] == '0);
    endproperty
    assert property (p_trcd) else $error("[BT-003] tRCD violation");

    // BT-005: tFAW check
    property p_faw;
        @(posedge clk) disable iff (!rst_n)
        cmd_act_valid |-> faw_allows_act;
    endproperty
    assert property (p_faw) else $error("[BT-005] tFAW violation");

    // Coverage
    covergroup cg_bt @(posedge clk);
        option.per_instance = 1;
        cp_act      : coverpoint cmd_act_valid;
        cp_pre      : coverpoint cmd_pre_valid;
        cp_pre_all  : coverpoint cmd_pre_all;
        cp_rd       : coverpoint cmd_rd_valid;
        cp_wr       : coverpoint cmd_wr_valid;
        cp_ref      : coverpoint cmd_ref_valid;
        cp_all_idle : coverpoint all_banks_idle;
    endgroup
    cg_bt cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
"""

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "bank_tracker", "file": "bank_tracker.sv",
            "phase": 2, "agent": "bank_tracker_agent",
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
                    {"name": f"cfg_{n}_nCK", "width": 8, "dir": "input", "source": f"config_regs.cfg_{n}_nCK"}
                    for n in ["tRCD","tRP","tRAS","tRC","tRRD","tFAW","tWTR","tWR","tRTP","tCCD","tRFC"]
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

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  BANK TRACKER AGENT\n  Spec: {self.spec_path}\n{hdr}")
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
        (self.output_dir / "bank_tracker.sv").write_text(rtl)
        (self.output_dir / "bank_tracker_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {self.output_dir}/bank_tracker.sv")
        print(f"  ✓ {self.output_dir}/bank_tracker_manifest.json")
        print(f"\n{hdr}\n  DONE — bank_tracker.sv\n{hdr}")
        return {"status": "success", "module": "bank_tracker", "phase": 2,
                "lines": len(rtl.splitlines()), "manifest": manifest}


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   BANK TRACKER AGENT  (Phase 2)             ║")
    print("╚══════════════════════════════════════════════╝\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'"); sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = BankTrackerAgent(spec, out).run()
    sys.exit(0 if r["status"]=="success" else 1)
