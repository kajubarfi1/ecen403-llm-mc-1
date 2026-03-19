#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 CALIBRATION AGENT                                    ║
║  Phase 2 — Depends on: Init/Reset FSM (init_fsm)                    ║
║  Generates: calibration.sv + calibration_manifest.json               ║
║                                                                      ║
║  Minimal calibration block for abstract PHY boundary.                ║
║  Waits for init_done, asserts cal_done one cycle later.              ║
║  Issues periodic ZQCS every 512,000 nCK.                            ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json, sys, os, math
from pathlib import Path
from datetime import datetime


class CalibrationAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.cal     = self.spec["calibration"]
        self.clocking= self.spec["clocking_model"]
        self.p       = self._derive()

    def _derive(self) -> dict:
        p = {}
        p["PERIODIC_ZQCS"]    = self.cal["periodic_recalibration_enable"]
        zqcs_nCK = self.cal.get("$derived", {}).get("periodic_zqcs_interval_nCK", 512000)
        p["ZQCS_INTERVAL"]    = zqcs_nCK

        ctrl_period = self.clocking["controller_clock_period_ns"]
        tCK = self.clocking["$derived"]["tCK_ns"]
        # Convert nCK to controller cycles
        p["ZQCS_CTRL_CYC"]   = math.ceil(zqcs_nCK * tCK / ctrl_period)
        p["ZQCS_CTR_W"]      = max(1, p["ZQCS_CTRL_CYC"].bit_length())

        # tZQCS = 64 nCK per JEDEC
        tZQCS_nCK = 64
        p["tZQCS_CYC"]       = math.ceil(tZQCS_nCK * tCK / ctrl_period)

        p["WL_ENABLE"]       = self.cal["enable_write_leveling"]
        p["RL_ENABLE"]       = self.cal["enable_read_leveling"]

        return p

    def validate(self) -> list:
        errors = []
        if self.p["ZQCS_INTERVAL"] < 1:
            errors.append("ZQCS interval must be > 0")
        return errors

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        return f"""\
////////////////////////////////////////////////////////////////////////////////
// Module:    calibration
// File:      calibration.sv
// Generated: {ts}
// Agent:     Calibration Agent (Phase 2)
// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}
//
// Description:
//   Minimal calibration block for abstract PHY boundary.
//   - Waits for init_done from init_fsm
//   - Asserts cal_done one cycle after init_done (no actual leveling)
//   - Issues periodic ZQCS request every {p['ZQCS_INTERVAL']} nCK
//     ({p['ZQCS_CTRL_CYC']} controller cycles)
//   - Write/read leveling disabled (PHY not modeled)
//
// Dependency: Init/Reset FSM (init_done)
// Validation: CL-001 .. CL-003
////////////////////////////////////////////////////////////////////////////////

module calibration #(
    parameter ZQCS_CTR_W = {p['ZQCS_CTR_W']},
    parameter ZQCS_WAIT  = {p['ZQCS_CTRL_CYC']},
    parameter TZQCS_CYC  = {p['tZQCS_CYC']}
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,
    input  logic                    rst_n,

    // ────────────── From init_fsm ──────────────
    input  logic                    init_done,

    // ────────────── Status outputs ──────────────
    output logic                    cal_done,       // calibration complete
    output logic                    cal_fail,       // always 0 (abstract PHY)

    // ────────────── ZQCS request (to cmd_gen / scheduler) ──────────────
    output logic                    zqcs_req,       // request periodic ZQCS
    input  logic                    zqcs_ack        // scheduler completed ZQCS
);

    // ================================================================
    // cal_done — one cycle after init_done
    // ================================================================
    logic init_done_d;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) init_done_d <= 1'b0;
        else        init_done_d <= init_done;

    // cal_done latches high once init completes
    logic cal_done_r;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)                          cal_done_r <= 1'b0;
        else if (init_done && !init_done_d)  cal_done_r <= 1'b1;  // rising edge of init_done

    assign cal_done = cal_done_r;
    assign cal_fail = 1'b0;  // abstract PHY — calibration never fails

    // ================================================================
    // Periodic ZQCS counter
    // ================================================================
    logic [ZQCS_CTR_W-1:0] zqcs_ctr;
    logic                  zqcs_pending;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            zqcs_ctr     <= '0;
            zqcs_pending <= 1'b0;
        end else if (!cal_done_r) begin
            zqcs_ctr     <= '0;
            zqcs_pending <= 1'b0;
        end else begin
            // Count down
            if (zqcs_ctr == '0) begin
                zqcs_ctr     <= ZQCS_WAIT[ZQCS_CTR_W-1:0];
                zqcs_pending <= 1'b1;
            end else begin
                zqcs_ctr <= zqcs_ctr - 1'b1;
            end

            // Clear pending on ack
            if (zqcs_ack)
                zqcs_pending <= 1'b0;
        end
    end

    assign zqcs_req = zqcs_pending & cal_done_r;

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // CL-001: cal_done only after init_done
    property p_cal_after_init;
        @(posedge clk) disable iff (!rst_n)
        cal_done |-> init_done;
    endproperty
    assert property (p_cal_after_init)
        else $error("[CL-001] cal_done before init_done");

    // CL-002: cal_fail always 0 (abstract PHY)
    property p_no_fail;
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (!cal_fail);
    endproperty
    assert property (p_no_fail)
        else $error("[CL-002] cal_fail asserted in abstract PHY mode");

    // CL-003: ZQCS only after cal_done
    property p_zqcs_after_cal;
        @(posedge clk) disable iff (!rst_n)
        zqcs_req |-> cal_done;
    endproperty
    assert property (p_zqcs_after_cal)
        else $error("[CL-003] ZQCS requested before cal_done");

    // Coverage
    covergroup cg_cal @(posedge clk);
        option.per_instance = 1;
        cp_cal_done  : coverpoint cal_done;
        cp_zqcs_req  : coverpoint zqcs_req;
        cp_zqcs_ack  : coverpoint zqcs_ack;
    endgroup
    cg_cal cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
"""

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "calibration", "file": "calibration.sv",
            "phase": 2, "agent": "calibration_agent",
            "dependencies": ["init_fsm"],
            "parameters": {
                "ZQCS_CTR_W": p["ZQCS_CTR_W"],
                "ZQCS_CTRL_CYC": p["ZQCS_CTRL_CYC"],
                "tZQCS_CYC": p["tZQCS_CYC"],
                "PERIODIC_ZQCS": p["PERIODIC_ZQCS"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "control": [
                    {"name": "init_done", "width": 1, "dir": "input", "source": "init_fsm.init_done"},
                ],
                "status_out": [
                    {"name": "cal_done", "width": 1, "dir": "output"},
                    {"name": "cal_fail", "width": 1, "dir": "output"},
                ],
                "zqcs_if": [
                    {"name": "zqcs_req", "width": 1, "dir": "output"},
                    {"name": "zqcs_ack", "width": 1, "dir": "input"},
                ],
            },
        }

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  CALIBRATION AGENT\n  Spec: {self.spec_path}\n{hdr}")
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
        (self.output_dir / "calibration.sv").write_text(rtl)
        (self.output_dir / "calibration_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {self.output_dir}/calibration.sv")
        print(f"  ✓ {self.output_dir}/calibration_manifest.json")
        print(f"\n{hdr}\n  DONE — calibration.sv\n{hdr}")
        return {"status": "success", "module": "calibration", "phase": 2,
                "lines": len(rtl.splitlines()), "manifest": manifest}


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   CALIBRATION AGENT  (Phase 2)              ║")
    print("╚══════════════════════════════════════════════╝\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'"); sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = CalibrationAgent(spec, out).run()
    sys.exit(0 if r["status"]=="success" else 1)
