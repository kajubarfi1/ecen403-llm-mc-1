#!/usr/bin/env python3
"""A fake flow.py run for the GUI: writes RUN_STATE.json, flow.log and ORFS
step logs in the shapes the real ones have, on a compressed timeline. Used by
`flow_gui.py --demo` and the GUI tests; touches nothing outside its temp dir.

  python3 gui/demo_run.py --minutes 2 --out /tmp/demo     (standalone)
"""

import argparse
import json
import os
import random
import tempfile
import time
from datetime import datetime, timezone

DESIGN = "ddr3_controller"
PLATFORM = "sky130hd"

# (file, share of the ORFS pass)
ORFS_FILES = [
    ("1_1_yosys_canonicalize", 0.5), ("1_2_yosys", 6.5),
    ("2_1_floorplan", 1.5), ("2_2_floorplan_macro", 0.3), ("2_3_floorplan_tapcell", 0.3),
    ("2_4_floorplan_pdn", 1.9),
    ("3_1_place_gp_skip_io", 1.5), ("3_2_place_iop", 0.5), ("3_3_place_gp", 10.0),
    ("3_4_place_resized", 2.0), ("3_5_place_dp", 2.0),
    ("4_1_cts", 8.0), ("5_1_grt", 7.0), ("5_2_route", 34.0), ("5_3_fillcell", 2.0),
    ("6_1_merge", 4.0), ("6_report", 2.0),
]


def _now():
    return datetime.now(timezone.utc).isoformat()


class Demo:
    def __init__(self, minutes=4.0, root=None, fail_backend=False):
        self.root = root or tempfile.mkdtemp(prefix="flow_gui_demo_")
        self.runs_root = os.path.join(self.root, "runs")
        self.run_dir = os.path.join(self.runs_root, datetime.now().strftime("%Y%m%d-%H%M%S") + "-demo")
        self.orfs_dir = os.path.join(self.root, "orfs")
        self.logs = os.path.join(self.orfs_dir, "flow", "logs", PLATFORM, DESIGN, "base")
        self.reports = os.path.join(self.orfs_dir, "flow", "reports", PLATFORM, DESIGN, "base")
        self.total = minutes * 60.0
        self.fail_backend = fail_backend
        self.rng = random.Random(7)
        os.makedirs(self.run_dir, exist_ok=True)
        os.makedirs(self.logs, exist_ok=True)
        os.makedirs(self.reports, exist_ok=True)
        self.state = {"$schema": "llmmc-flow-run/1", "run_id": os.path.basename(self.run_dir),
                      "created_utc": _now(), "request": {"demo": True}, "stages": [],
                      "rounds": {"spec": 0, "rtl": 0, "backend": 0}, "status": "running",
                      "halt": None}
        self._save()

    # -- writing ------------------------------------------------------------
    def _save(self):
        self.state["updated_utc"] = _now()
        tmp = os.path.join(self.run_dir, "RUN_STATE.json.tmp")
        with open(tmp, "w") as f:
            json.dump(self.state, f, indent=2)
        os.replace(tmp, os.path.join(self.run_dir, "RUN_STATE.json"))

    def log(self, msg, indent=False):
        line = f"[{datetime.now().strftime('%H:%M:%S')}] " + ("    " if indent else "") + msg
        with open(os.path.join(self.run_dir, "flow.log"), "a") as f:
            f.write(line + "\n")

    def record(self, stage, status, detail=""):
        self.state["stages"].append({"stage": stage, "status": status, "detail": detail, "utc": _now()})
        self._save()
        self.log(f"{stage:22} {status:8} {detail}")

    def wait(self, share):
        """Sleep `share` percent of the whole demo."""
        time.sleep(max(0.0, self.total * share / 100.0))

    # -- the run ----------------------------------------------------------
    def run(self):
        L = self.log
        L("$ Frontend2/scripts/Microarch/microarch_cli.py --request 'DDR3-1600 x8, 2 lanes'")
        L("[microarch] compiling spec ...", True)
        self.wait(3)
        self.record("spec_synthesis", "PASS", "generated: spec/generated_spec.json")
        L("$ Validation/spec/validate_spec_stage.py --spec spec/generated_spec.json")
        self.wait(2)
        self.record("spec_review", "PASS", "0 open gap(s)")
        mods = {1: ["init_fsm", "config_regs", "wb_port"],
                2: ["addr_decoder", "bank_tracker", "refresh_ctrl", "calibration"],
                3: ["cmd_queue", "scheduler", "cmd_gen"],
                4: ["data_path"]}
        for n in range(1, 5):
            L(f"-- phase {n}: {', '.join(mods[n])}")
            L(f"$ Frontend2/scripts/Phase{n}/phase{n}_pipeline.py --spec spec/generated_spec.json")
            L("    ==============================================================", True)
            L("      GENERATION CHECK", True)
            L("    ==============================================================", True)
            for m in mods[n]:
                L(f"      OK   {m:15} success", True)
                self.wait(0.3)
            if n == 4:
                # one module fails its own sim gate, Frontend fixes it itself
                L("    ==============================================================", True)
                L("      PHASE 4 PIPELINE FAILED AT SIM GATE", True)
                L("    ==============================================================", True)
                L("        FAIL data_path -- see data_path_xrun.log", True)
                self.record("rtl_generation", "FAIL", "phase 4 failed at BEHAVIORAL_SIMULATION (data_path)")
                L("Failing module(s): data_path")
                L("##############################################################")
                L("#  data_path: fix attempt 1/3")
                L("##############################################################")
                L("  asking Claude to diagnose + propose a fix...", True)
                self.wait(1.5)
                L("  ROOT CAUSE (high confidence):", True)
                L("    a single-driver violation in the write-buffer valid bit.", True)
                L("  data_path: FIXED -- lint PASS, sim PASS on re-verification.", True)
                self.wait(0.3)
            L("    ==============================================================", True)
            L(f"      PHASE {n} PIPELINE -- ALL CHECKS PASSED", True)
            L("    ==============================================================", True)
            self.record("rtl_generation", "PASS", f"phase {n}")
        L("$ Frontend2/scripts/generate_top.py --drop drop")
        self.wait(1)
        self.record("rtl_generation", "PASS", "top-level assembled: drop/TOPRTL")

        path_names = [
            "path_01_write_cmd", "path_02_read_cmd", "path_03_read_return",
            "path_04_scheduler_bank_loop", "path_05_scheduler_refresh_loop",
            "path_07_backpressure", "path_08_init_to_cal", "path_09_init_to_refresh",
            "path_12_csr_timing_to_scheduling", "path_13_csr_refresh_to_scheduling",
            "path_14_status_init", "path_15_status_cal", "path_16_status_refresh",
            "path_17_full_boot", "path_18_full_write", "path_19_row_conflict",
            "path_20_refresh_preempt", "path_21_wb_port_standalone",
            "path_22_csr_standalone", "path_23_host_ack_collision"]

        def validate_round(fail_paths, failed_modules, round_n):
            L("$ Validation/tools/validate_drop.py --drop drop")
            L(f"    [4] simulate {len(path_names)} path(s), 4 at a time", True)
            for name in path_names:
                st = "FAIL" if name in fail_paths else "PASS"
                L(f"        {name:35} {st}", True)
                self.wait(0.25)
            nfail = len(fail_paths)
            L(f"        pass={len(path_names) - nfail} fail={nfail} error=0", True)
            if failed_modules:
                detail = (f"FAIL; failed modules: {', '.join(failed_modules)}; "
                          f"package: runs/demo/validation/round_{round_n}")
                self.record("rtl_validation", "FAIL", detail)
            else:
                self.record("rtl_validation", "PASS", "PASS; failed modules: none")

        self.state["rounds"]["rtl"] = 1
        self._save()
        validate_round({"path_02_read_cmd", "path_18_full_write"}, ["wb_port"], 1)
        L("Failing module(s): wb_port")
        L("##############################################################")
        L("#  wb_port: fix attempt 1/3")
        L("##############################################################")
        L("  asking Claude to diagnose + propose a fix...", True)
        self.wait(1.5)
        L("  ROOT CAUSE (medium confidence):", True)
        L("    a tag-indexed response buffer gated on a stale pending bit.", True)
        L("  wb_port: FIXED -- lint PASS, sim PASS on re-verification.", True)
        self.wait(0.3)
        self.record("frontend_regeneration", "PASS", "phase 1 agent exited 0; fixed: wb_port")
        self.state["rounds"]["rtl"] = 2
        self._save()
        validate_round(set(), [], 2)
        L("$ Validation/tools/run_formal.py --drop drop")
        self.wait(2)
        self.record("formal", "PASS", "informational: 6/6 properties proven")
        self.backend()
        L("$ Validation/tools/run_path.py --netlist backend/runner/ddr3_controller/6_final.v")
        self.wait(3)
        self.record("final_validation", "PASS", "20/20 paths on the routed netlist")
        self.state["status"] = "done"
        self._save()
        L("flow complete")

    def backend(self):
        L = self.log
        self.state["rounds"]["backend"] += 1
        self._save()
        L("$ backend/agents/pipeline.py --bundle_dir drop/TOPRTL --out_root backend --mode build"
          "   (cwd backend/agents)")
        L("[intake] Running intake validation...", True)
        self.wait(0.8)
        L("[intake] Status=PASS  errors=0  warnings=1", True)
        L("[packager] Running packager...", True)
        self.wait(0.8)
        L("[packager] Status=PASS  errors=0", True)
        L("[runner] Executing: docker run --rm -v ...", True)
        orfs_share = 54.0
        total_w = sum(w for _, w in ORFS_FILES)
        for name, w in ORFS_FILES:
            self.orfs_step(name, orfs_share * w / total_w)
        L("[runner] exit_code=0  failed_stage=None  artifacts=['gds', 'def', 'v', 'spef']", True)
        L("[reporter] run_passed=True", True)
        L(f"[validator] Running sign-off (DRC + LVS + pin audit) for {DESIGN}...", True)
        self.wait(8)
        L("[validator] Running DRC check...", True)
        L("[validator] Running LVS check...", True)
        L("[validator] Running STA sign-off check...", True)
        self.wait(2)
        os.makedirs(os.path.join(self.run_dir, "backend"), exist_ok=True)
        rep = {"pipeline_status": "FAIL" if self.fail_backend else "PASS", "error_message": None,
               "tuner_iterations": 0, "failed_stage": None, "drc_violations": 0,
               "lvs_status": "PASS", "sta_wns_ns": 0.142, "sta_status": "PASS",
               "artifacts": ["backend/runner/ddr3_controller/6_final.v"]}
        with open(os.path.join(self.run_dir, "backend", f"pipeline_final_report_{DESIGN}.json"), "w") as f:
            json.dump(rep, f, indent=2)
        L(f"  Full report     : backend/pipeline_final_report_{DESIGN}.json", True)
        self.record("backend", rep["pipeline_status"],
                    "exit 0; failed_stage=None; drc=0 lvs=PASS sta=PASS; netlist 6_final.v")

    def orfs_step(self, name, share):
        tmp = os.path.join(self.logs, name + ".tmp.log")
        dur = self.total * share / 100.0
        ticks = max(3, int(dur / 0.5))
        with open(tmp, "w") as f:
            f.write(f"OpenROAD {name} start\n")
        for i in range(ticks):
            with open(tmp, "a") as f:
                f.write(self.step_line(name, i, ticks))
            time.sleep(dur / ticks)
        if name == "1_2_yosys":
            with open(os.path.join(self.reports, "synth_stat.txt"), "w") as f:
                f.write("=== ddr3_controller ===\n\n   Number of cells:              23587\n")
        os.replace(tmp, os.path.join(self.logs, name + ".log"))

    def step_line(self, name, i, n):
        frac = (i + 1) / n
        if name == "3_3_place_gp":
            ov = 1.0 - 0.9 * frac
            return f"[NESTEROV] Iter: {(i + 1) * 10:4d} overflow: {ov:.3f} HPWL: {9e8 * (1.2 - frac * 0.4):.0f}\n"
        if name == "5_2_route":
            # iteration 0 is 60% of the step, then four cleanup iterations
            if frac <= 0.6:
                p = frac / 0.6
                out = "[INFO DRT-0195] Start 0th optimization iteration.\n" if i == 0 else ""
                return out + f"    Completing {int(p * 10) * 10}% with {int(4200 * p)} violations.\n"
            k = 1 + int((frac - 0.6) / 0.1)
            k = min(k, 4)
            v = int(4200 * (0.25 ** k))
            suffix = {1: "st", 2: "nd", 3: "rd"}.get(k, "th")
            return (f"[INFO DRT-0195] Start {k}{suffix} optimization iteration.\n"
                    f"    Completing 100% with {v} violations.\n"
                    + ("[INFO DRT-0199]   Number of violations = 0.\n" if i == n - 1 else ""))
        return f"[INFO] {name} {frac * 100:.0f}%\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--minutes", type=float, default=4.0)
    ap.add_argument("--out")
    a = ap.parse_args()
    d = Demo(a.minutes, a.out)
    print(f"runs root {d.runs_root}\norfs dir  {d.orfs_dir}")
    d.run()


if __name__ == "__main__":
    main()
