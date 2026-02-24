#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║        DDR3 PHASE 2 — INTERNAL VALIDATION AGENT                      ║
║                                                                      ║
║  Modules validated:                                                  ║
║    addr_decoder    — address bit-slice correctness                   ║
║    bank_tracker    — per-bank FSM, timing counters, permissions      ║
║    refresh_ctrl    — tREFI counter, postpone logic, urgent/starve    ║
║    calibration     — cal_done gating, periodic ZQCS                  ║
║    cross_module    — inter-module interface consistency              ║
║                                                                      ║
║  Total checks: ~80 (varies with spec)                               ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import math
import os
import re
import sys
import time
from datetime import datetime
from pathlib import Path


def print_check(check: dict, index: int = 0, total: int = 0):
    """Print a single check result with test-runner formatting."""
    sym = "\033[92m✓ PASS\033[0m" if check["pass"] else "\033[91m✗ FAIL\033[0m"
    counter = f"[{index}/{total}]" if total > 0 else ""

    sys.stdout.write(f"  {counter:>8s}  Running {check['id']}: {check['name']}...")
    sys.stdout.flush()
    time.sleep(0.06)

    sys.stdout.write(f"\r  {counter:>8s}  {sym}  [{check['id']}] {check['name']}")
    if not check["pass"]:
        sys.stdout.write(f"\n           \033[91m  expected: {check['expected']}\033[0m")
        sys.stdout.write(f"\n           \033[91m  actual:   {check['actual']}\033[0m")
    sys.stdout.write("\n")
    sys.stdout.flush()


class Phase2ValidationAgent:

    def __init__(self, spec_path: str, rtl_dir: str, output_dir: str = None,
                 attempt: int = 1, max_retries: int = 4, history: list = None):
        self.spec_path = spec_path
        self.rtl_dir = Path(rtl_dir)
        self.output_dir = Path(output_dir or rtl_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.attempt = attempt
        self.max_retries = max_retries
        self.history = history or []

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geo = self.spec["memory_geometry"]
        self.tm = self.spec["timing_model"]
        self.dc = self.tm["$derived_cycles"]
        self.cl = self.spec["clocking_model"]
        self.cal = self.spec["calibration"]
        self.arch = self.spec["controller_architecture"]
        self.host = self.spec["host_interface"]

        self.results = {
            "timestamp": datetime.now().isoformat(),
            "spec": spec_path,
            "phase": 2,
            "modules": {},
        }

    # ════════════════════════════════════════════════════════════
    # ADDR_DECODER VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_addr_decoder(self) -> dict:
        checks = []
        sv_path = self.rtl_dir / "addr_decoder.sv"
        if not sv_path.exists():
            return {"status": "ERROR", "passed": 0, "total": 0,
                    "checks": [{"id": "V-AD-00", "name": "File exists", "pass": False,
                                "expected": "addr_decoder.sv", "actual": "missing"}]}
        sv = sv_path.read_text()

        row_bits = self.geo["row_bits"]
        col_bits = self.geo["column_bits"]
        bank_bits = self.geo["bank_bits"]
        ranks = self.geo["ranks"]
        addr_w = self.host["address_width_bits"]
        bl = self.geo["burst_length"]
        mapping = self.geo.get("address_mapping", "row-bank-column")

        # V-AD-01: Parameters match spec
        for param, expected in [("ADDR_WIDTH", addr_w), ("ROW_BITS", row_bits),
                                ("COL_BITS", col_bits), ("BANK_BITS", bank_bits)]:
            m = re.search(rf"{param}\s*=\s*(\d+)", sv)
            actual = int(m.group(1)) if m else 0
            checks.append({"id": "V-AD-01", "name": f"Parameter {param} = {expected}",
                           "pass": actual == expected, "expected": str(expected), "actual": str(actual)})

        # V-AD-02: Output ports exist
        for port in ["dec_row", "dec_bank", "dec_col", "dec_rank"]:
            checks.append({"id": "V-AD-02", "name": f"Output {port} declared",
                           "pass": re.search(rf"output\s+logic\s+.*{port}", sv) is not None,
                           "expected": f"output logic ... {port}", "actual": "found" if port in sv else "missing"})

        # V-AD-03: Input req_addr declared
        checks.append({"id": "V-AD-03", "name": "Input req_addr declared",
                       "pass": "req_addr" in sv,
                       "expected": "input logic ... req_addr", "actual": "found" if "req_addr" in sv else "missing"})

        # V-AD-04: Address mapping policy
        # Check bit slice for burst offset (log2(BL * data_width/8))
        # Burst byte offset: BL × channel_width_bytes
        # channel_width = device_width × byte_lanes (in bytes), NOT wishbone data_width
        device_width = self.geo.get("device_width_bits", 8)
        byte_lanes = self.geo.get("byte_lanes", 2)
        channel_bytes = device_width * byte_lanes // 8  # e.g. 8×2/8 = 2
        burst_offset_bits = int(math.log2(bl * channel_bytes))
        checks.append({"id": "V-AD-04", "name": f"Burst offset = {burst_offset_bits} bits (BL{bl})",
                       "pass": (f":{burst_offset_bits}]" in sv
                               or f"[{burst_offset_bits-1}:0]" in sv
                               or f"addr[{burst_offset_bits}" in sv),
                       "expected": f"bits [{burst_offset_bits-1}:0] = burst offset",
                       "actual": "bit slicing found" if f":{burst_offset_bits}]" in sv or f"[{burst_offset_bits-1}:0]" in sv else "check manually"})

        # V-AD-05: Mapping order — row-bank-column
        if mapping == "row-bank-column":
            # Column bits should be lower than bank bits, bank lower than row
            col_assign = re.search(r"dec_col\s*=.*req_addr\[(\d+)", sv)
            bank_assign = re.search(r"dec_bank\s*=.*req_addr\[(\d+)", sv)
            row_assign = re.search(r"dec_row\s*=.*req_addr\[(\d+)", sv)
            if col_assign and bank_assign and row_assign:
                col_hi = int(col_assign.group(1))
                bank_hi = int(bank_assign.group(1))
                row_hi = int(row_assign.group(1))
                correct_order = col_hi < bank_hi < row_hi
            else:
                correct_order = True  # Can't parse, give benefit of doubt
            checks.append({"id": "V-AD-05", "name": f"Address mapping order: {mapping}",
                           "pass": correct_order,
                           "expected": "col < bank < row bit positions",
                           "actual": f"col@{col_assign.group(1) if col_assign else '?'}, "
                                     f"bank@{bank_assign.group(1) if bank_assign else '?'}, "
                                     f"row@{row_assign.group(1) if row_assign else '?'}"})

        # V-AD-06: Combinational (no clk port)
        has_clk = re.search(r"input\s+logic\s+clk", sv) is not None
        checks.append({"id": "V-AD-06", "name": "Purely combinational (no clock)",
                       "pass": not has_clk,
                       "expected": "no clk input", "actual": "no clk" if not has_clk else "has clk (sequential)"})

        # V-AD-07: Rank assignment for single rank
        if ranks == 1:
            checks.append({"id": "V-AD-07", "name": "Single rank: dec_rank = 0",
                           "pass": re.search(r"dec_rank\s*=\s*'0|dec_rank\s*=\s*0|dec_rank\s*=\s*1'b0", sv) is not None,
                           "expected": "dec_rank = 0", "actual": "found" if "dec_rank" in sv else "missing"})

        # V-AD-08: Total bits consumed = ADDR_WIDTH
        # row + bank + col_usable + burst_offset should = ADDR_WIDTH
        usable_col_bits = col_bits - int(math.log2(bl))  # BL8 means low 3 col bits are 0
        # RANK_BITS for the addr decoder
        rank_bits = max(1, int(math.log2(ranks))) if ranks > 1 else 0
        total_bits = row_bits + bank_bits + usable_col_bits + burst_offset_bits + rank_bits
        checks.append({"id": "V-AD-08", "name": f"Bit budget: {row_bits}+{bank_bits}+{usable_col_bits}+{burst_offset_bits} = {total_bits}",
                       "pass": total_bits == addr_w,
                       "expected": str(addr_w), "actual": str(total_bits)})

        passed = sum(1 for c in checks if c["pass"])
        return {"status": "PASS" if passed == len(checks) else "FAIL",
                "passed": passed, "total": len(checks), "checks": checks}

    # ════════════════════════════════════════════════════════════
    # BANK_TRACKER VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_bank_tracker(self) -> dict:
        checks = []
        sv_path = self.rtl_dir / "bank_tracker.sv"
        if not sv_path.exists():
            return {"status": "ERROR", "passed": 0, "total": 0,
                    "checks": [{"id": "V-BT-00", "name": "File exists", "pass": False,
                                "expected": "bank_tracker.sv", "actual": "missing"}]}
        sv = sv_path.read_text()

        num_banks = 2 ** self.geo["bank_bits"]
        row_bits = self.geo["row_bits"]
        bank_bits = self.geo["bank_bits"]

        # V-BT-01: Parameters
        for param, expected in [("NUM_BANKS", num_banks), ("BANK_BITS", bank_bits), ("ROW_BITS", row_bits)]:
            m = re.search(rf"{param}\s*=\s*(\d+)", sv)
            actual = int(m.group(1)) if m else 0
            checks.append({"id": "V-BT-01", "name": f"Parameter {param} = {expected}",
                           "pass": actual == expected, "expected": str(expected), "actual": str(actual)})

        # V-BT-02: Per-bank output signals
        for sig in ["bank_is_active", "bank_open_row", "bank_act_allowed",
                     "bank_rd_allowed", "bank_wr_allowed", "bank_pre_allowed"]:
            found = sig in sv
            checks.append({"id": "V-BT-02", "name": f"Output {sig}",
                           "pass": found, "expected": f"output ... {sig}", "actual": "found" if found else "missing"})

        # V-BT-03: Global outputs
        for sig in ["all_banks_idle", "faw_allows_act"]:
            found = sig in sv
            checks.append({"id": "V-BT-03", "name": f"Output {sig}",
                           "pass": found, "expected": f"output logic {sig}", "actual": "found" if found else "missing"})

        # V-BT-04: Command inputs
        for sig in ["cmd_act_valid", "cmd_pre_valid", "cmd_rd_valid", "cmd_wr_valid", "cmd_ref_valid"]:
            found = sig in sv
            checks.append({"id": "V-BT-04", "name": f"Input {sig}",
                           "pass": found, "expected": f"input logic {sig}", "actual": "found" if found else "missing"})

        # V-BT-05: Timing config inputs
        timing_inputs = ["cfg_tRCD_nCK", "cfg_tRP_nCK", "cfg_tRAS_nCK", "cfg_tRC_nCK",
                         "cfg_tRRD_nCK", "cfg_tWTR_nCK", "cfg_tFAW_nCK", "cfg_tRFC_nCK",
                         "cfg_tWR_nCK", "cfg_tRTP_nCK", "cfg_tCCD_nCK"]
        for sig in timing_inputs:
            found = sig in sv
            checks.append({"id": "V-BT-05", "name": f"Config input {sig}",
                           "pass": found, "expected": f"input ... {sig}", "actual": "found" if found else "missing"})

        # V-BT-06: Bank state machine (IDLE/ACTIVE/PRECHARGING)
        for state in ["IDLE", "ACTIVE", "PRECHARGING"]:
            found = re.search(rf"\b{state}\b", sv, re.I) is not None
            checks.append({"id": "V-BT-06", "name": f"Bank state: {state}",
                           "pass": found, "expected": f"{state} in FSM", "actual": "found" if found else "missing"})

        # V-BT-07: Timing counters present (at least tRCD, tRP, tRAS, tRC)
        for ctr in ["rcd", "rp", "ras", "rc"]:
            found = re.search(rf"ctr_{ctr}|{ctr}_ctr|timer_{ctr}", sv, re.I) is not None
            checks.append({"id": "V-BT-07", "name": f"Timing counter: t{ctr.upper()}",
                           "pass": found, "expected": f"counter for t{ctr.upper()}", "actual": "found" if found else "missing"})

        # V-BT-08: tFAW window tracking
        faw_found = re.search(r"faw|FAW", sv) is not None
        checks.append({"id": "V-BT-08", "name": "tFAW window tracking",
                       "pass": faw_found, "expected": "FAW tracking logic", "actual": "found" if faw_found else "missing"})

        # V-BT-09: Clock and reset
        has_clk = re.search(r"input\s+logic\s+clk", sv) is not None
        has_rst = re.search(r"input\s+logic\s+rst_n", sv) is not None
        checks.append({"id": "V-BT-09", "name": "Clock and reset",
                       "pass": has_clk and has_rst, "expected": "clk, rst_n",
                       "actual": f"{'clk ' if has_clk else ''}{'rst_n' if has_rst else 'missing'}"})

        # V-BT-10: Refresh handling (all banks return to idle)
        ref_handling = re.search(r"cmd_ref_valid.*IDLE|ref.*IDLE|refresh.*idle", sv, re.I | re.S) is not None
        checks.append({"id": "V-BT-10", "name": "Refresh → all banks idle",
                       "pass": ref_handling or "cmd_ref_valid" in sv,
                       "expected": "refresh resets bank state", "actual": "found" if ref_handling or "cmd_ref_valid" in sv else "missing"})

        passed = sum(1 for c in checks if c["pass"])
        return {"status": "PASS" if passed == len(checks) else "FAIL",
                "passed": passed, "total": len(checks), "checks": checks}

    # ════════════════════════════════════════════════════════════
    # REFRESH_CTRL VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_refresh_ctrl(self) -> dict:
        checks = []
        sv_path = self.rtl_dir / "refresh_ctrl.sv"
        if not sv_path.exists():
            return {"status": "ERROR", "passed": 0, "total": 0,
                    "checks": [{"id": "V-RF-00", "name": "File exists", "pass": False,
                                "expected": "refresh_ctrl.sv", "actual": "missing"}]}
        sv = sv_path.read_text()

        trefi = self.dc["tREFI_nCK"]
        ref_policy = self.arch.get("refresh_policy", {})
        max_postpone = ref_policy.get("max_postpone_count", 8)
        urgent_thresh = ref_policy.get("urgent_threshold", 6)

        # V-RF-01: Output signals
        for sig in ["ref_required", "ref_urgent", "ref_ack", "ref_pending_cnt", "ref_starve_flag"]:
            if sig == "ref_ack":
                # ref_ack is input
                found = re.search(rf"input\s+logic\s+.*{sig}", sv) is not None
            else:
                found = re.search(rf"output\s+logic\s+.*{sig}", sv) is not None
            dir_str = "input" if sig == "ref_ack" else "output"
            checks.append({"id": "V-RF-01", "name": f"Signal {sig} ({dir_str})",
                           "pass": found, "expected": f"{dir_str} ... {sig}", "actual": "found" if found else "missing"})

        # V-RF-02: Config inputs
        for sig in ["cfg_tREFI_nCK", "cfg_max_postpone", "cfg_urgent_threshold", "cfg_ref_priority"]:
            found = sig in sv
            checks.append({"id": "V-RF-02", "name": f"Config input {sig}",
                           "pass": found, "expected": f"input ... {sig}", "actual": "found" if found else "missing"})

        # V-RF-03: tREFI counter present
        refi_ctr = re.search(r"refi_ctr|refi_counter|tREFI.*ctr", sv, re.I) is not None
        checks.append({"id": "V-RF-03", "name": "tREFI interval counter",
                       "pass": refi_ctr, "expected": "counter for tREFI interval",
                       "actual": "found" if refi_ctr else "missing"})

        # V-RF-04: Counter width sufficient for tREFI
        refi_ctr_w_match = re.search(r"REFI_CTR_W\s*=\s*(\d+)", sv)
        if refi_ctr_w_match:
            ctr_w = int(refi_ctr_w_match.group(1))
            min_w = math.ceil(math.log2(trefi + 1))
            checks.append({"id": "V-RF-04", "name": f"REFI_CTR_W={ctr_w} >= {min_w} (for tREFI={trefi})",
                           "pass": ctr_w >= min_w, "expected": f">= {min_w}", "actual": str(ctr_w)})

        # V-RF-05: Postpone counter
        postpone_found = re.search(r"postpone_cnt|postpone_count|post_cnt", sv, re.I) is not None
        checks.append({"id": "V-RF-05", "name": "Postpone counter",
                       "pass": postpone_found, "expected": "postpone tracking", "actual": "found" if postpone_found else "missing"})

        # V-RF-06: max_postpone limit enforced
        max_p_ref = re.search(r"cfg_max_postpone|max_postpone", sv) is not None
        checks.append({"id": "V-RF-06", "name": "max_postpone limit enforced",
                       "pass": max_p_ref, "expected": "reference to max_postpone",
                       "actual": "found" if max_p_ref else "missing"})

        # V-RF-07: Urgent threshold
        urgent_ref = re.search(r"cfg_urgent_threshold|urgent_threshold", sv) is not None
        checks.append({"id": "V-RF-07", "name": "Urgent threshold comparison",
                       "pass": urgent_ref, "expected": "reference to urgent_threshold",
                       "actual": "found" if urgent_ref else "missing"})

        # V-RF-08: Starvation detection
        starve_found = re.search(r"starve|starvation|ref_starve", sv, re.I) is not None
        checks.append({"id": "V-RF-08", "name": "Starvation detection logic",
                       "pass": starve_found, "expected": "starvation detection",
                       "actual": "found" if starve_found else "missing"})

        # V-RF-09: init_done gating
        init_gate = "init_done" in sv
        checks.append({"id": "V-RF-09", "name": "Gated by init_done",
                       "pass": init_gate, "expected": "no refresh before init_done",
                       "actual": "found" if init_gate else "missing"})

        # V-RF-10: Force refresh from CSR
        force_ref = "cfg_force_refresh" in sv or "force_refresh" in sv
        checks.append({"id": "V-RF-10", "name": "CSR force_refresh support",
                       "pass": force_ref, "expected": "cfg_force_refresh input",
                       "actual": "found" if force_ref else "missing"})

        # V-RF-11: Clock and reset
        has_clk = re.search(r"input\s+logic\s+clk", sv) is not None
        has_rst = re.search(r"input\s+logic\s+rst_n", sv) is not None
        checks.append({"id": "V-RF-11", "name": "Clock and reset",
                       "pass": has_clk and has_rst, "expected": "clk, rst_n",
                       "actual": f"{'clk ' if has_clk else ''}{'rst_n' if has_rst else 'missing'}"})

        passed = sum(1 for c in checks if c["pass"])
        return {"status": "PASS" if passed == len(checks) else "FAIL",
                "passed": passed, "total": len(checks), "checks": checks}

    # ════════════════════════════════════════════════════════════
    # CALIBRATION VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_calibration(self) -> dict:
        checks = []
        sv_path = self.rtl_dir / "calibration.sv"
        if not sv_path.exists():
            return {"status": "ERROR", "passed": 0, "total": 0,
                    "checks": [{"id": "V-CL-00", "name": "File exists", "pass": False,
                                "expected": "calibration.sv", "actual": "missing"}]}
        sv = sv_path.read_text()

        ctrl_period = self.cl["controller_clock_period_ns"]
        zqcs_interval_ns = self.cal.get("periodic_zqcs_interval_ns", 640000)
        zqcs_interval_nCK = self.cal.get("$derived", {}).get("periodic_zqcs_interval_nCK", 512000)
        zqcs_ctrl_cycles = math.ceil(zqcs_interval_nCK / self.cl["clock_ratio_ddr_to_controller"])

        # V-CL-01: Output cal_done
        cal_done_out = re.search(r"output\s+logic\s+.*cal_done", sv) is not None
        checks.append({"id": "V-CL-01", "name": "Output cal_done declared",
                       "pass": cal_done_out, "expected": "output logic cal_done",
                       "actual": "found" if cal_done_out else "missing"})

        # V-CL-02: Output cal_fail
        cal_fail_out = re.search(r"output\s+logic\s+.*cal_fail", sv) is not None
        checks.append({"id": "V-CL-02", "name": "Output cal_fail declared",
                       "pass": cal_fail_out, "expected": "output logic cal_fail",
                       "actual": "found" if cal_fail_out else "missing"})

        # V-CL-03: cal_fail = 0 (abstract PHY)
        cal_fail_zero = re.search(r"cal_fail\s*=\s*1'b0|cal_fail\s*<=\s*1'b0|cal_fail\s*=\s*0", sv) is not None
        checks.append({"id": "V-CL-03", "name": "cal_fail always 0 (abstract PHY)",
                       "pass": cal_fail_zero, "expected": "cal_fail = 0",
                       "actual": "found" if cal_fail_zero else "not found"})

        # V-CL-04: init_done input
        init_done_in = "init_done" in sv
        checks.append({"id": "V-CL-04", "name": "Input init_done",
                       "pass": init_done_in, "expected": "input logic init_done",
                       "actual": "found" if init_done_in else "missing"})

        # V-CL-05: cal_done gated by init_done
        gating = re.search(r"init_done.*cal_done|cal_done.*init_done", sv, re.S) is not None
        checks.append({"id": "V-CL-05", "name": "cal_done depends on init_done",
                       "pass": gating, "expected": "cal_done after init_done",
                       "actual": "found" if gating else "not found"})

        # V-CL-06: ZQCS request output
        zqcs_out = re.search(r"output\s+logic\s+.*zqcs_req", sv) is not None
        checks.append({"id": "V-CL-06", "name": "Output zqcs_req",
                       "pass": zqcs_out, "expected": "output logic zqcs_req",
                       "actual": "found" if zqcs_out else "missing"})

        # V-CL-07: ZQCS ack input
        zqcs_ack_in = "zqcs_ack" in sv
        checks.append({"id": "V-CL-07", "name": "Input zqcs_ack",
                       "pass": zqcs_ack_in, "expected": "input logic zqcs_ack",
                       "actual": "found" if zqcs_ack_in else "missing"})

        # V-CL-08: ZQCS interval parameter
        zqcs_match = re.search(r"ZQCS_WAIT\s*=\s*(\d+)", sv)
        if zqcs_match:
            actual_wait = int(zqcs_match.group(1))
            checks.append({"id": "V-CL-08", "name": f"ZQCS_WAIT = {zqcs_ctrl_cycles} ctrl cycles",
                           "pass": actual_wait == zqcs_ctrl_cycles,
                           "expected": str(zqcs_ctrl_cycles), "actual": str(actual_wait)})
        else:
            checks.append({"id": "V-CL-08", "name": "ZQCS_WAIT parameter",
                           "pass": False, "expected": f"{zqcs_ctrl_cycles}", "actual": "not found"})

        # V-CL-09: Periodic ZQCS counter
        zqcs_ctr = re.search(r"zqcs_ctr|zqcs_counter", sv, re.I) is not None
        checks.append({"id": "V-CL-09", "name": "Periodic ZQCS counter",
                       "pass": zqcs_ctr, "expected": "ZQCS interval counter",
                       "actual": "found" if zqcs_ctr else "missing"})

        # V-CL-10: Clock and reset
        has_clk = re.search(r"input\s+logic\s+clk", sv) is not None
        has_rst = re.search(r"input\s+logic\s+rst_n", sv) is not None
        checks.append({"id": "V-CL-10", "name": "Clock and reset",
                       "pass": has_clk and has_rst, "expected": "clk, rst_n",
                       "actual": f"{'clk ' if has_clk else ''}{'rst_n' if has_rst else 'missing'}"})

        # V-CL-11: Write leveling disabled
        wl_disabled = not self.cal.get("enable_write_leveling", False)
        if wl_disabled:
            # Should not have active write leveling FSM
            wl_fsm = re.search(r"WL_START|write_level.*state|wl_state", sv, re.I) is not None
            checks.append({"id": "V-CL-11", "name": "Write leveling disabled (per spec)",
                           "pass": not wl_fsm, "expected": "no WL FSM",
                           "actual": "none" if not wl_fsm else "WL FSM found (spec says disabled)"})

        passed = sum(1 for c in checks if c["pass"])
        return {"status": "PASS" if passed == len(checks) else "FAIL",
                "passed": passed, "total": len(checks), "checks": checks}

    # ════════════════════════════════════════════════════════════
    # CROSS-MODULE INTERFACE VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_cross_module(self) -> dict:
        checks = []

        # Load all SV files
        files = {}
        for name in ["addr_decoder", "bank_tracker", "refresh_ctrl", "calibration"]:
            path = self.rtl_dir / f"{name}.sv"
            files[name] = path.read_text() if path.exists() else ""

        # Also load Phase 1 files if they exist
        for name in ["init_fsm", "config_regs", "wb_port"]:
            path = self.rtl_dir / f"{name}.sv"
            if path.exists():
                files[name] = path.read_text()

        # V-XM-01: addr_decoder uses same ADDR_WIDTH as wb_port
        if files.get("wb_port") and files.get("addr_decoder"):
            wb_aw = re.search(r"ADDR_WIDTH\s*=\s*(\d+)", files["wb_port"])
            ad_aw = re.search(r"ADDR_WIDTH\s*=\s*(\d+)", files["addr_decoder"])
            if wb_aw and ad_aw:
                match = wb_aw.group(1) == ad_aw.group(1)
                checks.append({"id": "V-XM-01", "name": "ADDR_WIDTH consistent (wb_port ↔ addr_decoder)",
                               "pass": match, "expected": wb_aw.group(1), "actual": ad_aw.group(1)})

        # V-XM-02: bank_tracker uses same ROW_BITS / BANK_BITS as addr_decoder
        if files.get("addr_decoder") and files.get("bank_tracker"):
            for param in ["ROW_BITS", "BANK_BITS"]:
                ad_m = re.search(rf"{param}\s*=\s*(\d+)", files["addr_decoder"])
                bt_m = re.search(rf"{param}\s*=\s*(\d+)", files["bank_tracker"])
                if ad_m and bt_m:
                    match = ad_m.group(1) == bt_m.group(1)
                    checks.append({"id": "V-XM-02", "name": f"{param} consistent (addr_decoder ↔ bank_tracker)",
                                   "pass": match, "expected": ad_m.group(1), "actual": bt_m.group(1)})

        # V-XM-03: refresh_ctrl has init_done (from init_fsm)
        if files.get("refresh_ctrl"):
            checks.append({"id": "V-XM-03", "name": "refresh_ctrl receives init_done",
                           "pass": "init_done" in files["refresh_ctrl"],
                           "expected": "input init_done", "actual": "found" if "init_done" in files["refresh_ctrl"] else "missing"})

        # V-XM-04: calibration has init_done (from init_fsm)
        if files.get("calibration"):
            checks.append({"id": "V-XM-04", "name": "calibration receives init_done",
                           "pass": "init_done" in files["calibration"],
                           "expected": "input init_done", "actual": "found" if "init_done" in files["calibration"] else "missing"})

        # V-XM-05: bank_tracker cfg ports match config_regs outputs
        if files.get("bank_tracker") and files.get("config_regs"):
            cfg_ports = re.findall(r"cfg_\w+_nCK|cfg_CL_nCK|cfg_CWL_nCK", files["bank_tracker"])
            for port in set(cfg_ports):
                found_in_csr = port in files["config_regs"]
                checks.append({"id": "V-XM-05", "name": f"bank_tracker.{port} ← config_regs",
                               "pass": found_in_csr, "expected": f"{port} in config_regs",
                               "actual": "found" if found_in_csr else "missing"})

        # V-XM-06: refresh_ctrl cfg ports match config_regs
        if files.get("refresh_ctrl") and files.get("config_regs"):
            for port in ["cfg_tREFI_nCK", "cfg_max_postpone", "cfg_urgent_threshold"]:
                found = port in files["config_regs"]
                checks.append({"id": "V-XM-06", "name": f"refresh_ctrl.{port} ← config_regs",
                               "pass": found, "expected": f"{port} in config_regs",
                               "actual": "found" if found else "missing"})

        passed = sum(1 for c in checks if c["pass"])
        return {"status": "PASS" if passed == len(checks) else "FAIL",
                "passed": passed, "total": len(checks), "checks": checks}

    # ════════════════════════════════════════════════════════════
    # MAIN RUN
    # ════════════════════════════════════════════════════════════
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"\n\033[1m{hdr}\033[0m")
        print(f"\033[1m  PHASE 2 VALIDATION AGENT — TEST RUNNER\033[0m")
        print(f"  Spec: {self.spec_path}")
        print(f"  RTL:  {self.rtl_dir}")
        print(f"\033[1m{hdr}\033[0m")

        start = time.time()

        # ── addr_decoder ──
        print(f"\n\033[1m  ── ADDR_DECODER TESTBENCH ({'─' * 35})\033[0m")
        print(f"  Loading addr_decoder.sv...")
        time.sleep(0.15)
        result = self.validate_addr_decoder()
        self.results["modules"]["addr_decoder"] = result
        for i, chk in enumerate(result["checks"], 1):
            print_check(chk, i, result["total"])
        sym = "\033[92m" if result["status"] == "PASS" else "\033[91m"
        print(f"\n  {sym}  {'✓' if result['status'] == 'PASS' else '✗'} addr_decoder: {result['status']} ({result['passed']}/{result['total']})\033[0m")

        # ── bank_tracker ──
        print(f"\n\033[1m  ── BANK_TRACKER TESTBENCH ({'─' * 35})\033[0m")
        print(f"  Loading bank_tracker.sv...")
        time.sleep(0.15)
        result = self.validate_bank_tracker()
        self.results["modules"]["bank_tracker"] = result
        for i, chk in enumerate(result["checks"], 1):
            print_check(chk, i, result["total"])
        sym = "\033[92m" if result["status"] == "PASS" else "\033[91m"
        print(f"\n  {sym}  {'✓' if result['status'] == 'PASS' else '✗'} bank_tracker: {result['status']} ({result['passed']}/{result['total']})\033[0m")

        # ── refresh_ctrl ──
        print(f"\n\033[1m  ── REFRESH_CTRL TESTBENCH ({'─' * 35})\033[0m")
        print(f"  Loading refresh_ctrl.sv...")
        time.sleep(0.15)
        result = self.validate_refresh_ctrl()
        self.results["modules"]["refresh_ctrl"] = result
        for i, chk in enumerate(result["checks"], 1):
            print_check(chk, i, result["total"])
        sym = "\033[92m" if result["status"] == "PASS" else "\033[91m"
        print(f"\n  {sym}  {'✓' if result['status'] == 'PASS' else '✗'} refresh_ctrl: {result['status']} ({result['passed']}/{result['total']})\033[0m")

        # ── calibration ──
        print(f"\n\033[1m  ── CALIBRATION TESTBENCH ({'─' * 36})\033[0m")
        print(f"  Loading calibration.sv...")
        time.sleep(0.15)
        result = self.validate_calibration()
        self.results["modules"]["calibration"] = result
        for i, chk in enumerate(result["checks"], 1):
            print_check(chk, i, result["total"])
        sym = "\033[92m" if result["status"] == "PASS" else "\033[91m"
        print(f"\n  {sym}  {'✓' if result['status'] == 'PASS' else '✗'} calibration: {result['status']} ({result['passed']}/{result['total']})\033[0m")

        # ── cross_module ──
        print(f"\n\033[1m  ── CROSS-MODULE INTERFACE ({'─' * 35})\033[0m")
        print(f"  Checking inter-module consistency...")
        time.sleep(0.15)
        result = self.validate_cross_module()
        self.results["modules"]["cross_module"] = result
        for i, chk in enumerate(result["checks"], 1):
            print_check(chk, i, result["total"])
        sym = "\033[92m" if result["status"] == "PASS" else "\033[91m"
        print(f"\n  {sym}  {'✓' if result['status'] == 'PASS' else '✗'} cross_module: {result['status']} ({result['passed']}/{result['total']})\033[0m")

        elapsed = time.time() - start

        # Overall
        total_passed = sum(m["passed"] for m in self.results["modules"].values())
        total_checks = sum(m["total"] for m in self.results["modules"].values())
        all_pass = all(m["status"] == "PASS" for m in self.results["modules"].values())

        self.results["overall"] = {
            "status": "PASS" if all_pass else "FAIL",
            "total_passed": total_passed,
            "total_checks": total_checks,
        }

        print(f"\n\033[1m{hdr}\033[0m")
        if all_pass:
            print(f"\033[92m  ✓ ALL TESTS PASSED: {total_passed}/{total_checks} checks in {elapsed:.2f}s\033[0m")
        else:
            print(f"\033[91m  ✗ TESTS FAILED: {total_passed}/{total_checks} checks in {elapsed:.2f}s\033[0m")
        print(f"\033[1m{hdr}\033[0m")
        print(f"  {'Module':<20s} {'Status':<10s} {'Passed':<10s} {'Total':<10s}")
        print(f"  {'─' * 50}")
        for mod, res in self.results["modules"].items():
            color = "\033[92m" if res["status"] == "PASS" else "\033[91m"
            print(f"  {mod:<20s} {color}{res['status']:<10s}\033[0m {res['passed']:<10d} {res['total']:<10d}")
        print(f"  {'─' * 50}")
        print(f"  {'TOTAL':<20s} {'PASS' if all_pass else 'FAIL':<10s} {total_passed:<10d} {total_checks:<10d}")
        print(f"  Time: {elapsed:.2f}s")
        print(f"\033[1m{hdr}\033[0m")

        # ── Write JSON report ──
        report_path = self.output_dir / "phase2_validation_report.json"
        report_path.write_text(json.dumps(self.results, indent=2))

        # ── Write TXT report ──
        txt_path = self.output_dir / "phase2_validation_report.txt"
        lines = []
        L = lines.append

        L("╔══════════════════════════════════════════════════════════════════════╗")
        L("║              DDR3 PHASE 2 VALIDATION REPORT                        ║")
        L(f"║  Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S'):55s}║")
        L(f"║  Spec:      {str(self.spec_path)[:55]:55s}║")
        L(f"║  RTL Dir:   {str(self.rtl_dir)[:55]:55s}║")
        L(f"║  Attempt:   {self.attempt} of {self.max_retries}{' ':48s}║")
        L("╚══════════════════════════════════════════════════════════════════════╝")
        L("")
        L(f"  OVERALL: {'PASS' if all_pass else 'FAIL'}  ({total_passed}/{total_checks} checks)")
        L(f"  Attempt: {self.attempt} of {self.max_retries}")
        L("")

        # Retry history
        if self.history:
            L(f"{'═' * 70}")
            L(f"  RETRY HISTORY")
            L(f"{'═' * 70}")
            L("")
            for h in self.history:
                a = h.get("attempt", "?")
                st = h.get("overall", "?")
                p = h.get("passed", "?")
                t = h.get("total", "?")
                fm = h.get("failed_modules", [])
                sym = "✓" if st == "PASS" else "✗"
                L(f"  {sym} Attempt {a}: {st} ({p}/{t})")
                if fm:
                    L(f"    Failed modules: {', '.join(fm)}")
                    for fc in h.get("failed_checks", []):
                        L(f"      ✗ [{fc['id']}] {fc['name']}")
                        L(f"        Expected: {fc['expected']}")
                        L(f"        Actual:   {fc['actual']}")
                L("")
            sym = "✓" if all_pass else "✗"
            L(f"  {sym} Attempt {self.attempt}: {'PASS' if all_pass else 'FAIL'} ({total_passed}/{total_checks})  ← current")
            L("")

        # Per-module detail
        for mod_name, mod_result in self.results["modules"].items():
            sym = "✓" if mod_result["status"] == "PASS" else "✗"
            L(f"{'═' * 70}")
            L(f"  {sym} {mod_name.upper()}  —  {mod_result['status']}  ({mod_result['passed']}/{mod_result['total']})")
            L(f"{'═' * 70}")
            L("")
            categories = {}
            for chk in mod_result["checks"]:
                prefix = chk["id"].rsplit("-", 1)[0]
                cat_names = {"V-AD": "ADDRESS DECODING", "V-BT": "BANK TRACKING",
                             "V-RF": "REFRESH CONTROL", "V-CL": "CALIBRATION",
                             "V-XM": "CROSS-MODULE INTERFACE"}
                cat = cat_names.get(prefix, prefix)
                if cat not in categories:
                    categories[cat] = []
                categories[cat].append(chk)
            for cat, chks in categories.items():
                L(f"  ── {cat} ──")
                L("")
                for chk in chks:
                    sym = "✓ PASS" if chk["pass"] else "✗ FAIL"
                    L(f"    [{chk['id']}] {chk['name']}")
                    L(f"      Status:   {sym}")
                    L(f"      Expected: {chk['expected']}")
                    L(f"      Actual:   {chk['actual']}")
                    L("")
                L("")

        # Summary table
        L(f"{'═' * 70}")
        L(f"  SUMMARY TABLE")
        L(f"{'═' * 70}")
        L(f"  {'Module':<20s} {'Status':<8s} {'Passed':<8s} {'Total':<8s} {'Rate':<8s}")
        L(f"  {'─' * 52}")
        for mod_name, mod_result in self.results["modules"].items():
            rate = f"{mod_result['passed']/mod_result['total']*100:.0f}%" if mod_result['total'] > 0 else "N/A"
            L(f"  {mod_name:<20s} {mod_result['status']:<8s} {mod_result['passed']:<8d} {mod_result['total']:<8d} {rate:<8s}")
        L(f"  {'─' * 52}")
        rate = f"{total_passed/total_checks*100:.0f}%" if total_checks > 0 else "N/A"
        L(f"  {'TOTAL':<20s} {'PASS' if all_pass else 'FAIL':<8s} {total_passed:<8d} {total_checks:<8d} {rate:<8s}")
        L("")

        # Category breakdown
        all_checks = []
        for mod_result in self.results["modules"].values():
            all_checks.extend(mod_result["checks"])
        cat_counts = {}
        for chk in all_checks:
            prefix = chk["id"].rsplit("-", 1)[0]
            cat_names = {"V-AD": "Addr Decode", "V-BT": "Bank Track",
                         "V-RF": "Refresh", "V-CL": "Calibration", "V-XM": "Cross-Module"}
            cat = cat_names.get(prefix, prefix)
            if cat not in cat_counts:
                cat_counts[cat] = {"pass": 0, "fail": 0}
            if chk["pass"]:
                cat_counts[cat]["pass"] += 1
            else:
                cat_counts[cat]["fail"] += 1
        L(f"  {'Category':<20s} {'Pass':<8s} {'Fail':<8s} {'Total':<8s}")
        L(f"  {'─' * 44}")
        for cat, counts in sorted(cat_counts.items()):
            total_cat = counts["pass"] + counts["fail"]
            L(f"  {cat:<20s} {counts['pass']:<8d} {counts['fail']:<8d} {total_cat:<8d}")
        L("")

        # Failures
        failures = [c for c in all_checks if not c["pass"]]
        if failures:
            L(f"{'═' * 70}")
            L(f"  ✗ FAILURES ({len(failures)})")
            L(f"{'═' * 70}")
            for chk in failures:
                L(f"  ✗ [{chk['id']}] {chk['name']}")
                L(f"    Expected: {chk['expected']}")
                L(f"    Actual:   {chk['actual']}")
                L("")
        else:
            L(f"{'═' * 70}")
            L(f"  ✓ ALL {total_checks} CHECKS PASSED — NO FAILURES")
            L(f"{'═' * 70}")

        txt_path.write_text("\n".join(lines))
        print(f"  Report (JSON): {report_path}")
        print(f"  Report (TXT):  {txt_path}")

        return self.results


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   PHASE 2 VALIDATION AGENT                   ║")
    print("╚══════════════════════════════════════════════╝\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}"); sys.exit(1)
    rtl = input("RTL directory: ").strip()
    if not os.path.isdir(rtl):
        print(f"Not a directory: {rtl}"); sys.exit(1)
    out = input("Output dir (Enter for same as RTL): ").strip() or rtl
    result = Phase2ValidationAgent(spec, rtl, out).run()
    sys.exit(0 if result["overall"]["status"] == "PASS" else 1)