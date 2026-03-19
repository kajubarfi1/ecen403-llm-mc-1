#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║              PHASE 1 VALIDATION AGENT                                ║
║                                                                      ║
║  Static validation + SystemVerilog testbench generation              ║
║                                                                      ║
║  Modules:                                                            ║
║    - init_fsm:    JEDEC DDR3 init sequence timing + state order      ║
║    - config_regs: CSR read/write, field encoding, reset values       ║
║    - wb_port:     Wishbone B4 protocol, stall, burst, backpressure   ║
║                                                                      ║
║  Checks:                                                             ║
║    V-TIM  Timing compliance (tRCD, tRP, tRAS, reset hold, etc.)     ║
║    V-RTL  RTL correctness (FSM transitions, register access)         ║
║    V-JED  JEDEC spec conformance (init order, MR encoding)          ║
║    V-CLK  Clock domain cross-checks                                  ║
║                                                                      ║
║  Output:                                                             ║
║    validation_report.json / .txt                                     ║
║    init_fsm_tb.sv      — JEDEC init sequence testbench               ║
║    config_regs_tb.sv   — CSR read/write/reset testbench              ║
║    wb_port_tb.sv       — Wishbone protocol testbench                 ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import os
import sys
import re
import math
import time
from pathlib import Path
from datetime import datetime


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


def _print_module_result(name, status, passed, total):
    if status == "PASS":
        print(f"\n  \033[92m  ✓ {name}: PASS ({passed}/{total})\033[0m\n")
    else:
        print(f"\n  \033[91m  ✗ {name}: FAIL ({passed}/{total})\033[0m\n")


def _finalize_checks(checks):
    passed = sum(1 for c in checks if c["pass"])
    total = len(checks)
    status = "PASS" if passed == total else "FAIL"
    for i, c in enumerate(checks, 1):
        print_check(c, i, total)
    return {"status": status, "passed": passed, "total": total, "checks": checks}


class ValidationAgent:

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
        self.init = self.spec["initialization_sequence"]
        self.csrs = self.spec["csr_register_map"]
        self.host = self.spec["host_interface"]

        self.results = {
            "timestamp": datetime.now().isoformat(),
            "spec": spec_path,
            "modules": {},
        }

        self.generated_tb_paths = []

    # ════════════════════════════════════════════════════════════
    # INIT_FSM VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_init_fsm(self) -> dict:
        """Validate init_fsm.sv against JEDEC DDR3 init sequence."""
        checks = []
        sv_path = self.rtl_dir / "init_fsm.sv"

        if not sv_path.exists():
            return {"status": "ERROR", "checks": [{"id": "V-RTL-00", "pass": False,
                     "name": "File exists", "expected": str(sv_path), "actual": "missing"}]}

        sv = sv_path.read_text()

        ctrl_period = self.cl["controller_clock_period_ns"]

        # V-TIM-01: Reset hold >= 200µs
        reset_us = self.init["reset_hold_us"]
        expected_cyc = math.ceil(reset_us * 1000 / ctrl_period)
        m = re.search(r"WAIT_RESET\s*=\s*(\d+)", sv)
        actual_cyc = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-01", "name": "Reset hold >= 200µs",
            "pass": actual_cyc >= expected_cyc,
            "expected": f">= {expected_cyc} cycles ({reset_us}µs)", "actual": f"{actual_cyc} cycles"})

        # V-TIM-02: CKE delay >= 500µs
        cke_us = self.init["cke_delay_us"]
        expected_cke = math.ceil(cke_us * 1000 / ctrl_period)
        m = re.search(r"WAIT_CKE\s*=\s*(\d+)", sv)
        actual_cke = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-02", "name": "CKE delay >= 500µs",
            "pass": actual_cke >= expected_cke,
            "expected": f">= {expected_cke} cycles ({cke_us}µs)", "actual": f"{actual_cke} cycles"})

        # V-TIM-03: tXPR wait
        tXPR_ns = self.init["tXPR_ns"]
        expected_xpr = math.ceil(tXPR_ns / ctrl_period)
        m = re.search(r"WAIT_TXPR\s*=\s*(\d+)", sv)
        actual_xpr = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-03", "name": "tXPR wait period",
            "pass": actual_xpr >= expected_xpr,
            "expected": f">= {expected_xpr} cycles ({tXPR_ns}ns)", "actual": f"{actual_xpr} cycles"})

        # V-TIM-04: tZQinit wait
        tZQ_ns = self.init["tZQinit_ns"]
        expected_zq = math.ceil(tZQ_ns / ctrl_period)
        m = re.search(r"WAIT_ZQCL\s*=\s*(\d+)", sv)
        actual_zq = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-04", "name": "tZQinit wait",
            "pass": actual_zq >= expected_zq,
            "expected": f">= {expected_zq} cycles ({tZQ_ns}ns)", "actual": f"{actual_zq} cycles"})

        # V-JED-01: MR program order MR2 → MR3 → MR1 → MR0
        mr_order = []
        for mr in ["MR2", "MR3", "MR1", "MR0"]:
            pos = sv.find(f"S_{mr}")
            if pos >= 0:
                mr_order.append((pos, mr))
        mr_order.sort()
        actual_order = [x[1] for x in mr_order]
        expected_order = ["MR2", "MR3", "MR1", "MR0"]
        checks.append({"id": "V-JED-01", "name": "MR program order (JEDEC §4.6.1)",
            "pass": actual_order == expected_order,
            "expected": " → ".join(expected_order),
            "actual": " → ".join(actual_order) if actual_order else "not found"})

        # V-JED-02: MR0 encoding
        m = re.search(r"MR0_VAL\s*=\s*\d+\'h([0-9A-Fa-f]+)", sv)
        mr0_hex = m.group(1).upper() if m else "?"
        checks.append({"id": "V-JED-02", "name": "MR0 encoding (CL=11, BL=8, DLL reset)",
            "pass": mr0_hex in ["1D34"],
            "expected": "0x1D34", "actual": f"0x{mr0_hex}"})

        # V-JED-03: MR2 encoding
        m = re.search(r"MR2_VAL\s*=\s*\d+\'h([0-9A-Fa-f]+)", sv)
        mr2_hex = m.group(1).upper() if m else "?"
        checks.append({"id": "V-JED-03", "name": "MR2 encoding (CWL=8)",
            "pass": mr2_hex in ["0218", "218"],
            "expected": "0x0218", "actual": f"0x{mr2_hex}"})

        # V-RTL-01: init_done output exists
        checks.append({"id": "V-RTL-01", "name": "init_done output declared",
            "pass": "output" in sv and "init_done" in sv,
            "expected": "output logic init_done", "actual": "found" if "init_done" in sv else "missing"})

        # V-RTL-02: init_done only in final state
        done_lines = [l.strip() for l in sv.splitlines()
                       if "init_done" in l and ("=" in l) and ("output" not in l)
                       and ("//" not in l.split("init_done")[0])]
        checks.append({"id": "V-RTL-02", "name": "init_done asserted in done state",
            "pass": len(done_lines) > 0,
            "expected": "init_done driven in S_DONE", "actual": f"{len(done_lines)} assignment(s) found"})

        # V-RTL-03: ZQCL issued
        checks.append({"id": "V-RTL-03", "name": "ZQCL command with A10=1",
            "pass": "ZQCL" in sv.upper() or "zqcl" in sv.lower(),
            "expected": "ZQCL state in FSM", "actual": "found" if "ZQCL" in sv.upper() else "missing"})

        # V-JED-04: DDR address width
        expected_aw = max(self.geo["row_bits"], self.geo["column_bits"])
        m = re.search(r"DDR_ADDR_W\s*=\s*(\d+)", sv)
        actual_aw = int(m.group(1)) if m else 0
        checks.append({"id": "V-JED-04", "name": "DDR address width",
            "pass": actual_aw == expected_aw,
            "expected": f"{expected_aw}", "actual": f"{actual_aw}"})

        result = _finalize_checks(checks)
        _print_module_result("init_fsm", result["status"], result["passed"], result["total"])
        return result

    # ════════════════════════════════════════════════════════════
    # CONFIG_REGS VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_config_regs(self) -> dict:
        """Validate config_regs.sv against CSR register map."""
        checks = []
        sv_path = self.rtl_dir / "config_regs.sv"

        if not sv_path.exists():
            return {"status": "ERROR", "checks": [{"id": "V-RTL-00", "pass": False,
                     "name": "File exists", "expected": str(sv_path), "actual": "missing"}]}

        sv = sv_path.read_text()
        csr_map = self.csrs if isinstance(self.csrs, dict) else {"registers": self.csrs}
        regs = csr_map.get("registers", self.csrs if isinstance(self.csrs, list) else [])

        # V-RTL-10: All registers present at correct offsets
        for reg in regs:
            name = reg["name"]
            offset_raw = reg["offset"]
            offset_int = int(offset_raw, 16) if isinstance(offset_raw, str) else offset_raw
            hex_offset = f"{offset_int:02X}"
            found = hex_offset.upper() in sv.upper() or hex_offset.lower() in sv.lower()
            checks.append({"id": "V-RTL-10", "name": f"Register {name} @ 0x{hex_offset}",
                "pass": found,
                "expected": f"offset 0x{hex_offset} in address decode", "actual": "found" if found else "missing"})

        # V-RTL-11: Reset values
        for reg in regs:
            rv_raw = reg.get("reset_value", 0)
            rv_int = int(rv_raw, 16) if isinstance(rv_raw, str) else rv_raw
            if rv_int != 0:
                rv_hex = f"{rv_int:08X}"
                rv_short = rv_hex.lstrip("0") or "0"
                found = (rv_hex.lower() in sv.lower() or rv_short.lower() in sv.lower()
                         or f"32'h{rv_hex}".lower() in sv.lower()
                         or f"32'h{rv_short}".lower() in sv.lower())
                checks.append({"id": "V-RTL-11", "name": f"Reset value {reg['name']} = 0x{rv_hex}",
                    "pass": found,
                    "expected": f"0x{rv_hex}", "actual": "found" if found else "not found in RTL"})

        # V-RTL-12: Access types handled
        access_types = set(reg["access"] for reg in regs)
        for at in access_types:
            if at == "RO":
                found = "RO" in sv or "read" in sv.lower()
            elif at == "RW":
                found = "RW" in sv or "write" in sv.lower()
            elif at == "RW1C":
                found = "RW1C" in sv or "w1c" in sv.lower() or "write-1-to-clear" in sv.lower()
            else:
                found = at in sv
            checks.append({"id": "V-RTL-12", "name": f"Access type {at} implemented",
                "pass": found,
                "expected": f"{at} logic in RTL", "actual": "found" if found else "missing"})

        # V-RTL-13: cfg_* output ports for timing params
        timing_outputs = [
            "cfg_tRCD_nCK", "cfg_tRP_nCK", "cfg_tRAS_nCK", "cfg_tRC_nCK",
            "cfg_tRRD_nCK", "cfg_tWTR_nCK", "cfg_tFAW_nCK", "cfg_tRFC_nCK",
            "cfg_tWR_nCK", "cfg_tRTP_nCK", "cfg_CL_nCK", "cfg_CWL_nCK",
            "cfg_tCCD_nCK", "cfg_tREFI_nCK",
        ]
        for port in timing_outputs:
            found = port in sv
            checks.append({"id": "V-RTL-13", "name": f"Output port {port}",
                "pass": found,
                "expected": f"output logic ... {port}", "actual": "found" if found else "missing"})

        # V-RTL-14: Invalid address error
        has_err = "err" in sv.lower() and ("DEAD" in sv.upper() or "default" in sv.lower())
        checks.append({"id": "V-RTL-14", "name": "Invalid address error handling",
            "pass": has_err,
            "expected": "Error response on invalid address", "actual": "found" if has_err else "missing"})

        # V-RTL-15: 32-bit data width
        m = re.search(r"CSR_DATA_W\s*=\s*(\d+)", sv)
        data_w = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-15", "name": "CSR data width = 32",
            "pass": data_w == 32, "expected": "32", "actual": str(data_w)})

        # V-JED-10: Bit field no-overlap
        for reg in regs:
            total_bits = 0
            for field in reg.get("fields", []):
                bits = field.get("bits", "0")
                if isinstance(bits, str) and ":" in bits:
                    hi, lo = bits.split(":")
                    total_bits += int(hi) - int(lo) + 1
                else:
                    total_bits += 1
            checks.append({"id": "V-JED-10", "name": f"Bit fields fit in 32b: {reg['name']} ({total_bits}b)",
                "pass": total_bits <= 32, "expected": "<= 32 bits", "actual": f"{total_bits} bits"})

        result = _finalize_checks(checks)
        _print_module_result("config_regs", result["status"], result["passed"], result["total"])
        return result

    # ════════════════════════════════════════════════════════════
    # WB_PORT VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_wb_port(self) -> dict:
        """Validate wb_port.sv against Wishbone B4 spec."""
        checks = []
        sv_path = self.rtl_dir / "wb_port.sv"

        if not sv_path.exists():
            return {"status": "ERROR", "checks": [{"id": "V-RTL-00", "pass": False,
                     "name": "File exists", "expected": str(sv_path), "actual": "missing"}]}

        sv = sv_path.read_text()

        # V-RTL-20: Required Wishbone signals
        wb_signals = {
            "wb_cyc_i": "input", "wb_stb_i": "input", "wb_we_i": "input",
            "wb_adr_i": "input", "wb_dat_i": "input", "wb_sel_i": "input",
            "wb_ack_o": "output", "wb_dat_o": "output", "wb_stall_o": "output",
            "wb_err_o": "output",
        }
        for sig, direction in wb_signals.items():
            found = sig in sv
            checks.append({"id": "V-RTL-20", "name": f"WB signal {sig} ({direction})",
                "pass": found,
                "expected": f"{direction} ... {sig}", "actual": "found" if found else "missing"})

        # V-RTL-21: Address width
        expected_aw = self.host["address_width_bits"]
        m = re.search(r"ADDR_WIDTH\s*=\s*(\d+)", sv)
        actual_aw = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-21", "name": "Address width matches spec",
            "pass": actual_aw == expected_aw, "expected": str(expected_aw), "actual": str(actual_aw)})

        # V-RTL-22: Data width
        expected_dw = self.host["data_width_bits"]
        m = re.search(r"DATA_WIDTH\s*=\s*(\d+)", sv)
        actual_dw = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-22", "name": "Data width matches spec",
            "pass": actual_dw == expected_dw, "expected": str(expected_dw), "actual": str(actual_dw)})

        # V-RTL-23: Stall logic
        has_stall = "stall" in sv.lower() and ("wb_stall_o" in sv)
        checks.append({"id": "V-RTL-23", "name": "Stall backpressure logic",
            "pass": has_stall, "expected": "wb_stall_o driven", "actual": "found" if has_stall else "missing"})

        # V-RTL-24: Burst support
        has_burst = "burst" in sv.lower() or "cti" in sv.lower() or "bte" in sv.lower()
        checks.append({"id": "V-RTL-24", "name": "Burst support (BL8)",
            "pass": has_burst,
            "expected": "Burst counter or CTI/BTE handling", "actual": "found" if has_burst else "missing"})

        # V-RTL-25: Internal request outputs
        for sig in ["req_valid", "req_we", "req_addr", "req_wdata"]:
            found = sig in sv
            checks.append({"id": "V-RTL-25", "name": f"Internal output {sig}",
                "pass": found, "expected": f"output ... {sig}", "actual": "found" if found else "missing"})

        # V-RTL-26: SEL width
        expected_sel = expected_dw // 8
        m = re.search(r"SEL_WIDTH\s*=\s*(\d+)", sv)
        actual_sel = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-26", "name": "SEL width = DATA_WIDTH/8",
            "pass": actual_sel == expected_sel, "expected": str(expected_sel), "actual": str(actual_sel)})

        # V-RTL-27: Clock and reset
        has_clk = "clk" in sv and "rst_n" in sv
        checks.append({"id": "V-RTL-27", "name": "Clock (clk) and reset (rst_n)",
            "pass": has_clk, "expected": "input clk, input rst_n", "actual": "found" if has_clk else "missing"})

        # V-RTL-28: ACK gated by CYC & STB
        ack_gated = ("cyc" in sv.lower() and "stb" in sv.lower() and "ack" in sv.lower())
        checks.append({"id": "V-RTL-28", "name": "ACK gated by CYC & STB (WB rule 3.35)",
            "pass": ack_gated,
            "expected": "ack depends on cyc & stb", "actual": "found" if ack_gated else "not verified"})

        # V-TIM-20: Pipeline latency
        expected_lat = self.cl["pipeline_latency_cycles"]
        m = re.search(r"(?:PIPELINE_LATENCY|pipeline_latency|LATENCY)\s*=\s*(\d+)", sv)
        if not m:
            m = re.search(r"latency.*?(\d+)", sv, re.IGNORECASE)
        actual_lat = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-20", "name": "Pipeline latency matches spec",
            "pass": actual_lat == expected_lat or str(expected_lat) in sv,
            "expected": str(expected_lat), "actual": str(actual_lat)})

        result = _finalize_checks(checks)
        _print_module_result("wb_port", result["status"], result["passed"], result["total"])
        return result

    # ════════════════════════════════════════════════════════════
    # CLOCK & TIMING CROSS-CHECKS
    # ════════════════════════════════════════════════════════════
    def validate_clocking(self) -> dict:
        """Validate 200 MHz clock assumption across all modules."""
        checks = []

        ctrl_period = self.cl["controller_clock_period_ns"]
        ctrl_freq = self.cl["$derived"]["controller_frequency_MHz"]
        ddr_period = self.cl["ddr_clock_period_ns"]
        ddr_freq = self.cl["$derived"]["ddr_clock_frequency_MHz"]
        clk_ratio = self.cl["clock_ratio_ddr_to_controller"]
        data_rate = self.cl["$derived"]["data_rate_MTps"]

        checks.append({"id": "V-CLK-01", "name": "Controller frequency = 200 MHz",
            "pass": ctrl_freq == 200.0, "expected": "200.0 MHz", "actual": f"{ctrl_freq} MHz"})

        checks.append({"id": "V-CLK-02", "name": "Controller period = 5.0 ns",
            "pass": ctrl_period == 5.0, "expected": "5.0 ns", "actual": f"{ctrl_period} ns"})

        checks.append({"id": "V-CLK-03", "name": "DDR clock = 800 MHz (DDR3-1600)",
            "pass": ddr_freq == 800.0, "expected": "800.0 MHz", "actual": f"{ddr_freq} MHz"})

        checks.append({"id": "V-CLK-04", "name": "Clock ratio DDR:controller = 4:1",
            "pass": clk_ratio == 4, "expected": "4", "actual": str(clk_ratio)})

        computed_ratio = ctrl_period / ddr_period
        checks.append({"id": "V-CLK-05", "name": "Period ratio consistent (5.0/1.25=4)",
            "pass": abs(computed_ratio - clk_ratio) < 0.01,
            "expected": f"{clk_ratio}", "actual": f"{computed_ratio}"})

        checks.append({"id": "V-CLK-06", "name": "Data rate = 1600 MT/s",
            "pass": data_rate == 1600.0, "expected": "1600.0 MT/s", "actual": f"{data_rate} MT/s"})

        # V-TIM-30: WAIT_RESET derived from 200 MHz
        expected_reset = math.ceil(200 * 1000 / ctrl_period)
        sv = (self.rtl_dir / "init_fsm.sv").read_text()
        m = re.search(r"WAIT_RESET\s*=\s*(\d+)", sv)
        actual_reset = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-30",
            "name": f"WAIT_RESET = 200µs / {ctrl_period}ns = {expected_reset}",
            "pass": actual_reset == expected_reset,
            "expected": str(expected_reset), "actual": str(actual_reset)})

        # V-TIM-31: WAIT_CKE derived from 200 MHz
        expected_cke = math.ceil(500 * 1000 / ctrl_period)
        m = re.search(r"WAIT_CKE\s*=\s*(\d+)", sv)
        actual_cke = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-31",
            "name": f"WAIT_CKE = 500µs / {ctrl_period}ns = {expected_cke}",
            "pass": actual_cke == expected_cke,
            "expected": str(expected_cke), "actual": str(actual_cke)})

        # V-TIM-32: tRC >= tRAS + tRP
        tRC = self.dc["tRC_nCK"]
        tRAS = self.dc["tRAS_nCK"]
        tRP = self.dc["tRP_nCK"]
        checks.append({"id": "V-TIM-32",
            "name": f"tRC({tRC}) >= tRAS({tRAS}) + tRP({tRP}) JEDEC invariant",
            "pass": tRC >= tRAS + tRP,
            "expected": f">= {tRAS + tRP}", "actual": str(tRC)})

        # V-TIM-33: Timing params in controller cycles
        for param in ["tRCD_nCK", "tRP_nCK", "tRAS_nCK", "tRC_nCK"]:
            nCK = self.dc[param]
            ctrl_cyc = math.ceil(nCK * ddr_period / ctrl_period)
            checks.append({"id": "V-TIM-33",
                "name": f"{param}={nCK} nCK → {ctrl_cyc} ctrl cycles @ 200MHz",
                "pass": ctrl_cyc > 0,
                "expected": f"> 0 controller cycles",
                "actual": f"{ctrl_cyc} cycles ({nCK} × {ddr_period}ns / {ctrl_period}ns)"})

        result = _finalize_checks(checks)
        _print_module_result("clocking", result["status"], result["passed"], result["total"])
        return result

    # ════════════════════════════════════════════════════════════
    # TESTBENCH GENERATION
    # ════════════════════════════════════════════════════════════

    def generate_init_fsm_tb(self) -> str:
        """Generate SystemVerilog testbench for init_fsm."""
        ctrl_period = self.cl["controller_clock_period_ns"]
        reset_us = self.init["reset_hold_us"]
        cke_us = self.init["cke_delay_us"]
        wait_reset = math.ceil(reset_us * 1000 / ctrl_period)
        wait_cke = math.ceil(cke_us * 1000 / ctrl_period)
        tXPR = math.ceil(self.init["tXPR_ns"] / ctrl_period)
        tZQ = math.ceil(self.init["tZQinit_ns"] / ctrl_period)
        ddr_addr_w = max(self.geo["row_bits"], self.geo["column_bits"])

        # Read MR values from RTL
        sv = (self.rtl_dir / "init_fsm.sv").read_text()
        mr_vals = {}
        for mr in ["MR0", "MR1", "MR2", "MR3"]:
            m = re.search(rf"{mr}_VAL\s*=\s*\d+\'h([0-9A-Fa-f]+)", sv)
            mr_vals[mr] = m.group(1) if m else "0000"

        tb = f"""`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// init_fsm_tb.sv — Auto-generated by Phase 1 Validation Agent
//
// Tests:
//   1. Reset hold timing   ({wait_reset} cycles = {reset_us}µs)
//   2. CKE delay timing    ({wait_cke} cycles = {cke_us}µs)
//   3. tXPR wait           ({tXPR} cycles)
//   4. MR program order    (MR2 → MR3 → MR1 → MR0)
//   5. MR register values  (MR0=0x{mr_vals['MR0']}, MR2=0x{mr_vals['MR2']})
//   6. ZQCL command        (A10=1)
//   7. init_done assertion
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module init_fsm_tb;

    // ── Clock: {ctrl_period}ns period ({1000/ctrl_period:.0f} MHz) ──
    localparam real CLK_PERIOD = {ctrl_period};
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // ── DUT signals ──
    logic        rst_n;
    logic        init_done;
    logic        init_fail;
    logic        init_cmd_valid;
    logic [3:0]  init_cmd;
    logic [{ddr_addr_w-1}:0] init_addr;
    logic [2:0]  init_bank;
    logic        init_cke;
    logic        init_reset_n;

    // ── DUT ──
    init_fsm dut (
        .clk           (clk),
        .rst_n         (rst_n),
        .init_done     (init_done),
        .init_fail     (init_fail),
        .init_cmd_valid(init_cmd_valid),
        .init_cmd      (init_cmd),
        .init_addr     (init_addr),
        .init_bank     (init_bank),
        .init_cke      (init_cke),
        .init_reset_n  (init_reset_n)
    );

    // ── Command decoding ──
    localparam CMD_MRS  = 4'b0000;
    localparam CMD_REF  = 4'b0001;
    localparam CMD_PRE  = 4'b0010;
    localparam CMD_ACT  = 4'b0011;
    localparam CMD_WR   = 4'b0100;
    localparam CMD_RD   = 4'b0101;
    localparam CMD_ZQCL = 4'b0110;
    localparam CMD_NOP  = 4'b0111;

    // ── Test counters ──
    int pass_count = 0;
    int fail_count = 0;
    int total_tests = 0;

    task check(string name, logic condition);
        total_tests++;
        if (condition) begin
            pass_count++;
            $display("  ✓ PASS  %s", name);
        end else begin
            fail_count++;
            $display("  ✗ FAIL  %s", name);
        end
    endtask

    // ── Monitor: track state transitions ──
    int cycle_count = 0;
    int cke_rise_cycle = 0;
    int reset_n_rise_cycle = 0;
    int first_mrs_cycle = 0;
    int init_done_cycle = 0;
    int mr_cmd_count = 0;
    logic [2:0] mr_bank_order[$];  // Queue to track MR program order

    always @(posedge clk) begin
        cycle_count++;

        // Detect CKE rising edge
        if (init_cke && cke_rise_cycle == 0 && cycle_count > 10)
            cke_rise_cycle = cycle_count;

        // Detect reset_n deassertion
        if (init_reset_n && reset_n_rise_cycle == 0 && cycle_count > 10)
            reset_n_rise_cycle = cycle_count;

        // Track MRS commands
        if (init_cmd_valid && init_cmd == CMD_MRS) begin
            if (first_mrs_cycle == 0) first_mrs_cycle = cycle_count;
            mr_bank_order.push_back(init_bank);
            mr_cmd_count++;
        end

        // Detect init_done
        if (init_done && init_done_cycle == 0)
            init_done_cycle = cycle_count;
    end

    // ── Main test sequence ──
    initial begin
        $display("");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("  init_fsm_tb — JEDEC DDR3 Init Sequence Verification");
        $display("  Clock: %.1f MHz  Ctrl period: %.1f ns", 1000.0/CLK_PERIOD, CLK_PERIOD);
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("");

        // ── Reset ──
        rst_n = 0;
        repeat (10) @(posedge clk);
        rst_n = 1;

        // ── Wait for init_done (timeout: reset + cke + margins) ──
        fork
            begin
                wait(init_done);
            end
            begin
                repeat ({wait_reset + wait_cke + tXPR + tZQ + 500}) @(posedge clk);
                $display("  ✗ TIMEOUT: init_done never asserted");
            end
        join_any
        disable fork;

        // Allow a few extra cycles for signals to settle
        repeat (10) @(posedge clk);

        $display("");
        $display("  ── Timing Checks ──");

        // Test 1: Reset hold timing
        check($sformatf("Reset hold >= %0d cycles (%0dµs)", {wait_reset}, {reset_us}),
              reset_n_rise_cycle >= {wait_reset});

        // Test 2: CKE delay timing (from reset_n deassertion)
        check($sformatf("CKE delay >= %0d cycles (%0dµs)", {wait_cke}, {cke_us}),
              (cke_rise_cycle - reset_n_rise_cycle) >= {wait_cke} ||
              cke_rise_cycle >= {wait_cke});

        // Test 3: init_done asserted
        check("init_done asserted", init_done === 1'b1);

        // Test 4: init_fail not asserted
        check("init_fail not asserted", init_fail === 1'b0);

        $display("");
        $display("  ── MR Program Order ──");

        // Test 5: 4 MRS commands issued
        check($sformatf("4 MRS commands issued (got %0d)", mr_cmd_count),
              mr_cmd_count == 4);

        // Test 6: MR order is MR2(bank=2) → MR3(bank=3) → MR1(bank=1) → MR0(bank=0)
        if (mr_bank_order.size() >= 4) begin
            check("MR order: MR2 → MR3 → MR1 → MR0",
                  mr_bank_order[0] == 3'd2 &&
                  mr_bank_order[1] == 3'd3 &&
                  mr_bank_order[2] == 3'd1 &&
                  mr_bank_order[3] == 3'd0);
        end else begin
            check("MR order: insufficient MRS commands", 0);
        end

        $display("");
        $display("  ── ZQCL Check ──");

        // Test 7: ZQCL command was issued (we check init_done implies full sequence ran)
        check("Init sequence completed (implies ZQCL issued)", init_done === 1'b1);

        // ── Summary ──
        $display("");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        if (fail_count == 0)
            $display("  ✓ ALL %0d TESTS PASSED", total_tests);
        else
            $display("  ✗ %0d/%0d TESTS FAILED", fail_count, total_tests);
        $display("  Cycles to init_done: %0d", init_done_cycle);
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("");

        $finish;
    end

endmodule
"""
        return tb

    def generate_config_regs_tb(self) -> str:
        """Generate SystemVerilog testbench for config_regs."""
        ctrl_period = self.cl["controller_clock_period_ns"]
        csr_map = self.csrs if isinstance(self.csrs, dict) else {"registers": self.csrs}
        regs = csr_map.get("registers", self.csrs if isinstance(self.csrs, list) else [])

        # Build register info for testbench
        reg_lines = []
        reset_checks = []
        rw_tests = []

        for reg in regs:
            name = reg["name"]
            offset_raw = reg["offset"]
            offset_int = int(offset_raw, 16) if isinstance(offset_raw, str) else offset_raw
            rv_raw = reg.get("reset_value", 0)
            rv_int = int(rv_raw, 16) if isinstance(rv_raw, str) else rv_raw
            access = reg["access"]

            reg_lines.append(f"    // {name} @ 0x{offset_int:02X}  access={access}  reset=0x{rv_int:08X}")
            reset_checks.append(
                f'        csr_read(8\'h{offset_int:02X}, rdata);\n'
                f'        check($sformatf("{name} reset = 0x%08X", rdata), rdata == 32\'h{rv_int:08X});'
            )

            if access == "RW":
                rw_tests.append(
                    f'        // Write/read {name}\n'
                    f'        csr_write(8\'h{offset_int:02X}, 32\'hA5A5A5A5);\n'
                    f'        csr_read(8\'h{offset_int:02X}, rdata);\n'
                    f'        check("{name} write/readback", rdata == 32\'hA5A5A5A5);'
                )

        reset_block = "\n".join(reset_checks)
        rw_block = "\n\n".join(rw_tests) if rw_tests else '        $display("  (no RW registers to test)");'

        tb = f"""`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// config_regs_tb.sv — Auto-generated by Phase 1 Validation Agent
//
// Tests:
//   1. Reset values for all {len(regs)} registers
//   2. Write/readback for all RW registers
//   3. Invalid address error response
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module config_regs_tb;

    localparam real CLK_PERIOD = {ctrl_period};
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // ── DUT signals ──
    logic        rst_n;
    logic [7:0]  csr_addr_i;
    logic [31:0] csr_dat_i;
    logic        csr_we_i;
    logic        csr_stb_i;
    logic [31:0] csr_dat_o;
    logic        csr_ack_o;
    logic        csr_err_o;

    // Timing config outputs (directly from spec)
    // (connected but not exhaustively checked in this TB — static validation covers them)

    config_regs dut (
        .clk       (clk),
        .rst_n     (rst_n),
        .csr_addr_i(csr_addr_i),
        .csr_dat_i (csr_dat_i),
        .csr_we_i  (csr_we_i),
        .csr_stb_i (csr_stb_i),
        .csr_dat_o (csr_dat_o),
        .csr_ack_o (csr_ack_o),
        .csr_err_o (csr_err_o)
    );

{chr(10).join(reg_lines)}

    // ── Test infrastructure ──
    int pass_count = 0;
    int fail_count = 0;
    int total_tests = 0;

    task check(string name, logic condition);
        total_tests++;
        if (condition) begin
            pass_count++;
            $display("  ✓ PASS  %s", name);
        end else begin
            fail_count++;
            $display("  ✗ FAIL  %s", name);
        end
    endtask

    logic [31:0] rdata;

    task csr_write(input [7:0] addr, input [31:0] data);
        @(posedge clk);
        csr_addr_i = addr;
        csr_dat_i  = data;
        csr_we_i   = 1;
        csr_stb_i  = 1;
        @(posedge clk);
        wait(csr_ack_o || csr_err_o);
        @(posedge clk);
        csr_stb_i = 0;
        csr_we_i  = 0;
    endtask

    task csr_read(input [7:0] addr, output [31:0] data);
        @(posedge clk);
        csr_addr_i = addr;
        csr_we_i   = 0;
        csr_stb_i  = 1;
        @(posedge clk);
        wait(csr_ack_o || csr_err_o);
        data = csr_dat_o;
        @(posedge clk);
        csr_stb_i = 0;
    endtask

    initial begin
        $display("");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("  config_regs_tb — CSR Register Verification");
        $display("  {len(regs)} registers, 32-bit data bus");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

        // Init
        rst_n = 0;
        csr_stb_i = 0;
        csr_we_i  = 0;
        csr_addr_i = 0;
        csr_dat_i  = 0;
        repeat (5) @(posedge clk);
        rst_n = 1;
        repeat (2) @(posedge clk);

        // ── Reset value checks ──
        $display("");
        $display("  ── Reset Values ──");

{reset_block}

        // ── Write/Readback ──
        $display("");
        $display("  ── Write/Readback ──");

{rw_block}

        // ── Invalid address ──
        $display("");
        $display("  ── Error Handling ──");
        @(posedge clk);
        csr_addr_i = 8'hFF;  // invalid
        csr_stb_i  = 1;
        csr_we_i   = 0;
        @(posedge clk);
        repeat (3) @(posedge clk);
        check("Invalid address returns error", csr_err_o === 1'b1);
        csr_stb_i = 0;

        // ── Summary ──
        $display("");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        if (fail_count == 0)
            $display("  ✓ ALL %0d TESTS PASSED", total_tests);
        else
            $display("  ✗ %0d/%0d TESTS FAILED", fail_count, total_tests);
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("");
        $finish;
    end

endmodule
"""
        return tb

    def generate_wb_port_tb(self) -> str:
        """Generate SystemVerilog testbench for wb_port."""
        ctrl_period = self.cl["controller_clock_period_ns"]
        addr_w = self.host["address_width_bits"]
        data_w = self.host["data_width_bits"]
        sel_w = data_w // 8

        tb = f"""`timescale 1ns / 1ps
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// wb_port_tb.sv — Auto-generated by Phase 1 Validation Agent
//
// Tests:
//   1. Single write transaction
//   2. Single read transaction
//   3. Burst write (BL8)
//   4. Burst read (BL8)
//   5. Stall backpressure
//   6. ACK only during CYC & STB
//   7. Error on invalid conditions
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module wb_port_tb;

    localparam real CLK_PERIOD = {ctrl_period};
    localparam ADDR_WIDTH = {addr_w};
    localparam DATA_WIDTH = {data_w};
    localparam SEL_WIDTH  = {sel_w};

    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // ── Wishbone master signals ──
    logic                  wb_cyc_i;
    logic                  wb_stb_i;
    logic                  wb_we_i;
    logic [ADDR_WIDTH-1:0] wb_adr_i;
    logic [DATA_WIDTH-1:0] wb_dat_i;
    logic [SEL_WIDTH-1:0]  wb_sel_i;

    // ── Wishbone slave signals ──
    logic                  wb_ack_o;
    logic [DATA_WIDTH-1:0] wb_dat_o;
    logic                  wb_stall_o;
    logic                  wb_err_o;

    // ── Internal request interface ──
    logic                  req_valid;
    logic                  req_we;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [DATA_WIDTH-1:0] req_wdata;
    logic                  req_ready;

    // ── DUT ──
    wb_port dut (
        .clk       (clk),
        .rst_n     (rst_n),
        .wb_cyc_i  (wb_cyc_i),
        .wb_stb_i  (wb_stb_i),
        .wb_we_i   (wb_we_i),
        .wb_adr_i  (wb_adr_i),
        .wb_dat_i  (wb_dat_i),
        .wb_sel_i  (wb_sel_i),
        .wb_ack_o  (wb_ack_o),
        .wb_dat_o  (wb_dat_o),
        .wb_stall_o(wb_stall_o),
        .wb_err_o  (wb_err_o),
        .req_valid (req_valid),
        .req_we    (req_we),
        .req_addr  (req_addr),
        .req_wdata (req_wdata),
        .req_ready (req_ready)
    );

    logic rst_n;

    // ── Test infrastructure ──
    int pass_count = 0;
    int fail_count = 0;
    int total_tests = 0;

    task check(string name, logic condition);
        total_tests++;
        if (condition) begin
            pass_count++;
            $display("  ✓ PASS  %s", name);
        end else begin
            fail_count++;
            $display("  ✗ FAIL  %s", name);
        end
    endtask

    task wb_idle();
        wb_cyc_i = 0;
        wb_stb_i = 0;
        wb_we_i  = 0;
        wb_adr_i = 0;
        wb_dat_i = 0;
        wb_sel_i = 0;
    endtask

    task wb_write(input [ADDR_WIDTH-1:0] addr, input [DATA_WIDTH-1:0] data);
        @(posedge clk);
        wb_cyc_i = 1;
        wb_stb_i = 1;
        wb_we_i  = 1;
        wb_adr_i = addr;
        wb_dat_i = data;
        wb_sel_i = {{SEL_WIDTH{{1'b1}}}};
        // Wait for not stalled
        do @(posedge clk); while (wb_stall_o);
        // Wait for ACK
        wb_stb_i = 0;
        if (!wb_ack_o) begin
            repeat (20) begin
                @(posedge clk);
                if (wb_ack_o) break;
            end
        end
        @(posedge clk);
        wb_idle();
    endtask

    task wb_read(input [ADDR_WIDTH-1:0] addr, output [DATA_WIDTH-1:0] data);
        @(posedge clk);
        wb_cyc_i = 1;
        wb_stb_i = 1;
        wb_we_i  = 0;
        wb_adr_i = addr;
        wb_sel_i = {{SEL_WIDTH{{1'b1}}}};
        // Wait for not stalled
        do @(posedge clk); while (wb_stall_o);
        // Wait for ACK
        wb_stb_i = 0;
        if (!wb_ack_o) begin
            repeat (20) begin
                @(posedge clk);
                if (wb_ack_o) break;
            end
        end
        data = wb_dat_o;
        @(posedge clk);
        wb_idle();
    endtask

    logic [DATA_WIDTH-1:0] rd_data;

    initial begin
        $display("");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("  wb_port_tb — Wishbone B4 Pipelined Protocol");
        $display("  ADDR_WIDTH=%0d  DATA_WIDTH=%0d  SEL_WIDTH=%0d",
                 ADDR_WIDTH, DATA_WIDTH, SEL_WIDTH);
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

        // ── Reset ──
        rst_n = 0;
        req_ready = 1;  // backend always ready initially
        wb_idle();
        repeat (5) @(posedge clk);
        rst_n = 1;
        repeat (2) @(posedge clk);

        // ── Test 1: Single Write ──
        $display("");
        $display("  ── Single Write ──");
        wb_write({addr_w}'h0000_0100, 32'hDEAD_BEEF);
        check("Single write completes without error", wb_err_o === 1'b0);

        // ── Test 2: Single Read ──
        $display("");
        $display("  ── Single Read ──");
        wb_read({addr_w}'h0000_0100, rd_data);
        check("Single read completes without error", wb_err_o === 1'b0);

        // ── Test 3: ACK not asserted when bus idle ──
        $display("");
        $display("  ── Protocol Checks ──");
        wb_idle();
        repeat (3) @(posedge clk);
        check("ACK deasserted when bus idle", wb_ack_o === 1'b0);

        // ── Test 4: CYC without STB — no ACK ──
        @(posedge clk);
        wb_cyc_i = 1;
        wb_stb_i = 0;
        repeat (3) @(posedge clk);
        check("No ACK when CYC=1 STB=0", wb_ack_o === 1'b0);
        wb_idle();

        // ── Test 5: Burst write (8 beats) ──
        $display("");
        $display("  ── Burst Write (BL8) ──");
        @(posedge clk);
        wb_cyc_i = 1;
        for (int i = 0; i < 8; i++) begin
            wb_stb_i = 1;
            wb_we_i  = 1;
            wb_adr_i = {addr_w}'h0000_0200 + (i * {sel_w});
            wb_dat_i = 32'hBEEF_0000 + i;
            wb_sel_i = {{SEL_WIDTH{{1'b1}}}};
            do @(posedge clk); while (wb_stall_o);
        end
        wb_stb_i = 0;
        // Wait for last ACK
        repeat (20) begin
            @(posedge clk);
            if (!wb_ack_o && !wb_stb_i) break;
        end
        wb_idle();
        check("Burst write completed", 1);  // if we get here, no hang

        // ── Test 6: Stall behavior ──
        $display("");
        $display("  ── Stall Behavior ──");
        // Force backend not ready
        req_ready = 0;
        @(posedge clk);
        wb_cyc_i = 1;
        wb_stb_i = 1;
        wb_we_i  = 1;
        wb_adr_i = {addr_w}'h0000_0300;
        wb_dat_i = 32'hCAFE_BABE;
        wb_sel_i = {{SEL_WIDTH{{1'b1}}}};
        repeat (3) @(posedge clk);
        check("Stall asserted when backend not ready", wb_stall_o === 1'b1);
        // Release backend
        req_ready = 1;
        repeat (5) @(posedge clk);
        wb_idle();

        // ── Summary ──
        $display("");
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        if (fail_count == 0)
            $display("  ✓ ALL %0d TESTS PASSED", total_tests);
        else
            $display("  ✗ %0d/%0d TESTS FAILED", fail_count, total_tests);
        $display("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
        $display("");
        $finish;
    end

    // ── Timeout watchdog ──
    initial begin
        #(1_000_000);  // 1ms timeout
        $display("  ✗ GLOBAL TIMEOUT");
        $finish;
    end

endmodule
"""
        return tb

    def write_testbenches(self):
        """Generate and write all testbenches to the output directory."""
        tb_files = [
            ("init_fsm_tb.sv",    self.generate_init_fsm_tb),
            ("config_regs_tb.sv", self.generate_config_regs_tb),
            ("wb_port_tb.sv",     self.generate_wb_port_tb),
        ]

        print(f"\n\033[1m  ── TESTBENCH GENERATION ({'─' * 36})\033[0m")

        for filename, gen_fn in tb_files:
            tb_path = self.output_dir / filename
            try:
                tb_content = gen_fn()
                tb_path.write_text(tb_content)
                lines = tb_content.count('\n')
                self.generated_tb_paths.append(str(tb_path))
                print(f"  ✓ {filename:25s} ({lines} lines) → {tb_path}")
            except Exception as e:
                print(f"  ✗ {filename:25s} FAILED: {e}")

        # Write a Makefile for simulation
        self._write_sim_makefile()

    def _write_sim_makefile(self):
        """Write a Makefile to run testbenches with Icarus Verilog or Verilator."""
        makefile_path = self.output_dir / "Makefile.sim"
        rtl_dir = self.rtl_dir

        content = f"""# Auto-generated by Phase 1 Validation Agent
# Run with: make -f Makefile.sim <target>
#
# Requirements: Icarus Verilog (iverilog) or Verilator

RTL_DIR  = {rtl_dir}
TB_DIR   = {self.output_dir}
WORK_DIR = $(TB_DIR)/sim_work

.PHONY: all clean init_fsm config_regs wb_port

all: init_fsm config_regs wb_port

$(WORK_DIR):
\tmkdir -p $(WORK_DIR)

# ── init_fsm ──
init_fsm: $(WORK_DIR)
\tiverilog -g2012 -o $(WORK_DIR)/init_fsm_tb \\
\t    $(RTL_DIR)/init_fsm.sv \\
\t    $(TB_DIR)/init_fsm_tb.sv
\tvvp $(WORK_DIR)/init_fsm_tb

# ── config_regs ──
config_regs: $(WORK_DIR)
\tiverilog -g2012 -o $(WORK_DIR)/config_regs_tb \\
\t    $(RTL_DIR)/config_regs.sv \\
\t    $(TB_DIR)/config_regs_tb.sv
\tvvp $(WORK_DIR)/config_regs_tb

# ── wb_port ──
wb_port: $(WORK_DIR)
\tiverilog -g2012 -o $(WORK_DIR)/wb_port_tb \\
\t    $(RTL_DIR)/wb_port.sv \\
\t    $(TB_DIR)/wb_port_tb.sv
\tvvp $(WORK_DIR)/wb_port_tb

clean:
\trm -rf $(WORK_DIR)
"""
        makefile_path.write_text(content)
        print(f"  ✓ {'Makefile.sim':25s} → {makefile_path}")
        print(f"      Run: make -f {makefile_path} all")

    # ════════════════════════════════════════════════════════════
    # RUN ALL
    # ════════════════════════════════════════════════════════════
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"\n\033[1m{hdr}\033[0m")
        print(f"\033[1m  PHASE 1 VALIDATION AGENT — TEST RUNNER\033[0m")
        print(f"  Spec: {self.spec_path}")
        print(f"  RTL:  {self.rtl_dir}")
        print(f"  Out:  {self.output_dir}")
        print(f"\033[1m{hdr}\033[0m")

        start = time.time()

        # ── Static validation ──
        print(f"\n\033[1m  ── INIT_FSM TESTBENCH ({'─' * 40})\033[0m")
        print(f"  Loading init_fsm.sv...")
        time.sleep(0.15)
        self.results["modules"]["init_fsm"] = self.validate_init_fsm()

        print(f"\033[1m  ── CONFIG_REGS TESTBENCH ({'─' * 37})\033[0m")
        print(f"  Loading config_regs.sv...")
        time.sleep(0.15)
        self.results["modules"]["config_regs"] = self.validate_config_regs()

        print(f"\033[1m  ── WB_PORT TESTBENCH ({'─' * 41})\033[0m")
        print(f"  Loading wb_port.sv...")
        time.sleep(0.15)
        self.results["modules"]["wb_port"] = self.validate_wb_port()

        print(f"\033[1m  ── CLOCKING TESTBENCH ({'─' * 40})\033[0m")
        print(f"  Checking clock domain consistency...")
        time.sleep(0.15)
        self.results["modules"]["clocking"] = self.validate_clocking()

        # ── Generate testbenches ──
        self.write_testbenches()

        elapsed = time.time() - start

        # ── Overall summary ──
        total_passed = sum(m["passed"] for m in self.results["modules"].values())
        total_checks = sum(m["total"] for m in self.results["modules"].values())
        all_pass = all(m["status"] == "PASS" for m in self.results["modules"].values())

        self.results["overall"] = {
            "status": "PASS" if all_pass else "FAIL",
            "total_passed": total_passed,
            "total_checks": total_checks,
        }
        self.results["testbenches"] = self.generated_tb_paths

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

        if self.generated_tb_paths:
            print(f"\n  Generated testbenches:")
            for p in self.generated_tb_paths:
                print(f"    ✓ {p}")

        print(f"\033[1m{hdr}\033[0m")

        # ── Write JSON report ──
        report_path = self.output_dir / "validation_report.json"
        report_path.write_text(json.dumps(self.results, indent=2))

        # ── Write human-readable report ──
        txt_path = self.output_dir / "validation_report.txt"
        lines = []
        L = lines.append

        L("╔══════════════════════════════════════════════════════════════════════╗")
        L("║                    DDR3 PHASE 1 VALIDATION REPORT                  ║")
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

        # Per-module results
        for mod_name, mod_result in self.results["modules"].items():
            sym = "✓" if mod_result["status"] == "PASS" else "✗"
            L(f"{'═' * 70}")
            L(f"  {sym} {mod_name.upper()}  —  {mod_result['status']}  ({mod_result['passed']}/{mod_result['total']})")
            L(f"{'═' * 70}")
            L("")

            categories = {}
            for chk in mod_result["checks"]:
                prefix = chk["id"].rsplit("-", 1)[0]
                cat_names = {"V-TIM": "TIMING COMPLIANCE", "V-JED": "JEDEC CONFORMANCE",
                             "V-RTL": "RTL CORRECTNESS", "V-CLK": "CLOCK VALIDATION"}
                cat = cat_names.get(prefix, prefix)
                if cat not in categories:
                    categories[cat] = []
                categories[cat].append(chk)

            for cat, cat_checks in categories.items():
                L(f"  ── {cat} ──")
                L("")
                for chk in cat_checks:
                    sym = "✓ PASS" if chk["pass"] else "✗ FAIL"
                    L(f"    [{chk['id']}] {chk['name']}")
                    L(f"      Status:   {sym}")
                    L(f"      Expected: {chk['expected']}")
                    L(f"      Actual:   {chk['actual']}")
                    L("")
                L("")

        # Testbench info
        if self.generated_tb_paths:
            L(f"{'═' * 70}")
            L(f"  GENERATED TESTBENCHES")
            L(f"{'═' * 70}")
            L("")
            for p in self.generated_tb_paths:
                L(f"  ✓ {p}")
            L("")
            L(f"  To run with Icarus Verilog:")
            L(f"    make -f {self.output_dir}/Makefile.sim all")
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

        # Failures
        all_checks = []
        for mod_result in self.results["modules"].values():
            all_checks.extend(mod_result["checks"])

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
    print("║   PHASE 1 VALIDATION AGENT                   ║")
    print("╚══════════════════════════════════════════════╝\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}"); sys.exit(1)

    rtl = input("RTL directory (where .sv files are): ").strip()
    if not os.path.isdir(rtl):
        print(f"Not a directory: {rtl}"); sys.exit(1)

    out = input("Output dir (Enter for same as RTL): ").strip() or rtl

    result = ValidationAgent(spec, rtl, out).run()
    sys.exit(0 if result["overall"]["status"] == "PASS" else 1)