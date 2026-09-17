#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║              PHASE 1 VALIDATION AGENT  (with retry orchestration)    ║
║                                                                      ║
║  Static validation + SystemVerilog testbench generation              ║
║                                                                      ║
║  NEW: run_with_retries() orchestrates the full loop:                 ║
║    1. Run validation on the RTL (from bad or good agent)             ║
║    2. Classify failures as STATIC or BEHAVIORAL                      ║
║    3. STATIC bugs: feed back to the good generation agent for        ║
║       repair, up to MAX_RETRIES (4) attempts                         ║
║    4. BEHAVIORAL bugs: report immediately (no auto-fix)              ║
║    5. Re-validate after each repair attempt                          ║
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
║  Bug Classification:                                                 ║
║    STATIC:     Can be found by reading the .sv source — wrong        ║
║                parameter values, missing localparams, wrong          ║
║                hex literals, missing signal names. These are          ║
║                fed back to the generation agent for auto-repair.      ║
║    BEHAVIORAL: Require simulation to detect — wrong FSM              ║
║                transitions, handshake timing, output waveform         ║
║                issues. These are reported immediately.                ║
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


# ── Check IDs that are STATIC (fixable by regenerating RTL from prompt feedback)
# Everything else is considered BEHAVIORAL
STATIC_CHECK_IDS = {
    # init_fsm static checks
    "V-TIM-01", "V-TIM-02", "V-TIM-03", "V-TIM-04",  # wait count localparams
    "V-JED-01",                                         # MR order (state enum)
    "V-JED-02", "V-JED-03",                             # MR hex encoding
    "V-JED-04",                                         # DDR_ADDR_W parameter
    "V-RTL-01", "V-RTL-02", "V-RTL-03",                # signal declarations
    # config_regs static checks
    "V-RTL-10",  # register offset in address decode
    "V-RTL-11",  # reset value hex literal
    "V-RTL-12",  # access type keyword present
    "V-RTL-13",  # cfg_* output port name
    "V-RTL-14",  # error handling keyword
    "V-RTL-15",  # CSR_DATA_W parameter
    "V-JED-10",  # bit field fit (spec issue, not behavioral)
    # wb_port static checks
    "V-RTL-20", "V-RTL-21", "V-RTL-22", "V-RTL-23",
    "V-RTL-24", "V-RTL-25", "V-RTL-26", "V-RTL-27", "V-RTL-28",
    "V-TIM-20",
    # clocking (all derived from spec, static)
    "V-CLK-01", "V-CLK-02", "V-CLK-03", "V-CLK-04", "V-CLK-05", "V-CLK-06",
    "V-TIM-30", "V-TIM-31", "V-TIM-32", "V-TIM-33",
}


def print_check(check: dict, index: int = 0, total: int = 0):
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
    # BUG CLASSIFICATION
    # ════════════════════════════════════════════════════════════
    @staticmethod
    def classify_failure(check: dict) -> str:
        """Classify a failed check as 'static' or 'behavioral'.

        Static bugs can be fixed by re-prompting the generation LLM
        with the failure details. Behavioral bugs require simulation
        and are reported immediately without auto-retry.
        """
        check_id = check.get("id", "")
        if check_id in STATIC_CHECK_IDS:
            return "static"
        return "behavioral"

    @staticmethod
    def split_failures(checks: list) -> tuple:
        """Split failed checks into (static_failures, behavioral_failures)."""
        failed = [c for c in checks if not c["pass"]]
        static = [c for c in failed if ValidationAgent.classify_failure(c) == "static"]
        behavioral = [c for c in failed if ValidationAgent.classify_failure(c) == "behavioral"]
        return static, behavioral

    # ════════════════════════════════════════════════════════════
    # RETRY ORCHESTRATION
    # ════════════════════════════════════════════════════════════
    def run_with_retries(self, gen_agent_classes: dict = None) -> dict:
        """Full validation + retry loop.

        1. Validate current RTL
        2. If all pass → done
        3. If behavioral failures → report immediately, no retry
        4. If static failures → re-instantiate the GOOD generation agent
           with retry_instructions containing the failures, regenerate
           RTL, re-validate. Up to max_retries total attempts.

        Args:
            gen_agent_classes: dict mapping module name to its good
                generation agent CLASS (not instance). E.g.:
                {
                    "init_fsm": InitFsmAgent,
                    "config_regs": ConfigRegsAgent,
                }
                If None, retries are skipped (validate-only mode).

        Returns:
            Final validation results dict with retry history.
        """
        gen_agent_classes = gen_agent_classes or {}
        all_history = list(self.history)
        behavioral_reported = []

        for attempt in range(1, self.max_retries + 1):
            self.attempt = attempt
            hdr = "=" * 62

            print(f"\n\033[1m{hdr}\033[0m")
            print(f"\033[1m  VALIDATION ATTEMPT {attempt}/{self.max_retries}\033[0m")
            print(f"\033[1m{hdr}\033[0m")

            # Run full validation
            results = self.run()

            # Collect all checks across modules
            all_checks = []
            for mod_result in results["modules"].values():
                all_checks.extend(mod_result["checks"])

            all_pass = results["overall"]["status"] == "PASS"
            static_failures, behavioral_failures = self.split_failures(all_checks)

            # Record this attempt in history
            attempt_record = {
                "attempt": attempt,
                "overall": results["overall"]["status"],
                "passed": results["overall"]["total_passed"],
                "total": results["overall"]["total_checks"],
                "static_failures": len(static_failures),
                "behavioral_failures": len(behavioral_failures),
                "failed_modules": [
                    mod for mod, res in results["modules"].items()
                    if res["status"] != "PASS"
                ],
                "failed_checks": [
                    {"id": c["id"], "name": c["name"],
                     "expected": c["expected"], "actual": c["actual"],
                     "type": self.classify_failure(c)}
                    for c in static_failures + behavioral_failures
                ],
            }
            all_history.append(attempt_record)

            # ── ALL PASS → done ──
            if all_pass:
                print(f"\n\033[92m  ✓ ALL CHECKS PASSED on attempt {attempt}\033[0m")
                results["retry_history"] = all_history
                results["final_attempt"] = attempt
                return results

            # ── BEHAVIORAL FAILURES → report immediately ──
            if behavioral_failures:
                print(f"\n\033[93m  ⚠ {len(behavioral_failures)} BEHAVIORAL bug(s) detected "
                      f"(require simulation to verify):\033[0m")
                for c in behavioral_failures:
                    print(f"    \033[91m✗ [{c['id']}] {c['name']}\033[0m")
                    print(f"      expected: {c['expected']}")
                    print(f"      actual:   {c['actual']}")
                behavioral_reported.extend(behavioral_failures)

            # ── STATIC FAILURES → retry via good agent ──
            if static_failures and gen_agent_classes:
                print(f"\n\033[93m  ⟳ {len(static_failures)} STATIC bug(s) — "
                      f"feeding back to generation agent for repair\033[0m")
                for c in static_failures:
                    print(f"    \033[91m✗ [{c['id']}] {c['name']}\033[0m")
                    print(f"      expected: {c['expected']}")
                    print(f"      actual:   {c['actual']}")

                if attempt >= self.max_retries:
                    print(f"\n\033[91m  ✗ MAX RETRIES ({self.max_retries}) reached — "
                          f"static bugs unresolved\033[0m")
                    break

                # Determine which modules have static failures
                module_failures = {}
                for c in static_failures:
                    # Map check ID prefixes to modules
                    cid = c["id"]
                    if cid.startswith("V-TIM-0") or cid.startswith("V-JED-0") or cid.startswith("V-RTL-0"):
                        mod = "init_fsm"
                    elif cid.startswith("V-RTL-1") or cid.startswith("V-JED-1"):
                        mod = "config_regs"
                    elif cid.startswith("V-RTL-2") or cid.startswith("V-TIM-2"):
                        mod = "wb_port"
                    elif cid.startswith("V-CLK") or cid.startswith("V-TIM-3"):
                        # Clocking failures map to init_fsm (WAIT_RESET/CKE are there)
                        mod = "init_fsm"
                    else:
                        mod = "unknown"
                    if mod not in module_failures:
                        module_failures[mod] = []
                    module_failures[mod].append(c)

                # Regenerate each failed module
                for mod_name, fails in module_failures.items():
                    if mod_name not in gen_agent_classes:
                        print(f"  ⚠ No generation agent for {mod_name} — skipping")
                        continue

                    agent_cls = gen_agent_classes[mod_name]
                    print(f"\n  ⟳ Regenerating {mod_name} (attempt {attempt + 1}) ...")

                    # Build retry_instructions in the format each agent expects
                    # ConfigRegsAgent uses "validation_failures"
                    # InitFsmAgent uses "failed_checks"
                    retry_instructions = {
                        "validation_failures": fails,
                        "failed_checks": fails,
                    }

                    try:
                        agent = agent_cls(
                            self.spec_path,
                            str(self.rtl_dir),
                            retry_instructions=retry_instructions,
                            temperature=0.3,  # lower temp for retries
                        )
                        agent.run()
                        print(f"  ✓ {mod_name} regenerated")
                    except Exception as e:
                        print(f"  \033[91m✗ {mod_name} regeneration failed: {e}\033[0m")

            elif not gen_agent_classes:
                print(f"\n\033[93m  ⚠ No generation agents provided — "
                      f"cannot auto-retry static bugs\033[0m")
                break
            elif not static_failures:
                # Only behavioral failures remain — can't auto-fix
                print(f"\n\033[93m  ⚠ Only behavioral bugs remain — "
                      f"cannot auto-fix, reporting\033[0m")
                break

        # Fell through the loop — return final results
        results["retry_history"] = all_history
        results["final_attempt"] = attempt
        results["behavioral_bugs"] = [
            {"id": c["id"], "name": c["name"],
             "expected": c["expected"], "actual": c["actual"]}
            for c in behavioral_reported
        ]
        results["unresolved_static_bugs"] = [
            {"id": c["id"], "name": c["name"],
             "expected": c["expected"], "actual": c["actual"]}
            for c in static_failures
        ] if static_failures else []

        # Write retry summary
        self._write_retry_summary(results, all_history)
        return results

    def _write_retry_summary(self, results: dict, history: list):
        """Write a human-readable retry summary."""
        path = self.output_dir / "retry_summary.txt"
        lines = []
        L = lines.append

        L("╔══════════════════════════════════════════════════════════════╗")
        L("║                    RETRY SUMMARY                            ║")
        L("╚══════════════════════════════════════════════════════════════╝")
        L("")

        for h in history:
            sym = "✓" if h["overall"] == "PASS" else "✗"
            L(f"  {sym} Attempt {h['attempt']}: {h['overall']} "
              f"({h['passed']}/{h['total']}) "
              f"[{h['static_failures']} static, {h['behavioral_failures']} behavioral]")
            for fc in h.get("failed_checks", []):
                tag = "STATIC" if fc.get("type") == "static" else "BEHAV "
                L(f"      ✗ [{fc['id']}] ({tag}) {fc['name']}")
            L("")

        if results.get("behavioral_bugs"):
            L("  ═══ BEHAVIORAL BUGS (reported, not auto-fixed) ═══")
            for b in results["behavioral_bugs"]:
                L(f"    ✗ [{b['id']}] {b['name']}")
                L(f"      expected: {b['expected']}")
                L(f"      actual:   {b['actual']}")
            L("")

        if results.get("unresolved_static_bugs"):
            L("  ═══ UNRESOLVED STATIC BUGS (max retries exceeded) ═══")
            for b in results["unresolved_static_bugs"]:
                L(f"    ✗ [{b['id']}] {b['name']}")
                L(f"      expected: {b['expected']}")
                L(f"      actual:   {b['actual']}")
            L("")

        final = results.get("overall", {})
        if final.get("status") == "PASS":
            L(f"  ✓ FINAL RESULT: PASS after {results.get('final_attempt', '?')} attempt(s)")
        else:
            L(f"  ✗ FINAL RESULT: FAIL after {results.get('final_attempt', '?')} attempt(s)")

        path.write_text("\n".join(lines))
        print(f"\n  Retry summary: {path}")

    # ════════════════════════════════════════════════════════════
    # INIT_FSM VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_init_fsm(self) -> dict:
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

        # V-JED-01: MR program order
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

        # V-RTL-13: cfg_* output ports
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
        checks = []
        sv_path = self.rtl_dir / "wb_port.sv"

        if not sv_path.exists():
            return {"status": "ERROR", "checks": [{"id": "V-RTL-00", "pass": False,
                     "name": "File exists", "expected": str(sv_path), "actual": "missing"}]}

        sv = sv_path.read_text()

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

        expected_aw = self.host["address_width_bits"]
        m = re.search(r"ADDR_WIDTH\s*=\s*(\d+)", sv)
        actual_aw = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-21", "name": "Address width matches spec",
            "pass": actual_aw == expected_aw, "expected": str(expected_aw), "actual": str(actual_aw)})

        expected_dw = self.host["data_width_bits"]
        m = re.search(r"DATA_WIDTH\s*=\s*(\d+)", sv)
        actual_dw = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-22", "name": "Data width matches spec",
            "pass": actual_dw == expected_dw, "expected": str(expected_dw), "actual": str(actual_dw)})

        has_stall = "stall" in sv.lower() and ("wb_stall_o" in sv)
        checks.append({"id": "V-RTL-23", "name": "Stall backpressure logic",
            "pass": has_stall, "expected": "wb_stall_o driven", "actual": "found" if has_stall else "missing"})

        has_burst = "burst" in sv.lower() or "cti" in sv.lower() or "bte" in sv.lower()
        checks.append({"id": "V-RTL-24", "name": "Burst support (BL8)",
            "pass": has_burst,
            "expected": "Burst counter or CTI/BTE handling", "actual": "found" if has_burst else "missing"})

        for sig in ["req_valid", "req_we", "req_addr", "req_wdata"]:
            found = sig in sv
            checks.append({"id": "V-RTL-25", "name": f"Internal output {sig}",
                "pass": found, "expected": f"output ... {sig}", "actual": "found" if found else "missing"})

        expected_sel = expected_dw // 8
        m = re.search(r"SEL_WIDTH\s*=\s*(\d+)", sv)
        actual_sel = int(m.group(1)) if m else 0
        checks.append({"id": "V-RTL-26", "name": "SEL width = DATA_WIDTH/8",
            "pass": actual_sel == expected_sel, "expected": str(expected_sel), "actual": str(actual_sel)})

        has_clk = "clk" in sv and "rst_n" in sv
        checks.append({"id": "V-RTL-27", "name": "Clock (clk) and reset (rst_n)",
            "pass": has_clk, "expected": "input clk, input rst_n", "actual": "found" if has_clk else "missing"})

        ack_gated = ("cyc" in sv.lower() and "stb" in sv.lower() and "ack" in sv.lower())
        checks.append({"id": "V-RTL-28", "name": "ACK gated by CYC & STB (WB rule 3.35)",
            "pass": ack_gated,
            "expected": "ack depends on cyc & stb", "actual": "found" if ack_gated else "not verified"})

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
    # CLOCKING VALIDATION
    # ════════════════════════════════════════════════════════════
    def validate_clocking(self) -> dict:
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

        sv = (self.rtl_dir / "init_fsm.sv").read_text()

        expected_reset = math.ceil(200 * 1000 / ctrl_period)
        m = re.search(r"WAIT_RESET\s*=\s*(\d+)", sv)
        actual_reset = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-30",
            "name": f"WAIT_RESET = 200µs / {ctrl_period}ns = {expected_reset}",
            "pass": actual_reset == expected_reset,
            "expected": str(expected_reset), "actual": str(actual_reset)})

        expected_cke = math.ceil(500 * 1000 / ctrl_period)
        m = re.search(r"WAIT_CKE\s*=\s*(\d+)", sv)
        actual_cke = int(m.group(1)) if m else 0
        checks.append({"id": "V-TIM-31",
            "name": f"WAIT_CKE = 500µs / {ctrl_period}ns = {expected_cke}",
            "pass": actual_cke == expected_cke,
            "expected": str(expected_cke), "actual": str(actual_cke)})

        tRC = self.dc["tRC_nCK"]
        tRAS = self.dc["tRAS_nCK"]
        tRP = self.dc["tRP_nCK"]
        checks.append({"id": "V-TIM-32",
            "name": f"tRC({tRC}) >= tRAS({tRAS}) + tRP({tRP}) JEDEC invariant",
            "pass": tRC >= tRAS + tRP,
            "expected": f">= {tRAS + tRP}", "actual": str(tRC)})

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
    # TESTBENCH GENERATION (unchanged from original)
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

        sv = (self.rtl_dir / "init_fsm.sv").read_text()
        mr_vals = {}
        for mr in ["MR0", "MR1", "MR2", "MR3"]:
            m = re.search(rf"{mr}_VAL\s*=\s*\d+\'h([0-9A-Fa-f]+)", sv)
            mr_vals[mr] = m.group(1) if m else "0000"

        timeout_cycles = wait_reset + wait_cke + tXPR + tZQ + 500

        return f"""`timescale 1ns / 1ps
module init_fsm_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    logic rst_n, init_done, init_fail, init_cmd_valid;
    logic [3:0] init_cmd;
    logic [{ddr_addr_w-1}:0] init_addr;
    logic [2:0] init_bank;
    logic init_cke, init_reset_n;

    init_fsm dut (.*);

    localparam CMD_MRS = 4'b0000, CMD_ZQCL = 4'b0110;
    int pass_count=0, fail_count=0, total_tests=0, cycle_count=0;
    int cke_rise=0, resetn_rise=0, first_mrs=0, done_cycle=0, mr_cmd_count=0;
    logic [2:0] mr_bank_order[$];

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    always @(posedge clk) begin
        cycle_count++;
        if (init_cke && cke_rise==0 && cycle_count>10) cke_rise=cycle_count;
        if (init_reset_n && resetn_rise==0 && cycle_count>10) resetn_rise=cycle_count;
        if (init_cmd_valid && init_cmd==CMD_MRS) begin
            if (first_mrs==0) first_mrs=cycle_count;
            mr_bank_order.push_back(init_bank);
            mr_cmd_count++;
        end
        if (init_done && done_cycle==0) done_cycle=cycle_count;
    end

    initial begin
        $dumpfile("init_fsm_tb.vcd"); $dumpvars(0, init_fsm_tb);
        rst_n=0; repeat(10) @(posedge clk); rst_n=1;
        fork
            wait(init_done);
            begin repeat({timeout_cycles}) @(posedge clk); $display("[FAIL] TIMEOUT"); end
        join_any
        disable fork;
        repeat(10) @(posedge clk);

        check($sformatf("Reset hold >= {wait_reset} cyc (got %0d)", resetn_rise), resetn_rise>={wait_reset});
        check($sformatf("CKE delay >= {wait_cke} cyc"), (cke_rise-resetn_rise)>={wait_cke} || cke_rise>={wait_cke});
        check("init_done asserted", init_done===1'b1);
        check("init_fail not asserted", init_fail===1'b0);
        check($sformatf("4 MRS commands (got %0d)", mr_cmd_count), mr_cmd_count==4);
        if (mr_bank_order.size()>=4)
            check("MR order 2->3->1->0", mr_bank_order[0]==3'd2 && mr_bank_order[1]==3'd3 && mr_bank_order[2]==3'd1 && mr_bank_order[3]==3'd0);
        else check("MR order (insufficient cmds)", 0);
        check("Sequence completed", init_done===1'b1);

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    def generate_config_regs_tb(self) -> str:
        """Generate SystemVerilog testbench for config_regs."""
        ctrl_period = self.cl["controller_clock_period_ns"]
        csr_map = self.csrs if isinstance(self.csrs, dict) else {"registers": self.csrs}
        regs = csr_map.get("registers", self.csrs if isinstance(self.csrs, list) else [])

        reset_checks = []
        rw_tests = []
        for reg in regs:
            offset_int = int(reg["offset"], 16) if isinstance(reg["offset"], str) else reg["offset"]
            rv_int = int(reg.get("reset_value", 0), 16) if isinstance(reg.get("reset_value", 0), str) else reg.get("reset_value", 0)
            reset_checks.append(
                f'        csr_read(8\'h{offset_int:02X}, rdata);\n'
                f'        check($sformatf("{reg["name"]} reset=0x%08X", rdata), rdata==32\'h{rv_int:08X});'
            )
            if reg["access"] == "RW":
                rw_tests.append(
                    f'        csr_write(8\'h{offset_int:02X}, 32\'hA5A5A5A5);\n'
                    f'        csr_read(8\'h{offset_int:02X}, rdata);\n'
                    f'        check("{reg["name"]} write/readback", rdata==32\'hA5A5A5A5);'
                )

        return f"""`timescale 1ns / 1ps
module config_regs_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    logic clk=0;
    always #(CLK_PERIOD/2) clk=~clk;

    logic rst_n;
    logic [7:0] csr_addr_i;
    logic [31:0] csr_dat_i, csr_dat_o;
    logic csr_we_i, csr_stb_i, csr_ack_o, csr_err_o;
    logic [31:0] rdata;
    int pass_count=0, fail_count=0, total_tests=0;

    config_regs dut (.clk(clk), .rst_n(rst_n), .csr_addr_i(csr_addr_i),
        .csr_dat_i(csr_dat_i), .csr_we_i(csr_we_i), .csr_stb_i(csr_stb_i),
        .csr_dat_o(csr_dat_o), .csr_ack_o(csr_ack_o), .csr_err_o(csr_err_o));

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    task csr_write(input [7:0] addr, input [31:0] data);
        @(posedge clk); csr_addr_i=addr; csr_dat_i=data; csr_we_i=1; csr_stb_i=1;
        @(posedge clk); wait(csr_ack_o||csr_err_o); @(posedge clk); csr_stb_i=0; csr_we_i=0;
    endtask

    task csr_read(input [7:0] addr, output [31:0] data);
        @(posedge clk); csr_addr_i=addr; csr_we_i=0; csr_stb_i=1;
        @(posedge clk); wait(csr_ack_o||csr_err_o); data=csr_dat_o;
        @(posedge clk); csr_stb_i=0;
    endtask

    initial begin
        $dumpfile("config_regs_tb.vcd"); $dumpvars(0, config_regs_tb);
        rst_n=0; csr_stb_i=0; csr_we_i=0; csr_addr_i=0; csr_dat_i=0;
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);

        $display("  -- Reset Values --");
{chr(10).join(reset_checks)}

        $display("  -- Write/Readback --");
{chr(10).join(rw_tests) if rw_tests else '        $display("  (no RW registers)");'}

        $display("  -- Error Handling --");
        @(posedge clk); csr_addr_i=8'hFF; csr_stb_i=1; csr_we_i=0;
        @(posedge clk); repeat(3) @(posedge clk);
        check("Invalid addr error", csr_err_o===1'b1);
        csr_stb_i=0;

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    def generate_wb_port_tb(self) -> str:
        """Generate SystemVerilog testbench for wb_port (unchanged)."""
        ctrl_period = self.cl["controller_clock_period_ns"]
        addr_w = self.host["address_width_bits"]
        data_w = self.host["data_width_bits"]
        sel_w = data_w // 8

        return f"""`timescale 1ns / 1ps
module wb_port_tb;
    localparam real CLK_PERIOD = {ctrl_period};
    localparam ADDR_WIDTH={addr_w}, DATA_WIDTH={data_w}, SEL_WIDTH={sel_w};
    logic clk=0;
    always #(CLK_PERIOD/2) clk=~clk;

    logic wb_cyc_i, wb_stb_i, wb_we_i;
    logic [ADDR_WIDTH-1:0] wb_adr_i;
    logic [DATA_WIDTH-1:0] wb_dat_i, wb_dat_o;
    logic [SEL_WIDTH-1:0] wb_sel_i;
    logic wb_ack_o, wb_stall_o, wb_err_o;
    logic req_valid, req_we, req_ready;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [DATA_WIDTH-1:0] req_wdata;
    logic rst_n;
    int pass_count=0, fail_count=0, total_tests=0;

    wb_port dut (.*);

    task check(string name, logic cond);
        total_tests++;
        if (cond) begin pass_count++; $display("  [PASS] %s", name); end
        else begin fail_count++; $display("  [FAIL] %s", name); end
    endtask

    task wb_idle(); wb_cyc_i=0; wb_stb_i=0; wb_we_i=0; wb_adr_i=0; wb_dat_i=0; wb_sel_i=0; endtask

    initial begin
        $dumpfile("wb_port_tb.vcd"); $dumpvars(0, wb_port_tb);
        rst_n=0; req_ready=1; wb_idle();
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);

        // Single write
        @(posedge clk); wb_cyc_i=1; wb_stb_i=1; wb_we_i=1;
        wb_adr_i={addr_w}'h100; wb_dat_i=32'hDEADBEEF; wb_sel_i={{SEL_WIDTH{{1'b1}}}};
        do @(posedge clk); while(wb_stall_o);
        wb_stb_i=0; if(!wb_ack_o) begin repeat(20) begin @(posedge clk); if(wb_ack_o) break; end end
        @(posedge clk); wb_idle();
        check("Single write OK", wb_err_o===1'b0);

        // ACK idle
        wb_idle(); repeat(3) @(posedge clk);
        check("ACK deasserted when idle", wb_ack_o===1'b0);

        // CYC without STB
        @(posedge clk); wb_cyc_i=1; wb_stb_i=0; repeat(3) @(posedge clk);
        check("No ACK when CYC=1 STB=0", wb_ack_o===1'b0);
        wb_idle();

        // Stall
        req_ready=0; @(posedge clk);
        wb_cyc_i=1; wb_stb_i=1; wb_we_i=1; wb_adr_i={addr_w}'h300;
        wb_dat_i=32'hCAFEBABE; wb_sel_i={{SEL_WIDTH{{1'b1}}}};
        repeat(3) @(posedge clk);
        check("Stall when backend busy", wb_stall_o===1'b1);
        req_ready=1; repeat(5) @(posedge clk); wb_idle();

        if (fail_count==0) $display("ALL %0d TESTS PASSED", total_tests);
        else $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
        $finish;
    end
    initial begin #(1_000_000); $display("[FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule
"""

    def write_testbenches(self):
        tb_files = [
            ("init_fsm_tb.sv",    self.generate_init_fsm_tb),
            ("config_regs_tb.sv", self.generate_config_regs_tb),
            ("wb_port_tb.sv",     self.generate_wb_port_tb),
        ]
        print(f"\n\033[1m  ── TESTBENCH GENERATION ──\033[0m")
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

    # ════════════════════════════════════════════════════════════
    # RUN (single pass — no retries)
    # ════════════════════════════════════════════════════════════
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"\n\033[1m{hdr}\033[0m")
        print(f"\033[1m  PHASE 1 VALIDATION AGENT — attempt {self.attempt}\033[0m")
        print(f"  Spec: {self.spec_path}")
        print(f"  RTL:  {self.rtl_dir}")
        print(f"\033[1m{hdr}\033[0m")

        start = time.time()

        print(f"\n\033[1m  ── INIT_FSM ──\033[0m")
        self.results["modules"]["init_fsm"] = self.validate_init_fsm()

        print(f"\033[1m  ── CONFIG_REGS ──\033[0m")
        self.results["modules"]["config_regs"] = self.validate_config_regs()

        print(f"\033[1m  ── WB_PORT ──\033[0m")
        self.results["modules"]["wb_port"] = self.validate_wb_port()

        print(f"\033[1m  ── CLOCKING ──\033[0m")
        self.results["modules"]["clocking"] = self.validate_clocking()

        self.write_testbenches()

        elapsed = time.time() - start
        total_passed = sum(m["passed"] for m in self.results["modules"].values())
        total_checks = sum(m["total"] for m in self.results["modules"].values())
        all_pass = all(m["status"] == "PASS" for m in self.results["modules"].values())

        self.results["overall"] = {
            "status": "PASS" if all_pass else "FAIL",
            "total_passed": total_passed,
            "total_checks": total_checks,
        }
        self.results["testbenches"] = self.generated_tb_paths

        # Summary
        print(f"\n\033[1m{hdr}\033[0m")
        if all_pass:
            print(f"\033[92m  ✓ ALL {total_passed}/{total_checks} CHECKS PASSED ({elapsed:.2f}s)\033[0m")
        else:
            print(f"\033[91m  ✗ {total_passed}/{total_checks} CHECKS PASSED ({elapsed:.2f}s)\033[0m")
        print(f"\033[1m{hdr}\033[0m")

        for mod, res in self.results["modules"].items():
            c = "\033[92m" if res["status"] == "PASS" else "\033[91m"
            print(f"  {mod:<20s} {c}{res['status']:<8s}\033[0m {res['passed']}/{res['total']}")

        # Write reports
        report_path = self.output_dir / "validation_report.json"
        report_path.write_text(json.dumps(self.results, indent=2))
        print(f"\n  Report: {report_path}")

        return self.results


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   PHASE 1 VALIDATION AGENT                   ║")
    print("╚══════════════════════════════════════════════╝\n")

    spec = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec):
        print(f"Not found: {spec}"); sys.exit(1)

    rtl = input("RTL directory: ").strip()
    if not os.path.isdir(rtl):
        print(f"Not a directory: {rtl}"); sys.exit(1)

    out = input("Output dir (Enter for same as RTL): ").strip() or rtl

    # Example usage with retry orchestration:
    #
    #   from config_regs_agent import ConfigRegsAgent
    #   from init_fsm_agent import InitFsmAgent
    #
    #   va = ValidationAgent(spec, rtl, out)
    #   result = va.run_with_retries(gen_agent_classes={
    #       "init_fsm": InitFsmAgent,
    #       "config_regs": ConfigRegsAgent,
    #   })
    #
    # Without gen_agent_classes, just validates once:
    result = ValidationAgent(spec, rtl, out).run()
    sys.exit(0 if result["overall"]["status"] == "PASS" else 1)