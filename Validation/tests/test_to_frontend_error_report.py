#!/usr/bin/env python3
"""Our retry package rendered as the Frontend's phase error report: the
shape phase{N}_validation_agent.py reads (BEHAVIORAL_SIMULATION, per-module
fail_lines / assertion_errors), one report per phase that has a failed
module, carrying the check id, expected/actual, anchor and repro."""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "findings"))
import to_frontend_error_report as T  # noqa: E402

RETRY = {"drop": "abc", "spec_revision": "rev", "requires_human_review": False,
         "failed_modules": ["wb_port", "scheduler"],
         "retry_instructions": {
             "wb_port": {"module": "wb_port", "failed_checks": [
                 {"id": "MISMATCH/req[addr]", "name": "req carries the host address",
                  "expected": "addr=0x10", "actual": "addr=0x14", "spec_ref": "host_interface",
                  "anchor": [{"file": "PHASE1RTL/wb_port.sv", "line": 142, "signal": "req_addr",
                              "text": "req_addr <= wb_adr_i;"}],
                  "repro": {"cmd": "python3 run_path.py --path path_21"}, "detectors": ["predictor"],
                  "occurrences": 3, "paths": ["path_21_wb_port_standalone"]}]},
             "scheduler": {"module": "scheduler", "failed_checks": [
                 {"id": "TIMING_004", "name": "tRCD", "expected": ">= 11", "actual": "3",
                  "detectors": ["assert:a_TIMING_004"], "anchor": [], "repro": {},
                  "occurrences": 10, "paths": ["path_01_write_cmd"]}]}}}


class TestErrorReport(unittest.TestCase):
    def test_one_report_per_phase_in_the_agents_shape(self):
        tmp = tempfile.mkdtemp()
        written = T.write_error_reports(RETRY, tmp)
        self.assertEqual(sorted(written), [1, 3])
        with open(written[1]) as f:
            r1 = json.load(f)
        self.assertEqual(r1["failure_stage"], "BEHAVIORAL_SIMULATION")
        self.assertEqual(r1["failed_modules"], ["wb_port"])
        m = r1["sim_result"]["modules"]["wb_port"]
        self.assertEqual(m["status"], "FAIL")
        self.assertEqual(m["test_count"], 1)
        text = "\n".join(m["fail_lines"])
        for needle in ("MISMATCH/req[addr]", "addr=0x10", "addr=0x14", "wb_port.sv:142", "run_path.py --path path_21"):
            self.assertIn(needle, text)
        with open(written[3]) as f:
            r3 = json.load(f)
        m = r3["sim_result"]["modules"]["scheduler"]
        self.assertTrue(m["assertion_errors"], "an assertion-detected check lands in assertion_errors")
        self.assertEqual(m["fail_lines"], [])
        self.assertTrue(os.path.exists(os.path.join(tmp, "VALIDATIONREPORT", "phase3_error_report.json")))

    def test_backend_timing_anchor_and_repro_survive(self):
        """The backend's findings have no line, a signal with bit and role, and
        repro.command; the renderer lost all three (Backend handoff 2026-10-08)."""
        retry = {"drop": "abc", "failed_modules": ["scheduler"], "retry_instructions": {
            "scheduler": {"module": "scheduler", "failed_checks": [
                {"id": "TIMING/cmd_aux", "name": "closes timing at 5 ns", "expected": "slack >= 0",
                 "actual": "WNS -0.9 ns", "detectors": ["sta:opensta:setup"], "occurrences": 1, "paths": [],
                 "anchor": [{"file": "PHASE3RTL/scheduler.sv", "signal": "cmd_aux", "bit": 3, "role": "endpoint"},
                            {"file": "PHASE3RTL/scheduler.sv", "signal": "q_bank", "bit": 33, "role": "startpoint"}],
                 "repro": {"command": "pipeline_batch.py --bundle_dirs bundles/scheduler"},
                 "fix": "split the compare"}]}}}
        tmp = tempfile.mkdtemp()
        written = T.write_error_reports(retry, tmp)
        with open(written[3]) as f:
            text = "\n".join(json.load(f)["sim_result"]["modules"]["scheduler"]["fail_lines"])
        self.assertNotIn(":None", text)
        self.assertIn("cmd_aux[3] (endpoint)", text)
        self.assertIn("q_bank[33] (startpoint)", text)
        self.assertIn("repro: pipeline_batch.py --bundle_dirs bundles/scheduler", text)
        self.assertNotIn("occurrences: 1 on\n", text + "\n")
        self.assertIn("occurrences: 1", text)

    def test_no_failed_modules_writes_nothing(self):
        tmp = tempfile.mkdtemp()
        self.assertEqual(T.write_error_reports({"retry_instructions": {}, "failed_modules": []}, tmp), {})


if __name__ == "__main__":
    unittest.main()
