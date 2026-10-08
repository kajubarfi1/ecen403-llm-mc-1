#!/usr/bin/env python3
"""A fired assertion is the verdict of the stage it is bound into: an
SVA-owned (autonomous) stage fails on it, and a modelled stage fails on it
even when its model matched (the backend's init_fsm netlist, 2026-10-07:
a_INIT_001 fired 4x and the path still said PASS)."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import run_path as RP  # noqa: E402


class TestFiredAssertionsDecideVerdict(unittest.TestCase):
    def test_autonomous_stage_fails_when_its_assertion_fired(self):
        jobs = [{"stage": "init_fsm", "kind": "autonomous", "scope": "init_fsm", "model": None}]
        res = RP.judge("/nonexistent/trace.jsonl", jobs, "path_x", "/tmp",
                       fired_by_block={"init_fsm": {"a_INIT_001": 4}})
        self.assertEqual(res[0]["verdict"], "fail")
        self.assertIn("a_INIT_001 x4", res[0]["summary"])

    def test_autonomous_stage_is_sva_owned_when_silent(self):
        jobs = [{"stage": "init_fsm", "kind": "autonomous", "scope": "init_fsm", "model": None}]
        res = RP.judge("/nonexistent/trace.jsonl", jobs, "path_x", "/tmp", fired_by_block={})
        self.assertEqual(res[0]["verdict"], "sva")

    def test_other_blocks_assertions_do_not_touch_this_stage(self):
        jobs = [{"stage": "config_regs", "kind": "autonomous", "scope": "config_regs", "model": None}]
        res = RP.judge("/nonexistent/trace.jsonl", jobs, "path_x", "/tmp",
                       fired_by_block={"init_fsm": {"a_INIT_001": 4}})
        self.assertEqual(res[0]["verdict"], "sva")

    def test_support_block_assertion_fails_the_path(self):
        jobs = [{"stage": "config_regs", "kind": "autonomous", "scope": "config_regs", "model": None}]
        res = RP.judge("/nonexistent/trace.jsonl", jobs, "path_x", "/tmp",
                       fired_by_block={"cmd_gen": {"a_TIMING_004": 4}})
        self.assertEqual(res[0]["verdict"], "sva")
        extra = [r for r in res if r["stage"] == "cmd_gen (support)"]
        self.assertEqual(len(extra), 1)
        self.assertEqual(extra[0]["verdict"], "fail")

    def test_log_line_maps_to_block(self):
        import re
        line = ("xmsim: *E,ASRTST (./init_fsm_sva.sv,69): (time 700212500 PS) Assertion "
                "chain_harness.u_init_fsm.u_init_fsm_sva.a_INIT_001 has failed")
        self.assertEqual(re.search(r"\.u_(\w+)\.u_\w+_sva\.", line).group(1), "init_fsm")
        line2 = "... Assertion chain_harness.u_calibration.u_calibration_order_sva.a_CAL_001 has failed"
        self.assertEqual(re.search(r"\.u_(\w+)\.u_\w+_sva\.", line2).group(1), "calibration")


if __name__ == "__main__":
    unittest.main()
