#!/usr/bin/env python3
"""apply_exclusions.py's design-wide pair (2026-11-12): measured over every
module, adjusted with the approved bits of the instances that have an
uncovered-items report; a module without one excludes nothing."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "coverage"))
import apply_exclusions as AX  # noqa: E402


class TestDesignTotal(unittest.TestCase):
    def test_measured_and_adjusted(self):
        code = {"cmd_queue": {"covered": 80, "total": 100}, "data_path": {"covered": 60, "total": 100},
                "wb_port": {"covered": 90, "total": 100}, "calibration": {"covered": 0, "total": 0}}
        inst = {"u_cmd_queue": {"excluded_approved": 10}, "u_data_path": {"excluded_approved": 20}}
        d = AX.design_total(code, inst)
        self.assertEqual((d["covered"], d["total"], d["excluded_approved"]), (230, 300, 30))
        self.assertEqual(d["measured_percent"], 76.7)
        self.assertEqual(d["adjusted_percent"], 85.2)          # 230 / 270
        self.assertEqual(d["instances_applied"], ["cmd_queue", "data_path"])
        self.assertEqual(d["instances_without_uncovered_report"], ["wb_port"])

    def test_nothing_measured(self):
        self.assertIsNone(AX.design_total({}, {}))
        self.assertIsNone(AX.design_total({"x": {"covered": 0, "total": 0}}, {}))


if __name__ == "__main__":
    unittest.main()


class TestDiagonalMatch(unittest.TestCase):
    def test_only_the_i_i_bits(self):
        e = {"instance": "u_cmd_queue", "signals": ["conf", "older"], "bits": "diagonal"}
        self.assertTrue(AX.matches(e, "u_cmd_queue", "conf", [3, 3]))
        self.assertFalse(AX.matches(e, "u_cmd_queue", "conf", [3, 4]))
        self.assertFalse(AX.matches(e, "u_cmd_queue", "conf", [3]))
        self.assertFalse(AX.matches(e, "u_scheduler", "conf", [3, 3]))
