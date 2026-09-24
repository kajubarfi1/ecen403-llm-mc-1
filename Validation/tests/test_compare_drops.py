#!/usr/bin/env python3
"""Tests for the drop comparison classifier."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import compare_drops as CD  # noqa: E402


class TestClassify(unittest.TestCase):

    def test_identical_is_same(self):
        s = {"stage:x": 1, "id:SCHED_002": 5, "matched:cmd_gen": 42, "_verdict": "fail"}
        self.assertEqual(CD.classify(s, dict(s))[0], "same")
        self.assertEqual(CD.classify(s, dict(s), strict=True)[0], "same")

    def test_new_detector_is_regression(self):
        a = {"matched:config_regs": 102, "_verdict": "fail"}
        b = {"matched:config_regs": 87, "id:CSR_001": 15, "_verdict": "fail"}
        kind, det = CD.classify(a, b)
        self.assertEqual(kind, "regression")
        self.assertIn("id:CSR_001", det["new"])
        self.assertEqual(det["matched_down"]["matched:config_regs"], (102, 87))

    def test_gone_detector_is_fixed(self):
        a = {"stage:scheduler": 1, "id:SCHED_002": 12, "_verdict": "fail"}
        b = {"_verdict": "pass"}
        self.assertEqual(CD.classify(a, b)[0], "fixed")

    def test_small_count_drift_is_same_unless_strict(self):
        a = {"id:SCHED_002": 12, "_verdict": "fail"}
        b = {"id:SCHED_002": 13, "_verdict": "fail"}
        self.assertEqual(CD.classify(a, b)[0], "same")
        self.assertEqual(CD.classify(a, b, strict=True)[0], "changed")

    def test_mixed_is_changed(self):
        a = {"id:A_001": 5, "id:B_001": 5, "_verdict": "fail"}
        b = {"id:A_001": 50, "_verdict": "fail"}
        self.assertEqual(CD.classify(a, b)[0], "changed")

    def test_verdict_flip_alone_counts(self):
        self.assertEqual(CD.classify({"_verdict": "pass"}, {"_verdict": "fail"})[0],
                         "regression")
        self.assertEqual(CD.classify({"_verdict": "fail"}, {"_verdict": "pass"})[0],
                         "fixed")


if __name__ == "__main__":
    unittest.main()
