#!/usr/bin/env python3
"""
Tests for the seeded-fault scorer.

The scorer is differential: the drop under test is already broken, so a
fault counts as killed only when the mutant run shows something the baseline
did not. These tests pin that down with synthetic signatures, and check the
mutation builder refuses a substitution that does not match exactly once.
"""

import json
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "faults"))
import seed_faults as SF  # noqa: E402


class TestCompare(unittest.TestCase):

    def test_same_failures_as_baseline_is_not_a_kill(self):
        base = {"stage:scheduler": 1, "id:SCHED_002": 12, "_verdict": "fail"}
        mut = dict(base)
        r = SF.compare(base, mut, ["id:SCHED_002"], "scheduler")
        self.assertFalse(r["killed"])
        self.assertEqual(r["expected_hit"], [])

    def test_new_detector_kills(self):
        base = {"stage:scheduler": 1, "id:SCHED_002": 12, "_verdict": "fail"}
        mut = dict(base, **{"assert:a_TIMING_001": 4})
        r = SF.compare(base, mut, ["assert:a_TIMING_001"], "bank_tracker")
        self.assertTrue(r["killed"])
        self.assertEqual(r["expected_hit"], ["assert:a_TIMING_001"])
        self.assertIn("assert:a_TIMING_001", r["new"])

    def test_count_growth_kills_only_when_large(self):
        base = {"id:SCHED_002": 12}
        self.assertFalse(SF.compare(base, {"id:SCHED_002": 14}, [], "x")["killed"])
        r = SF.compare(base, {"id:SCHED_002": 40}, ["id:SCHED_002"], "x")
        self.assertTrue(r["killed"])
        self.assertIn("id:SCHED_002", r["grew"])

    def test_fewer_matched_kills_and_blames_stage(self):
        base = {"stage:config_regs": 1, "matched:config_regs": 87}
        mut = {"stage:config_regs": 1, "matched:config_regs": 86}
        r = SF.compare(base, mut, ["matched:config_regs"], "config_regs")
        self.assertTrue(r["killed"])
        self.assertEqual(r["blamed_stages"], ["config_regs"])
        self.assertTrue(r["blame_names_block"])

    def test_blame_on_wrong_block_is_flagged(self):
        base = {}
        mut = {"stage:cmd_gen": 1}
        r = SF.compare(base, mut, ["stage:cmd_gen"], "addr_decoder")
        self.assertTrue(r["killed"])
        self.assertFalse(r["blame_names_block"])

    def test_path_level_checker_counts_as_named_block(self):
        r = SF.compare({}, {"stage:(path-level)": 1, "id:REF_004": 1},
                       ["id:REF_004"], "refresh_ctrl")
        self.assertTrue(r["blame_names_block"])


class TestBuild(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self._root, self._work = SF.ROOT, SF.WORK
        SF.ROOT = self.tmp
        SF.WORK = os.path.join(self.tmp, "work")
        os.makedirs(os.path.join(self.tmp, "drop", "p"))
        with open(os.path.join(self.tmp, "drop", "p", "blk.sv"), "w") as f:
            f.write("a <= b;\nc <= b;\n")

    def tearDown(self):
        SF.ROOT, SF.WORK = self._root, self._work
        shutil.rmtree(self.tmp)

    def test_unique_substitution_applies_to_a_copy(self):
        fault = {"id": "F1", "file": "p/blk.sv", "from": "a <= b;", "to": "a <= ~b;"}
        dst = SF.build(fault, "drop")
        with open(os.path.join(dst, "p", "blk.sv")) as f:
            self.assertEqual(f.read(), "a <= ~b;\nc <= b;\n")
        with open(os.path.join(self.tmp, "drop", "p", "blk.sv")) as f:
            self.assertEqual(f.read(), "a <= b;\nc <= b;\n")   # original untouched

    def test_ambiguous_or_missing_substitution_is_an_error(self):
        for frm in ("<= b;", "zzz"):
            with self.assertRaises(SF.FaultError):
                SF.build({"id": "F2", "file": "p/blk.sv", "from": frm, "to": "x"},
                         "drop")


if __name__ == "__main__":
    unittest.main()
