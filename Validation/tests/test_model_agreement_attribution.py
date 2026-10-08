#!/usr/bin/env python3
"""Two checkers that file the same number of violations under a rule but
blame different witness transactions agree about the design; the comparator
records that as attribution, not disagreement (2026-10-08: 15 'disagreements'
on cmd_queue_scheduler were SCHED_004 110 vs 110 with different witnesses)."""

import collections
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "agreement"))
sys.path.insert(0, os.path.join(HERE, "..", "txn"))
sys.path.insert(0, os.path.join(HERE, "..", "agents"))
import model_agreement as MA  # noqa: E402


def run(pairs):
    c = collections.Counter()
    first = {}
    for tid, seq in pairs:
        c[(tid, seq)] += 1
        first.setdefault(tid, f"{tid} @ seq {seq}")
    return c, first


class TestCompareChk(unittest.TestCase):
    def test_same_count_different_witness_is_attribution(self):
        a = run([("SCHED_004", 10), ("SCHED_004", 20)])
        b = run([("SCHED_004", 11), ("SCHED_004", 21)])
        d = MA.compare_chk(a, b)
        self.assertEqual(len(d), 1)
        self.assertTrue(d[0]["attribution_differs"])
        self.assertEqual(d[0]["count"], 2)

    def test_different_count_is_a_disagreement(self):
        a = run([("PROTO_002", 10)])
        b = run([("PROTO_002", 10), ("PROTO_002", 30)])
        d = MA.compare_chk(a, b)
        self.assertEqual(len(d), 1)
        self.assertNotIn("attribution_differs", d[0])
        self.assertEqual((d[0]["primary_count"], d[0]["second_count"]), (1, 2))
        self.assertEqual(d[0]["second_only"], 1)

    def test_identical_is_silent(self):
        a = run([("REF_002", 5)])
        self.assertEqual(MA.compare_chk(a, run([("REF_002", 5)])), [])


if __name__ == "__main__":
    unittest.main()
