#!/usr/bin/env python3
"""
Tests for declared comparison waivers
======================================
A waiver stops the checker looking at something. That is legitimate when the
spec says the value is undefined, and it is exactly how the previous flow's
+/-2-cycle tolerance window came to exist when it is not (audit V-17). These
tests pin the properties that keep the two apart.

Run:  python3 Validation/tests/test_waivers.py
"""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "waivers"))
sys.path.insert(0, os.path.join(HERE, "..", "txn"))

import waivers as W
from txn_contract import Txn, TransactionPredictor
from scoreboard import Scoreboard

REV = "rev_under_test"


def a_waiver(**over):
    base = dict(id="W-T", scope="s", iface="rsp", kind="read_data",
                field_name="data", when={"err": 1},
                reason="The specification does not define this field under "
                       "this condition, so comparing it would assert a "
                       "requirement the spec never states.",
                approved_by="A Person", spec_revision=REV)
    base.update(over)
    return W.Waiver(**base)


class TestAWaiverMustBeAccountable(unittest.TestCase):

    def test_anonymous_waiver_is_rejected(self):
        with self.assertRaises(W.WaiverError) as cm:
            a_waiver(approved_by="").validate()
        self.assertIn("approved_by", str(cm.exception))

    def test_reason_must_be_a_reason(self):
        with self.assertRaises(W.WaiverError):
            a_waiver(reason="n/a").validate()

    def test_missing_spec_revision_is_rejected(self):
        with self.assertRaises(W.WaiverError):
            a_waiver(spec_revision="").validate()

    def test_a_complete_waiver_validates(self):
        a_waiver().validate()          # must not raise


class TestAWaiverIsNarrowAndExpiring(unittest.TestCase):

    def test_does_not_apply_to_a_different_spec_revision(self):
        """The decision was made against one revision of the spec. A new
        revision may be exactly the change that resolves it."""
        ws = W.WaiverSet([a_waiver()], scope="s", spec_revision="a_new_rev")
        t = Txn("rsp", "read_data", {"addr": 1, "data": 9, "err": 1})
        self.assertIsNone(ws.applies(t, "data"))
        self.assertEqual([w.id for w in ws.expired("a_new_rev")], ["W-T"])

    def test_condition_is_honoured(self):
        ws = W.WaiverSet([a_waiver()], scope="s", spec_revision=REV)
        errored = Txn("rsp", "read_data", {"addr": 1, "data": 9, "err": 1})
        clean = Txn("rsp", "read_data", {"addr": 1, "data": 9, "err": 0})
        self.assertIsNotNone(ws.applies(errored, "data"))
        self.assertIsNone(ws.applies(clean, "data"),
                          "a waiver conditioned on err=1 must not apply when err=0")

    def test_only_the_named_field_is_waived(self):
        ws = W.WaiverSet([a_waiver()], scope="s", spec_revision=REV)
        t = Txn("rsp", "read_data", {"addr": 1, "data": 9, "err": 1})
        self.assertEqual(ws.waived_fields(t), {"data"})
        self.assertIsNone(ws.applies(t, "err"),
                          "waiving 'data' must not waive 'err'")

    def test_does_not_apply_to_another_scope(self):
        ws = W.WaiverSet([a_waiver()], scope="other", spec_revision=REV)
        t = Txn("rsp", "read_data", {"addr": 1, "data": 9, "err": 1})
        self.assertIsNone(ws.applies(t, "data"))


class TestUsageIsTrackedHonestly(unittest.TestCase):

    def test_a_firing_waiver_is_not_reported_unused(self):
        """unused() drives a real decision — withdraw the waiver. If a live
        waiver reports as dead, someone removes a check that was working."""
        ws = W.WaiverSet([a_waiver()], scope="s", spec_revision=REV)
        ws.waived_fields(Txn("rsp", "read_data", {"data": 9, "err": 1}))
        self.assertEqual(ws.unused(), [])

    def test_a_waiver_that_never_fires_is_reported(self):
        ws = W.WaiverSet([a_waiver()], scope="s", spec_revision=REV)
        ws.waived_fields(Txn("rsp", "read_data", {"data": 9, "err": 0}))
        self.assertEqual([w.id for w in ws.unused()], ["W-T"])


class Pred(TransactionPredictor):
    INPUT_IFACES = ("req",)
    OUTPUT_IFACES = ("rsp",)
    def __init__(self, spec): self.reset()
    def reset(self): pass
    def process(self, txn):
        if txn.iface != "req":
            return []
        a = txn.fields["addr"]
        # predicts data=0 with err=1 for the "unmapped" address 0xFF
        return [Txn("rsp", "read_data",
                    {"addr": a, "data": 0, "err": 1 if a == 0xFF else 0})]
    def drain(self): return []


class TestScoreboardIntegration(unittest.TestCase):

    def _trace(self, observed_data):
        return [Txn("req", "read", {"addr": 0xFF}, 0),
                Txn("rsp", "read_data",
                    {"addr": 0xFF, "data": observed_data, "err": 1}, 1)]

    def test_without_a_waiver_the_disagreement_is_reported(self):
        res = Scoreboard("exact", Pred({}), scope="s").run(self._trace(0xDEADBEEF))
        self.assertEqual(res.status, "fail")

    def test_with_a_waiver_it_passes_and_says_so(self):
        ws = W.WaiverSet([a_waiver(scope="s")], scope="s", spec_revision=REV)
        res = Scoreboard("exact", Pred({}), scope="s",
                         waivers=ws).run(self._trace(0xDEADBEEF))
        self.assertEqual(res.status, "pass")
        self.assertGreater(res.waived_fields, 0,
                           "a run that waived a comparison must report it")
        self.assertIn("WAIVED", res.summary(),
                      "the summary must show the waiver, not a clean pass")

    def test_a_waiver_does_not_mask_a_neighbouring_field(self):
        """The narrowness property, end to end: waiving 'data' must not let a
        wrong 'err' through."""
        ws = W.WaiverSet([a_waiver(scope="s")], scope="s", spec_revision=REV)
        trace = [Txn("req", "read", {"addr": 0xFF}, 0),
                 Txn("rsp", "read_data",
                     {"addr": 0xFF, "data": 0xDEADBEEF, "err": 0}, 1)]
        res = Scoreboard("exact", Pred({}), scope="s", waivers=ws).run(trace)
        self.assertEqual(res.status, "fail",
                         "err disagreed; waiving data must not hide it")

    def test_expired_waiver_does_not_rescue_the_run(self):
        ws = W.WaiverSet([a_waiver(scope="s", spec_revision="old_rev")],
                         scope="s", spec_revision=REV)
        res = Scoreboard("exact", Pred({}), scope="s",
                         waivers=ws).run(self._trace(0xDEADBEEF))
        self.assertEqual(res.status, "fail")


if __name__ == "__main__":
    unittest.main(verbosity=1)
