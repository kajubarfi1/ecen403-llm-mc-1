#!/usr/bin/env python3
"""
Tests for the transaction scoreboard
=====================================
The scoreboard decides pass/fail, so its own failure modes are the ones that
matter most:

  * it must never report `pass` for a run in which nothing was compared
    (the shape of audit V-02, where an unparseable run scored as a pass)
  * a single missing transaction must not cascade into a mismatch on every
    following one — that turns one defect into an unreadable report
  * it must distinguish wrong value / missing / unexpected, because those
    three route to different diagnoses

Everything here runs on synthetic traces: no simulator, no cluster, no LLM.

Run:  python3 Validation/tests/test_scoreboard.py
"""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "txn"))

from txn_contract import Txn, Violation, TransactionPredictor, LegalityChecker
from scoreboard import (Scoreboard, CompositePredictor, align, align_keyed,
                        Mismatch)

SPEC = {"revision": "test"}


# --------------------------------------------------------------- fixtures --

class EchoPredictor(TransactionPredictor):
    """csr write -> a csr read carrying the same data (a trivial register)."""
    INPUT_IFACES = ("csr_in",)
    OUTPUT_IFACES = ("csr_out",)

    def __init__(self, spec):
        self.spec = spec
        self.reset()

    def reset(self):
        self.store = {}

    def process(self, txn):
        if txn.iface not in self.INPUT_IFACES:
            return []
        if txn.kind == "write":
            self.store[txn.fields["addr"]] = txn.fields["data"]
            return []
        if txn.kind == "read":
            return [Txn("csr_out", "read",
                        {"addr": txn.fields["addr"],
                         "data": self.store.get(txn.fields["addr"], 0)})]
        return []

    def drain(self):
        return []


class DoublerPredictor(TransactionPredictor):
    """Second stage for composition: doubles the data field."""
    INPUT_IFACES = ("csr_out",)
    OUTPUT_IFACES = ("final",)

    def __init__(self, spec):
        self.reset()

    def reset(self):
        pass

    def process(self, txn):
        if txn.iface not in self.INPUT_IFACES:
            return []
        return [Txn("final", "value", {"data": txn.fields["data"] * 2})]

    def drain(self):
        return []


class LivenessChecker(LegalityChecker):
    """Every request must eventually be served."""
    INPUT_IFACES = ("req", "done")
    OUTPUT_IFACES = ()

    def __init__(self, spec):
        self.reset()

    def reset(self):
        self.outstanding = []

    def observe(self, txn):
        if txn.iface == "req":
            self.outstanding.append(txn)
        elif txn.iface == "done" and self.outstanding:
            self.outstanding.pop(0)
        return []

    def final(self):
        if self.outstanding:
            return [Violation("no_starvation",
                              f"{len(self.outstanding)} request(s) never served",
                              taxonomy_id="REF_001", txns=self.outstanding[:2])]
        return []


def w(addr, data):
    return Txn("csr_in", "write", {"addr": addr, "data": data})


def r(addr):
    return Txn("csr_in", "read", {"addr": addr})


def out(addr, data):
    return Txn("csr_out", "read", {"addr": addr, "data": data})


# ------------------------------------------------------- vacuous passes ----

class TestNeverPassesVacuously(unittest.TestCase):
    """The single most important property: no pass without a comparison."""

    def test_empty_trace_is_unknown_not_pass(self):
        sb = Scoreboard("exact", EchoPredictor(SPEC))
        res = sb.run([])
        self.assertEqual(res.status, "unknown")
        self.assertIn("nothing", res.reason)

    def test_no_input_interface_transactions_is_unknown(self):
        """Monitors bound to the wrong interfaces, or a schema/model naming
        disagreement — silence here must not read as success."""
        sb = Scoreboard("exact", EchoPredictor(SPEC))
        res = sb.run([Txn("some_other_iface", "thing", {"x": 1})])
        self.assertEqual(res.status, "unknown")
        self.assertIn("input interfaces", res.reason)

    def test_inputs_but_no_outputs_either_side_is_unknown(self):
        """Writes produce no output transactions. Replaying them compares
        nothing, so the verdict is unknown even though nothing disagreed."""
        sb = Scoreboard("exact", EchoPredictor(SPEC))
        res = sb.run([w(4, 0xAA), w(8, 0xBB)])
        self.assertEqual(res.status, "unknown")
        self.assertIn("nothing was compared", res.reason)

    def test_invariant_with_no_relevant_transactions_is_unknown(self):
        sb = Scoreboard("invariant", LivenessChecker(SPEC))
        res = sb.run([Txn("unrelated", "x", {})])
        self.assertEqual(res.status, "unknown")

    def test_observe_strategy_is_not_applicable_not_pass(self):
        """An autonomous scope is not 'passed' by the scoreboard — it has no
        opinion, and saying so is different from claiming success."""
        sb = Scoreboard("observe")
        res = sb.run([Txn("anything", "x", {})])
        self.assertEqual(res.status, "not_applicable")


# ------------------------------------------------------------- matching ----

class TestExactMatching(unittest.TestCase):
    def test_clean_match_passes(self):
        sb = Scoreboard("exact", EchoPredictor(SPEC), scope="csr")
        trace = [w(4, 0xAA), r(4), out(4, 0xAA)]
        res = sb.run(trace)
        self.assertEqual(res.status, "pass")
        self.assertEqual(res.matched, 1)
        self.assertEqual(res.mismatches, [])

    def test_wrong_value_is_a_value_mismatch(self):
        sb = Scoreboard("exact", EchoPredictor(SPEC), scope="csr")
        res = sb.run([w(4, 0xAA), r(4), out(4, 0xBAD)])
        self.assertEqual(res.status, "fail")
        self.assertEqual(len(res.mismatches), 1)
        self.assertEqual(res.mismatches[0].kind, "value")
        self.assertEqual(res.mismatches[0].observed.fields["data"], 0xBAD)

    def test_design_produced_nothing_is_missing(self):
        sb = Scoreboard("exact", EchoPredictor(SPEC), scope="csr")
        res = sb.run([w(4, 0xAA), r(4)])          # no observed output
        self.assertEqual(res.status, "fail")
        self.assertEqual([m.kind for m in res.mismatches], ["missing"])

    def test_design_produced_extra_is_unexpected(self):
        sb = Scoreboard("exact", EchoPredictor(SPEC), scope="csr")
        res = sb.run([w(4, 0xAA), r(4), out(4, 0xAA), out(9, 0x1)])
        self.assertEqual(res.status, "fail")
        self.assertEqual([m.kind for m in res.mismatches], ["unexpected"])


class TestAlignmentDoesNotCascade(unittest.TestCase):
    """A dropped transaction must cost one finding, not N."""

    def test_single_drop_in_long_stream_reports_once(self):
        pred = [out(i, i * 2) for i in range(20)]
        obs = [t for t in pred if t.fields["addr"] != 7]   # drop exactly one
        matched, mm = align(pred, obs, "csr_out")
        self.assertEqual(len(mm), 1, f"expected 1 finding, got {len(mm)}")
        self.assertEqual(mm[0].kind, "missing")
        self.assertEqual(matched, 19)

    def test_single_extra_in_long_stream_reports_once(self):
        pred = [out(i, i * 2) for i in range(20)]
        obs = pred[:10] + [out(99, 0xFF)] + pred[10:]
        matched, mm = align(pred, obs, "csr_out")
        self.assertEqual(len(mm), 1)
        self.assertEqual(mm[0].kind, "unexpected")
        self.assertEqual(matched, 20)

    def test_one_wrong_value_among_many_reports_once(self):
        pred = [out(i, i * 2) for i in range(20)]
        obs = [out(i, (i * 2) if i != 5 else 0xDEAD) for i in range(20)]
        matched, mm = align(pred, obs, "csr_out")
        self.assertEqual(len(mm), 1)
        self.assertEqual(mm[0].kind, "value")
        self.assertEqual(matched, 19)


class TestKeyedMatching(unittest.TestCase):
    """Where the spec permits out-of-order responses, position is not identity."""

    def test_reordered_responses_still_match(self):
        pred = [out(1, 0x10), out(2, 0x20), out(3, 0x30)]
        obs = [out(3, 0x30), out(1, 0x10), out(2, 0x20)]
        matched, mm = align_keyed(pred, obs, "csr_out", "addr")
        self.assertEqual(matched, 3)
        self.assertEqual(mm, [])

    def test_reorder_would_fail_in_order_matching(self):
        """Confirms the keyed mode is doing real work."""
        pred = [out(1, 0x10), out(2, 0x20), out(3, 0x30)]
        obs = [out(3, 0x30), out(1, 0x10), out(2, 0x20)]
        _, mm = align(pred, obs, "csr_out")
        self.assertTrue(mm)

    def test_keyed_still_catches_a_wrong_value(self):
        pred = [out(1, 0x10), out(2, 0x20)]
        obs = [out(2, 0xBAD), out(1, 0x10)]
        matched, mm = align_keyed(pred, obs, "csr_out", "addr")
        self.assertEqual(matched, 1)
        self.assertEqual([m.kind for m in mm], ["value"])

    def test_keyed_catches_a_never_answered_request(self):
        pred = [out(1, 0x10), out(2, 0x20)]
        obs = [out(1, 0x10)]
        matched, mm = align_keyed(pred, obs, "csr_out", "addr")
        self.assertEqual(matched, 1)
        self.assertEqual([m.kind for m in mm], ["missing"])


# ------------------------------------------------------------ composition --

class TestComposition(unittest.TestCase):
    def test_two_stage_chain_predicts_through(self):
        comp = CompositePredictor([EchoPredictor(SPEC), DoublerPredictor(SPEC)])
        self.assertEqual(comp.INPUT_IFACES, ("csr_in",))
        self.assertEqual(comp.OUTPUT_IFACES, ("final",))
        sb = Scoreboard("composed", comp, scope="path")
        trace = [w(4, 0x10), r(4), Txn("final", "value", {"data": 0x20})]
        res = sb.run(trace)
        self.assertEqual(res.status, "pass", res.summary())
        self.assertEqual(res.matched, 1)

    def test_chain_detects_a_wrong_final_value(self):
        comp = CompositePredictor([EchoPredictor(SPEC), DoublerPredictor(SPEC)])
        sb = Scoreboard("composed", comp, scope="path")
        res = sb.run([w(4, 0x10), r(4), Txn("final", "value", {"data": 0x99})])
        self.assertEqual(res.status, "fail")
        self.assertEqual(res.mismatches[0].kind, "value")

    def test_empty_chain_rejected(self):
        with self.assertRaises(ValueError):
            CompositePredictor([])


# -------------------------------------------------------------- invariant --

class TestInvariantStrategy(unittest.TestCase):
    def test_all_requests_served_passes(self):
        sb = Scoreboard("invariant", LivenessChecker(SPEC), scope="loop")
        trace = [Txn("req", "r", {"id": 1}), Txn("done", "d", {"id": 1})]
        res = sb.run(trace)
        self.assertEqual(res.status, "pass")
        self.assertEqual(res.violations, [])

    def test_starved_request_is_a_violation(self):
        sb = Scoreboard("invariant", LivenessChecker(SPEC), scope="loop")
        trace = [Txn("req", "r", {"id": 1}), Txn("req", "r", {"id": 2}),
                 Txn("done", "d", {"id": 1})]
        res = sb.run(trace)
        self.assertEqual(res.status, "fail")
        self.assertEqual(len(res.violations), 1)
        self.assertEqual(res.violations[0].taxonomy_id, "REF_001")


# ---------------------------------------------------------- wrong wiring ---

class TestStrategyModelAgreement(unittest.TestCase):
    def test_predictor_for_invariant_strategy_is_rejected(self):
        with self.assertRaises(TypeError):
            Scoreboard("invariant", EchoPredictor(SPEC))

    def test_checker_for_exact_strategy_is_rejected(self):
        with self.assertRaises(TypeError):
            Scoreboard("exact", LivenessChecker(SPEC))

    def test_unknown_strategy_is_rejected(self):
        with self.assertRaises(ValueError):
            Scoreboard("vibes", EchoPredictor(SPEC))


# ---------------------------------------------------------------- output ---

class TestFindingEmission(unittest.TestCase):
    def test_mismatches_become_findings_in_the_agreed_schema(self):
        sb = Scoreboard("exact", EchoPredictor(SPEC), scope="config_regs")
        res = sb.run([w(4, 0xAA), r(4), out(4, 0xBAD)])
        f = res.to_findings(spec_revision="rev1", drop_id="drop_a")[0]
        for k in ("source", "target", "kind", "scope", "severity",
                  "spec_revision", "rtl_drop", "detail", "evidence", "status"):
            self.assertIn(k, f)
        self.assertEqual(f["scope"], "config_regs")
        self.assertEqual(f["spec_revision"], "rev1")

    def test_violations_carry_their_taxonomy_id_into_findings(self):
        sb = Scoreboard("invariant", LivenessChecker(SPEC), scope="loop")
        res = sb.run([Txn("req", "r", {"id": 1})])
        f = res.to_findings()[0]
        self.assertEqual(f["taxonomy_id"], "REF_001")

    def test_timing_is_never_compared(self):
        """time_ns differences must not affect the verdict — SVA owns timing."""
        sb = Scoreboard("exact", EchoPredictor(SPEC), scope="csr")
        o = out(4, 0xAA)
        o.time_ns = 999999
        res = sb.run([w(4, 0xAA), r(4), o])
        self.assertEqual(res.status, "pass")


if __name__ == "__main__":
    unittest.main(verbosity=1)
