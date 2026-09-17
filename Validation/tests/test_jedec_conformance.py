#!/usr/bin/env python3
"""
Tests for JEDEC spec conformance checking
==========================================
Two properties matter, and the second is the one that is usually missing:

  1. The golden spec passes.
  2. Every rule actually FIRES when its condition is violated.

Without (2) a conformance checker is indistinguishable from a function that
returns "pass" — the same failure this project already shipped once, where a
harness reported passes it had not earned. Each test below injects one
specific fault and asserts the corresponding rule catches it.

Run:  python3 Validation/tests/test_jedec_conformance.py
"""

import copy
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "jedec"))

import spec_conformance as sc

with open(sc.DEFAULT_SPEC) as f:
    GOLDEN = json.load(f)
with open(sc.RULES_PATH) as f:
    RULES = json.load(f)["rules"]


def run(spec):
    """Return {rule_id: status} for a spec."""
    return {r.rule["id"]: r.status for r in sc.check(spec, RULES)}


def fails(spec, rule_id):
    return run(spec).get(rule_id) == "fail"


class TestGoldenSpec(unittest.TestCase):
    def test_golden_spec_is_conformant(self):
        res = run(GOLDEN)
        bad = [k for k, v in res.items() if v == "fail"]
        self.assertEqual(bad, [], f"golden spec now violates {bad}")

    def test_no_rule_is_silently_skipped_on_golden(self):
        """A skip means the checker could not evaluate the rule. On the golden
        spec every rule should have the data it needs; a new skip signals the
        spec dropped a section the checker depends on."""
        res = run(GOLDEN)
        skipped = [k for k, v in res.items() if v == "skip"]
        self.assertEqual(skipped, [], f"unexpectedly skipped: {skipped}")

    def test_every_catalogued_rule_is_implemented(self):
        """The JSON catalog and the Python logic must not drift apart."""
        res = run(GOLDEN)
        catalogued = {r["id"] for r in RULES}
        self.assertEqual(catalogued - set(res), set(),
                         "catalogued rules with no implementation")

    def test_spec_self_claims_hold(self):
        self.assertEqual(sc.audit_self_claims(GOLDEN), [])


class TestRulesActuallyFire(unittest.TestCase):
    """Fault injection: one violation each, and the matching rule must catch it."""

    def mutate(self, fn):
        s = copy.deepcopy(GOLDEN)
        fn(s)
        return s

    def test_tRC_not_sum(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tRC", 50.0)), "J-TIM-001"))

    def test_tFAW_below_4x_tRRD(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tFAW", 25.0)), "J-TIM-002"))

    def test_tRRD_below_floor(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tRRD", 5.0)), "J-TIM-003"))

    def test_tWTR_below_floor(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tWTR", 4.0)), "J-TIM-004"))

    def test_tRTP_below_floor(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tRTP", 4.0)), "J-TIM-005"))

    def test_tCCD_not_4_clocks(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tCCD", 6.0)), "J-TIM-006"))

    def test_tWR_not_15ns(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tWR", 20.0)), "J-TIM-007"))

    def test_CWL_illegal_for_tCK(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("CWL_cycles", 6)), "J-TIM-008"))

    def test_tRFC_wrong_for_density(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tRFC", 110.0)), "J-TIM-009"))

    def test_tREFI_not_standard(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"].__setitem__("tREFI", 5000.0)), "J-TIM-010"))

    def test_reset_hold_too_short(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["initialization_sequence"].__setitem__("reset_hold_us", 100)),
            "J-INI-001"))

    def test_cke_delay_too_short(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["initialization_sequence"].__setitem__("cke_delay_us", 100)),
            "J-INI-002"))

    def test_tXPR_below_floor(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["initialization_sequence"].__setitem__("tXPR_ns", 20.0)),
            "J-INI-003"))

    def test_tZQinit_too_short(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["initialization_sequence"].__setitem__("tZQinit_ns", 200.0)),
            "J-INI-004"))

    def test_wrong_MRS_order(self):
        def f(s):
            d = s["initialization_sequence"]["$derived"]
            d["init_sequence_order"] = "CKE high → MR0 → MR1 → MR2 → MR3 → ZQCL"
        self.assertTrue(fails(self.mutate(f), "J-INI-005"))

    def test_MR0_without_dll_reset(self):
        def f(s):
            s["initialization_sequence"]["mode_registers"]["MR0"]["dll_reset"] = False
        self.assertTrue(fails(self.mutate(f), "J-INI-006"))

    def test_wrong_bank_count(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["memory_geometry"].__setitem__("bank_bits", 4)), "J-GEO-001"))

    def test_illegal_burst_length(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["memory_geometry"].__setitem__("burst_length", 16)),
            "J-GEO-002"))

    def test_tCK_mismatch_across_sections(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["clocking_model"].__setitem__("ddr_clock_period_ns", 1.5)),
            "J-CON-001"))

    def test_derived_cycles_inconsistent(self):
        self.assertTrue(fails(self.mutate(
            lambda s: s["timing_model"]["$derived_cycles"].__setitem__("tRCD_nCK", 99)),
            "J-CON-002"))

    def test_MR0_CL_disagrees_with_timing_model(self):
        def f(s):
            s["initialization_sequence"]["mode_registers"]["MR0"]["cas_latency_cycles"] = 9
        self.assertTrue(fails(self.mutate(f), "J-CON-003"))

    def test_MR2_CWL_disagrees_with_timing_model(self):
        def f(s):
            s["initialization_sequence"]["mode_registers"]["MR2"]["cas_write_latency_cycles"] = 6
        self.assertTrue(fails(self.mutate(f), "J-CON-004"))


class TestSelfClaimAudit(unittest.TestCase):
    """The spec carries its own '...-> 48.75 == 35.0 + 13.75 [check]' strings.
    A generator can write a passing-looking claim over a failing value."""

    def test_contradicted_claim_is_caught(self):
        s = copy.deepcopy(GOLDEN)
        s["timing_model"]["$consistency_checks"]["tRC_rule"] = \
            "tRC == tRAS + tRP → 99.0 == 35.0 + 13.75 ✓"
        issues = sc.audit_self_claims(s)
        self.assertTrue(any("tRC_rule" in i for i in issues), issues)


class TestMissingDataIsSkipNotPass(unittest.TestCase):
    """A rule whose inputs are absent must report skip — never pass. Silently
    passing on missing data is how an incomplete spec looks conformant."""

    def test_missing_timing_section_skips_not_passes(self):
        s = copy.deepcopy(GOLDEN)
        s["timing_model"].pop("tRC")
        self.assertEqual(run(s)["J-TIM-001"], "skip")

    def test_missing_geometry_skips_not_passes(self):
        s = copy.deepcopy(GOLDEN)
        s["memory_geometry"].pop("bank_bits")
        self.assertEqual(run(s)["J-GEO-001"], "skip")


if __name__ == "__main__":
    unittest.main(verbosity=1)
