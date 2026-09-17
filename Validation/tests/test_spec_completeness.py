#!/usr/bin/env python3
"""
Tests for the spec intake gate.

The gate must (a) flag every question the current spec is silent on, (b) pass
once those questions are answered, (c) reject an answer outside the allowed
vocabulary, and (d) stay quiet about sections a spec does not have — a spec
with no register map owes no register-map answers.
"""

import copy
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "spec"))
import spec_completeness as sc  # noqa: E402

SPEC = os.path.join(HERE, "..", "spec", "llmmc_microarchitecturespec_filled.json")


def load():
    with open(SPEC) as f:
        spec = json.load(f)
    with open(sc.RULES) as f:
        rules = json.load(f)["rules"]
    with open(sc.PATH_DEFS) as f:
        pdefs = json.load(f)["paths"]
    return spec, rules, pdefs


def statuses(spec, rules, pdefs):
    return {r["id"]: sc.check_rule(r, spec, pdefs)[0] for r in rules}


class TestIntakeGate(unittest.TestCase):

    def test_current_spec_gaps_are_the_ones_found_in_simulation(self):
        spec, rules, pdefs = load()
        st = statuses(spec, rules, pdefs)
        for rid in ("CSR_UNMAPPED_READ_DATA", "CSR_READ_BYTE_ENABLES",
                    "CSR_STATUS_READ_SAMPLING", "DDR_DM_POLARITY",
                    "TAXONOMY_SCHEDULER_FAMILY", "INTERFACE_CONTRACTS",
                    "TAXONOMY_NAMES_TIMING_PARAMS", "INIT_TMRD", "INIT_TMOD"):
            self.assertEqual(st[rid], "gap", rid)
        # the one unnamed timing parameter is tREFI
        rule = next(r for r in rules if r["id"] == "TAXONOMY_NAMES_TIMING_PARAMS")
        _, detail = sc.check_rule(rule, spec, pdefs)
        self.assertIn("tREFI", detail)
        self.assertNotIn("tRFC", detail)

    def test_completed_spec_passes(self):
        spec, rules, pdefs = load()
        spec = copy.deepcopy(spec)
        spec["csr_register_map"].update({
            "unmapped_read_data": "zero",
            "unmapped_write_behavior": "ignored_with_error",
            "read_byte_enable_semantics": "ignored",
            "status_read_sampling": "previous_edge"})
        spec["data_path_mapping"]["ddr_dm_polarity"] = "active_high_mask"
        spec["failure_taxonomy"]["categories"].append(
            {"id": "SCHED_001", "name": "dropped request"})
        spec["failure_taxonomy"]["categories"].append(
            {"id": "TIMING_012", "name": "tREFI violation"})
        # stating tMRD/tMOD obliges the taxonomy to name them too
        spec["timing_model"]["tMRD"] = 5.0
        spec["timing_model"]["tMOD"] = 15.0
        spec["failure_taxonomy"]["categories"].append(
            {"id": "INIT_004", "name": "tMRD / tMOD violation"})
        spec["block_interfaces"] = [
            {"from": a, "to": b} for p in pdefs
            for a, b in zip(p["blocks"], p["blocks"][1:])]
        st = statuses(spec, rules, pdefs)
        self.assertTrue(all(s == "ok" for s in st.values()), st)

    def test_value_outside_vocabulary_is_rejected(self):
        spec, rules, pdefs = load()
        spec = copy.deepcopy(spec)
        spec["csr_register_map"]["unmapped_read_data"] = "whatever"
        st = statuses(spec, rules, pdefs)
        self.assertEqual(st["CSR_UNMAPPED_READ_DATA"], "invalid_value")

    def test_absent_section_owes_nothing(self):
        spec, rules, pdefs = load()
        spec = copy.deepcopy(spec)
        del spec["csr_register_map"]
        del spec["data_path_mapping"]["pack_mode"]
        st = statuses(spec, rules, pdefs)
        self.assertEqual(st["CSR_UNMAPPED_READ_DATA"], "not_applicable")
        self.assertEqual(st["DDR_DM_POLARITY"], "not_applicable")

    def test_missing_hop_contract_is_named(self):
        spec, rules, pdefs = load()
        spec = copy.deepcopy(spec)
        hops = sorted({(a, b) for p in pdefs
                       for a, b in zip(p["blocks"], p["blocks"][1:])})
        spec["block_interfaces"] = [{"from": a, "to": b} for a, b in hops[1:]]
        rule = next(r for r in rules if r["kind"] == "path_interfaces")
        status, detail = sc.check_rule(rule, spec, pdefs)
        self.assertEqual(status, "gap")
        self.assertIn(f"{hops[0][0]}->{hops[0][1]}", detail)

    def test_findings_carry_a_patch_and_the_standard(self):
        spec, rules, pdefs = load()
        gaps = [(r,) + sc.check_rule(r, spec, pdefs) for r in rules
                if sc.check_rule(r, spec, pdefs)[0] == "gap"]
        out = sc.findings_for(gaps, spec)
        self.assertEqual(len(out), len(gaps))
        dm = next(f for f in out if f["evidence"]["rule"] == "DDR_DM_POLARITY")
        self.assertEqual(dm["evidence"]["proposed_patch"],
                         {"data_path_mapping": {"ddr_dm_polarity": "active_high_mask"}})
        self.assertIn("JESD79-3", dm["detail"])
        self.assertTrue(all(f["kind"] == "spec_gap" for f in out))


if __name__ == "__main__":
    unittest.main()
