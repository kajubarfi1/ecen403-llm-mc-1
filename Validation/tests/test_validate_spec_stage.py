#!/usr/bin/env python3
"""The spec-review stage (Frontend pipeline contract: validate_spec(spec,
compile_result) -> status/findings/validator). Blocking problems FAIL
(schema, JEDEC, register map, compiler checks, missing revision); intake
gaps are advisory and routed with requires_human_review."""

import copy
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
V = os.path.abspath(os.path.join(HERE, ".."))
ROOT = os.path.abspath(os.path.join(V, ".."))
sys.path.insert(0, os.path.join(V, "spec"))
import validate_spec_stage as VS  # noqa: E402

with open(os.path.join(V, "spec", "llmmc_microarchitecturespec_filled.json")) as f:
    GOLDEN = json.load(f)


def run(spec, cr=None):
    return VS.validate_spec(spec, cr, write=False)


class TestContract(unittest.TestCase):
    def test_shape(self):
        r = run(GOLDEN)
        self.assertIn(r["status"], ("PASS", "FAIL"))
        self.assertIsInstance(r["findings"], list)
        self.assertTrue(all(isinstance(x, str) for x in r["findings"]))
        self.assertIsInstance(r["validator"], str)

    def test_golden_passes(self):
        r = run(GOLDEN)
        self.assertEqual(r["status"], "PASS", r["findings"][:3])
        self.assertEqual(r["review"]["blocking"], [])

    def test_gaps_are_advisory_and_ask_for_a_human(self):
        # the golden spec answers every intake question since 2026-10-08;
        # a spec that does not still PASSES, with the gap advisory
        s = copy.deepcopy(GOLDEN)
        s["csr_register_map"].pop("unmapped_read_data", None)
        r = run(s)
        self.assertEqual(r["status"], "PASS", r["findings"][:3])
        self.assertTrue(any(x.startswith("[gap:") for x in r["findings"]), r["findings"][:3])
        self.assertTrue(r["review"]["requires_human_review"])


class TestBlocking(unittest.TestCase):
    def test_missing_revision(self):
        s = copy.deepcopy(GOLDEN)
        s.pop("revision")
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("revision" in x for x in r["review"]["blocking"]))

    def test_missing_required_section(self):
        s = copy.deepcopy(GOLDEN)
        s.pop("observability")          # in the schema's required list
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("observability" in x and "schema" in x for x in r["review"]["blocking"]))

    def test_enum_violation(self):
        s = copy.deepcopy(GOLDEN)
        s["host_interface"]["interface_type"] = "pcie"
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("interface_type" in x for x in r["review"]["blocking"]))

    def test_jedec_violation(self):
        s = copy.deepcopy(GOLDEN)
        s["timing_model"]["tRAS"] = 1.0           # far below JESD79-3 for any bin
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any(x.startswith("JEDEC") for x in r["review"]["blocking"]), r["review"]["blocking"][:3])

    def test_false_self_claim(self):
        s = copy.deepcopy(GOLDEN)
        cc = s["timing_model"].setdefault("$consistency_checks", {})
        cc["unit_test_rule"] = "tRC == tRAS + tRP -> 48.75 == 35.0 + 10.0 [check]"
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("self-claim" in x for x in r["review"]["blocking"]))

    def test_register_reset_disagrees_with_derived_timing(self):
        s = copy.deepcopy(GOLDEN)
        reg = next(r for r in s["csr_register_map"]["registers"] if r["name"] == "TIMING_0")
        fld = next(f for f in reg["fields"] if f["name"] == "tRCD_nCK")
        fld["reset_value"] = int(fld["reset_value"]) + 1
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("tRCD_nCK" in x and "derived_cycles" in x for x in r["review"]["blocking"]))

    def test_overlapping_fields(self):
        s = copy.deepcopy(GOLDEN)
        reg = next(r for r in s["csr_register_map"]["registers"] if r["name"] == "TIMING_0")
        reg["fields"][1]["bits"] = "9:2"
        r = run(s)
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("overlap" in x for x in r["review"]["blocking"]))

    def test_compiler_checks_failed(self):
        r = run(GOLDEN, {"consistency_ok": False,
                         "consistency_checks": [{"name": "tRC_rule", "pass": False}]})
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(any("compiler" in x and "tRC_rule" in x for x in r["review"]["blocking"]))


class TestCompiledSpec(unittest.TestCase):
    PATH = os.path.join(ROOT, "Frontend2", "OutputFolders", "generated_spec.json")

    @unittest.skipUnless(os.path.exists(PATH), "no compiled spec in the drop")
    def test_compiled_spec_is_reviewed_against_the_shared_schema(self):
        with open(self.PATH) as f:
            spec = json.load(f)
        r = run(spec)
        # JEDEC and registers hold for the compiled spec; whatever the
        # schema says about it is reported, not hidden
        self.assertEqual([x for x in r["review"]["blocking"] if x.startswith("JEDEC")], [])
        self.assertEqual([x for x in r["review"]["blocking"] if x.startswith("registers")], [])


if __name__ == "__main__":
    unittest.main()
