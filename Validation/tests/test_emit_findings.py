#!/usr/bin/env python3
"""Tests for the findings v2 emitter and the retry-instructions adapter."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "findings"))
import emit_findings as EF  # noqa: E402
import retry_adapter as RA  # noqa: E402


class TestParsing(unittest.TestCase):

    def test_checker_line_with_rule_and_txn(self):
        ln = ("  SCHED_004 (activate_wrong_row): ACT to bank 2 row 9 but row 5 was "
              "requested @ [sched_cmd.command aux=0x1 bank=0x2 row=0x9 type=0x1]")
        m = EF.CHECK_RE.match(ln)
        self.assertEqual(m.group(1), "SCHED_004")
        self.assertEqual(m.group(2), "activate_wrong_row")
        self.assertEqual(EF._iface_kind(m.group(4)), ("sched_cmd", "command"))

    def test_checker_line_without_rule_name(self):
        m = EF.CHECK_RE.match("  REF_004: no refresh requested after init_done")
        self.assertEqual(m.group(1), "REF_004")
        self.assertIsNone(m.group(2))

    def test_mismatch_line(self):
        ln = ("  csr_rsp[56] value: predicted [csr_rsp.read_data addr=0x18 data=0x1ff] "
              "but observed [csr_rsp.read_data addr=0x18 data=0xffffffff]")
        m = EF.MISMATCH_RE.match(ln)
        self.assertEqual((m.group(1), m.group(3)), ("csr_rsp", "value"))
        po = EF.PRED_OBS_RE.search(m.group(4))
        self.assertIn("data=0x1ff", po.group(1))
        self.assertIn("data=0xffffffff", po.group(2))

    def test_x_value_line(self):
        ln = ("  x_value: wb_rsp.read_data seq=474 carries X/Z on ['data'] — the "
              "design drove an undefined value @ [wb_rsp.read_data addr=0x36]")
        m = EF.XVAL_RE.match(ln)
        self.assertEqual((m.group(1), m.group(2), m.group(3)), ("wb_rsp", "read_data", "474"))


class TestDiscriminator(unittest.TestCase):

    def test_register_name_and_differing_fields(self):
        regs = {0x18: "REFRESH_CONFIG", 0x0: "CTRL_STATUS"}
        d = EF._mismatch_discriminator(
            "csr_rsp.read_data addr=0x18 data=0x1ff err=0x0",
            "csr_rsp.read_data addr=0x18 data=0xffffffff err=0x0", regs)
        self.assertEqual(d, "[data]@REFRESH_CONFIG")
        d = EF._mismatch_discriminator(
            "ddr_cmd.command addr=0x63ca bank=0x4 cmd=0x2",
            "ddr_cmd.command addr=0x0 bank=0x4 cmd=0x2", regs)
        self.assertEqual(d, "[addr]")

    def test_no_fields_no_tag(self):
        self.assertEqual(EF._mismatch_discriminator("", "x", {}), "")


class TestOwners(unittest.TestCase):

    def test_rule_owner_and_family_fallback(self):
        r = EF.Rules()
        self.assertEqual(r.owners("SCHED_004", "x")[0], "cmd_queue")
        self.assertEqual(r.owners("TIMING_003", "x")[0], "scheduler")
        self.assertEqual(r.owners("INIT_002", "x"), ["init_fsm"])
        self.assertEqual(r.owners("ZZZ_001", "fallback"), ["fallback"])

    def test_requirements_come_from_rules_and_taxonomy(self):
        r = EF.Rules()
        self.assertIn("ACTIVATE", r.req["SCHED_004"])
        self.assertTrue(r.req.get("TIMING_001"))
        self.assertTrue(r.req.get("CSR_001"))


class TestHistory(unittest.TestCase):

    def test_introduced_and_first_seen(self):
        snaps = [("aaa", "2026-01-01", {"id:SCHED_002"}),
                 ("bbb", "2026-02-01", {"id:SCHED_002"}),
                 ("ccc", "2026-03-01", {"id:SCHED_002", "id:CSR_001"})]
        first, intro = EF.history_for("CSR_001", "exact:config_regs:value", snaps, "ccc")
        self.assertEqual((first, intro), ("ccc", "ccc"))
        first, intro = EF.history_for("SCHED_002", "invariant:s:cas_no_matching_request",
                                      snaps, "ccc")
        self.assertEqual((first, intro), ("aaa", None))

    def test_unseen_is_first_seen_now(self):
        first, intro = EF.history_for("NEW_001", "exact:x", [], "head")
        self.assertEqual((first, intro), ("head", None))


class TestAdapter(unittest.TestCase):

    def test_shape_matches_frontend_contract(self):
        doc = {"drop": "b4d6f45", "spec_revision": "r", "resolved": [],
               "findings": [{
                   "id": "config_regs/MISMATCH/csr_rsp", "kind": "rtl_defect",
                   "check_id": "MISMATCH/csr_rsp", "owner_module": "config_regs",
                   "detectors": ["exact:config_regs:value"],
                   "owner_candidates": ["config_regs"], "severity": "major",
                   "confidence": "observed", "title": "t", "requirement": "req",
                   "spec_ref": "csr_register_map", "expected": "0x1ff",
                   "actual": "0xffffffff", "anchor": [{"file": "f", "line": 230}],
                   "paths": ["path_12"], "occurrences": 15,
                   "repro": {"path": "path_12", "command": "c"}, "status": "open"}]}
        ri = RA.adapt(doc)
        self.assertEqual(ri["status"], "FAIL")
        self.assertEqual(ri["failed_modules"], ["config_regs"])
        fc = ri["retry_instructions"]["config_regs"]["failed_checks"][0]
        for k in ("id", "name", "pass", "expected", "actual"):
            self.assertIn(k, fc)
        self.assertFalse(fc["pass"])
        self.assertEqual(fc["anchor"][0]["line"], 230)
        self.assertFalse(ri["requires_human_review"])

    def test_resolved_findings_are_not_retry_items(self):
        doc = {"drop": "x", "resolved": [], "findings": [
            {"id": "a/b", "kind": "rtl_defect", "check_id": "b", "owner_module": "a",
             "severity": "major", "confidence": "observed", "title": "t",
             "expected": "", "actual": "", "paths": [], "occurrences": 1,
             "repro": {"path": "p", "command": "c"}, "status": "resolved"}]}
        self.assertEqual(RA.adapt(doc)["status"], "PASS")


if __name__ == "__main__":
    unittest.main()
