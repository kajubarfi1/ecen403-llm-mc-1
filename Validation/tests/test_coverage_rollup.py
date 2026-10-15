#!/usr/bin/env python3
"""The rollup distinguishes a stimulus gap from a bin the spec itself places
out of reach, and the timing covergroup carries the enforced-window bin that
makes the distinction measurable (2026-10-15)."""

import json
import os
import sys
import tempfile
import unittest
import zipfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "coverage"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sva"))
import coverage_rollup as CR  # noqa: E402
import coverage_gen as CG  # noqa: E402


def _report(points):
    """An imc-shaped report dir: {cp: {bin: hit}} -> zipData1.zip/covData0.json."""
    d = tempfile.mkdtemp()
    tree = {"title": "top", "subitems": []}
    for cp, bins in points.items():
        n = sum(1 for h in bins.values() if h)
        tree["subitems"].append({
            "title": cp, "All Cov": f"{n} / {len(bins)} ({100.0 * n / len(bins):.0f}%)",
            "subitems": [{"title": b, "All Cov": f"{int(h)} / 1 ({100 * int(h)}%)"}
                         for b, h in bins.items()]})
    with zipfile.ZipFile(os.path.join(d, "zipData1.zip"), "w") as z:
        z.writestr("covData0.json", json.dumps(tree))
    return d


VPLAN = {"items": [
    {"id": "VP_TIME_004", "title": "tRCD boundary exercised", "scope": "timing",
     "coverage_items": [{"type": "functional", "name": "cg_timing.cp_trcd_spacing", "goal": 100}]},
    {"id": "VP_FLOW_001", "title": "back-pressure", "scope": "cmd_queue",
     "coverage_items": [{"type": "functional", "name": "cg_cmd_queue.cp_backpressure_exercised", "goal": 100}]},
]}


class TestPerBinParse(unittest.TestCase):

    def test_bins_detail_is_read(self):
        m = CR.parse_imc_report(_report({"cp_trcd_spacing": {"at_minimum": False, "above_minimum": True}}))
        self.assertEqual(m["cp_trcd_spacing"]["bins_detail"], {"at_minimum": False, "above_minimum": True})
        self.assertEqual(m["cp_trcd_spacing"]["bins_hit"], 1)


class TestUnreachableBySpec(unittest.TestCase):

    def _measured(self, unhit_backpressure=True):
        return CR.parse_imc_report(_report({
            "cp_trcd_spacing": {"at_minimum": False, "within_enforced_window": False,
                                "at_or_above_enforced": True},
            "cp_backpressure_exercised": {"occurred": not unhit_backpressure}}))

    def test_window_scale_marks_only_the_spec_bound_bins(self):
        items = {i["id"]: i for i in CR.rollup(VPLAN, self._measured(), window_scale=4)}
        self.assertEqual(items["VP_TIME_004"]["status"], "unreachable_by_spec")
        self.assertIn("window_scale = 4", items["VP_TIME_004"]["reason"])
        self.assertEqual(items["VP_TIME_004"]["coverage"][0]["unhit_bins"],
                         ["at_minimum", "within_enforced_window"])
        # a 0% occurred bin is a real gap whatever the spec says
        self.assertEqual(items["VP_FLOW_001"]["status"], "partial")

    def test_without_the_declaration_it_is_a_stimulus_gap(self):
        items = {i["id"]: i for i in CR.rollup(VPLAN, self._measured(), window_scale=1)}
        self.assertEqual(items["VP_TIME_004"]["status"], "partial")

    def test_a_short_reachable_bin_keeps_the_item_partial(self):
        m = CR.parse_imc_report(_report({
            "cp_trcd_spacing": {"at_minimum": False, "within_enforced_window": False,
                                "at_or_above_enforced": False}}))
        items = {i["id"]: i for i in CR.rollup(VPLAN, m, window_scale=4)}
        self.assertEqual(items["VP_TIME_004"]["status"], "partial")

    def test_window_scale_read_from_spec(self):
        self.assertEqual(CR.window_scale_of({"timing_model": {"counter_clock": {"window_scale": 4}}}), 4)
        self.assertEqual(CR.window_scale_of({"timing_model": {}}), 1)
        self.assertEqual(CR.window_scale_of({}), 1)


class TestEnforcedWindowBins(unittest.TestCase):

    def test_enforced_window_from_spec(self):
        ws, params = CG.enforced_window({"timing_model": {"counter_clock": {
            "window_scale": 4, "applies_to": ["bank_tracker: tRCD, tRP, tFAW"]}}})
        self.assertEqual((ws, params), (4, {"tRCD", "tRP", "tFAW"}))
        self.assertEqual(CG.enforced_window({"timing_model": {}}), (1, None))

    def test_golden_spec_gets_the_margin_bin(self):
        with open(CG.SPEC_PATH) as f:
            spec = json.load(f)
        with open(CG.RULES_PATH) as f:
            rules = json.load(f)
        with open(CG.CATALOG_PATH) as f:
            catalog = json.load(f)["interfaces"]
        with open(CG.SCHEMA_PATH) as f:
            schemas = json.load(f)["interfaces"]
        want = CG.vplan_expects(CG.VPLAN_PATH)
        if rules["command_signals"]["interface"] not in schemas:
            self.skipTest("command interface not in the current drop's schemas")
        _, src, _, generated, _ = CG.generate(spec, rules, catalog, schemas, want)
        ws, _ = CG.enforced_window(spec)
        if ws > 1:
            self.assertIn("bins within_enforced_window", src)
            self.assertIn("bins at_or_above_enforced", src)
            self.assertIn("bins at_minimum   = {3}", src)      # tRCD at 5ns: still the JEDEC boundary
        else:
            self.assertIn("bins above_minimum", src)


if __name__ == "__main__":
    unittest.main()
