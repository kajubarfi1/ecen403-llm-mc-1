#!/usr/bin/env python3
"""Optional schema fields are filled from their defaults, and a pipelined
handshake interface drives consecutive steps as one run (2026-10-28)."""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
import sequence_contract as SC  # noqa: E402
import driver_gen as DG  # noqa: E402


def _load():
    with open(os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")) as f:
        schemas = json.load(f)["interfaces"]
    with open(os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")) as f:
        catalog = json.load(f)["interfaces"]
    return schemas, catalog


class TestDefaults(unittest.TestCase):

    def test_a_step_without_the_optional_fields_is_filled_not_refused(self):
        schemas, catalog = _load()
        if "cti" not in schemas["wb"]["kinds"]["read"]:
            self.skipTest("schemas not regenerated with the burst fields")
        seq = {"name": "t", "targets": ["x"], "steps": [
            {"op": "reset"}, {"op": "drive", "iface": "wb", "kind": "read", "fields": {"addr": 4}}]}
        self.assertEqual(SC.validate(seq, schemas, {"wb"}), [])
        self.assertEqual(seq["steps"][1]["fields"], {"addr": 4, "cti": 0, "bte": 0})


class TestPipelinedRun(unittest.TestCase):

    def test_consecutive_drives_form_one_run(self):
        schemas, catalog = _load()
        if not catalog["wb"].get("drive", {}).get("pipelined"):
            self.skipTest("wb is not declared pipelined")
        seq = {"name": "t", "targets": ["x"], "steps": [
            {"op": "reset"},
            {"op": "drive", "iface": "wb", "kind": "read", "fields": {"addr": 0, "cti": 2, "bte": 0}},
            {"op": "drive", "iface": "wb", "kind": "read", "fields": {"addr": 4, "cti": 7, "bte": 0}},
            {"op": "idle", "cycles": 2},
            {"op": "drive", "iface": "wb", "kind": "write", "fields": {"addr": 8, "data": 1, "sel": 15, "cti": 0, "bte": 0}}]}
        self.assertEqual(SC.validate(seq, schemas, {"wb"}), [])
        sv = DG.generate(seq, schemas, catalog)
        self.assertIn("int issued_wb", sv)
        self.assertIn("task automatic wait_all_wb", sv)
        self.assertEqual(sv.count("pipelined beat; run continues"), 1)
        self.assertEqual(sv.count("pipelined beat; run ends"), 2)
        self.assertEqual(sv.count("      wait_all_wb();"), 2, "one wait per run")
        # the second beat of the run is presented right after the first one's
        # acceptance, with no fresh negedge in between: back to back
        second = sv.split("run continues")[1].split("run ends")[1].split("\n")[1]
        self.assertTrue(second.strip().startswith("wb_adr_i"), second)


if __name__ == "__main__":
    unittest.main()


class TestGapInsideRun(unittest.TestCase):
    """An idle marked within_run is a gap between two beats of one pipelined
    run: the run does not end before it and does not restart after it."""

    def _seq(self):
        sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
        import ack_collision as AC
        spec = json.load(open(AC.SPEC)); schemas = json.load(open(AC.SCHEMAS))["interfaces"]
        catalog = json.load(open(AC.CATALOG))["interfaces"]
        return AC.generate(spec, schemas, catalog, 1), schemas, catalog

    def test_sequence_validates_and_gap_is_inside_the_run(self):
        seq, schemas, catalog = self._seq()
        import sequence_contract as SC
        drivable = {i for i, d in catalog.items() if d.get("drive")}
        self.assertEqual(SC.validate(seq, schemas, drivable), [])
        import driver_gen as DG
        src = DG.generate(seq, schemas, catalog) if hasattr(DG, "generate") else DG.generate_driver(seq, schemas, catalog)
        text = src if isinstance(src, str) else src[1]
        # the read before a within_run gap does not wait for its ack; the write after it
        # does not open a new run (no negedge wait before its beat)
        i = text.index("gap inside a pipelined run")
        before = text[:i].rsplit("// wb.read", 1)[1]
        self.assertNotIn("wait_all_wb", before)
        after = text[i:].split("// wb.write", 1)[1].split("\n", 2)
        self.assertNotIn("@(negedge clk);", after[1])
        self.assertIn("wait_all_wb", text[i:])

    def test_within_run_idle_outside_a_run_is_rejected(self):
        seq, schemas, catalog = self._seq()
        import sequence_contract as SC
        bad = dict(seq, steps=[{"op": "reset"}, {"op": "idle", "cycles": 3, "within_run": True},
                               {"op": "drive", "iface": "wb", "kind": "read", "fields": seq["steps"][1]["fields"]}])
        drivable = {i for i, d in catalog.items() if d.get("drive")}
        errs = SC.validate(bad, schemas, drivable, require_targets=False)
        self.assertTrue(any("within_run" in e for e in errs), errs)
