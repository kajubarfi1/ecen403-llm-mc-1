#!/usr/bin/env python3
"""write_read.py: every read follows a write of the same address with no
idle between them, so the controller (not the host) sets the write-to-read
turnaround (2026-10-15)."""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
import write_read as WR  # noqa: E402
from register_walk import SPEC, SCHEMAS, CATALOG  # noqa: E402


class TestWriteRead(unittest.TestCase):

    def setUp(self):
        with open(SPEC) as f:
            self.spec = json.load(f)
        with open(SCHEMAS) as f:
            self.schemas = json.load(f)["interfaces"]
        with open(CATALOG) as f:
            self.catalog = json.load(f)["interfaces"]

    def test_pairs_share_an_address_and_have_no_idle(self):
        seq = WR.generate(self.spec, self.schemas, self.catalog, seed=3, pairs=5)
        steps = seq["steps"]
        self.assertEqual(steps[0], {"op": "reset"})
        drives = steps[1:]
        self.assertEqual(len(drives), 10)
        self.assertTrue(all(s["op"] == "drive" for s in drives), "no idle steps")
        for w, r in zip(drives[0::2], drives[1::2]):
            self.assertEqual((w["kind"], r["kind"]), ("write", "read"))
            self.assertEqual(w["fields"]["addr"], r["fields"]["addr"])
        self.assertIn("VP_TIME_012", seq["targets"])
        self.assertEqual(seq["_provenance"]["generator"], "write_read.py")

    def test_deterministic_per_seed(self):
        a = WR.generate(self.spec, self.schemas, self.catalog, seed=7, pairs=4)
        b = WR.generate(self.spec, self.schemas, self.catalog, seed=7, pairs=4)
        self.assertEqual(a["steps"], b["steps"])


if __name__ == "__main__":
    unittest.main()
