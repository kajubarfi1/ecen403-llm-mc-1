#!/usr/bin/env python3
"""
Tests for the RTL drop resolver.

The property that matters: a block resolves ONLY inside the declared roots,
in root order, preferring the drop's consolidated manifest — and a block no
root provides is an error, never a copy from somewhere else in the tree.
"""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "structural"))
import rtl_drop as RD  # noqa: E402


def _write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)


MANIFEST = json.dumps({"ports": {"g": [{"name": "clk", "width": 1, "dir": "input"}]}})


class TestResolver(unittest.TestCase):

    def setUp(self):
        self.tmp = os.path.realpath(tempfile.mkdtemp())
        self.cfg = os.path.join(self.tmp, "rtl_drop.json")
        self.root_a = os.path.join(self.tmp, "drop_a")
        self.root_b = os.path.join(self.tmp, "drop_b")
        os.makedirs(self.root_a)
        os.makedirs(self.root_b)
        # a decoy OUTSIDE every root, newer than anything inside
        _write(os.path.join(self.tmp, "decoy", "blk.sv"), "// decoy")
        _write(os.path.join(self.tmp, "decoy", "blk_manifest.json"), MANIFEST)
        with open(self.cfg, "w") as f:
            json.dump({"roots": [os.path.relpath(self.root_a, RD.ROOT),
                                 os.path.relpath(self.root_b, RD.ROOT)],
                       "manifest_dirs_preferred": ["lint"]}, f)
        self._old = RD.CONFIG
        RD.CONFIG = self.cfg

    def tearDown(self):
        RD.CONFIG = self._old

    def test_first_root_wins(self):
        _write(os.path.join(self.root_a, "p1", "blk.sv"), "// a")
        _write(os.path.join(self.root_b, "p1", "blk.sv"), "// b")
        self.assertTrue(RD.rtl_file("blk").startswith(self.root_a))

    def test_falls_back_to_second_root_per_block(self):
        _write(os.path.join(self.root_a, "p1", "one.sv"), "// a")
        _write(os.path.join(self.root_b, "p1", "two.sv"), "// b")
        self.assertTrue(RD.rtl_file("one").startswith(self.root_a))
        self.assertTrue(RD.rtl_file("two").startswith(self.root_b))

    def test_never_leaves_the_roots(self):
        # only the decoy exists: must be an error, not the decoy
        with self.assertRaises(RD.DropError):
            RD.rtl_file("blk")
        with self.assertRaises(RD.DropError):
            RD.manifest_file("blk")
        self.assertEqual(RD.missing(["blk"]), ["blk"])

    def test_prefers_consolidated_manifest_dir(self):
        _write(os.path.join(self.root_a, "phase", "blk_manifest.json"), MANIFEST)
        _write(os.path.join(self.root_a, "lint", "blk_manifest.json"), MANIFEST)
        # make the phase copy newer; preference must still win
        os.utime(os.path.join(self.root_a, "phase", "blk_manifest.json"),
                 (2_000_000_000, 2_000_000_000))
        self.assertIn(os.sep + "lint" + os.sep, RD.manifest_file("blk"))
        self.assertEqual(RD.manifest_ports("blk")["clk"]["width"], 1)

    def test_stamp_names_source_per_block(self):
        _write(os.path.join(self.root_a, "p1", "one.sv"), "// a")
        _write(os.path.join(self.root_a, "p1", "one_manifest.json"), MANIFEST)
        st = RD.stamp(["one", "ghost"])
        self.assertTrue(st["blocks"]["one"]["rtl"].startswith(
            os.path.relpath(self.root_a, RD.ROOT)))
        self.assertIsNone(st["blocks"]["ghost"]["rtl"])


if __name__ == "__main__":
    unittest.main()
