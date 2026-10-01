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


class TestCopiesAndStamps(TestResolver):
    """Two copies of a block inside one root: identical copies are one file;
    differing copies resolve only through a preferred directory, never by
    age (2026-10-01: TOPRTL/wb_port from the golden spec vs PHASE1RTL/wb_port
    from a compiled one). Every block carries the spec revision that
    generated it, and the drop may ship that spec."""

    def test_identical_copies_are_one_file(self):
        _write(os.path.join(self.root_a, "p1", "blk.sv"), "// same")
        _write(os.path.join(self.root_a, "top", "blk.sv"), "// same")
        self.assertTrue(RD.rtl_file("blk").endswith("blk.sv"))

    def test_differing_copies_refuse_without_a_preferred_dir(self):
        _write(os.path.join(self.root_a, "p1", "blk.sv"), "// phase output")
        _write(os.path.join(self.root_a, "top", "blk.sv"), "// assembly copy")
        os.utime(os.path.join(self.root_a, "top", "blk.sv"), (2_000_000_000, 2_000_000_000))
        with self.assertRaises(RD.DropError) as cm:
            RD.rtl_file("blk")
        self.assertIn("differing copies", str(cm.exception))
        self.assertIn("rtl_dirs_preferred", str(cm.exception))

    def test_preferred_dir_decides_differing_copies(self):
        with open(self.cfg) as f:
            cfg = json.load(f)
        cfg["rtl_dirs_preferred"] = ["p1"]
        with open(self.cfg, "w") as f:
            json.dump(cfg, f)
        _write(os.path.join(self.root_a, "p1", "blk.sv"), "// phase output")
        _write(os.path.join(self.root_a, "top", "blk.sv"), "// assembly copy")
        os.utime(os.path.join(self.root_a, "top", "blk.sv"), (2_000_000_000, 2_000_000_000))
        self.assertTrue(RD.rtl_file("blk").endswith(os.path.join("p1", "blk.sv")))

    def test_spec_stamp_from_manifest_then_header(self):
        _write(os.path.join(self.root_a, "p1", "blk.sv"), "// Spec:      design_x rev rev_from_header\nmodule blk; endmodule")
        _write(os.path.join(self.root_a, "p1", "blk_manifest.json"),
               json.dumps({"ports": {}, "design_id": "design_x", "spec_revision": "rev_from_manifest"}))
        self.assertEqual(RD.spec_stamp("blk"), ("design_x", "rev_from_manifest"))
        _write(os.path.join(self.root_a, "p1", "blk_manifest.json"), json.dumps({"ports": {}}))
        self.assertEqual(RD.spec_stamp("blk"), ("design_x", "rev_from_header"))
        _write(os.path.join(self.root_a, "p1", "blk.sv"), "module blk; endmodule")
        self.assertEqual(RD.spec_stamp("blk"), (None, None))

    def test_shipped_spec(self):
        self.assertEqual(RD.shipped_spec(), (None, None))
        _write(os.path.join(self.root_a, "generated_spec.json"), json.dumps({"revision": "rev_z"}))
        p, rev = RD.shipped_spec()
        self.assertEqual(rev, "rev_z")
        self.assertTrue(p.endswith("generated_spec.json"))


class TestDropId(TestResolver):
    """The drop is named by its content -- a hash of its own RTL and
    manifests -- so the same files always get the same id, a changed byte
    is a new drop, and nothing about git is involved."""

    def _blk(self, name, body, commit="c0ffee"):
        _write(os.path.join(self.root_a, "p1", f"{name}.sv"), body)
        _write(os.path.join(self.root_a, "p1", f"{name}_manifest.json"),
               json.dumps({"ports": {}, "git_commit": commit}))

    def test_same_files_same_id_regardless_of_git_or_time(self):
        self._blk("a", "module a; endmodule")
        self._blk("b", "module b; endmodule")
        one = RD.drop_id(["a", "b"])
        os.utime(os.path.join(self.root_a, "p1", "a.sv"), (1_700_000_000, 1_700_000_000))
        self._blk("b", "module b; endmodule", commit="deadbeef")   # manifest commit changes
        self.assertNotEqual(one, RD.drop_id(["a", "b"]), "the manifest is part of the drop")
        self._blk("b", "module b; endmodule")
        self.assertEqual(one, RD.drop_id(["a", "b"]))
        self.assertEqual(len(one), 12)

    def test_one_byte_is_a_new_drop(self):
        self._blk("a", "module a; endmodule")
        one = RD.drop_id(["a"])
        self._blk("a", "module a;  endmodule")
        self.assertNotEqual(one, RD.drop_id(["a"]))

    def test_partial_and_complete_drops_differ(self):
        self._blk("a", "module a; endmodule")
        one = RD.drop_id(["a", "b"])
        self._blk("b", "module b; endmodule")
        self.assertNotEqual(one, RD.drop_id(["a", "b"]))

    def test_stamp_carries_the_id_and_only_informational_git(self):
        self._blk("a", "module a; endmodule")
        st = RD.stamp(["a"])
        self.assertEqual(st["git_head"], st["drop_id"])
        self.assertEqual(st["drop_id"], RD.drop_id(["a"]))
        self.assertIn("validated_at", st)


if __name__ == "__main__":
    unittest.main()
