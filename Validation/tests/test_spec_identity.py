#!/usr/bin/env python3
"""The spec id is a content id: formatting and key order do not change it,
any value does, and `revision` is not part of what makes two specs equal."""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "spec"))
from spec_identity import spec_sha256  # noqa: E402


def _tmp(doc, **kw):
    f = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
    json.dump(doc, f, **kw)
    f.close()
    return f.name


class TestSpecIdentity(unittest.TestCase):
    def test_formatting_and_key_order_do_not_matter(self):
        a = {"revision": "r1", "b": {"y": 2, "x": 1}, "a": [1, 2]}
        b = {"a": [1, 2], "b": {"x": 1, "y": 2}, "revision": "r1"}
        self.assertEqual(spec_sha256(_tmp(a, indent=2)), spec_sha256(_tmp(b)))

    def test_any_value_changes_the_id(self):
        a = {"revision": "r1", "csr": {"bits": "7:5"}}
        b = {"revision": "r1", "csr": {"bits": "8:5"}}
        self.assertNotEqual(spec_sha256(_tmp(a)), spec_sha256(_tmp(b)),
                            "same revision, different content, same id")

    def test_sixteen_hex_digits(self):
        self.assertRegex(spec_sha256(_tmp({"x": 1})), r"^[0-9a-f]{16}$")


if __name__ == "__main__":
    unittest.main()


class TestJudgingSpec(unittest.TestCase):
    """validate_drop's choice of spec when the drop ships one under a known
    revision with different content."""

    def setUp(self):
        sys.path.insert(0, os.path.join(HERE, "..", "tools"))
        import validate_drop as VD
        self.VD = VD
        self.default = _tmp({"revision": "r1", "f": "old"})
        self.ship = _tmp({"revision": "r1", "f": "new"})
        # a private ledger per test: the real one records real revisions
        self._ledger = VD.REVISION_IDS
        VD.REVISION_IDS = _tmp({"revisions": {}})

    def tearDown(self):
        self.VD.REVISION_IDS = self._ledger

    def test_default_copy_adopts_the_shipped_spec_and_refreshes(self):
        a, b = spec_sha256(self.default), spec_sha256(self.ship)
        path, sid, reused, prev, adopted = self.VD.resolve_judging_spec(
            self.default, "r1", a, self.ship, "r1", b, explicit=False, default_spec=self.default)
        self.assertTrue(reused and adopted)
        self.assertEqual((path, sid, prev), (self.default, b, a))
        self.assertEqual(spec_sha256(self.default), b, "the copy now IS the shipped spec")

    def test_explicit_spec_is_kept_and_only_reported(self):
        a, b = spec_sha256(self.default), spec_sha256(self.ship)
        path, sid, reused, prev, adopted = self.VD.resolve_judging_spec(
            self.default, "r1", a, self.ship, "r1", b, explicit=True, default_spec=self.default)
        self.assertTrue(reused)
        self.assertFalse(adopted)
        self.assertEqual((path, sid), (self.default, a))
        self.assertEqual(spec_sha256(self.default), a, "nothing overwritten")

    def test_reuse_persists_in_the_ledger_after_adoption(self):
        a, b = spec_sha256(self.default), spec_sha256(self.ship)
        self.VD.resolve_judging_spec(self.default, "r1", a, self.ship, "r1", b, False, self.default)
        # next run: the copy now equals the shipped spec, yet the revision
        # has still named two specs
        _, _, reused, prev, adopted = self.VD.resolve_judging_spec(
            self.default, "r1", b, self.ship, "r1", b, False, self.default)
        self.assertTrue(reused)
        self.assertFalse(adopted)
        self.assertEqual(prev, a)
        self.assertEqual(self.VD.record_revision_id("r1", b), [a, b])

    def test_same_content_or_other_revision_is_not_reuse(self):
        a = spec_sha256(self.default)
        same = _tmp({"f": "old", "revision": "r1"}, indent=4)
        _, _, reused, _, adopted = self.VD.resolve_judging_spec(
            self.default, "r1", a, same, "r1", spec_sha256(same), False, self.default)
        self.assertFalse(reused or adopted)
        _, _, reused, _, adopted = self.VD.resolve_judging_spec(
            self.default, "r1", a, self.ship, "r2", spec_sha256(self.ship), False, self.default)
        self.assertFalse(reused or adopted, "a different revision is the foreign-spec case, not reuse")
