"""The spec matrix: a covering set over the Tier-1 choices, judged per spec."""
import itertools
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "tools"))
import spec_matrix as SM  # noqa: E402


class Matrix(unittest.TestCase):

    def test_covering_set_holds_every_feasible_pair(self):
        MC = SM._mc()
        chosen, infeasible = SM.pairwise_covering(MC, seed=3)
        params = {k: v for k, v in MC.TIER1_CHOICES.items() if k not in SM.TIER1_FIXED}
        keys = sorted(params)
        covered = set()
        for c in chosen:
            ok, errs, _ = SM.valid(MC, c)
            self.assertTrue(ok, errs)
            covered |= {(a, c[a], b, c[b]) for a, b in itertools.combinations(keys, 2)}
        for a, b in itertools.combinations(keys, 2):
            for va in params[a]:
                for vb in params[b]:
                    self.assertTrue((a, va, b, vb) in covered or (a, va, b, vb) in infeasible,
                                    f"pair {a}={va}, {b}={vb} neither covered nor declared infeasible")

    def test_checked_in_matrix_entries_are_valid_choices(self):
        if not os.path.exists(SM.MATRIX):
            self.skipTest("no matrix built")
        MC = SM._mc()
        doc = json.load(open(SM.MATRIX))
        self.assertGreaterEqual(len(doc["entries"]), 5)
        for e in doc["entries"]:
            ok, errs, _ = SM.valid(MC, e["choices"])
            self.assertTrue(ok, (e["name"], errs))

    def test_level1_on_the_default_preset_passes(self):
        import tempfile
        MC = SM._mc()
        e = {"name": "t", "choices": dict(MC.PRESETS["default"])}
        res = SM.level1(e, tempfile.mkdtemp())
        self.assertEqual(res["status"], "PASS", res["blocking"])


if __name__ == "__main__":
    unittest.main()
