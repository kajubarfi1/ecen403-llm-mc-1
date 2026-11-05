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



class Level3Command(unittest.TestCase):
    """What level 3 actually asks flow.py to do. Getting this wrong costs
    hours per spec, so it is pinned rather than eyeballed."""

    def _cmd(self, **kw):
        """Run level2 with subprocess.run faked, and return the argv it built."""
        import subprocess
        import tempfile
        seen = {}

        class R:
            returncode = 0

        def fake_run(cmd, **kwargs):
            seen["cmd"] = list(cmd)
            seen["timeout"] = kwargs.get("timeout")
            return R()

        entry = {"name": "preset_default", "choices": {}}
        real = subprocess.run
        subprocess.run = fake_run
        # level 3 refuses to start without Docker, which is correct and is
        # pinned separately below; these cases are about the argv it builds
        prev = os.environ.get("USE_DOCKER")
        os.environ["USE_DOCKER"] = "1"
        try:
            with tempfile.TemporaryDirectory() as d:
                SM.level2(entry, d, **kw)
        finally:
            subprocess.run = real
            if prev is None:
                os.environ.pop("USE_DOCKER", None)
            else:
                os.environ["USE_DOCKER"] = prev
        return seen

    def test_level2_skips_the_backend(self):
        c = self._cmd()["cmd"]
        self.assertIn("--skip-backend", c)
        self.assertNotIn("--per-block-netlists", c)

    def test_level3_runs_the_backend_and_omits_per_block_by_default(self):
        c = self._cmd(backend=True)["cmd"]
        self.assertNotIn("--skip-backend", c)
        self.assertNotIn("--per-block-netlists", c,
                         "per-block adds ~1 h per spec; it must stay opt-in")

    def test_level3_passes_per_block_when_asked(self):
        # without this the flow's final stage halts: it excludes the
        # top-level netlist and no top-level path exists yet
        c = self._cmd(backend=True, per_block_netlists=True)["cmd"]
        self.assertIn("--per-block-netlists", c)

    def test_per_block_is_ignored_at_level_2(self):
        c = self._cmd(per_block_netlists=True)["cmd"]
        self.assertIn("--skip-backend", c)
        self.assertNotIn("--per-block-netlists", c,
                         "there is no backend build to cut netlists from")

    def test_the_timeout_reaches_subprocess(self):
        self.assertEqual(self._cmd(backend=True, timeout=21600)["timeout"], 21600)

    def test_level3_without_docker_is_infrastructure_not_a_verdict(self):
        # a spec must not be judged on a backend stage that never ran
        import subprocess
        import tempfile
        prev = os.environ.pop("USE_DOCKER", None)
        called = []
        real = subprocess.run
        subprocess.run = lambda *a, **k: called.append(1)
        try:
            with tempfile.TemporaryDirectory() as d:
                res = SM.level2({"name": "preset_default", "choices": {}}, d, backend=True)
        finally:
            subprocess.run = real
            if prev is not None:
                os.environ["USE_DOCKER"] = prev
        self.assertIn("infrastructure", res)
        self.assertIsNone(res.get("flow_rc"))
        self.assertFalse(called, "nothing is run without Docker")

if __name__ == "__main__":
    unittest.main()
