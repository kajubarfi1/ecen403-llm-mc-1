"""run_formal: the JasperGold RESULTS table parser."""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
import run_formal as R  # noqa: E402

SAMPLE = """
[1]   chain_formal.u_cmd_gen.u_cmd_gen_sva.a_TIMING_001                         proven          Hp     Infinite    58.215 s
[2]   chain_formal.u_cmd_gen.u_cmd_gen_sva.a_TIMING_001:precondition1           covered         Bm            5    0.170 s
[10]  chain_formal.u_cmd_gen.u_cmd_gen_sva.a_TIMING_004                         cex             Ht            6    0.325 s
[16]  chain_formal.u_cmd_gen.u_cmd_gen_sva.a_TIMING_007                         cex             L      136 - 147   38.644 s
[35]  chain_formal.u_cmd_gen.u_cmd_gen_sva.a_TIMING_012                         undetermined    Oh          201    -
"""


class Parser(unittest.TestCase):
    def test_rows(self):
        rows = {r["short"]: r for r in R.parse_results(SAMPLE)}
        self.assertEqual(rows["a_TIMING_001"]["status"], "proven")
        self.assertEqual(rows["a_TIMING_001"]["bound"], "Infinite")
        self.assertEqual(rows["a_TIMING_004"]["status"], "cex")
        self.assertEqual(rows["a_TIMING_007"]["bound"], "136 - 147")
        self.assertEqual(rows["a_TIMING_012"]["status"], "undetermined")
        self.assertIn("a_TIMING_001:precondition1", rows)

    def test_archived_report_parses(self):
        p = os.path.join(HERE, "..", "reports", "formal", "jg_cmd_path_1fea117_report.txt")
        if not os.path.exists(p):
            self.skipTest("no archived report")
        rows = R.parse_results(open(p).read())
        asserts = [r for r in rows if r["short"].startswith("a_") and ":" not in r["short"]]
        self.assertEqual(len(asserts), 13)


if __name__ == "__main__":
    unittest.main()


class Vacuity(unittest.TestCase):
    """A bounded proof whose trigger was never reached proves nothing."""

    def rows(self, cover_status):
        asserts = [{"short": "a_PROTO_001", "status": "undetermined", "bound": "8245"},
                   {"short": "a_TIMING_001", "status": "proven", "bound": "Infinite"},
                   {"short": "a_REF_001", "status": "undetermined", "bound": "8245"}]
        covers = [{"short": "c_PROTO_001", "status": cover_status},
                  {"short": "c_TIMING_001", "status": cover_status},
                  {"short": "c_REF_001", "status": "covered"}]
        R.classify_bounded(asserts, {"PROTO_001": 100, "REF_001": 100, "*": 100})
        R.apply_vacuity(asserts, covers)
        return {r["short"]: r for r in asserts}

    def test_bounded_with_unreached_cover_is_vacuous(self):
        by = self.rows("undetermined")
        self.assertEqual(by["a_PROTO_001"]["status"], "bounded_vacuous")
        self.assertIn("VACUOUS", by["a_PROTO_001"]["note"])
        self.assertEqual(by["a_REF_001"]["status"], "bounded_proven")   # its cover was reached
        self.assertEqual(by["a_TIMING_001"]["status"], "proven")        # sound; noted only
        self.assertIn("not witnessed", by["a_TIMING_001"]["note"])

    def test_bounded_with_reached_cover_counts(self):
        by = self.rows("covered")
        self.assertEqual(by["a_PROTO_001"]["status"], "bounded_proven")
        self.assertNotIn("note", by["a_TIMING_001"])

    def test_proven_with_unreachable_cover_is_vacuous(self):
        by = self.rows("unreachable")
        self.assertEqual(by["a_TIMING_001"]["status"], "proven_vacuous")
        self.assertEqual(by["a_PROTO_001"]["status"], "bounded_vacuous")

    def test_emitter_counts_only_real_proofs(self):
        sys.path.insert(0, os.path.join(HERE, "..", "findings"))
        import inspect
        import emit_findings as E
        src = inspect.getsource(E.formal_proof_sets)
        self.assertIn('("proven", "bounded_proven")', src)
        self.assertNotIn('"bounded_vacuous"', src)      # a vacuous result never closes a finding
