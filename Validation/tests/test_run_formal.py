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
