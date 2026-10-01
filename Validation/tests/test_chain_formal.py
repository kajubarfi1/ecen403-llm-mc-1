"""chain_harness_gen --formal: a synthesizable top with free host inputs."""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "structural"))
import chain_harness_gen as G  # noqa: E402


class FormalTop(unittest.TestCase):
    def setUp(self):
        with open(os.path.join(HERE, "..", "structural", "integration_map.json")) as f:
            self.imap = json.load(f)

    def _skip_if_blocked(self):
        for e in self.imap.get("inconsistent_connections", []):
            raise unittest.SkipTest(
                f"the checked-in drop cannot wire {e['from']} -> {e['to']} "
                f"({e['from_width']} vs {e['to_width']}); the finding is filed, the formal "
                f"top waits for a drop that agrees")

    def test_formal_top_has_no_testbench_scaffolding(self):
        self._skip_if_blocked()
        sv, blocks = G.generate("path_01_write_cmd", None, self.imap, formal=True)
        self.assertIn("module chain_formal (", sv)
        for forbidden in ("initial", "always #", "$finish", "$display", "dram_stub", "seq_driver"):
            self.assertNotIn(forbidden, sv, forbidden)
        # host inputs of the entry block are free ports, CSR inputs stay tied
        self.assertIn("input logic free__wb_port__wb_cyc_i", sv)
        self.assertIn("assign tie__config_regs__csr_stb_i = '0;", sv)
        # DRAM data comes in as a free port, not from a stub
        # width follows the drop's manifest (16 since the DQ-width fix; 32 before it)
        self.assertRegex(sv, r"input logic \[\d+:0\] stub__u_dram__ddr_dq_i")
        self.assertIn("scheduler", blocks)

    def test_simulation_harness_still_has_its_scaffolding(self):
        self._skip_if_blocked()
        sv, _ = G.generate("path_01_write_cmd", None, self.imap, formal=False)
        self.assertIn("module chain_harness;", sv)
        self.assertIn("dram_stub", sv)
        self.assertIn("HARNESS_TIMEOUT", sv)


if __name__ == "__main__":
    unittest.main()
