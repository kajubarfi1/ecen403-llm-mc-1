#!/usr/bin/env python3
"""The mirrored sky130 library must define every cell the backend's netlists
instantiate; the installer fetches what is missing (2026-10-20)."""

import glob
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "tools"))
import install_sky130_models as ISM  # noqa: E402


class TestCellInventory(unittest.TestCase):

    def test_cells_used_reads_instantiations_only(self):
        d = tempfile.mkdtemp()
        p = os.path.join(d, "n.v")
        with open(p, "w") as f:
            f.write("module x;\n  sky130_fd_sc_hd__nand2_1 _1_ (.A(a));\n"
                    "  sky130_fd_sc_hd__dfxtp_1 _2_ (\n .CLK(clk));\n  wire sky130_fd_sc_hd__notacell;\nendmodule\n")
        self.assertEqual(ISM.cells_used([p]), {"sky130_fd_sc_hd__nand2_1", "sky130_fd_sc_hd__dfxtp_1"})

    def test_library_covers_every_checked_in_netlist(self):
        netlists = sorted(glob.glob(ISM.NETLIST_GLOB))
        if not netlists:
            self.skipTest("no backend netlists checked in")
        missing = sorted(ISM.cells_used(netlists) - ISM.library_cells())
        self.assertEqual(missing, [], "run install_sky130_models.py (it fetches these from the open PDK)")


if __name__ == "__main__":
    unittest.main()
