"""scoreboard: catalog-declared don't-care fields are normalised before alignment."""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "txn"))
import scoreboard as SB  # noqa: E402
from txn_contract import Txn  # noqa: E402


class DontCare(unittest.TestCase):
    def test_precharge_address_keeps_only_a10(self):
        pre = Txn(iface="ddr_cmd", kind="command", fields={"cmd": 0b0010, "bank": 6, "addr": 0x38C0})
        n = SB._apply_dont_care(pre)
        self.assertEqual(n.fields["addr"], 0x38C0 & 0x400)
        act = Txn(iface="ddr_cmd", kind="command", fields={"cmd": 0b0011, "bank": 6, "addr": 0x38C0})
        self.assertEqual(SB._apply_dont_care(act).fields["addr"], 0x38C0)

    def test_precharge_all_bit_is_still_compared(self):
        a = SB._apply_dont_care(Txn(iface="ddr_cmd", kind="command", fields={"cmd": 2, "bank": 0, "addr": 0x400}))
        b = SB._apply_dont_care(Txn(iface="ddr_cmd", kind="command", fields={"cmd": 2, "bank": 0, "addr": 0x000}))
        self.assertNotEqual(a.key(), b.key())

    def test_predicted_and_observed_pre_align(self):
        p = [Txn(iface="ddr_cmd", kind="command", fields={"cmd": 2, "bank": 1, "addr": 0x1234})]
        o = [Txn(iface="ddr_cmd", kind="command", fields={"cmd": 2, "bank": 1, "addr": 0x0})]
        p = [SB._apply_dont_care(t) for t in p]
        o = [SB._apply_dont_care(t) for t in o]
        matched, mism = SB.align(p, o, "ddr_cmd")
        self.assertEqual((matched, mism), (1, []))


if __name__ == "__main__":
    unittest.main()
