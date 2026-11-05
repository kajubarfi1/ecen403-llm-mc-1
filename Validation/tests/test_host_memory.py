"""What the host wrote is what it reads back, in order (Validation/txn/host_memory.py)."""
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
import host_memory as HM  # noqa: E402


def trace(events):
    fd, p = tempfile.mkstemp(suffix=".jsonl")
    with os.fdopen(fd, "w") as f:
        for i, (t, iface, kind, fields) in enumerate(events):
            f.write(json.dumps({"iface": iface, "kind": kind, "fields": fields, "seq": i, "time_ns": t}) + "\n")
    return p


class HostMemory(unittest.TestCase):

    def test_in_order_readback_passes(self):
        p = trace([(10, "wb", "write", {"addr": "100", "data": "aabbccdd", "sel": "f"}),
                   (20, "wb", "write", {"addr": "104", "data": "11223344", "sel": "f"}),
                   (30, "wb", "read", {"addr": "100"}), (40, "wb", "read", {"addr": "104"}),
                   (90, "wb_rsp", "read_data", {"addr": "100", "data": "aabbccdd"}),
                   (95, "wb_rsp", "read_data", {"addr": "104", "data": "11223344"})])
        status, head, mism = HM.check(p)
        self.assertEqual((status, mism), ("pass", []))
        self.assertIn("checked=2", head)

    def test_reordered_responses_are_a_mismatch_naming_the_other_address(self):
        p = trace([(10, "wb", "write", {"addr": "100", "data": "aabbccdd", "sel": "f"}),
                   (20, "wb", "write", {"addr": "104", "data": "11223344", "sel": "f"}),
                   (30, "wb", "read", {"addr": "100"}), (40, "wb", "read", {"addr": "104"}),
                   (90, "wb_rsp", "read_data", {"addr": "x", "data": "11223344"}),     # 104's data first
                   (95, "wb_rsp", "read_data", {"addr": "x", "data": "aabbccdd"})])
        status, head, mism = HM.check(p)
        self.assertEqual(status, "fail")
        self.assertEqual(len(mism), 2)
        self.assertIn("addr=0x100 expected=0xaabbccdd observed=0x11223344 (the data the host wrote at 0x104)", mism[0])

    def test_byte_enables_and_unwritten_reads(self):
        p = trace([(10, "wb", "write", {"addr": "200", "data": "ffffffff", "sel": "f"}),
                   (20, "wb", "write", {"addr": "200", "data": "00000012", "sel": "1"}),   # low byte only
                   (30, "wb", "read", {"addr": "200"}), (31, "wb", "read", {"addr": "300"}),
                   (90, "wb_rsp", "read_data", {"addr": "x", "data": "ffffff12"}),
                   (95, "wb_rsp", "read_data", {"addr": "x", "data": "deadbeef"})])      # never written: skipped
        status, head, mism = HM.check(p)
        self.assertEqual((status, mism), ("pass", []))
        self.assertIn("skipped_unwritten=1", head)

    def test_emitter_parses_the_line(self):
        sys.path.insert(0, os.path.join(ROOT, "Validation", "findings"))
        import emit_findings as E
        m = E.HOSTMEM_RE.match("  HOSTMEM wb_rsp[3] addr=0x100 expected=0xaabbccdd observed=0x11223344 (the data the host wrote at 0x104) read accepted t=30 answered t=90")
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1), "wb_rsp")


if __name__ == "__main__":
    unittest.main()
