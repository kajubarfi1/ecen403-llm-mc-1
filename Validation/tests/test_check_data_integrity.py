"""check_data_integrity: host memory model and host<->pin address consistency
on a synthetic UberDDR3-style log."""

import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "refdesigns", "uberddr3"))
import check_data_integrity as C  # noqa: E402

ROW, BANK, COL, BL2 = 16, 3, 10, 3      # UberDDR3 8Gb x16: col field in wb addr = 7 bits


def wb_addr(row, bank, col):
    return (row << (7 + BANK)) | (bank << 7) | (col >> BL2)


def log(lines):
    f = tempfile.NamedTemporaryFile("w", suffix=".log", delete=False)
    f.write("\n".join(lines) + "\n"); f.close()
    return f.name


class MemoryModel(unittest.TestCase):
    def test_read_returns_last_write_with_byte_enables(self):
        a = wb_addr(5, 2, 0x18)
        lines = [f"TXN wb calib_complete t=100",
                 f"TXN wb request t=200 ps addr={a:x} we=1 data={0x11223344:x} sel=f",
                 f"TXN wb response t=210 ps data=0",
                 f"TXN wb request t=300 ps addr={a:x} we=1 data={0xAABBCCDD:x} sel=3",   # low two bytes only
                 f"TXN wb response t=310 ps data=0",
                 f"TXN wb request t=400 ps addr={a:x} we=0 data=0 sel=f",
                 f"TXN wb response t=410 ps data={0x1122CCDD:x}"]
        reqs, rsps, pins, calib = C.parse(log(lines))
        n, mism, unpaired = C.memory_model(reqs, rsps, 4)
        self.assertEqual((n, mism, unpaired), (1, [], 0))

    def test_read_between_two_writes_expects_the_first(self):
        a = wb_addr(2, 2, 0)
        lines = [f"TXN wb request t=1 ps addr={a:x} we=1 data=aaaaaaaa sel=f", "TXN wb response t=2 ps data=x",
                 f"TXN wb request t=3 ps addr={a:x} we=0 data=0 sel=f", "TXN wb response t=4 ps data=aaaaaaaa",
                 f"TXN wb request t=5 ps addr={a:x} we=1 data=bbbbbbbb sel=f", "TXN wb response t=6 ps data=x",
                 f"TXN wb request t=7 ps addr={a:x} we=0 data=0 sel=f", "TXN wb response t=8 ps data=bbbbbbbb"]
        reqs, rsps, _, _ = C.parse(log(lines))
        n, mism, unpaired = C.memory_model(reqs, rsps, 4)
        self.assertEqual((n, mism, unpaired), (2, [], 0))

    def test_wrong_read_data_is_a_mismatch(self):
        a = wb_addr(1, 1, 8)
        lines = [f"TXN wb request t=1 ps addr={a:x} we=1 data=deadbeef sel=f", "TXN wb response t=2 ps data=0",
                 f"TXN wb request t=3 ps addr={a:x} we=0 data=0 sel=f", "TXN wb response t=4 ps data=deadbeee"]
        reqs, rsps, _, _ = C.parse(log(lines))
        n, mism, _ = C.memory_model(reqs, rsps, 4)
        self.assertEqual(len(mism), 1)
        self.assertEqual(mism[0]["expected"], hex(0xdeadbeef))


class AddressConsistency(unittest.TestCase):
    def pins_for(self, t, row, bank, col, cmd):
        return [f"TXN ddr_cmd command t={t} ps addr={row:x} bank={bank:x} cmd=3",
                f"TXN ddr_cmd command t={t+3000} ps addr={col:x} bank={bank:x} cmd={cmd:x}"]

    def test_host_request_matches_pin_cas(self):
        a = wb_addr(0x1234, 5, 0x38)
        lines = ["TXN wb calib_complete t=100",
                 f"TXN wb request t=200 ps addr={a:x} we=1 data=1 sel=f", "TXN wb response t=250 ps data=0",
                 *self.pins_for(210, 0x1234, 5, 0x38, C.WR),
                 f"TXN wb request t=300 ps addr={a:x} we=0 data=0 sel=f", "TXN wb response t=350 ps data=1",
                 f"TXN ddr_cmd command t=320 ps addr={0x38:x} bank=5 cmd=5"]            # row still open
        reqs, rsps, pins, calib = C.parse(log(lines))
        n_hosts, n_cas, matched, errs = C.address_check(reqs, pins, calib, ROW, BANK, COL, BL2)
        self.assertEqual((n_hosts, n_cas, matched, errs), (2, 2, 2, []))

    def test_wrong_bank_at_pins_is_an_error(self):
        a = wb_addr(7, 3, 0)
        lines = ["TXN wb calib_complete t=100",
                 f"TXN wb request t=200 ps addr={a:x} we=1 data=1 sel=f", "TXN wb response t=250 ps data=0",
                 *self.pins_for(210, 7, 4, 0, C.WR)]                                   # bank 4, not 3
        reqs, rsps, pins, calib = C.parse(log(lines))
        _, _, matched, errs = C.address_check(reqs, pins, calib, ROW, BANK, COL, BL2)
        self.assertEqual(matched, 0)
        self.assertEqual(errs[0]["expected"]["bank"], 3)

    def test_calibration_traffic_before_calib_complete_is_ignored(self):
        a = wb_addr(1, 0, 0)
        lines = [f"TXN ddr_cmd command t=10 ps addr=0 bank=0 cmd=3", f"TXN ddr_cmd command t=13 ps addr=0 bank=0 cmd=4",
                 "TXN wb calib_complete t=100",
                 f"TXN wb request t=200 ps addr={a:x} we=1 data=1 sel=f", "TXN wb response t=250 ps data=0",
                 *self.pins_for(210, 1, 0, 0, C.WR)]
        reqs, rsps, pins, calib = C.parse(log(lines))
        n_hosts, n_cas, matched, errs = C.address_check(reqs, pins, calib, ROW, BANK, COL, BL2)
        self.assertEqual((n_hosts, n_cas, matched, errs), (1, 1, 1, []))


if __name__ == "__main__":
    unittest.main()
