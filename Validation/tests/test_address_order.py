"""Same-address requests reach the memory in host order (Validation/txn/address_order.py)."""
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
import address_order as AO  # noqa: E402

RULE = {"id": "SAME_ADDRESS_HOST_ORDER",
        "request": {"iface": "req", "addr": "addr", "we": "we", "aux": "aux"},
        "issue": {"iface": "dp_cmd", "aux": "aux", "kind_we": {"read": 0, "write": 1}},
        "owner": "scheduler", "owner_candidates": ["scheduler", "cmd_queue"]}
IFS = {"req": {"block": "wb_port"}, "dp_cmd": {"block": "data_path"}}
BLOCKS = ["wb_port", "scheduler", "data_path"]


def trace(events):
    fd, p = tempfile.mkstemp(suffix=".jsonl")
    with os.fdopen(fd, "w") as f:
        for i, (t, iface, kind, fields) in enumerate(events):
            f.write(json.dumps({"iface": iface, "kind": kind, "fields": fields, "seq": i, "time_ns": t}) + "\n")
    return p


def req(t, we, addr, aux):
    return (t, "req", "request", {"we": we, "addr": addr, "aux": aux, "data": "0"})


def cmd(t, kind, aux):
    return (t, "dp_cmd", kind, {"aux": aux})


class AddressOrder(unittest.TestCase):

    def test_host_order_passes_even_when_other_addresses_reorder(self):
        p = trace([req(10, 1, "100", 0), req(20, 1, "200", 1), req(30, 0, "100", 0),
                   cmd(100, "write", 1), cmd(110, "write", 0), cmd(120, "read", 0)])   # 200 ahead of 100: fine
        status, head, lines = AO.check(p, BLOCKS, [RULE], IFS)
        self.assertEqual((status, lines), ("pass", []))
        self.assertIn("checked=3", head)

    def test_read_issued_ahead_of_the_older_write_is_a_violation(self):
        # the shape of path_18 on 2a18a7929dce: write aux=10 then read aux=10 of the same
        # word; the read reached DDR first
        p = trace([req(933, 1, "17fb2263", 10), req(983, 0, "17fb2263", 10),
                   cmd(1424, "read", 10), cmd(1464, "write", 10)])
        status, head, lines = AO.check(p, BLOCKS, [RULE], IFS)
        self.assertEqual(status, "fail")
        self.assertEqual(len(lines), 1)
        self.assertIn("ADDRORDER SAME_ADDRESS_HOST_ORDER owner=scheduler addr=0x17fb2260 read accepted t=983 "
                      "issued t=1424 ahead of the older write accepted t=933 still unissued", lines[0])

    def test_write_after_read_and_write_after_write_are_violations_read_after_read_is_not(self):
        p = trace([req(10, 0, "100", 0), req(20, 1, "100", 0), req(30, 1, "100", 1), req(40, 0, "100", 1),
                   cmd(100, "write", 1),      # ahead of the older read (aux 0) AND the older write (aux 0)
                   cmd(110, "read", 1),       # ahead of the older read aux 0: fine; older write aux 0 unissued: violation
                   cmd(120, "write", 0),      # ahead of the older read aux 0 (still unissued): violation
                   cmd(130, "read", 0)])
        status, _head, lines = AO.check(p, BLOCKS, [RULE], IFS)
        self.assertEqual(status, "fail")
        self.assertEqual(len(lines), 4)
        self.assertEqual(sum("ahead of the older read" in l for l in lines), 2)
        self.assertEqual(sum("ahead of the older write" in l for l in lines), 2)

    def test_tags_wrap_only_after_the_older_request_issued(self):
        p = trace([req(10, 1, "100", 3), cmd(100, "write", 3),
                   req(110, 1, "200", 3), req(120, 0, "100", 3),
                   cmd(200, "read", 3), cmd(210, "write", 3)])
        status, head, lines = AO.check(p, BLOCKS, [RULE], IFS)
        self.assertEqual((status, lines), ("pass", []))
        self.assertIn("unpaired=0", head)

    def test_tag_reused_in_flight_is_reported_and_draws_no_ordering_verdict(self):
        # path_07 on 2a18a7929dce: the write accepted at 94 (tag 4) still queued when the
        # write at 2199 took tag 4; the older one was later issued with the newer data
        rule = dict(RULE, tag_reuse={"owner": "data_path", "owner_candidates": ["data_path", "wb_port"]})
        p = trace([req(94, 1, "160165c", 4), req(2199, 1, "e1e4e64", 4), req(2204, 1, "e1e4e64", 5),
                   cmd(2529, "write", 4), cmd(2629, "write", 5), cmd(2929, "write", 4)])
        status, head, lines = AO.check(p, BLOCKS, [rule], IFS)
        self.assertEqual(status, "fail")
        self.assertEqual(len(lines), 1, lines)
        self.assertIn("ADDRORDER SAME_ADDRESS_HOST_ORDER_TAG_REUSE owner=data_path addr=0xe1e4e64 write accepted "
                      "t=2199 reuses tag 4 of the older write accepted t=94 to 0x160165c still unissued", lines[0])
        # without the reuse the same issue order would be a write-after-write violation
        q = trace([req(2199, 1, "e1e4e64", 4), req(2204, 1, "e1e4e64", 5),
                   cmd(2629, "write", 5), cmd(2929, "write", 4)])
        status, _h, lines = AO.check(q, BLOCKS, [rule], IFS)
        self.assertEqual(status, "fail")
        self.assertIn("ahead of the older write", lines[0])

    def test_tag_freed_and_retaken_in_the_same_cycle_is_not_a_reuse(self):
        rule = dict(RULE, tag_reuse={"owner": "data_path"})
        p = trace([req(10, 1, "100", 0), (100, "req", "request", {"we": 1, "addr": "200", "aux": 0}),
                   cmd(100, "write", 0), cmd(300, "write", 0)])     # the req is logged before the pop at t=100
        status, head, lines = AO.check(p, BLOCKS, [rule], IFS)
        self.assertEqual((status, lines), ("pass", []))
        self.assertIn("checked=2", head)

    def test_not_applicable_without_both_blocks_and_unknown_without_the_tag_field(self):
        p = trace([req(10, 1, "100", 0), cmd(100, "write", 0)])
        status, head, _ = AO.check(p, ["wb_port", "scheduler"], [RULE], IFS)
        self.assertEqual(status, "not_applicable")
        q = trace([(10, "req", "request", {"we": 1, "addr": "100"}), cmd(100, "write", 0)])
        status, head, lines = AO.check(q, BLOCKS, [RULE], IFS)
        self.assertEqual((status, lines), ("unknown", []))
        self.assertIn("uncheckable=1", head)
        self.assertIn("carries no aux", head)

    def test_catalog_rule_is_well_formed(self):
        rules, ifs = AO.load_rules()
        self.assertTrue(rules)
        for r in rules:
            for k in ("id", "request", "issue", "owner", "requirement", "taxonomy", "tag_reuse"):
                self.assertIn(k, r, r.get("id"))
            self.assertIn("owner", r["tag_reuse"])
            self.assertIn(r["request"]["iface"], ifs)
            self.assertIn(r["issue"]["iface"], ifs)
            # the paired fields are declared on the catalog kinds
            rk = ifs[r["request"]["iface"]]["kinds"]
            self.assertTrue(all(r["request"][f] in next(iter(rk.values())) for f in ("addr", "we", "aux")))
            ik = ifs[r["issue"]["iface"]]["kinds"]
            self.assertTrue(all(r["issue"]["aux"] in ik[k] for k in r["issue"]["kind_we"]))


if __name__ == "__main__":
    unittest.main()
