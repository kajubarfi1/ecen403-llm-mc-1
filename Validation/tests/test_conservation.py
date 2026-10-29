"""Request conservation: what the design never produced (Validation/txn/conservation.py)."""
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
import conservation as C  # noqa: E402

CATALOG = json.load(open(os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")))
# resolved in memory from the declared drop, not read from the generated
# file: a flow run on a partial drop regenerates that file for its own drop
# (2026-10-29, every rule's interfaces "missing" after runs/oct29_loop)
import schema_gen as SG  # noqa: E402
SCHEMAS = SG.resolve()["interfaces"]
SPEC = json.load(open(C.SPEC_PATH))


def _trace(txns):
    fd, path = tempfile.mkstemp(suffix=".jsonl")
    with os.fdopen(fd, "w") as f:
        for i, (iface, kind, fields) in enumerate(txns):
            f.write(json.dumps({"iface": iface, "kind": kind, "fields": fields,
                                "seq": i, "time_ns": i * 5}) + "\n")
    return path


ALL = ["wb_port", "addr_decoder", "cmd_queue", "scheduler", "cmd_gen", "data_path"]


class TestRules(unittest.TestCase):

    def test_every_rule_names_real_interfaces_and_owner(self):
        for r in CATALOG["conservation"]["rules"]:
            self.assertIn(r["from"]["iface"], SCHEMAS, r["id"])
            self.assertIn(r["to"]["iface"], SCHEMAS, r["id"])
            self.assertIn(r["owner"], {SCHEMAS[r["to"]["iface"]]["block"], SCHEMAS[r["from"]["iface"]]["block"]},
                          f"{r['id']}: owner must be one of the two blocks on the edge")
            for k in r["from"].get("kinds", []):
                self.assertIn(k, SCHEMAS[r["from"]["iface"]]["kinds"], r["id"])
            self.assertTrue(r.get("requirement") and r.get("taxonomy"), r["id"])

    def test_per_source_from_spec_arithmetic(self):
        n = C.resolve_count({"$spec": "data_path_mapping.host_width_bits / data_path_mapping.ddr_channel_width_bits"}, SPEC)
        self.assertEqual(n, SPEC["data_path_mapping"]["host_width_bits"] // SPEC["data_path_mapping"]["ddr_channel_width_bits"])
        self.assertEqual(C.resolve_count(None, SPEC), 1)
        with self.assertRaises(ValueError):
            C.resolve_count({"$spec": "__import__('os')"}, SPEC)

    def test_balanced_trace_passes(self):
        t = _trace([("wb", "write", {"addr": "10"}), ("req", "request", {"we": "1"}),
                    ("cq_enq", "enqueue", {}), ("dp_wr", "write", {}),
                    ("dp_cmd", "write", {}), ("ddr_wr_beat", "beat", {}), ("ddr_wr_beat", "beat", {}),
                    ("wb", "read", {}), ("req", "request", {"we": "0"}), ("cq_enq", "enqueue", {}),
                    ("dp_cmd", "read", {}), ("dp_rd_rsp", "response", {}), ("wb_rsp", "read_data", {})])
        status, rows = C.check(t, ALL, CATALOG, SCHEMAS, SPEC)
        self.assertEqual(status, "pass", C.render(status, rows))
        self.assertTrue(all(r["status"] == "checked" for r in rows))

    def test_dropped_read_is_blamed_on_the_block_that_lost_it(self):
        """The 2026-10-28 case: the port delivered the read, the queue took
        it, the data path saw the RD command and never answered."""
        t = _trace([("wb", "read", {}), ("req", "request", {"we": "0"}), ("cq_enq", "enqueue", {}),
                    ("dp_cmd", "read", {}),
                    ("wb", "read", {}), ("req", "request", {"we": "0"}), ("cq_enq", "enqueue", {}),
                    ("dp_cmd", "read", {}), ("dp_rd_rsp", "response", {}), ("wb_rsp", "read_data", {})])
        status, rows = C.check(t, ALL, CATALOG, SCHEMAS, SPEC)
        self.assertEqual(status, "fail")
        broken = {r["id"]: r for r in rows if r["status"] == "broken"}
        self.assertEqual(set(broken), {"READ_CMD_TO_RESPONSE"})
        self.assertEqual(broken["READ_CMD_TO_RESPONSE"]["owner"], "data_path")
        self.assertEqual(broken["READ_CMD_TO_RESPONSE"]["lost"], 1)
        line = [l for l in C.render(status, rows).splitlines() if "CONSERVE" in l][0]
        self.assertIn("owner=data_path lost=1 of=2 from=dp_cmd.read to=dp_rd_rsp observed=1", line)

    def test_beat_lost_at_the_port_is_blamed_on_the_port_only(self):
        t = _trace([("wb", "write", {}), ("req", "request", {"we": "1"}), ("cq_enq", "enqueue", {}),
                    ("dp_wr", "write", {}), ("dp_cmd", "write", {}), ("ddr_wr_beat", "beat", {}), ("ddr_wr_beat", "beat", {}),
                    ("wb", "write", {})])          # accepted, never delivered
        status, rows = C.check(t, ALL, CATALOG, SCHEMAS, SPEC)
        broken = {r["id"] for r in rows if r["status"] == "broken"}
        self.assertEqual(broken, {"HOST_BEAT_TO_REQUEST"})

    def test_write_field_filter_counts_only_writes(self):
        t = _trace([("req", "request", {"we": "0"}), ("req", "request", {"we": "1"}), ("dp_wr", "write", {}),
                    ("cq_enq", "enqueue", {}), ("cq_enq", "enqueue", {})])
        status, rows = C.check(t, ["wb_port", "cmd_queue", "data_path"], CATALOG, SCHEMAS, SPEC)
        r = next(r for r in rows if r["id"] == "WRITE_REQUEST_TO_DATA")
        self.assertEqual((r["sources"], r["observed"], r["status"]), (1, 1, "checked"))

    def test_rule_skipped_when_a_block_is_absent(self):
        t = _trace([("wb", "read", {}), ("req", "request", {"we": "0"})])
        status, rows = C.check(t, ["wb_port"], CATALOG, SCHEMAS, SPEC)
        self.assertEqual(status, "pass")
        by = {r["id"]: r["status"] for r in rows}
        self.assertEqual(by["HOST_BEAT_TO_REQUEST"], "checked")
        self.assertEqual(by["RESPONSE_TO_HOST"], "not_applicable")
        self.assertEqual(by["READ_CMD_TO_RESPONSE"], "not_applicable")

    def test_reset_lines_are_not_transactions(self):
        t = _trace([("wb", "reset", {}), ("req", "reset", {})])
        status, rows = C.check(t, ALL, CATALOG, SCHEMAS, SPEC)
        self.assertEqual(status, "pass")


class TestEmitterParsesTheLines(unittest.TestCase):

    def test_conserve_and_stall_lines_match(self):
        sys.path.insert(0, os.path.join(ROOT, "Validation", "findings"))
        import emit_findings as E
        m = E.CONSERVE_RE.match("  CONSERVE WRITE_CMD_TO_BEATS owner=data_path lost=38 of=62 from=dp_cmd.write "
                                "to=ddr_wr_beat observed=24 per_source=2 | Every WR command drives one full host word")
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1), "WRITE_CMD_TO_BEATS")
        self.assertEqual(m.group(9), "2")
        m = E.CONSERVE_RE.match("CONSERVE HOST_BEAT_TO_REQUEST owner=wb_port lost=25 of=243 from=wb to=req observed=218 | Every host beat")
        self.assertIsNotNone(m)
        self.assertIsNone(m.group(9))
        m = E.STALL_RE.match("DRIVER_STALL: wb — 12 of 240 pipelined beat(s) never acknowledged (wb_ack_o)")
        self.assertIsNotNone(m)
        self.assertEqual(E.STALL_BEATS_RE.search(m.group(2)).groups(), ("12", "240", "wb_ack_o"))


if __name__ == "__main__":
    unittest.main()


class TestPartialDrop(unittest.TestCase):
    def test_interfaces_of_absent_blocks_make_the_rule_not_applicable(self):
        """A partial drop's schemas lack the absent blocks' interfaces; the
        rule must step aside, not crash (every Phase 1-3 path came back
        INCOMPLETE on runs/oct29_loop, 2026-10-29)."""
        partial = {k: v for k, v in SCHEMAS.items() if v["block"] != "data_path"}
        t = _trace([("wb", "read", {}), ("req", "request", {"we": "0"}), ("cq_enq", "enqueue", {})])
        status, rows = C.check(t, ["wb_port", "cmd_queue"], CATALOG, partial, SPEC)
        self.assertEqual(status, "pass")
        by = {r["id"]: r for r in rows}
        self.assertEqual(by["READ_CMD_TO_RESPONSE"]["status"], "not_applicable")
        self.assertIn("dp_cmd", by["READ_CMD_TO_RESPONSE"]["why"])
        self.assertEqual(by["HOST_BEAT_TO_REQUEST"]["status"], "checked")


class TestWaiverFileLoads(unittest.TestCase):
    def test_documentation_keys_do_not_break_the_loader(self):
        """A '$'-prefixed key in waivers.json is a note, not a field: the
        W-003 entry's notes broke every scoreboard run on 2026-10-29."""
        sys.path.insert(0, os.path.join(ROOT, "Validation", "waivers"))
        import waivers as W
        ws = W.WaiverSet.load()
        ids = {w.id for w in (ws.waivers if hasattr(ws, "waivers") else [])}
        self.assertIn("W-003", ids)
