#!/usr/bin/env python3
"""
Tests for phase-partial drops (one Frontend phase at a time).

What must hold:
  * a `standalone` path instantiates only its own block, and every edge it
    cuts takes the tie the map declares — or generation refuses; the silent
    zero tie-off never stands in for a missing block;
  * the map keeps edges whose source block is absent as `deferred`, so a
    standalone harness still knows they are cut edges;
  * the generators leave out what the absent blocks own instead of failing;
  * findings owned by absent blocks, or whose every path was blocked, are
    carried `untested` — never `resolved`.
"""

import json
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
V = os.path.abspath(os.path.join(HERE, ".."))
ROOT = os.path.abspath(os.path.join(V, ".."))
for d in ("structural", "findings", "txn", "sequences"):
    sys.path.insert(0, os.path.join(V, d))
import chain_harness_gen as CHG  # noqa: E402
import rtl_drop as RD  # noqa: E402

DROP = os.path.join(ROOT, "Frontend2", "OutputFolders")
PHASE1 = ("init_fsm", "config_regs", "wb_port")


def _map():
    with open(os.path.join(V, "structural", "integration_map.json")) as f:
        return json.load(f)


class TestStandaloneClosure(unittest.TestCase):
    def test_standalone_takes_no_support_closure(self):
        imap = _map()
        self.assertEqual(CHG.block_closure(["wb_port"], imap, standalone=True), ["wb_port"])
        full = CHG.block_closure(["wb_port"], imap)
        self.assertGreater(len(full), 1, "wb_port's ordinary closure pulls its neighbours")

    def test_every_cut_edge_of_the_standalone_paths_has_a_tie(self):
        imap = _map()
        ties = imap["standalone_ties"]
        with open(os.path.join(V, "spec", "path_definitions.json")) as f:
            pdefs = json.load(f)["paths"]
        edges = imap["connections"] + imap.get("deferred_connections", [])
        for p in pdefs:
            if not p.get("standalone"):
                continue
            for c in edges:
                blk = c["to"].partition(".")[0]
                src = c["from"].partition(".")[0]
                if blk in p["blocks"] and src not in p["blocks"]:
                    self.assertIn(c["to"], ties, f"{p['id']} cuts {c['to']} without a tie")

    def test_generation_refuses_an_undeclared_cut(self):
        imap = _map()
        imap = json.loads(json.dumps(imap))
        imap["standalone_ties"].pop("wb_port.req_ready")
        tmp = tempfile.mkdtemp()
        try:
            mp = os.path.join(tmp, "integration_map.json")
            with open(mp, "w") as f:
                json.dump(imap, f)
            with self.assertRaises(CHG.WiringError) as cm:
                CHG.generate("path_21_wb_port_standalone", None, imap)
            self.assertIn("standalone_ties", str(cm.exception))
            self.assertIn("wb_port.req_ready", str(cm.exception))
        finally:
            shutil.rmtree(tmp)

    def test_standalone_harness_uses_declared_ties_not_zero(self):
        sv, blocks = CHG.generate("path_21_wb_port_standalone", None, _map())
        self.assertEqual(blocks, ["wb_port"])
        self.assertIn("assign tie__wb_port__req_ready = 1'b1;", sv)
        self.assertIn("assign tie__wb_port__rsp_valid = 1'b0;", sv)


class TestPartialDropGenerators(unittest.TestCase):
    """Run the generators against a copy of the drop that has PHASE1RTL only."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="p1drop_")
        src = os.path.join(DROP, "PHASE1RTL")
        if not os.path.isdir(src):
            raise unittest.SkipTest("no PHASE1RTL in the drop")
        shutil.copytree(src, os.path.join(cls.tmp, "PHASE1RTL"))
        cls.env = dict(os.environ, VALIDATION_RTL_DROP_ROOTS=cls.tmp)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def _run(self, *cmd):
        import subprocess
        r = subprocess.run([sys.executable, "-W", "ignore", *cmd], cwd=ROOT, env=self.env,
                           capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    def test_resolver_reports_missing_never_substitutes(self):
        os.environ["VALIDATION_RTL_DROP_ROOTS"] = self.tmp
        try:
            RD._config.cache_clear() if hasattr(RD._config, "cache_clear") else None
            missing = RD.missing(["wb_port", "scheduler", "init_fsm", "data_path"])
        finally:
            os.environ.pop("VALIDATION_RTL_DROP_ROOTS", None)
        self.assertEqual(sorted(missing), ["data_path", "scheduler"])

    def test_map_defers_edges_of_absent_blocks(self):
        out = os.path.join(self.tmp, "imap.json")
        rc, txt = self._run("Validation/structural/integration_map_gen.py",
                            "--findings", os.devnull, "--out", out)
        self.assertEqual(rc, 0, txt)
        with open(out) as f:
            m = json.load(f)
        deferred = {d["to"] for d in m["deferred_connections"]}
        self.assertIn("wb_port.req_ready", deferred)
        self.assertIn("config_regs.sts_cal_done", deferred)
        self.assertTrue(all(b not in PHASE1 for b in m["$derivation"]["blocks_missing_from_drop"]))

    def test_schema_gen_leaves_out_absent_streams_only_when_allowed(self):
        out = tempfile.mkdtemp()
        try:
            import schema_gen as SG
            os.environ["VALIDATION_RTL_DROP_ROOTS"] = self.tmp
            try:
                with self.assertRaises(SG.SchemaError):
                    SG.resolve(allow_missing=False)
                doc = SG.resolve(allow_missing=True)
            finally:
                os.environ.pop("VALIDATION_RTL_DROP_ROOTS", None)
            self.assertIn("wb", doc["interfaces"])
            self.assertNotIn("ddr_cmd", doc["interfaces"])
            self.assertTrue(any(x.startswith("ddr_cmd ") for x in doc["streams_without_block"]))
        finally:
            shutil.rmtree(out)


class TestPartialFindings(unittest.TestCase):
    def test_blocked_findings_are_untested_not_resolved(self):
        import emit_findings as EF
        tmp = tempfile.mkdtemp()
        saved = EF.previous_outbox
        try:
            # a previous outbox with one scheduler finding on a blocked path and
            # one wb_port finding on a path that ran
            base = {"schema": "validation-findings/2", "kind": "defect", "severity": "major",
                    "title": "t", "taxonomy_id": "X", "first_seen": "aaaaaaa", "status": "open"}
            prev_doc = {"drop": "aaaaaaa", "generated_utc": "2026-01-01T00:00:00Z",
                        "findings": [
                            {**base, "id": "scheduler/PROTO_002", "check_id": "PROTO_002",
                             "owner_module": "scheduler", "paths": ["path_01_write_cmd"]},
                            {**base, "id": "wb_port/MISMATCH/req[addr]", "check_id": "MISMATCH/req[addr]",
                             "owner_module": "wb_port", "paths": ["path_21_wb_port_standalone"]}]}
            EF.previous_outbox = lambda spec_rev, head: ("aaaaaaa", prev_doc)
            # the partial drop's reports: one passing standalone wb_port path
            reports = os.path.join(tmp, "reports")
            os.makedirs(reports)
            with open(os.path.join(reports, "path_21_wb_port_standalone_report.json"), "w") as f:
                json.dump({"path": "path_21_wb_port_standalone", "verdict": "pass", "stages": [],
                           "rtl_drop": {"git_head": "bbbbbbb", "blocks": {}}}, f)
            ds = {"partial": True, "blocks_absent": ["scheduler"],
                  "paths_blocked": {"path_01_write_cmd": ["scheduler"]},
                  "paths_run": ["path_21_wb_port_standalone"]}
            out = os.path.join(tmp, "out")
            doc, _ = EF.emit(reports, out, ds)
            untested = {f["id"] for f in doc["findings"] if f.get("status") == "untested"}
            resolved = {f["id"] for f in doc["resolved"]}
            self.assertIn("scheduler/PROTO_002", untested)
            self.assertNotIn("scheduler/PROTO_002", resolved)
            self.assertIn("wb_port/MISMATCH/req[addr]", resolved)
            self.assertTrue(os.path.exists(os.path.join(out, "DROP_STATUS.json")))
        finally:
            EF.previous_outbox = saved
            shutil.rmtree(tmp, ignore_errors=True)


class TestPipelinedWishboneDriver(unittest.TestCase):
    """The spec's host interface is wishbone_pipelined: the driver drops stb
    the cycle after acceptance and holds cyc until ack; the request event is
    the accepted beat, not the ack."""

    def test_catalog_declares_pipelined_wb(self):
        with open(os.path.join(V, "txn", "interface_catalog.json")) as f:
            wb = json.load(f)["interfaces"]["wb"]
        self.assertEqual(wb["qualifier"], "wb_cyc_i && wb_stb_i && !wb_stall_o")
        self.assertEqual(wb["drive"]["accept"], "!wb_stall_o")
        self.assertEqual(wb["drive"]["release_on_accept"], ["wb_stb_i"])
        self.assertEqual(wb["drive"]["complete"], "wb_ack_o")

    def test_driver_releases_stb_on_accept_and_waits_for_ack(self):
        import driver_gen as DG
        with open(os.path.join(V, "txn", "interface_catalog.json")) as f:
            catalog = json.load(f)["interfaces"]
        with open(os.path.join(V, "txn", "generated", "schemas.json")) as f:
            schemas = json.load(f)["interfaces"]
        seq = {"name": "t", "steps": [{"op": "reset"},
                                      {"op": "drive", "iface": "wb", "kind": "read",
                                       "fields": {"addr": 64}},
                                      {"op": "idle", "cycles": 2}]}
        sv = DG.generate(seq, schemas, catalog)
        self.assertIn("accept_wb();", sv)
        self.assertIn("wait_wb();", sv)
        self.assertIn("while (!(!wb_stall_o)", sv)
        # stb is released at acceptance; cyc only after completion
        self.assertLess(sv.index("accept_wb();"), sv.index("wait_wb();"))
        self.assertIn("wb_stb_i = '0;\n  endtask", sv)


if __name__ == "__main__":
    unittest.main()
