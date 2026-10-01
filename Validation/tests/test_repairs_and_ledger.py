#!/usr/bin/env python3
"""Tests for the repair suite builder, the bridge gate's constant-bit and
two-pattern checks, and the UberDDR3 trace adapter."""
import json, os, shutil, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
V = os.path.join(HERE, "..")
for d in ("repairs", "faults", "txn", "gates", os.path.join("refdesigns", "uberddr3")):
    sys.path.insert(0, os.path.join(V, d))
import repair_suite as RS  # noqa: E402
import path_checkers_on_uberddr3 as UB  # noqa: E402


class TestRepairBuild(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self._r, self._w = RS.ROOT, RS.WORK
        RS.ROOT, RS.WORK = self.tmp, os.path.join(self.tmp, "work")
        os.makedirs(os.path.join(self.tmp, "drop"))
        with open(os.path.join(self.tmp, "drop", "a.sv"), "w") as f:
            f.write("x <= 1;\ny <= 1;\ny <= 1;\n")

    def tearDown(self):
        RS.ROOT, RS.WORK = self._r, self._w
        shutil.rmtree(self.tmp)

    def _read(self, dst):
        return open(os.path.join(dst, "a.sv")).read()

    def test_counted_edit_and_stacking(self):
        base = {"id": "R1", "file": "a.sv", "edits": [{"from": "x <= 1;", "to": "x <= 2;"}]}
        top = {"id": "R2", "file": "a.sv", "base": ["R1"],
               "edits": [{"from": "y <= 1;", "to": "y <= 3;", "count": 2}]}
        dst = RS.build(top, "drop", {"repairs": [base, top]})
        self.assertEqual(self._read(dst), "x <= 2;\ny <= 3;\ny <= 3;\n")
        self.assertEqual(open(os.path.join(self.tmp, "drop", "a.sv")).read(),
                         "x <= 1;\ny <= 1;\ny <= 1;\n")

    def test_wrong_count_is_an_error(self):
        bad = {"id": "R3", "file": "a.sv", "edits": [{"from": "y <= 1;", "to": "z"}]}
        with self.assertRaises(RS.RepairError):
            RS.build(bad, "drop", {"repairs": [bad]})


class TestCatalogAppliesToDrop(unittest.TestCase):
    def test_every_repair_applies_to_the_current_drop(self):
        cat = json.load(open(RS.CATALOG))
        tmp = tempfile.mkdtemp()
        w = RS.WORK
        RS.WORK = tmp
        try:
            for r in cat["repairs"]:
                RS.build(r, cat["drop_root"], cat)
        finally:
            RS.WORK = w
            shutil.rmtree(tmp)


class TestUberAdapter(unittest.TestCase):
    def test_address_mapping_and_calibration_filter(self):
        spec = {"memory_geometry": {"row_bits": 4, "bank_bits": 3, "column_bits": 10,
                                    "burst_length": 8}}
        enc = {"MRS": "4'b0000", "REF": "4'b0001", "PRE": "4'b0010", "ACT": "4'b0011",
               "WR": "4'b0100", "RD": "4'b0101", "NOP": "4'b0111"}
        addr = (5 << (7 + 3)) | (2 << 7) | 3          # row 5, bank 2, col field 3
        log = os.path.join(tempfile.mkdtemp(), "l.txt")
        with open(log, "w") as f:
            f.write("TXN ddr_cmd command t=10.0 ps addr=0 bank=1 cmd=5\n"      # calib READ: dropped
                    "TXN ddr_cmd command t=20.0 ps addr=7 bank=1 cmd=3\n"      # calib ACT: kept
                    "TXN wb calib_complete t=100\n"
                    f"TXN wb request t=200 ps addr={addr:x} we=1 data=0 sel=f\n"
                    "TXN ddr_cmd command t=300.0 ps addr=418 bank=2 cmd=4\n")  # WR, A10 set
        tr, calib, dropped = UB.build_trace(log, spec, enc)
        self.assertEqual((calib, dropped), (100, 1))
        self.assertEqual([t.iface for t in tr], ["ddr_cmd", "cq_enq", "ddr_cmd"])
        self.assertEqual(tr[1].fields, {"row": 5, "bank": 2, "col": 24, "we": 1})
        self.assertEqual(tr[2].fields["addr"], 0x18)                         # A10 stripped


class TestGateCatchesPrechargeA10(unittest.TestCase):
    def test_row_on_precharge_is_rejected(self):
        import predictor_gates as PG
        from txn_contract import TransactionPredictor, Txn
        spec = json.load(open(os.path.join(V, "spec", "llmmc_microarchitecturespec_filled.json")))
        schemas = json.load(open(os.path.join(V, "txn", "generated", "schemas.json")))["interfaces"]
        cat = json.load(open(os.path.join(V, "txn", "interface_catalog.json")))["interfaces"]
        senc = {k: PG.BusBridgeGate._numeric(v) for k, v in cat["sched_in"]["command_encoding"].items()
                if not k.startswith("$")}
        denc = {k: PG.BusBridgeGate._numeric(v) for k, v in cat["ddr_cmd"]["command_encoding"].items()
                if not k.startswith("$")}
        inv = {v: k for k, v in senc.items()}

        def make(pre_addr):
            class P(TransactionPredictor):
                INPUT_IFACES = ("sched_in",)
                OUTPUT_IFACES = ("ddr_cmd",)

                def __init__(self, spec):
                    pass

                def reset(self):
                    pass

                def process(self, t):
                    n = inv.get(t.fields["type"])
                    if n in (None, "NOP") or n not in denc:
                        return []
                    a = {"ACT": t.fields["row"], "RD": t.fields["col"], "WR": t.fields["col"],
                         "PRE": pre_addr(t)}.get(n, 0)
                    return [Txn("ddr_cmd", "command",
                                {"cmd": denc[n], "addr": a, "bank": t.fields["bank"]})]

                def drain(self):
                    return []
            return P(spec)
        good = PG.BusBridgeGate.grade(make(lambda t: 0), spec, schemas, cat)
        bad = PG.BusBridgeGate.grade(make(lambda t: t.fields["row"]), spec, schemas, cat)
        self.assertEqual(good, [])
        self.assertTrue(any("bit 10" in f for f in bad), bad)




class TestGateCompletesOn(unittest.TestCase):
    """A read response completes on dp_rd_rsp: the gate expects nothing on
    the request and exactly one response, carrying the completion's data."""

    def _grade(self, wait):
        import predictor_gates as PG
        from txn_contract import TransactionPredictor, Txn
        spec = json.load(open(os.path.join(V, "spec", "llmmc_microarchitecturespec_filled.json")))
        schemas = json.load(open(os.path.join(V, "txn", "generated", "schemas.json")))["interfaces"]
        cat = json.load(open(os.path.join(V, "txn", "interface_catalog.json")))["interfaces"]

        class P(TransactionPredictor):
            INPUT_IFACES = ("wb", "dp_rd_rsp")
            OUTPUT_IFACES = ("req", "wb_rsp")

            def __init__(self, spec):
                self.reset()

            def reset(self):
                self.pending = []

            def process(self, t):
                out = []
                if t.iface == "wb":
                    f = {"we": 1 if t.kind == "write" else 0, "addr": t.fields["addr"],
                         "data": t.fields.get("data", 0), "mask": t.fields.get("sel", 0)}
                    out.append(Txn("req", "request", f))
                    if t.kind == "read":
                        if wait:
                            self.pending.append(t.fields["addr"])
                        else:
                            out.append(Txn("wb_rsp", "read_data", {"addr": t.fields["addr"], "data": 0}))
                elif t.iface == "dp_rd_rsp" and self.pending:
                    out.append(Txn("wb_rsp", "read_data",
                                   {"addr": self.pending.pop(0), "data": t.fields["data"]}))
                return out

            def drain(self):
                return []
        return PG.BusBridgeGate.grade(P(spec), spec, schemas, cat)

    def test_waiting_for_the_completion_is_accepted(self):
        self.assertEqual(self._grade(wait=True), [])

    def test_answering_from_the_request_alone_is_rejected(self):
        self.assertTrue(any("before its dp_rd_rsp" in f for f in self._grade(wait=False)))


if __name__ == "__main__":
    unittest.main()


class TestFormalAbstraction(unittest.TestCase):
    """--stopat renders a JasperGold cut before the clock is declared, and the
    ledger never takes a cex found under a cut as fired evidence (it may be
    spurious) while a proof under one still counts as silent evidence."""

    def test_tcl_places_stopat_after_elaborate(self):
        sys.path.insert(0, os.path.join(V, "tools"))
        import run_formal as RF
        tcl = RF.TCL.format(time="1m", trace=10, stopat="stopat u_init_fsm.wait_cnt\n")
        lines = tcl.splitlines()
        self.assertLess(lines.index("elaborate -top chain_formal"),
                        lines.index("stopat u_init_fsm.wait_cnt"))
        self.assertLess(lines.index("stopat u_init_fsm.wait_cnt"), lines.index("clock clk"))
        self.assertNotIn("stopat", RF.TCL.format(time="1m", trace=10, stopat=""))

    def test_ledger_reports_abstracted_proofs_not_abstracted_cex(self):
        led = json.load(open(os.path.join(V, "reports", "check_ledger.json")))
        rows = {r["check"]: r for r in led["rows"] if r["kind"] == "assertion"}
        self.assertIn("proven (u_init_fsm.wait_cnt cut)", rows["a_INIT_001"]["silent"])
        self.assertNotIn("formal-cex", rows["a_INIT_002_init_done"]["fired"])
        self.assertIn("proven", rows["a_CAL_001"]["silent"])
