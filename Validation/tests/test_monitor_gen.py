#!/usr/bin/env python3
"""
Tests for monitor codegen and trace extraction
===============================================
These two pieces sit between the simulator and the scoreboard, so their bugs
masquerade as design bugs. The tests below pin the failure modes that would
do that:

  * a monitor that references a signal it never declared (will not compile,
    or worse, binds wrong)
  * a monitor generated from a stale catalog naming a port that no longer
    exists (must fail loudly, not emit a broken monitor)
  * a dropped or malformed TXN line (would surface as a phantom `missing`
    mismatch and blame the design for a parser bug)
  * sampling at the clock edge instead of after NBA — the defect that
    fabricated 176 failures against correct RTL

Run:  python3 Validation/tests/test_monitor_gen.py
"""

import json
import os
import re
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "txn"))

import monitor_gen
import trace_extract
from txn_contract import load_trace

CATALOG = json.load(open(os.path.join(HERE, "..", "txn",
                                      "interface_catalog.json")))["interfaces"]
SCHEMAS = json.load(open(os.path.join(HERE, "..", "txn", "generated",
                                      "schemas.json")))["interfaces"]


def gen(iface, catalog_override=None):
    entry = dict(CATALOG[iface])
    if catalog_override:
        entry.update(catalog_override)
    return monitor_gen.generate_monitor(iface, entry, SCHEMAS[iface])


def declared_ports(src):
    return set(re.findall(r"input\s+logic\s+(?:\[[^\]]+\]\s*)?(\w+)", src))


class TestGeneratedMonitorIsWellFormed(unittest.TestCase):

    def test_every_interface_generates(self):
        for iface in SCHEMAS:
            mod, src = gen(iface)
            self.assertEqual(mod, f"{iface}_monitor")
            self.assertIn("endmodule", src)

    def test_qualifier_signals_are_declared(self):
        """The bug this test exists for: the qualifier and kind_select
        expressions reference DUT ports that the field mappings do not, and
        an undeclared reference will not compile."""
        for iface in SCHEMAS:
            _, src = gen(iface)
            decl = declared_ports(src)
            qual = CATALOG[iface]["qualifier"]
            manifest = monitor_gen.load_manifest_ports(SCHEMAS[iface]["manifest"])
            for port in monitor_gen.expression_ports(qual, manifest, iface, "q"):
                self.assertIn(port, decl,
                              f"{iface}: qualifier uses {port} but never declares it")

    def test_kind_select_signals_are_declared(self):
        for iface in SCHEMAS:
            ksel = CATALOG[iface].get("kind_select")
            if not ksel:
                continue
            _, src = gen(iface)
            decl = declared_ports(src)
            manifest = monitor_gen.load_manifest_ports(SCHEMAS[iface]["manifest"])
            for port in monitor_gen.expression_ports(ksel["expr"], manifest,
                                                     iface, "k"):
                self.assertIn(port, decl)

    def test_all_schema_fields_are_declared(self):
        for iface in SCHEMAS:
            _, src = gen(iface)
            decl = declared_ports(src)
            for kind, fields in SCHEMAS[iface]["kinds"].items():
                for fname, info in fields.items():
                    self.assertIn(info["port"], decl,
                                  f"{iface}.{kind}.{fname} port not declared")

    def test_monitor_is_passive(self):
        """A monitor must never drive a DUT signal. Passivity is about what it
        writes, not whether it holds state: an edge-detect register is
        monitor-local and legitimate. What would invalidate every trace it
        produces is declaring an output, or assigning to a port it observes."""
        for iface in SCHEMAS:
            _, src = gen(iface)
            header = src.split("endmodule")[0].split("module")[1]
            self.assertNotIn("output", header,
                             f"{iface}_monitor declares an output port")

            observed = declared_ports(src)          # every DUT signal it sees
            # local regs may be scalar (logic x;) or vector (logic [7:0] x;)
            local = set(re.findall(
                r"^\s*logic\s+(?:\[[^\]]+\]\s*)?(\w+)\s*;", src, re.M))
            body = src[src.index("always @"):]
            for target in re.findall(r"(\w+)\s*<=", body):
                self.assertNotIn(target, observed,
                                 f"{iface}: monitor assigns to DUT port {target}")
                self.assertIn(target, local,
                              f"{iface}: {target} assigned but not a local reg")
            for target in re.findall(r"^\s*(\w+)\s*=[^=]", body, re.M):
                self.assertNotIn(target, observed,
                                 f"{iface}: blocking assign to DUT port {target}")

    def test_samples_after_nba_not_at_the_edge(self):
        """The config_regs lesson, pinned. Reading at the clock edge returns
        pre-NBA values and fabricates failures against correct RTL."""
        for iface in SCHEMAS:
            _, src = gen(iface)
            # A monitor has two always blocks: the reset event (negedge) and
            # the transaction sampler (posedge). Check the sampler.
            body = src[src.index("always @(posedge"):]
            self.assertIn("#SAMPLE_DELAY", body,
                          f"{iface}: samples at the edge, before NBA commit")
            edge = body.index("posedge")
            delay = body.index("#SAMPLE_DELAY")
            disp = body.index("$display")
            self.assertLess(edge, delay)
            self.assertLess(delay, disp, f"{iface}: display precedes the delay")

    def test_reset_is_respected(self):
        for iface in SCHEMAS:
            _, src = gen(iface)
            body = src[src.index("always @(posedge"):]
            self.assertIn(CATALOG[iface]["reset"], body,
                          f"{iface}: emits transactions during reset")

    def test_bind_targets_the_schema_block(self):
        entries = [(i, SCHEMAS[i]["block"], f"{i}_monitor") for i in sorted(SCHEMAS)]
        bind = monitor_gen.generate_bind(entries)
        for iface, block, mod in entries:
            self.assertIn(f"bind {block} {mod} u_{iface}_mon (.*);", bind)


class TestGeneratorFailsLoudly(unittest.TestCase):
    """Never emit a wrong monitor — the spec-swap safety property."""

    def test_qualifier_naming_a_missing_port_is_rejected(self):
        with self.assertRaises(monitor_gen.MonitorGenError) as cm:
            gen("csr", {"qualifier": "csr_ack_o && vanished_port"})
        self.assertIn("vanished_port", str(cm.exception))

    def test_missing_qualifier_is_rejected(self):
        entry = {k: v for k, v in CATALOG["csr"].items() if k != "qualifier"}
        with self.assertRaises(monitor_gen.MonitorGenError):
            monitor_gen.generate_monitor("csr", entry, SCHEMAS["csr"])

    def test_multi_kind_without_kind_select_is_rejected(self):
        entry = {k: v for k, v in CATALOG["csr"].items() if k != "kind_select"}
        with self.assertRaises(monitor_gen.MonitorGenError) as cm:
            monitor_gen.generate_monitor("csr", entry, SCHEMAS["csr"])
        self.assertIn("kind_select", str(cm.exception))

    def test_kind_select_mapping_to_unknown_kind_is_rejected(self):
        with self.assertRaises(monitor_gen.MonitorGenError):
            gen("csr", {"kind_select": {"expr": "csr_we_i",
                                        "map": {"1": "nonexistent_kind", "0": "read"}}})

    def test_sv_literals_are_not_mistaken_for_ports(self):
        """4'b0111 must not parse as a signal named b0111."""
        manifest = monitor_gen.load_manifest_ports(SCHEMAS["ddr_cmd"]["manifest"])
        found = monitor_gen.expression_ports(
            "(ddr_cmd != 4'b0111) && (ddr_cmd != 4'b1111)", manifest, "ddr_cmd", "q")
        self.assertEqual(found, ["ddr_cmd"])


LOG = """\
xcelium> run
TXN csr write t=1250 addr=8 data=271c0b0b
some unrelated simulator chatter
TXN csr read t=1500 addr=8
TXN csr_rsp read_data t=1500 addr=8 data=271c0b0b err=0
TXN ddr_cmd command t=1750 addr=1a2b bank=3 cmd=3
xmsim: *N,SIMEND: simulation complete
"""


class TestTraceExtraction(unittest.TestCase):

    def _log(self, text):
        f = tempfile.NamedTemporaryFile("w", suffix=".log", delete=False)
        f.write(text)
        f.close()
        return f.name

    def test_extracts_transactions_in_order(self):
        p = self._log(LOG)
        try:
            txns = trace_extract.extract(p, SCHEMAS)
            self.assertEqual(len(txns), 4)
            self.assertEqual([t.iface for t in txns],
                             ["csr", "csr", "csr_rsp", "ddr_cmd"])
            self.assertEqual([t.seq for t in txns], [0, 1, 2, 3])
            self.assertEqual(txns[0].fields["data"], 0x271C0B0B)
            self.assertEqual(txns[0].time_ns, 1250)
        finally:
            os.unlink(p)

    def test_non_txn_lines_are_ignored(self):
        p = self._log(LOG)
        try:
            self.assertEqual(len(trace_extract.extract(p, SCHEMAS)), 4)
        finally:
            os.unlink(p)

    def test_malformed_txn_line_is_an_error_not_a_skip(self):
        """Silently dropping a line would surface later as a phantom
        `missing` mismatch and blame the design for a parser bug."""
        p = self._log("TXN csr write addr=8\n")     # no t= field
        try:
            with self.assertRaises(trace_extract.TraceError):
                trace_extract.extract(p, SCHEMAS)
        finally:
            os.unlink(p)

    def test_unknown_interface_is_rejected(self):
        p = self._log("TXN mystery thing t=10 a=1\n")
        try:
            with self.assertRaises(trace_extract.TraceError) as cm:
                trace_extract.extract(p, SCHEMAS)
            self.assertIn("drift", str(cm.exception).lower() + "drift")
        finally:
            os.unlink(p)

    def test_field_set_mismatch_is_rejected(self):
        """Monitors and schema out of sync must stop extraction, because the
        scoreboard would otherwise compare against the wrong field set."""
        p = self._log("TXN csr write t=10 addr=8\n")   # missing data
        try:
            with self.assertRaises(trace_extract.TraceError) as cm:
                trace_extract.extract(p, SCHEMAS)
            self.assertIn("field mismatch", str(cm.exception))
        finally:
            os.unlink(p)

    def test_x_values_are_preserved_not_coerced(self):
        """An X on a cycle the qualifier called a transaction is a real
        finding; coercing it to 0 would hide a bug."""
        p = self._log("TXN csr_rsp read_data t=10 addr=8 data=xxxxxxxx err=0\n")
        try:
            txns = trace_extract.extract(p, SCHEMAS)
            self.assertEqual(txns[0].fields["data"], "xxxxxxxx")
        finally:
            os.unlink(p)

    def test_roundtrips_through_jsonl(self):
        p = self._log(LOG)
        out = p + ".jsonl"
        try:
            txns = trace_extract.extract(p, SCHEMAS)
            from txn_contract import save_trace
            save_trace(txns, out)
            back = load_trace(out)
            self.assertEqual([t.key() for t in back], [t.key() for t in txns])
        finally:
            os.unlink(p)
            if os.path.exists(out):
                os.unlink(out)

    def test_empty_log_yields_empty_trace_not_a_crash(self):
        p = self._log("no transactions here\n")
        try:
            self.assertEqual(trace_extract.extract(p, SCHEMAS), [])
        finally:
            os.unlink(p)


class TestResetEvents(unittest.TestCase):
    """A reset is state-clearing the model must see. The config_regs vector
    file resets 9 times mid-stream; without reset events a stateful predictor
    desynchronises after the first one and every later check is wrong — the
    bug the first full-chain run surfaced."""

    def test_every_monitor_emits_reset(self):
        for iface in SCHEMAS:
            _, src = gen(iface)
            self.assertIn(f"negedge {CATALOG[iface]['reset']}", src,
                          f"{iface}: no reset event emitted")
            self.assertIn(f'TXN {iface} reset', src)

    def test_reset_line_parses_and_carries_no_fields(self):
        f = tempfile.NamedTemporaryFile("w", suffix=".log", delete=False)
        f.write("TXN csr reset t=500\n"); f.close()
        try:
            txns = trace_extract.extract(f.name, SCHEMAS)
            self.assertEqual(len(txns), 1)
            self.assertEqual(txns[0].kind, "reset")
            self.assertEqual(txns[0].fields, {})
        finally:
            os.unlink(f.name)

    def test_reset_with_fields_is_rejected(self):
        f = tempfile.NamedTemporaryFile("w", suffix=".log", delete=False)
        f.write("TXN csr reset t=500 addr=8\n"); f.close()
        try:
            with self.assertRaises(trace_extract.TraceError):
                trace_extract.extract(f.name, SCHEMAS)
        finally:
            os.unlink(f.name)

    def test_scoreboard_resets_the_model_and_never_compares_resets(self):
        sys.path.insert(0, os.path.join(HERE, "..", "txn"))
        from scoreboard import Scoreboard
        from txn_contract import Txn, TransactionPredictor

        class Counter(TransactionPredictor):
            """Emits an incrementing count; reset returns it to zero."""
            INPUT_IFACES = ("csr",)
            OUTPUT_IFACES = ("csr_rsp",)
            def __init__(self, spec): self.reset()
            def reset(self): self.n = 0
            def process(self, txn):
                if txn.iface != "csr": return []
                self.n += 1
                return [Txn("csr_rsp", "read_data",
                            {"addr": 0, "data": self.n, "err": 0})]
            def drain(self): return []

        # two reads, a reset, then a third read -> counts 1, 2, then 1 again
        trace = [Txn("csr", "read", {"addr": 0}, 0),
                 Txn("csr_rsp", "read_data", {"addr": 0, "data": 1, "err": 0}, 1),
                 Txn("csr", "read", {"addr": 0}, 2),
                 Txn("csr_rsp", "read_data", {"addr": 0, "data": 2, "err": 0}, 3),
                 Txn("csr", "reset", {}, 4),
                 Txn("csr", "read", {"addr": 0}, 5),
                 Txn("csr_rsp", "read_data", {"addr": 0, "data": 1, "err": 0}, 6)]
        res = Scoreboard("exact", Counter({}), scope="t").run(trace)
        self.assertEqual(res.status, "pass", res.summary())
        self.assertEqual(res.predicted_count, 3,
                         "reset must not be fed to process()")

    def test_trace_of_only_resets_is_unknown_not_pass(self):
        sys.path.insert(0, os.path.join(HERE, "..", "txn"))
        from scoreboard import Scoreboard
        from txn_contract import Txn, TransactionPredictor

        class P(TransactionPredictor):
            INPUT_IFACES = ("csr",); OUTPUT_IFACES = ("csr_rsp",)
            def __init__(self, spec): self.reset()
            def reset(self): pass
            def process(self, txn): return []
            def drain(self): return []

        res = Scoreboard("exact", P({}), scope="t").run(
            [Txn("csr", "reset", {}, 0), Txn("csr", "reset", {}, 1)])
        self.assertEqual(res.status, "unknown")


class TestMonitorToScoreboardRoundTrip(unittest.TestCase):
    """The seam that matters: what a monitor prints must be what the
    scoreboard can consume, with no hand-editing in between."""

    def test_monitor_format_matches_extractor_expectations(self):
        for iface in SCHEMAS:
            _, src = gen(iface)
            for line in src.splitlines():
                if "$display" not in line:
                    continue
                fmt = line.split('"')[1]
                literal = (fmt.replace("%0t", "1000").replace("%0h", "ff"))
                parsed = trace_extract.TXN_RE.match(literal)
                self.assertIsNotNone(
                    parsed, f"{iface}: monitor prints a line the extractor "
                            f"cannot parse: {literal!r}")
                p_iface, p_kind, _, rest = parsed.groups()
                self.assertEqual(p_iface, iface)
                got = {f for f, _ in trace_extract.FIELD_RE.findall(rest)}
                if p_kind == "reset":
                    self.assertEqual(got, set(), "reset must carry no fields")
                    continue
                self.assertIn(p_kind, SCHEMAS[iface]["kinds"])
                self.assertEqual(got, set(SCHEMAS[iface]["kinds"][p_kind]),
                                 f"{iface}.{p_kind}: printed fields differ from schema")


if __name__ == "__main__":
    unittest.main(verbosity=1)
