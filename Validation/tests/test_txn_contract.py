#!/usr/bin/env python3
"""
Tests for the transaction contract and schema generation
=========================================================
Includes a rehearsal of the agent's generate-validate-repair loop: a good
predictor file passes contract_check, and each contract violation an agent is
likely to commit produces an actionable error string — because those strings
are the repair prompt.

Run:  python3 Validation/tests/test_txn_contract.py
"""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "txn"))

from txn_contract import (Txn, Violation, TransactionPredictor, LegalityChecker,
                          contract_check, load_trace, save_trace,
                          CHECK_STRATEGIES, strategy_for_scope)
import schema_gen

SPEC_PATH = os.path.join(HERE, "..", "spec",
                         "llmmc_microarchitecturespec_filled.json")
with open(SPEC_PATH) as f:
    SPEC = json.load(f)


# --------------------------------------------------------------------- Txn --

class TestTxn(unittest.TestCase):
    def test_key_ignores_seq_and_time(self):
        a = Txn("csr", "read", {"addr": 4, "data": 9}, seq=1, time_ns=100)
        b = Txn("csr", "read", {"addr": 4, "data": 9}, seq=7, time_ns=999)
        self.assertEqual(a.key(), b.key())

    def test_key_distinguishes_fields(self):
        a = Txn("csr", "read", {"addr": 4, "data": 9})
        b = Txn("csr", "read", {"addr": 4, "data": 8})
        self.assertNotEqual(a.key(), b.key())

    def test_trace_roundtrip(self):
        txns = [Txn("csr", "write", {"addr": 8, "data": 0x271C0B0B}, seq=0),
                Txn("csr", "read", {"addr": 8, "data": 0x271C0B0B}, seq=1)]
        with tempfile.NamedTemporaryFile("w", suffix=".jsonl",
                                         delete=False) as f:
            path = f.name
        try:
            save_trace(txns, path)
            back = load_trace(path)
            self.assertEqual([t.key() for t in back], [t.key() for t in txns])
        finally:
            os.unlink(path)


# ------------------------------------------------------------- the gate ----

GOOD_PREDICTOR = '''
import os, sys
sys.path.insert(0, {txn_dir!r})
from txn_contract import TransactionPredictor, Txn

class EchoPredictor(TransactionPredictor):
    """Minimal legal predictor: echoes csr writes as reads."""
    INPUT_IFACES = ("csr",)
    OUTPUT_IFACES = ("csr",)

    def __init__(self, spec):
        self.spec = spec
        self.reset()

    def reset(self):
        self.pending = []

    def process(self, txn):
        if txn.iface not in self.INPUT_IFACES:
            return []
        if txn.kind == "write":
            return [Txn("csr", "read", dict(txn.fields))]
        return []

    def drain(self):
        return []
'''

NO_SUBCLASS = "class NotAPredictor:\n    pass\n"

CRASHY_PROCESS = '''
import sys
sys.path.insert(0, {txn_dir!r})
from txn_contract import TransactionPredictor

class BadPredictor(TransactionPredictor):
    INPUT_IFACES = ("csr",)
    OUTPUT_IFACES = ("csr",)
    def __init__(self, spec): pass
    def reset(self): pass
    def process(self, txn):
        return txn.fields["addr"]     # KeyError on unknown iface, wrong type
    def drain(self): return []
'''


def write_tmp(content):
    """Materialise a template as a temp .py file.

    Uses a literal token replace rather than str.format(): these templates are
    Python source and contain their own braces (f-strings, dicts), which
    .format() would try to interpret."""
    txn_dir = os.path.abspath(os.path.join(HERE, "..", "txn"))
    f = tempfile.NamedTemporaryFile("w", suffix=".py", delete=False)
    f.write(content.replace("{txn_dir!r}", repr(txn_dir)))
    f.close()
    return f.name


class TestContractCheck(unittest.TestCase):
    def test_good_predictor_passes(self):
        path = write_tmp(GOOD_PREDICTOR)
        try:
            self.assertEqual(contract_check(path, SPEC), [])
        finally:
            os.unlink(path)

    def test_syntax_error_is_reported_with_line(self):
        path = write_tmp("def broken(:\n")
        try:
            errs = contract_check(path, SPEC)
            self.assertEqual(len(errs), 1)
            self.assertIn("does not parse", errs[0])
        finally:
            os.unlink(path)

    def test_missing_subclass_names_the_requirement(self):
        path = write_tmp(NO_SUBCLASS)
        try:
            errs = contract_check(path, SPEC)
            self.assertTrue(any("TransactionPredictor" in e for e in errs))
        finally:
            os.unlink(path)

    def test_crashy_process_is_caught_not_raised(self):
        path = write_tmp(CRASHY_PROCESS)
        try:
            errs = contract_check(path, SPEC)
            self.assertTrue(any("ignore unknown interfaces" in e for e in errs),
                            errs)
        finally:
            os.unlink(path)


GOOD_CHECKER = '''
import sys
sys.path.insert(0, {txn_dir!r})
from txn_contract import LegalityChecker, Violation

class QueueLivenessChecker(LegalityChecker):
    """Minimal legal checker: every request must eventually be served."""
    INPUT_IFACES = ("req", "ddr_cmd")
    OUTPUT_IFACES = ()

    def __init__(self, spec):
        self.spec = spec
        self.reset()

    def reset(self):
        self.outstanding = []

    def observe(self, txn):
        if txn.iface == "req":
            self.outstanding.append(txn)
        elif txn.iface == "ddr_cmd" and self.outstanding:
            self.outstanding.pop(0)
        return []

    def final(self):
        if self.outstanding:
            return [Violation("no_starvation",
                              f"{len(self.outstanding)} request(s) never served",
                              taxonomy_id="REF_001",
                              txns=self.outstanding[:3])]
        return []
'''


class TestLegalityCheckerContract(unittest.TestCase):
    """The `invariant` strategy gates a different shape of model."""

    def test_good_checker_passes_invariant_strategy(self):
        path = write_tmp(GOOD_CHECKER)
        try:
            self.assertEqual(contract_check(path, SPEC, "invariant"), [])
        finally:
            os.unlink(path)

    def test_checker_rejected_when_strategy_wants_a_predictor(self):
        """Handing a LegalityChecker to an 'exact' scope must say so plainly —
        this string goes back to the agent as its repair instruction."""
        path = write_tmp(GOOD_CHECKER)
        try:
            errs = contract_check(path, SPEC, "exact")
            self.assertTrue(errs)
            self.assertIn("TransactionPredictor", errs[0])
            self.assertIn("exact", errs[0])
        finally:
            os.unlink(path)

    def test_predictor_rejected_when_strategy_wants_a_checker(self):
        path = write_tmp(GOOD_PREDICTOR)
        try:
            errs = contract_check(path, SPEC, "invariant")
            self.assertTrue(errs)
            self.assertIn("LegalityChecker", errs[0])
        finally:
            os.unlink(path)

    def test_observe_strategy_needs_no_model(self):
        """Autonomous scopes have nothing to gate — an empty file is fine."""
        path = write_tmp("# no model: monitors and SVA carry this scope\n")
        try:
            self.assertEqual(contract_check(path, SPEC, "observe"), [])
        finally:
            os.unlink(path)

    def test_unknown_strategy_is_rejected(self):
        path = write_tmp(GOOD_PREDICTOR)
        try:
            errs = contract_check(path, SPEC, "guesswork")
            self.assertTrue(any("unknown check strategy" in e for e in errs))
        finally:
            os.unlink(path)

    def test_violation_serializes(self):
        v = Violation("tRCD", "READ 3 cycles after ACT", taxonomy_id="TIMING_001",
                      txns=[Txn("ddr_cmd", "command", {"cmd": 5, "bank": 2})])
        d = v.to_dict()
        self.assertEqual(d["taxonomy_id"], "TIMING_001")
        self.assertEqual(len(d["txns"]), 1)
        self.assertIn("tRCD", str(v))


class TestStrategyFromPathDefs(unittest.TestCase):
    """Strategy comes from data, never from the scope's name."""

    PATH_DEFS = os.path.join(HERE, "..", "spec", "path_definitions.json")

    def test_every_path_declares_a_valid_strategy(self):
        with open(self.PATH_DEFS) as f:
            defs = json.load(f)
        for p in defs["paths"]:
            self.assertIn("check_strategy", p, f"{p['id']} has no strategy")
            self.assertIn(p["check_strategy"], CHECK_STRATEGIES,
                          f"{p['id']}: {p['check_strategy']!r} is not a strategy")

    def test_feedback_loops_are_not_exact(self):
        """A feedback loop has no entry/exit to predict across; assigning it
        'exact' would demand a prediction that cannot be made."""
        with open(self.PATH_DEFS) as f:
            defs = json.load(f)
        for p in defs["paths"]:
            if p.get("category") == "feedback_loop":
                self.assertIn(p["check_strategy"], ("invariant", "observe"),
                              f"{p['id']} is a feedback loop but is {p['check_strategy']}")

    def test_autonomous_paths_do_not_require_a_predictor(self):
        """An init/status path runs from reset with nothing to predict FROM,
        so it can never be 'exact'. It may be observed, judged by an
        invariant checker over what it emitted (then the stage rules must
        exist for it), or composed with its autonomous stage left to SVA."""
        with open(self.PATH_DEFS) as f:
            defs = json.load(f)
        with open(os.path.join(HERE, "..", "gates",
                               "stage_invariant_rules.json")) as f:
            stages = json.load(f)["stages"]
        for p in defs["paths"]:
            if p.get("category") in ("init", "status"):
                self.assertIn(p["check_strategy"],
                              ("observe", "invariant", "composed"),
                              f"{p['id']} is autonomous but is {p['check_strategy']}")
                if p["check_strategy"] == "invariant":
                    self.assertIn(p["id"], stages,
                                  f"{p['id']} is judged by an invariant checker "
                                  f"but stage_invariant_rules.json has no rules "
                                  f"to grade one")

    def test_lookup_reads_the_file(self):
        self.assertEqual(
            strategy_for_scope("path_04_scheduler_bank_loop", self.PATH_DEFS),
            "invariant")
        self.assertEqual(
            strategy_for_scope("path_07_backpressure", self.PATH_DEFS), "exact")

    def test_unknown_scope_falls_back_to_default(self):
        self.assertEqual(
            strategy_for_scope("no_such_scope", self.PATH_DEFS), "exact")


# ------------------------------------------------------------ schema gen ---

class TestSchemaGen(unittest.TestCase):
    def test_resolves_against_current_design(self):
        """A request/response bus is two interfaces: csr carries what was
        asked, csr_rsp what the design answered. Collapsing them would make
        the scoreboard's input/output partition ambiguous."""
        result = schema_gen.resolve()
        ifaces = result["interfaces"]
        self.assertIn("csr", ifaces)
        self.assertIn("csr_rsp", ifaces)

        # request stream: address in, write data in
        req = ifaces["csr"]["kinds"]
        self.assertEqual(req["read"]["addr"]["width"], 8)
        self.assertEqual(req["read"]["addr"]["dir"], "input")
        self.assertEqual(req["write"]["data"]["width"], 32)
        self.assertEqual(req["write"]["data"]["dir"], "input")
        self.assertNotIn("data", req["read"],
                         "a read REQUEST cannot carry read data")

        # response stream: read data out
        rsp = ifaces["csr_rsp"]["kinds"]
        self.assertEqual(rsp["read_data"]["data"]["width"], 32)
        self.assertEqual(rsp["read_data"]["data"]["dir"], "output")

    def test_unknown_port_fails_loudly(self):
        """Spec-swap safety: a catalog referencing a vanished port must stop
        generation with the port named, never emit a silently wrong schema."""
        import tempfile
        bad = {"schema_version": "1.0", "interfaces": {
            "csr": {"block": "config_regs",
                    "kinds": {"read": {"addr": "no_such_port_xyz"}}}}}
        with tempfile.NamedTemporaryFile("w", suffix=".json",
                                         delete=False) as f:
            json.dump(bad, f)
            path = f.name
        try:
            with self.assertRaises(schema_gen.SchemaError) as cm:
                schema_gen.resolve(catalog_path=path)
            self.assertIn("no_such_port_xyz", str(cm.exception))
        finally:
            os.unlink(path)


if __name__ == "__main__":
    unittest.main(verbosity=1)
