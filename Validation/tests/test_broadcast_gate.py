#!/usr/bin/env python3
"""The register gate's broadcast step (2026-10-01): a register block's level
streams (cfg_timing, cfg_refresh) mirror register fields, so a predictor that
leaves them undeclared, never emits them, carries a wrong value, or maps a
field to the wrong register is rejected -- and a faithful model is not.

The primary config_regs predictor had been accepted on csr_rsp alone, from
before the cfg_* streams existed; the second model disagreed with it 21/57
and was right. The reference model below is hand-written from the spec so
the mutations are stable (an LLM-generated model's text changes every
regeneration)."""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
V = os.path.abspath(os.path.join(HERE, ".."))
ROOT = os.path.abspath(os.path.join(V, ".."))
for d in ("agents", "txn", "gates"):
    sys.path.insert(0, os.path.join(V, d))

INS = ["csr", "csr_sts", "csr_sts_level"]
OUTS = ["cfg_refresh", "cfg_timing", "csr_rsp"]

# A minimal config_regs model: registers from the spec map, RW retains, RO
# ignores writes, RW1C clears on 1, WO reads zero, err only on an unmapped
# address, and every write re-derives the cfg_* broadcasts (one update per
# stream when it changed). The two marked lines are the mutation points.
REFERENCE = r'''
from txn_contract import TransactionPredictor, Txn
from typing import List


def _bits(b):
    hi, _, lo = str(b).partition(":")
    hi = int(hi); lo = int(lo) if lo else hi
    return hi, lo


class Predictor(TransactionPredictor):
    INPUT_IFACES = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES = ('cfg_refresh', 'cfg_timing', 'csr_rsp')
    TIMING = {"trcd": "tRCD_nCK", "trp": "tRP_nCK", "tras": "tRAS_nCK", "trc": "tRC_nCK",
              "trrd": "tRRD_nCK", "tfaw": "tFAW_nCK", "twtr": "tWTR_nCK", "twr": "tWR_nCK",
              "trtp": "tRTP_nCK", "tccd": "tCCD_nCK", "trfc": "tRFC_nCK"}
    REFRESH = {"trefi": "tREFI_nCK", "max_postpone": "max_postpone",
               "urgent_threshold": "urgent_threshold", "priority": "ref_priority"}

    def __init__(self, spec):
        rm = spec["csr_register_map"]
        self.width = int(rm.get("data_width_bits", 32))
        self.regs = {int(str(r["offset"]), 16): r for r in rm["registers"]}
        self.field_reg = {}
        for off, r in self.regs.items():
            for f in r["fields"]:
                self.field_reg[f["name"]] = (off, f)
        self.reset()

    def _field(self, name):
        off, f = self.field_reg[name]
        hi, lo = _bits(f["bits"])
        return (self.val[off] >> lo) & ((1 << (hi - lo + 1)) - 1)

    def _timing(self):
        return {k: self._field(v) for k, v in self.TIMING.items()}   # MUT:VALUE

    def _refresh(self):
        d = {k: self._field(v) for k, v in self.REFRESH.items()}
        d["force_refresh"] = self.force
        return d

    def reset(self):
        self.levels = {}
        self.val = {}
        for off, r in self.regs.items():
            v = 0
            for f in r["fields"]:
                hi, lo = _bits(f["bits"])
                v |= (int(f.get("reset_value", 0)) & ((1 << (hi - lo + 1)) - 1)) << lo
            self.val[off] = v
        self.force = 0
        self.last_t = self._timing()
        self.last_r = self._refresh()

    def _broadcast(self):
        out = []
        t = self._timing()
        if t != self.last_t:                                        # MUT:SILENT
            self.last_t = t
            out.append(Txn("cfg_timing", "update", dict(t)))
        r = self._refresh()
        if r != self.last_r:
            self.last_r = r
            out.append(Txn("cfg_refresh", "update", dict(r)))
        return out

    LEVELS = {"init_done": "init_done", "cal_done": "cal_done", "cal_fail": "cal_fail",
              "bist_done": "bist_done", "bist_fail": "bist_fail",
              "ref_pending": "ref_pending_cnt", "self_refresh": "self_refresh_active",
              "ecc_ce_count": "ecc_ce_count", "bist_fail_addr": "bist_fail_addr"}

    def process(self, txn):
        if txn.iface == "csr_sts_level":
            self.levels.update(txn.fields)
            return []
        if txn.iface != "csr":
            return []
        if txn.kind == "reset":
            self.reset()
            return []
        addr = txn.fields.get("addr", 0)
        if addr not in self.regs:
            if txn.kind == "write":
                return [Txn("csr_rsp", "write_ack", {"addr": addr, "err": 1})]
            return [Txn("csr_rsp", "read_data", {"addr": addr, "data": 0, "err": 1})]
        r = self.regs[addr]
        if txn.kind == "write":
            data = txn.fields.get("data", 0) & ((1 << self.width) - 1)
            v = self.val[addr]
            for f in r["fields"]:
                hi, lo = _bits(f["bits"])
                m = ((1 << (hi - lo + 1)) - 1) << lo
                acc = f.get("access", "RO").upper()
                if acc == "RW":
                    v = (v & ~m) | (data & m)
                elif acc == "RW1C":
                    v &= ~(data & m)
                elif acc == "WO" and f["name"] == "force_refresh":
                    self.force = (data & m) >> lo
            self.val[addr] = v
            out = [Txn("csr_rsp", "write_ack", {"addr": addr, "err": 0})] + self._broadcast()
            if self.force:
                self.force = 0
                out += self._broadcast()
            return out
        v = self.val[addr]
        for f in r["fields"]:
            hi, lo = _bits(f["bits"])
            fm = (1 << (hi - lo + 1)) - 1
            if f.get("access", "RO").upper() == "WO":
                v &= ~(fm << lo)
            for lname, fname in self.LEVELS.items():
                if fname == f["name"]:
                    v = (v & ~(fm << lo)) | ((self.levels.get(lname, 0) & fm) << lo)   # MUT:LEVELW
        return [Txn("csr_rsp", "read_data", {"addr": addr, "data": v, "err": 0})]

    def drain(self):
        return []
'''


def _grade(src):
    import predictor_agent as PA
    with open(os.path.join(ROOT, "Spec", "llmmc_microarchitecturespec_filled.json")) as f:
        spec = json.load(f)
    with open(os.path.join(V, "txn", "generated", "schemas.json")) as f:
        schemas = json.load(f)["interfaces"]
    tmp = tempfile.NamedTemporaryFile("w", suffix=".py", delete=False)
    tmp.write(src)
    tmp.close()
    try:
        return PA.evaluate(tmp.name, spec, schemas, "exact", INS, OUTS)
    finally:
        os.unlink(tmp.name)


class TestBroadcastStep(unittest.TestCase):
    def _mutant(self, old, new):
        self.assertIn(old, REFERENCE)
        return REFERENCE.replace(old, new)

    def test_reference_model_accepted(self):
        fails, gate = _grade(REFERENCE)
        self.assertEqual(fails, [])
        self.assertEqual(gate, "register_map")

    def test_undeclared_output_stream_is_a_contract_failure(self):
        fails, gate = _grade(self._mutant(
            "OUTPUT_IFACES = ('cfg_refresh', 'cfg_timing', 'csr_rsp')",
            "OUTPUT_IFACES = ('csr_rsp',)"))
        self.assertTrue(fails and "OUTPUT_IFACES" in fails[0])
        self.assertIsNone(gate)

    def test_wrong_broadcast_value_rejected(self):
        fails, _ = _grade(self._mutant(
            "return {k: self._field(v) for k, v in self.TIMING.items()}   # MUT:VALUE",
            "return {k: self._field(v) + (1 if k == 'trcd' else 0) for k, v in self.TIMING.items()}"))
        self.assertTrue(any("cfg_timing.update.trcd" in f for f in fails), fails[:2])

    def test_silent_broadcast_rejected(self):
        fails, _ = _grade(self._mutant("if t != self.last_t:                                        # MUT:SILENT",
                                       "if False:"))
        self.assertTrue(any("no cfg_timing.update followed" in f for f in fails), fails[:2])

    def test_swapped_field_mapping_rejected(self):
        fails, _ = _grade(self._mutant('"trcd": "tRCD_nCK", "trp": "tRP_nCK"',
                                       '"trcd": "tRP_nCK", "trp": "tRCD_nCK"'))
        self.assertTrue(fails, "a trcd<->trp swap passed the gate")

    def test_level_field_truncated_to_old_width_rejected(self):
        # the 2026-10-08 case: ref_pending_cnt became 4 bits under the same
        # spec revision; a model still masking it to 3 bits read 8 as 0
        fails, _ = _grade(self._mutant(
            "((self.levels.get(lname, 0) & fm) << lo)   # MUT:LEVELW",
            "((self.levels.get(lname, 0) & (fm >> 1)) << lo)"))
        self.assertTrue(any("ref_pending" in f and "whole width" in f for f in fails), fails[:3])

    def test_level_field_ignored_rejected(self):
        fails, _ = _grade(self._mutant(
            '        if txn.iface == "csr_sts_level":\n            self.levels.update(txn.fields)',
            '        if txn.iface == "csr_sts_level":\n            pass'))
        self.assertTrue(any("hardware level" in f for f in fails), fails[:3])

    def test_baseline_broadcast_after_reset_rejected(self):
        # the 2026-10-08 regeneration: 'last emitted' seeded with None, so the
        # first read after reset broadcast the reset values; the monitor is
        # change-qualified and records nothing, and 5 paths failed on it
        fails, _ = _grade(self._mutant("        self.last_t = self._timing()\n",
                                       "        self.last_t = None\n"))
        self.assertTrue(any("Nothing is emitted for reset itself" in f for f in fails), fails[:3])

    def test_generated_models_pass_the_same_gate(self):
        for p in (os.path.join(V, "predictors", "config_regs_predictor.py"),
                  os.path.join(V, "predictors", "second_opinion", "config_regs_predictor.py")):
            if os.path.exists(p):
                with open(p) as f:
                    fails, gate = _grade(f.read())
                self.assertEqual(fails, [], p)
                self.assertEqual(gate, "register_map")


if __name__ == "__main__":
    unittest.main()


class TestUnpackMaskPolarity(unittest.TestCase):
    """The bus-bridge gate grades the per-beat data mask with the polarity
    the spec declares (2026-10-08: ddr_dm_polarity decided; the second
    data_path model copied the byte enables through and was rejected)."""

    def _mine(self, masks):
        from txn_contract import Txn
        return [Txn("ddr_wr_beat", "beat", {"data": 0, "mask": m}) for m in masks]

    def _grade(self, pol, masks):
        import predictor_gates as G
        spec = {"data_path_mapping": ({"ddr_dm_polarity": pol} if pol else {})}
        u = {"geometry_section": "data_path_mapping", "from_field": "data", "data_field": "data",
             "mask_from_field": "mask", "mask_field": "mask", "polarity_key": "ddr_dm_polarity"}
        return G.BusBridgeGate._grade_unpack_mask(
            spec, u, "ddr_wr_beat", "dp_wr", {"data": 0, "mask": 0xD}, self._mine(masks),
            chan=16, endian="little", n=2)

    def test_active_high_mask_inverts_the_enables(self):
        self.assertEqual(self._grade("active_high_mask", [2, 0]), [])
        self.assertTrue(self._grade("active_high_mask", [1, 3]))

    def test_active_low_mask_copies_the_enables(self):
        self.assertEqual(self._grade("active_low_mask", [1, 3]), [])
        self.assertTrue(self._grade("active_low_mask", [2, 0]))

    def test_silent_spec_grades_nothing(self):
        self.assertEqual(self._grade(None, [1, 3]), [])
        self.assertEqual(self._grade(None, [2, 0]), [])
