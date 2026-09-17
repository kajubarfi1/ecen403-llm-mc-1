#!/usr/bin/env python3
"""
Conformance suite for the deterministic CSR reference model
============================================================
The rule that fixes audit V-05: the model must be graded by tests it did not
write, whose expectations come from the spec independently. Every expected
value below is computed HERE by iterating the spec JSON's fields — none of it
calls the model's own helper methods to learn what "correct" is.

Because the checks iterate the register map, all 11 registers and 46 fields
are covered by construction: a new field added to the spec is tested on the
next run with no test edits.

Run:  python3 Validation/tests/test_spec_register_model.py
"""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "refmodel"))

from spec_register_model import SpecRegisterModel, ConfigRegsModel, _parse_bits, _parse_offset

SPEC_PATH = os.path.join(HERE, "..", "spec", "llmmc_microarchitecturespec_filled.json")
with open(SPEC_PATH) as f:
    SPEC = json.load(f)
CSR = SPEC["csr_register_map"]
MASK = (1 << int(CSR["data_width_bits"])) - 1


# --- spec-side helpers: the INDEPENDENT derivation of expectations ----------

def spec_fields(reg):
    for f in reg.get("fields", []):
        hi, lo = _parse_bits(f["bits"])
        yield f["name"], hi, lo, f.get("access", "RO").upper(), int(f.get("reset_value", 0))


def spec_reset_readback(reg):
    """Architectural reset readback: every non-WO field at its reset value."""
    val = 0
    for _, hi, lo, acc, reset in spec_fields(reg):
        if acc == "WO":
            continue
        val |= (reset & ((1 << (hi - lo + 1)) - 1)) << lo
    return val & MASK


def readback_after_allones_write(reg):
    """Expected readback after reset -> write(0xFFFF_FFFF):
       RW fields become all-ones, RW1C fields clear (were reset anyway),
       RO fields keep reset, WO reads 0."""
    val = 0
    for _, hi, lo, acc, reset in spec_fields(reg):
        w = hi - lo + 1
        fm = (1 << w) - 1
        if acc == "RW":
            bits = fm
        elif acc == "RO":
            bits = reset & fm
        else:                      # RW1C cleared by 1s; WO reads 0
            bits = 0
        val |= bits << lo
    return val & MASK


class TestResetValues(unittest.TestCase):
    def test_every_register_reads_spec_reset_value(self):
        m = SpecRegisterModel(CSR)
        for reg in CSR["registers"]:
            acked, got = m.read(_parse_offset(reg["offset"]))
            self.assertTrue(acked, reg["name"])
            self.assertEqual(got, spec_reset_readback(reg),
                             f"{reg['name']}: reset readback wrong")


class TestAccessSemantics(unittest.TestCase):
    def test_allones_write_per_register(self):
        """One sweep exercises RW acceptance, RO immunity, RW1C clearing and
        WO self-clear on every register in the map."""
        for reg in CSR["registers"]:
            m = SpecRegisterModel(CSR)
            off = _parse_offset(reg["offset"])
            self.assertTrue(m.write(off, 0xFFFFFFFF))
            _, got = m.read(off)
            self.assertEqual(got, readback_after_allones_write(reg),
                             f"{reg['name']}: post-write readback wrong")

    def test_every_RW_field_roundtrips_walking_ones(self):
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _ in spec_fields(reg):
                if acc != "RW":
                    continue
                for bit in range(lo, hi + 1):
                    m = SpecRegisterModel(CSR)
                    m.write(off, 1 << bit)
                    _, got = m.read(off)
                    self.assertEqual((got >> bit) & 1, 1,
                                     f"{reg['name']}.{name} bit {bit} lost")

    def test_every_RO_field_ignores_bus_writes(self):
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, reset in spec_fields(reg):
                if acc != "RO":
                    continue
                m = SpecRegisterModel(CSR)
                m.write(off, 0xFFFFFFFF)
                fm = (1 << (hi - lo + 1)) - 1
                _, got = m.read(off)
                self.assertEqual((got >> lo) & fm, reset & fm,
                                 f"{reg['name']}.{name} changed by bus write")

    def test_every_WO_field_always_reads_zero(self):
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _ in spec_fields(reg):
                if acc != "WO":
                    continue
                m = SpecRegisterModel(CSR)
                m.write(off, ((1 << (hi - lo + 1)) - 1) << lo)
                _, got = m.read(off)
                fm = (1 << (hi - lo + 1)) - 1
                self.assertEqual((got >> lo) & fm, 0,
                                 f"{reg['name']}.{name} did not self-clear")

    def test_WO_self_clear_is_independent_of_read_masking(self):
        """WO has two mechanisms — self-clear on write, and read-as-zero —
        and each masks the other's failure. Mutation testing showed a model
        that skips self-clear still passes a read-based test, because the
        read path zeroes WO anyway. Check the STORED value directly."""
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _ in spec_fields(reg):
                if acc != "WO":
                    continue
                fm = (1 << (hi - lo + 1)) - 1
                m = SpecRegisterModel(CSR)
                m.write(off, fm << lo)
                self.assertEqual(
                    m.get_field(reg["name"], name), 0,
                    f"{reg['name']}.{name}: stored value survived a WO write")

    def test_WO_reads_zero_even_when_field_holds_a_value(self):
        """The mirror of the above: force a non-zero value into a WO field
        through the hardware path, then confirm the BUS read still returns 0.
        This isolates read-masking from self-clear."""
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _ in spec_fields(reg):
                if acc != "WO":
                    continue
                fm = (1 << (hi - lo + 1)) - 1
                m = SpecRegisterModel(CSR)
                m.inject_status(reg["name"], name, fm)
                _, got = m.read(off)
                self.assertEqual(
                    (got >> lo) & fm, 0,
                    f"{reg['name']}.{name}: WO field read back a non-zero value")

    def test_write_data_is_masked_to_bus_width(self):
        """Bits above the bus width must not reach any field. Every test that
        writes a 32-bit value passes whether or not masking happens, so this
        writes something wider on purpose."""
        width = int(CSR["data_width_bits"])
        oversize = (1 << (width + 4)) - 1        # 36 ones for a 32-bit bus
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            m = SpecRegisterModel(CSR)
            m.write(off, oversize)
            _, got = m.read(off)
            self.assertEqual(got >> width, 0,
                             f"{reg['name']}: data above bit {width-1} was stored")
            self.assertEqual(got, got & ((1 << width) - 1))

    def test_every_RW1C_field_clears_on_1_keeps_on_0(self):
        for reg in CSR["registers"]:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _ in spec_fields(reg):
                if acc != "RW1C":
                    continue
                fm = (1 << (hi - lo + 1)) - 1
                # set via hardware, write 0: unchanged
                m = SpecRegisterModel(CSR)
                m.inject_status(reg["name"], name, fm)
                m.write(off, 0)
                self.assertEqual(m.get_field(reg["name"], name), fm,
                                 f"{reg['name']}.{name}: write-0 disturbed it")
                # write 1s: cleared
                m.write(off, fm << lo)
                self.assertEqual(m.get_field(reg["name"], name), 0,
                                 f"{reg['name']}.{name}: write-1 did not clear")


class TestMixedRegisterIndependence(unittest.TestCase):
    def test_error_status_mixed_access(self):
        """ERROR_STATUS carries RO and RW1C fields together — writes must be
        applied per-field, never per-register (the #1 historical bug)."""
        reg = next(r for r in CSR["registers"] if r["name"] == "ERROR_STATUS")
        off = _parse_offset(reg["offset"])
        m = SpecRegisterModel(CSR)
        # hardware sets one RW1C flag and one RO counter
        rw1c = [n for n, *_r in
                ((n, hi, lo) for n, hi, lo, a, _ in spec_fields(reg) if a == "RW1C")]
        ro = [n for n, hi, lo, a, _ in spec_fields(reg) if a == "RO"]
        self.assertTrue(rw1c and ro, "spec no longer mixes RO and RW1C here")
        m.inject_status("ERROR_STATUS", rw1c[0], 1)
        m.inject_status("ERROR_STATUS", ro[0], 3)
        m.write(off, 0xFFFFFFFF)      # clears RW1C, must not touch RO
        self.assertEqual(m.get_field("ERROR_STATUS", rw1c[0]), 0)
        self.assertEqual(m.get_field("ERROR_STATUS", ro[0]), 3)

    def test_cross_register_independence(self):
        regs = CSR["registers"]
        rw_regs = [r for r in regs
                   if any(a == "RW" for _, _, _, a, _ in spec_fields(r))]
        self.assertGreaterEqual(len(rw_regs), 2)
        a, b = rw_regs[0], rw_regs[1]
        m = SpecRegisterModel(CSR)
        before = m.read(_parse_offset(b["offset"]))
        m.write(_parse_offset(a["offset"]), 0xFFFFFFFF)
        self.assertEqual(m.read(_parse_offset(b["offset"])), before,
                         f"write to {a['name']} disturbed {b['name']}")


class TestUnmappedPolicy(unittest.TestCase):
    """VP_CSR_006. The spec is silent; the policy is explicit and must match
    the observed RTL (ack + err + 0xDEADBEEF) until the spec rules."""

    def unmapped_addr(self):
        used = {_parse_offset(r["offset"]) for r in CSR["registers"]}
        addr = 0
        while addr in used:
            addr += 4
        return addr

    def test_unmapped_read(self):
        m = SpecRegisterModel(CSR)
        acked, data = m.read(self.unmapped_addr())
        self.assertTrue(acked)
        self.assertEqual(data, 0xDEADBEEF)
        self.assertTrue(m.last_err)

    def test_unmapped_write_dropped(self):
        m = SpecRegisterModel(CSR)
        self.assertFalse(m.write(self.unmapped_addr(), 0x1234))
        self.assertTrue(m.last_err)
        # and no register was disturbed
        for reg in CSR["registers"]:
            _, got = m.read(_parse_offset(reg["offset"]))
            self.assertEqual(got, spec_reset_readback(reg))


class TestExecutorCompatibility(unittest.TestCase):
    """The vector-generation executor's exact usage patterns."""

    def test_constructor_shapes(self):
        ConfigRegsModel(SPEC)      # full spec dict, as the executor passes
        ConfigRegsModel()          # no-arg fallback

    def test_interface_surface(self):
        m = ConfigRegsModel(SPEC)
        m.reset()
        self.assertTrue(m.write(_parse_offset(CSR["registers"][0]["offset"]), 0))
        acked, _ = m.read(_parse_offset(CSR["registers"][0]["offset"]))
        self.assertTrue(acked)
        m.inject_status("CTRL_STATUS", "init_done", 1)
        self.assertEqual(m.get_field("CTRL_STATUS", "init_done"), 1)


if __name__ == "__main__":
    unittest.main(verbosity=1)
