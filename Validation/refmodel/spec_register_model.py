#!/usr/bin/env python3
"""
spec_register_model.py — deterministic CSR reference model, derived from spec
=============================================================================
Replaces the LLM-generated config_regs reference model with a generic register
engine driven entirely by csr_register_map in the microarchitecture spec.

Why this exists (audit V-05/V-06): the previous model was produced by an LLM
that also wrote its own acceptance tests, from a prompt that dictated both the
implementation and the expected answers. For a register block that is all
waste: RW / RO / RW1C / WO are standardized semantics implemented once, and
the register map is machine-readable data. This is the software analogue of a
UVM register model generated from SystemRDL/IP-XACT — the industry-standard
way to get a CSR oracle, with zero generation step to go wrong.

Design rules:
  * The ONLY inputs are the spec JSON and this file. No RTL facts. Where the
    spec is silent (unmapped-address behaviour, vplan item VP_CSR_006), the
    policy is an explicit, documented parameter — not a buried assumption.
  * Acceptance is external: Validation/tests/test_spec_register_model.py
    derives its expectations from the spec JSON independently, by iterating
    fields — this module never grades itself (run_self_test simply reuses
    that suite).
  * Interface-compatible with the old generated model (reset / write / read /
    inject_status / get_field, class name ConfigRegsModel) so the existing
    vector-generation executor works unchanged.

Field semantics implemented:
  RW    bus write stores the field's slice of the data
  RO    bus writes ignored entirely; only inject_status() (hardware) changes it
  RW1C  writing 1 to a bit clears it; writing 0 leaves it unchanged
  WO    write side-effect accepted, then self-clears; always reads back 0
"""

import json
import os
from typing import Dict, Optional, Tuple

_DEFAULT_SPEC = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "..", "spec", "llmmc_microarchitecturespec_filled.json")


def _parse_bits(bits) -> Tuple[int, int]:
    """'15:0' -> (15, 0); '5' -> (5, 5); 7 -> (7, 7)."""
    s = str(bits)
    if ":" in s:
        hi, lo = s.split(":")
        return int(hi), int(lo)
    return int(s), int(s)


def _parse_offset(off) -> int:
    if isinstance(off, int):
        return off
    return int(str(off), 0)      # handles '0x04' and '4'


class SpecRegisterModel:
    """Generic register-map model. Construct from a csr_register_map dict."""

    def __init__(self, csr_map: dict, unmapped_read_data: int = 0xDEADBEEF,
                 unmapped_acks: bool = True):
        """unmapped_* is the VP_CSR_006 policy knob. The spec does not define
        unmapped-address behaviour; the current RTL acks with csr_err_o
        asserted and returns 0xDEADBEEF (observed 27 Aug via
        config_regs_probe_tb). These defaults match that observation and must
        be revisited when the spec gains a ruling."""
        self.data_width = int(csr_map.get("data_width_bits", 32))
        self._data_mask = (1 << self.data_width) - 1
        self.unmapped_read_data = unmapped_read_data & self._data_mask
        self.unmapped_acks = unmapped_acks

        self._regs: Dict[int, dict] = {}
        self._by_name: Dict[str, dict] = {}
        for reg in csr_map["registers"]:
            fields = []
            for f in reg.get("fields", []):
                hi, lo = _parse_bits(f["bits"])
                fields.append({
                    "name": f["name"], "hi": hi, "lo": lo,
                    "access": f.get("access", "RO").upper(),
                    "reset": int(f.get("reset_value", 0)),
                    "value": 0,
                })
            entry = {"name": reg["name"], "offset": _parse_offset(reg["offset"]),
                     "fields": fields}
            self._regs[entry["offset"]] = entry
            self._by_name[entry["name"]] = entry
        self.reset()

    # ------------------------------------------------------------------ core

    def reset(self):
        for reg in self._regs.values():
            for f in reg["fields"]:
                width = f["hi"] - f["lo"] + 1
                f["value"] = f["reset"] & ((1 << width) - 1)
        # error pulse mirrors csr_err_o's per-access behaviour
        self.last_err = False

    def write(self, addr: int, data: int) -> bool:
        """Bus write. Returns True if the address is mapped."""
        data &= self._data_mask
        reg = self._regs.get(addr)
        if reg is None:
            self.last_err = True
            return False
        self.last_err = False
        for f in reg["fields"]:
            width = f["hi"] - f["lo"] + 1
            fmask = (1 << width) - 1
            wbits = (data >> f["lo"]) & fmask
            acc = f["access"]
            if acc == "RW":
                f["value"] = wbits
            elif acc == "RW1C":
                f["value"] &= (~wbits) & fmask
            elif acc == "WO":
                f["value"] = 0          # side-effect accepted, self-clears
            # RO: never modified by bus writes
        return True

    def read(self, addr: int) -> Tuple[bool, int]:
        """Bus read. Returns (acked, data).

        For an unmapped address, `acked` follows the unmapped_acks policy and
        the data is unmapped_read_data; self.last_err records that the access
        was flagged as an error, matching the RTL's csr_err_o."""
        reg = self._regs.get(addr)
        if reg is None:
            self.last_err = True
            return (self.unmapped_acks, self.unmapped_read_data)
        self.last_err = False
        val = 0
        for f in reg["fields"]:
            if f["access"] == "WO":
                continue                # WO always reads 0
            width = f["hi"] - f["lo"] + 1
            val |= (f["value"] & ((1 << width) - 1)) << f["lo"]
        return (True, val & self._data_mask)

    # ---------------------------------------------------- hardware-side hooks

    def inject_status(self, reg_name: str, field_name: str, value: int):
        """Hardware-driven update: the only way RO fields change."""
        reg = self._by_name.get(reg_name)
        if reg is None:
            raise KeyError(f"no register named {reg_name!r}")
        for f in reg["fields"]:
            if f["name"] == field_name:
                width = f["hi"] - f["lo"] + 1
                f["value"] = int(value) & ((1 << width) - 1)
                return
        raise KeyError(f"no field {field_name!r} in {reg_name}")

    def get_field(self, reg_name: str, field_name: str) -> Optional[int]:
        reg = self._by_name.get(reg_name)
        if reg is None:
            return None
        for f in reg["fields"]:
            if f["name"] == field_name:
                return f["value"]
        return None

    # ------------------------------------------------------------- utilities

    def registers(self):
        """(offset, name) pairs, sorted — for tests and reports."""
        return sorted((r["offset"], r["name"]) for r in self._regs.values())

    def assemble_reset_value(self, reg_name: str) -> int:
        """The register's architectural reset value, from spec fields alone.
        WO fields are excluded because they always read back 0."""
        reg = self._by_name[reg_name]
        val = 0
        for f in reg["fields"]:
            if f["access"] == "WO":
                continue
            width = f["hi"] - f["lo"] + 1
            val |= (f["reset"] & ((1 << width) - 1)) << f["lo"]
        return val & self._data_mask


class ConfigRegsModel(SpecRegisterModel):
    """Drop-in replacement for the LLM-generated model.

    The vector-generation executor constructs this as ConfigRegsModel(spec)
    (full spec dict) with a no-argument fallback; both are supported."""

    def __init__(self, spec: Optional[dict] = None):
        if spec is None:
            with open(os.path.abspath(_DEFAULT_SPEC)) as f:
                spec = json.load(f)
        csr = spec["csr_register_map"] if "csr_register_map" in spec else spec
        super().__init__(csr)


def run_self_test():
    """Delegates to the EXTERNAL conformance suite (never self-graded).
    Prints 'ALL TESTS PASSED' on success for compatibility with the old
    validate() contract."""
    import subprocess
    import sys
    test = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "..", "tests", "test_spec_register_model.py")
    r = subprocess.run([sys.executable, os.path.abspath(test)],
                       capture_output=True, text=True)
    sys.stdout.write(r.stdout + r.stderr)
    if r.returncode == 0:
        print("ALL TESTS PASSED")
    return r.returncode == 0


if __name__ == "__main__":
    import sys
    sys.exit(0 if run_self_test() else 1)
