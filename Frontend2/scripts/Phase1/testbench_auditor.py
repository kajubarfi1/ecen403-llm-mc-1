#!/usr/bin/env python3
"""
testbench_auditor.py -- deterministic, spec-only cross-check of a
generated testbench against independently-recomputed expected values.
No LLM, no SSH -- runs locally in seconds, before Olympus is ever touched.

Why this exists: tb_generator.py and the per-module RTL generators
(config_regs_gen.py etc.) are two SEPARATE deterministic translations of
the same spec, and neither one reads the other's output -- nothing in
phase1_pipeline.py's graph ever compares their two interpretations of
"what should this register do" against each other. That's how a stale
hardcoded reset value (see the H1 finding below) and a write/readback test
that ignores a register's reserved-bit mask (see B8/B9) can both sit in a
generated testbench indefinitely: they only get caught if and when a real
Xcelium job happens to fail, hours after the bug was written.

This module never imports or reads config_regs_gen.py or tb_generator.py.
It independently reimplements the one piece of derivation logic that
matters here -- a register's reserved-bit mask, computed from its spec-
declared `fields` the same way config_regs_gen.py does -- specifically so
it doesn't share a blind spot with either generator by construction. If
that shared derivation itself is wrong, this won't catch it (see "what
this does NOT do" below); what it catches is the testbench and the spec
silently disagreeing, which is exactly the bug class this was built for.

Checks implemented (config_regs only -- the only Phase 1 module with a
CSR register map to audit against):

  1. reset_value: every `csr_read(...); check($sformatf("...reset...",
     rdata), rdata == 32'h...)` in the generated testbench, regardless of
     which test ID it's attached to, must match that register's
     spec-declared reset_value. (This is exactly what caught H1: TIMING_0
     was checked against a stale 0x271C0B0B despite the spec deriving
     0x21180909, the same value the A-series check for the same register,
     two lines above it, correctly computes.)

  2. write_readback_mask: every `csr_write(...); csr_read(...); check(...
     write/readback", rdata == 32'h{same value that was written})` is
     flagged if the written test value has any bit set inside that
     register's reserved-bit range. An EXACT round-trip check can never
     pass against correct RTL that pins reserved bits -- if the RTL fails
     it, that's the RTL working as designed; the test is unsound
     regardless of what the RTL actually does. (This is what caught B8/B9:
     BIST_ADDR_START/END are only writable in bits [27:0], and the test
     values picked for them, 0x1ABC0000 and 0x1FFFFFFF, both set bits in
     the reserved [31:28] range.)

What this does NOT do: verify every check in the testbench (only the two
classes above), verify the RTL is correct (only that the RTL and the
testbench derive the SAME expectation from the spec), or replace real
simulation. It's a fast, local, pre-sim second opinion -- not the last
word. The last word is still Xcelium, and eventually Jacob's independent
Validation subsystem.

Usage:
    python3 testbench_auditor.py
    (prompts for spec path + RTL dir; also importable as audit(spec_path, rtl_dir))
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

_RESET_CHECK_RE = re.compile(
    r"csr_read\(8'h([0-9A-Fa-f]{2}),\s*rdata\);\s*"
    r"check\(\$sformatf\(\"[^\"]*[Rr]eset[^\"]*\",\s*rdata\),\s*"
    r"rdata\s*==\s*32'h([0-9A-Fa-f]{8})\s*\)"
)

_WRITE_READBACK_RE = re.compile(
    r"csr_write\(8'h([0-9A-Fa-f]{2}),\s*32'h([0-9A-Fa-f]{8})\);\s*"
    r"csr_read\(8'h[0-9A-Fa-f]{2},\s*rdata\);\s*"
    r"check\(\"[^\"]*write/readback\",\s*rdata\s*==\s*32'h([0-9A-Fa-f]{8})\)"
)


def _parse_bits(bits_str: str) -> set:
    """Independently reimplemented from config_regs_gen.py's _parse_bits --
    deliberately not imported (see module docstring)."""
    if ":" in bits_str:
        hi, lo = bits_str.split(":")
        return set(range(int(lo), int(hi) + 1))
    return {int(bits_str)}


def _register_table(spec: dict) -> dict:
    """{offset_int: {"name", "reset_value", "reserved_mask"}}, reserved_mask
    computed from each register's spec-declared fields (same interpretation
    of the schema config_regs_gen.py uses: a field literally named
    "reserved", plus any bit no field covers at all, is non-writable)."""
    table = {}
    for r in spec["csr_register_map"]["registers"]:
        off = int(r["offset"], 16) if isinstance(r["offset"], str) else r["offset"]
        rst = int(r["reset_value"], 16) if isinstance(r["reset_value"], str) else r["reset_value"]
        covered, reserved = set(), set()
        for f in r["fields"]:
            fbits = _parse_bits(f["bits"])
            covered |= fbits
            if f["name"].strip().lower() == "reserved":
                reserved |= fbits
        reserved |= {b for b in range(32) if b not in covered}
        reserved_mask = 0
        for b in reserved:
            reserved_mask |= (1 << b)
        table[off] = {"name": r["name"], "reset_value": rst, "reserved_mask": reserved_mask}
    return table


def audit_config_regs_tb(spec: dict, tb_source: str) -> list:
    """Returns a list of finding dicts; empty means neither check class
    found a disagreement (not a claim that the testbench is fully correct
    -- see module docstring)."""
    findings = []
    table = _register_table(spec)

    for m in _RESET_CHECK_RE.finditer(tb_source):
        off, checked_hex = int(m.group(1), 16), int(m.group(2), 16)
        reg = table.get(off)
        if reg is None or checked_hex == reg["reset_value"]:
            continue
        findings.append({
            "check": "reset_value", "register": reg["name"], "offset": f"0x{off:02X}",
            "testbench_expects": f"0x{checked_hex:08X}",
            "spec_derived_value": f"0x{reg['reset_value']:08X}",
            "detail": (f"testbench checks {reg['name']} (offset 0x{off:02X}) resets to "
                       f"0x{checked_hex:08X}, but the spec's csr_register_map declares "
                       f"reset_value 0x{reg['reset_value']:08X}. Likely a stale hardcoded "
                       f"expected value in the testbench, not an RTL bug -- confirm what the "
                       f"RTL actually resets to before assuming otherwise."),
        })

    for m in _WRITE_READBACK_RE.finditer(tb_source):
        off, written, expected_readback = (int(m.group(1), 16), int(m.group(2), 16),
                                            int(m.group(3), 16))
        reg = table.get(off)
        if reg is None:
            continue
        hit_reserved = written & reg["reserved_mask"]
        if hit_reserved and expected_readback == written:
            findings.append({
                "check": "write_readback_mask", "register": reg["name"], "offset": f"0x{off:02X}",
                "written_value": f"0x{written:08X}", "reserved_mask": f"0x{reg['reserved_mask']:08X}",
                "detail": (f"testbench writes 0x{written:08X} to {reg['name']} (offset "
                           f"0x{off:02X}) and expects an EXACT readback match, but bits "
                           f"0x{hit_reserved:08X} of that value fall in this register's "
                           f"reserved range (mask 0x{reg['reserved_mask']:08X}, derived from "
                           f"its spec-declared fields). Correct RTL that pins reserved bits "
                           f"can never pass this exact-match check -- the test is unsound "
                           f"regardless of what the RTL does."),
            })

    return findings


# module -> audit function. Only config_regs has a register map to check
# against today; init_fsm/wb_port have no equivalent checks defined yet.
_AUDITORS = {"config_regs": audit_config_regs_tb}


def audit(spec_path: str, rtl_dir: str, modules=("init_fsm", "config_regs", "wb_port")) -> dict:
    spec = json.loads(Path(spec_path).read_text())
    results = {}
    for mod in modules:
        tb_path = Path(rtl_dir) / f"{mod}_tb.sv"
        auditor = _AUDITORS.get(mod)
        if auditor is None:
            results[mod] = {"status": "NO_CHECKS", "findings": []}
            continue
        if not tb_path.is_file():
            results[mod] = {"status": "SKIPPED", "reason": "testbench file not found", "findings": []}
            continue
        findings = auditor(spec, tb_path.read_text())
        results[mod] = {"status": "FAIL" if findings else "PASS", "findings": findings}
    return results


if __name__ == "__main__":
    spec_path = input("Spec JSON path: ").strip()
    rtl_dir = input("RTL dir (containing _tb.sv files): ").strip()
    result = audit(spec_path, rtl_dir)
    for mod, r in result.items():
        print(f"\n{mod}: {r['status']}")
        for f in r["findings"]:
            print(f"  [{f['check']}] {f['register']} ({f['offset']}): {f['detail']}")
    sys.exit(0 if all(r["status"] != "FAIL" for r in result.values()) else 1)
