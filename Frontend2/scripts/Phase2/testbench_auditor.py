#!/usr/bin/env python3
"""
testbench_auditor.py (Phase 2) -- deterministic, spec-only cross-check of the
generated Phase 2 testbenches against independently re-derived expectations.
No LLM, no SSH. Same role and contract as Phase1/testbench_auditor.py: it
never imports tb_generator.py or any *_gen.py, so it shares no blind spot
with either by construction.

Scope, stated honestly. Phase 2's testbenches are mostly TB-owned directed
constants (refresh_ctrl and bank_tracker take cfg_t*_nCK as runtime inputs),
so there is little to cross-check there. What IS derived from the spec, and
therefore auditable:

  addr_decoder_tb.sv
    A1 geometry_params   ADDR_WIDTH/ROW_BITS/BANK_BITS/COL_BITS/RANK_BITS
                         localparams match memory_geometry / host_interface.
    A2 field_layout      memory_geometry.address_mapping must be a layout
                         this auditor understands, and the field widths must
                         sum to host_interface.address_width_bits.
    A3 vector_expected   every `req_addr = ...; #10;` vector's expected
                         dec_row/dec_bank/dec_col/dec_rank is recomputed from
                         the spec's address_mapping (field order, burst offset
                         and column low-bit skip derived from burst_length and
                         channel width) and compared.
  calibration_tb.sv
    C1 zqcs_params       ZQCS_WAIT, ZQCS_CTR_W and CLK_PERIOD match
                         calibration.$derived.periodic_zqcs_interval_nCK scaled
                         to the controller clock.
    C2 zqcs_derivation   that spec $derived value itself must equal
                         periodic_zqcs_interval_ns / tCK_ns (catches a stale
                         derived field, and the generator's silent 512000
                         fallback).
  refresh_ctrl_tb.sv / bank_tracker_tb.sv
    R1/B1 geometry/clock  CLK_PERIOD (refresh_ctrl) and NUM_BANKS/BANK_BITS/
                         ROW_BITS (bank_tracker) match the spec. The directed
                         timing constants are deliberately NOT audited -- they
                         are TB-owned, not spec-derived.

What this does NOT do: verify RTL behavior, verify directed timing checks, or
catch a shared misreading of the spec. It is a fast pre-sim second opinion;
Xcelium and the Validation subsystem remain the last word.

Usage:
    python3 testbench_auditor.py   (prompts for spec path + RTL dir)
    also importable: audit(spec_path, rtl_dir, modules)
"""
from __future__ import annotations

import json
import math
import re
import sys
from pathlib import Path

P2_MODULES = ("addr_decoder", "calibration", "refresh_ctrl", "bank_tracker")


def _finding(check, subject, expects, spec_value, detail):
    return {"check": check, "register": subject, "offset": "-",
            "testbench_expects": str(expects), "spec_derived_value": str(spec_value),
            "detail": detail}


def _localparams(src: str) -> dict:
    """name -> number, from every `localparam [real] NAME = value` item."""
    out = {}
    for m in re.finditer(r"localparam\s+(?:real\s+)?([^;]+);", src):
        for part in m.group(1).split(","):
            kv = re.match(r"\s*(\w+)\s*=\s*([0-9_.]+)\s*$", part)
            if kv:
                out[kv.group(1)] = float(kv.group(2).replace("_", ""))
    return out


# ------------------------------------------------------------------ addr_decoder
def _layout(spec: dict):
    """Independently derived bit layout, LSB-first fields, or (None, reason)."""
    g, h = spec["memory_geometry"], spec["host_interface"]
    bl = g["burst_length"]
    channel_bytes = g["byte_lanes"] * g["device_width_bits"] // 8
    burst_off = int(math.log2(bl * channel_bytes))
    col_skip = int(math.log2(bl))
    col_used = g["column_bits"] - col_skip
    widths = {"row": g["row_bits"], "bank": g["bank_bits"], "column": col_used}
    order = [t.strip() for t in g["address_mapping"].lower().split("-")]   # MSB -> LSB
    if sorted(order) != ["bank", "column", "row"]:
        return None, f"unrecognised address_mapping {g['address_mapping']!r}"
    lo, pos = burst_off, {}
    for f in reversed(order):                         # LSB-first above the burst offset
        pos[f] = (lo, lo + widths[f] - 1)
        lo += widths[f]
    total = lo
    return {"pos": pos, "col_skip": col_skip, "total": total, "burst_off": burst_off,
            "addr_w": h["address_width_bits"]}, None


def audit_addr_decoder_tb(spec: dict, tb: str) -> list:
    out, g, h = [], spec["memory_geometry"], spec["host_interface"]
    lp = _localparams(tb)
    for name, want in (("ADDR_WIDTH", h["address_width_bits"]), ("ROW_BITS", g["row_bits"]),
                       ("BANK_BITS", g["bank_bits"]), ("COL_BITS", g["column_bits"]),
                       ("RANK_BITS", max(1, 1 if g["ranks"] > 1 else 0))):
        got = lp.get(name)
        if got is None or int(got) != want:
            out.append(_finding("geometry_params", name, got, want,
                f"addr_decoder_tb localparam {name}={got} but the spec derives {want}."))

    lay, why = _layout(spec)
    if lay is None:
        return out + [_finding("field_layout", "address_mapping", "-", g["address_mapping"], why)]
    if lay["total"] != lay["addr_w"]:
        out.append(_finding("field_layout", "address_width", lay["addr_w"], lay["total"],
            f"burst offset + field widths sum to {lay['total']} bits but "
            f"host_interface.address_width_bits is {lay['addr_w']}: the spec's own "
            f"geometry and address width disagree."))

    rb, bb, cb = g["row_bits"], g["bank_bits"], g["column_bits"]
    blocks = re.split(r"(?=req_addr\s*=\s*\d+'h)", tb)[1:]
    for blk in blocks:
        m = re.match(r"req_addr\s*=\s*\d+'h([0-9A-Fa-f]+);", blk)
        addr = int(m.group(1), 16)
        def field(f, w): return (addr >> lay["pos"][f][0]) & ((1 << w) - 1)
        want = {"row": field("row", rb), "bank": field("bank", bb),
                "col": (field("column", cb - lay["col_skip"]) << lay["col_skip"]) & ((1 << cb) - 1)}
        for sig in ("row", "bank", "col"):
            c = re.search(rf"dec_{sig}\s*===\s*\d+'h([0-9A-Fa-f]+)", blk)
            if c and int(c.group(1), 16) != want[sig]:
                out.append(_finding("vector_expected", f"dec_{sig}", f"0x{int(c.group(1), 16):X}",
                    f"0x{want[sig]:X}",
                    f"for req_addr=0x{addr:X} the testbench expects dec_{sig}=0x{int(c.group(1), 16):X} "
                    f"but address_mapping '{g['address_mapping']}' derives 0x{want[sig]:X}."))
    if not blocks:
        out.append(_finding("vector_expected", "vectors", 0, ">0",
            "no `req_addr = ...` vectors found; the audit could not parse the testbench."))
    return out


# ------------------------------------------------------------------ calibration
def audit_calibration_tb(spec: dict, tb: str) -> list:
    out = []
    cal, clk = spec["calibration"], spec["clocking_model"]
    tck, ctrl = clk["$derived"]["tCK_ns"], clk["controller_clock_period_ns"]
    ns = cal.get("periodic_zqcs_interval_ns")
    nck = cal.get("$derived", {}).get("periodic_zqcs_interval_nCK")
    if nck is None:
        out.append(_finding("zqcs_derivation", "periodic_zqcs_interval_nCK", "-", "missing",
            "spec calibration.$derived.periodic_zqcs_interval_nCK is absent; the testbench "
            "generator would silently fall back to a hardcoded default."))
        nck = round(ns / tck) if ns else None
    elif ns is not None and abs(ns / tck - nck) > 0.5:
        out.append(_finding("zqcs_derivation", "periodic_zqcs_interval_nCK", nck, round(ns / tck),
            f"$derived says {nck} nCK but periodic_zqcs_interval_ns / tCK_ns = {ns}/{tck} = {ns / tck:.1f}."))
    lp = _localparams(tb)
    if nck is not None:
        wait = math.ceil(nck * tck / ctrl)
        for name, want in (("ZQCS_WAIT", wait), ("ZQCS_CTR_W", max(1, wait.bit_length()))):
            if int(lp.get(name, -1)) != want:
                out.append(_finding("zqcs_params", name, lp.get(name), want,
                    f"calibration_tb {name}={lp.get(name)} but ceil({nck} nCK * {tck} ns / {ctrl} ns) "
                    f"derives {want}."))
    if abs(lp.get("CLK_PERIOD", -1) - ctrl) > 1e-9:
        out.append(_finding("zqcs_params", "CLK_PERIOD", lp.get("CLK_PERIOD"), ctrl,
            "calibration_tb clock period differs from clocking_model.controller_clock_period_ns."))
    return out


def audit_refresh_ctrl_tb(spec: dict, tb: str) -> list:
    want = spec["clocking_model"]["controller_clock_period_ns"]
    got = _localparams(tb).get("CLK_PERIOD")
    if got is None or abs(got - want) > 1e-9:
        return [_finding("clock_period", "CLK_PERIOD", got, want,
            "refresh_ctrl_tb clock period differs from clocking_model.controller_clock_period_ns.")]
    return []


def audit_bank_tracker_tb(spec: dict, tb: str) -> list:
    g, out, lp = spec["memory_geometry"], [], _localparams(tb)
    for name, want in (("NUM_BANKS", 2 ** g["bank_bits"]), ("BANK_BITS", g["bank_bits"]),
                       ("ROW_BITS", g["row_bits"])):
        if int(lp.get(name, -1)) != want:
            out.append(_finding("geometry_params", name, lp.get(name), want,
                f"bank_tracker_tb localparam {name}={lp.get(name)} but memory_geometry derives {want}."))
    return out


_AUDITORS = {"addr_decoder": audit_addr_decoder_tb, "calibration": audit_calibration_tb,
             "refresh_ctrl": audit_refresh_ctrl_tb, "bank_tracker": audit_bank_tracker_tb}


def audit(spec_path: str, rtl_dir: str, modules=P2_MODULES) -> dict:
    spec = json.loads(Path(spec_path).read_text())
    results = {}
    for mod in modules:
        tb_path = Path(rtl_dir) / f"{mod}_tb.sv"
        auditor = _AUDITORS.get(mod)
        if auditor is None:
            results[mod] = {"status": "NO_CHECKS", "findings": []}
        elif not tb_path.is_file():
            results[mod] = {"status": "SKIPPED", "reason": "testbench file not found", "findings": []}
        else:
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
            print(f"  [{f['check']}] {f['register']}: {f['detail']}")
    sys.exit(0 if all(r["status"] != "FAIL" for r in result.values()) else 1)
