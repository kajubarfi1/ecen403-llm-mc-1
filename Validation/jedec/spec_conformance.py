#!/usr/bin/env python3
"""
spec_conformance.py — check a generated spec against JEDEC JESD79-3
====================================================================
A new validation target. Until now the spec was treated as ground truth; once
the Frontend generates it from user input, the spec itself can be wrong — and
RTL that perfectly implements a non-compliant spec passes every downstream
check while describing a memory controller that cannot work with real DDR3.
This runs BEFORE RTL validation, because a finding here invalidates
everything after it.

Why this file is deterministic even though the spec is swappable: the SPEC
changes, JEDEC does not. JESD79-3 is the fixed reference. Hardcoding these
constants is correct precisely because they come from a published standard
rather than from this design.

Note on the spec's own $consistency_checks: the spec already carries eleven
rule strings ending in checkmarks, e.g.
    "tRC_rule": "tRC == tRAS + tRP -> 48.75 == 35.0 + 13.75 [check]"
Nothing verifies those. They are claims written by whoever wrote the values —
and when an LLM generates the spec, it writes both the numbers and the
checkmarks asserting they are right. This module recomputes them instead of
trusting them, and reports any string whose claim disagrees with arithmetic.

Findings are emitted in the team's agreed finding schema so they route up the
chain like any other defect (kind=spec_violation, target=frontend).

Usage:
    python3 Validation/jedec/spec_conformance.py                    # default spec
    python3 Validation/jedec/spec_conformance.py --spec other.json
    python3 Validation/jedec/spec_conformance.py --json findings.json
"""

import argparse
import json
import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
RULES_PATH = os.path.join(HERE, "jedec_ddr3_rules.json")
DEFAULT_SPEC = os.path.join(ROOT, "Validation", "spec",
                            "llmmc_microarchitecturespec_filled.json")

TOL = 1e-6          # float comparison tolerance, nanoseconds

# --- JEDEC constant tables (JESD79-3F) --------------------------------------

# CAS write latency banding by clock period. (lo_inclusive, hi_exclusive, CWL)
CWL_BANDS = [(2.5, 3.3, 5), (1.875, 2.5, 6), (1.5, 1.875, 7),
             (1.25, 1.5, 8), (1.07, 1.25, 9), (0.935, 1.07, 10)]

TRFC_BY_DENSITY_NS = {"512Mb": 90.0, "1Gb": 110.0, "2Gb": 160.0,
                      "4Gb": 300.0, "8Gb": 350.0}

TREFI_NS = {"normal": 7800.0, "extended": 3900.0}

LEGAL_PAGE_BYTES = {1024, 2048}
LEGAL_BURST_LENGTHS = {4, 8}


class Finding:
    def __init__(self, rule, status, detail, observed=None, expected=None):
        self.rule = rule
        self.status = status              # pass | fail | skip
        self.detail = detail
        self.observed = observed
        self.expected = expected

    def to_finding_schema(self, spec_rev):
        """The team's agreed cross-subsystem finding format."""
        return {
            "source": "validation", "target": "frontend",
            "kind": "spec_violation",
            "rule_id": self.rule["id"],
            "severity": self.rule["severity"],
            "standard": "JESD79-3F",
            "section": self.rule["section"],
            "spec_revision": spec_rev,
            "title": self.rule["title"],
            "requires": self.rule["requires"],
            "observed": self.observed,
            "expected": self.expected,
            "detail": self.detail,
            "confidence": self.rule.get("confidence", "high"),
            "status": "open",
        }


def _get(d, path, default=None):
    cur = d
    for k in path.split("."):
        if not isinstance(cur, dict) or k not in cur:
            return default
        cur = cur[k]
    return cur


def check(spec: dict, rules: list) -> list:
    """Run every rule. Returns Findings in rule order."""
    by_id = {r["id"]: r for r in rules}
    out = []

    def emit(rid, ok, detail, observed=None, expected=None):
        out.append(Finding(by_id[rid], "pass" if ok else "fail",
                           detail, observed, expected))

    def skip(rid, why):
        out.append(Finding(by_id[rid], "skip", why))

    tm = spec.get("timing_model", {})
    cm = spec.get("clocking_model", {})
    mg = spec.get("memory_geometry", {})
    init = spec.get("initialization_sequence", {})
    tck = tm.get("tCK_ns")

    # ---------------- timing relations ----------------
    tRC, tRAS, tRP = tm.get("tRC"), tm.get("tRAS"), tm.get("tRP")
    if None in (tRC, tRAS, tRP):
        skip("J-TIM-001", "timing_model missing tRC/tRAS/tRP")
    else:
        emit("J-TIM-001", abs(tRC - (tRAS + tRP)) < TOL,
             f"tRC={tRC}, tRAS+tRP={tRAS + tRP}", tRC, tRAS + tRP)

    tFAW, tRRD = tm.get("tFAW"), tm.get("tRRD")
    if None in (tFAW, tRRD):
        skip("J-TIM-002", "timing_model missing tFAW/tRRD")
    else:
        emit("J-TIM-002", tFAW >= 4 * tRRD - TOL,
             f"tFAW={tFAW}, 4*tRRD={4 * tRRD}", tFAW, 4 * tRRD)

    page = _get(mg, "$derived.page_size_bytes_per_device")
    if None in (tRRD, tck):
        skip("J-TIM-003", "missing tRRD or tCK")
    else:
        floor = max(4 * tck, 7.5 if (page or 1024) >= 1024 else 6.0)
        emit("J-TIM-003", tRRD >= floor - TOL,
             f"tRRD={tRRD}, floor=max(4*tCK={4*tck}, "
             f"{'7.5' if (page or 1024) >= 1024 else '6.0'})={floor}", tRRD, floor)

    for rid, name in (("J-TIM-004", "tWTR"), ("J-TIM-005", "tRTP")):
        v = tm.get(name)
        if v is None or tck is None:
            skip(rid, f"missing {name} or tCK")
        else:
            floor = max(4 * tck, 7.5)
            emit(rid, v >= floor - TOL,
                 f"{name}={v}, floor=max(4*tCK={4*tck}, 7.5)={floor}", v, floor)

    tCCD = tm.get("tCCD")
    if tCCD is None or tck is None:
        skip("J-TIM-006", "missing tCCD or tCK")
    else:
        emit("J-TIM-006", abs(tCCD - 4 * tck) < TOL,
             f"tCCD={tCCD}, 4*tCK={4 * tck}", tCCD, 4 * tck)

    tWR = tm.get("tWR")
    if tWR is None:
        skip("J-TIM-007", "missing tWR")
    else:
        emit("J-TIM-007", abs(tWR - 15.0) < TOL, f"tWR={tWR}", tWR, 15.0)

    cwl = tm.get("CWL_cycles")
    if cwl is None or tck is None:
        skip("J-TIM-008", "missing CWL_cycles or tCK")
    else:
        legal = [c for lo, hi, c in CWL_BANDS if lo - TOL <= tck < hi]
        emit("J-TIM-008", cwl in legal,
             f"CWL={cwl} at tCK={tck}; standard allows {legal or 'no band (tCK out of DDR3 range)'}",
             cwl, legal[0] if legal else None)

    density = _get(mg, "$derived.device_density_label")
    tRFC = tm.get("tRFC")
    if density is None or tRFC is None:
        skip("J-TIM-009", "missing density label or tRFC")
    elif density not in TRFC_BY_DENSITY_NS:
        skip("J-TIM-009", f"no tRFC table entry for density {density!r}")
    else:
        exp = TRFC_BY_DENSITY_NS[density]
        emit("J-TIM-009", abs(tRFC - exp) < TOL,
             f"tRFC={tRFC} for {density}; standard={exp}", tRFC, exp)

    tREFI = tm.get("tREFI")
    if tREFI is None:
        skip("J-TIM-010", "missing tREFI")
    else:
        emit("J-TIM-010", any(abs(tREFI - v) < TOL for v in TREFI_NS.values()),
             f"tREFI={tREFI}; standard 7800 (normal) or 3900 (extended)",
             tREFI, 7800.0)

    cl, tRCD = tm.get("CL_cycles"), tm.get("tRCD")
    if None in (cl, tRCD, tRP, tck):
        skip("J-TIM-011", "missing CL/tRCD/tRP/tCK")
    else:
        # A published bin has CL*tCK == tRCD == tRP (the "n-n-n" triple).
        cl_ns = cl * tck
        ok = abs(cl_ns - tRCD) < TOL and abs(tRCD - tRP) < TOL
        emit("J-TIM-011", ok,
             f"CL={cl} ({cl_ns}ns), tRCD={tRCD}, tRP={tRP} — a published bin "
             f"has all three equal", [cl_ns, tRCD, tRP], "all equal")

    # ---------------- initialization ----------------
    rh = init.get("reset_hold_us")
    emit("J-INI-001", rh is not None and rh >= 200,
         f"reset_hold_us={rh}", rh, 200) if rh is not None else \
        skip("J-INI-001", "missing reset_hold_us")

    cd = init.get("cke_delay_us")
    emit("J-INI-002", cd is not None and cd >= 500,
         f"cke_delay_us={cd}", cd, 500) if cd is not None else \
        skip("J-INI-002", "missing cke_delay_us")

    txpr = init.get("tXPR_ns")
    if txpr is None or tck is None or tRFC is None:
        skip("J-INI-003", "missing tXPR_ns, tCK or tRFC")
    else:
        floor = max(5 * tck, tRFC + 10.0)
        emit("J-INI-003", txpr >= floor - TOL,
             f"tXPR={txpr}, floor=max(5*tCK={5*tck}, tRFC+10={tRFC + 10})={floor}",
             txpr, floor)

    tzq = init.get("tZQinit_ns")
    if tzq is None or tck is None:
        skip("J-INI-004", "missing tZQinit_ns or tCK")
    else:
        floor = 512 * tck
        emit("J-INI-004", tzq >= floor - TOL,
             f"tZQinit={tzq}, floor=512*tCK={floor}", tzq, floor)

    order_txt = _get(init, "$derived.init_sequence_order") or ""
    mrs = re.findall(r"MR([0-3])", order_txt)
    if not mrs:
        mr = init.get("mode_registers", {})
        skip("J-INI-005", "no init_sequence_order string to read MRS order from"
             if not mr else "MRS order not stated in $derived.init_sequence_order")
    else:
        emit("J-INI-005", mrs[:4] == ["2", "3", "1", "0"],
             f"MRS order found: {'->'.join('MR'+m for m in mrs[:4])}",
             mrs[:4], ["2", "3", "1", "0"])

    dll = _get(init, "mode_registers.MR0.dll_reset")
    if dll is None:
        skip("J-INI-006", "MR0.dll_reset not present")
    else:
        emit("J-INI-006", bool(dll) is True, f"MR0.dll_reset={dll}", dll, True)

    # ---------------- geometry ----------------
    bb = mg.get("bank_bits")
    emit("J-GEO-001", bb == 3, f"bank_bits={bb}", bb, 3) if bb is not None else \
        skip("J-GEO-001", "missing bank_bits")

    bl = mg.get("burst_length")
    emit("J-GEO-002", bl in LEGAL_BURST_LENGTHS, f"burst_length={bl}",
         bl, sorted(LEGAL_BURST_LENGTHS)) if bl is not None else \
        skip("J-GEO-002", "missing burst_length")

    rb, cb, dw = mg.get("row_bits"), mg.get("column_bits"), mg.get("device_width_bits")
    dens_bits = _get(mg, "$derived.device_density_bits")
    if None in (rb, cb, bb, dw):
        skip("J-GEO-003", "missing row/column/bank bits or device width")
    else:
        computed = (1 << (rb + cb + bb)) * dw
        if dens_bits is None:
            skip("J-GEO-003", "no $derived.device_density_bits to compare")
        else:
            emit("J-GEO-003", computed == dens_bits,
                 f"2^({rb}+{cb}+{bb})*{dw} = {computed} bits; spec says {dens_bits}",
                 dens_bits, computed)

    if None in (cb, dw):
        skip("J-GEO-004", "missing column_bits or device_width_bits")
    else:
        pg = (1 << cb) * dw // 8
        emit("J-GEO-004", pg in LEGAL_PAGE_BYTES,
             f"page = 2^{cb} * {dw}/8 = {pg} bytes", pg, sorted(LEGAL_PAGE_BYTES))

    # ---------------- cross-section consistency ----------------
    ddr_ck = cm.get("ddr_clock_period_ns")
    if None in (tck, ddr_ck):
        skip("J-CON-001", "missing tCK_ns or ddr_clock_period_ns")
    else:
        emit("J-CON-001", abs(tck - ddr_ck) < TOL,
             f"timing_model.tCK_ns={tck}, clocking_model.ddr_clock_period_ns={ddr_ck}",
             tck, ddr_ck)

    derived = tm.get("$derived_cycles") or {}
    if not derived or tck is None:
        skip("J-CON-002", "no $derived_cycles section or no tCK")
    else:
        bad = []
        for key, cycles in derived.items():
            if not key.endswith("_nCK"):
                continue
            ns = tm.get(key[:-4])
            if ns is None:
                continue
            want = math.ceil(ns / tck - TOL)
            if cycles != want:
                bad.append(f"{key}={cycles} but ceil({ns}/{tck})={want}")
        emit("J-CON-002", not bad,
             "; ".join(bad) if bad else
             f"all {sum(1 for k in derived if k.endswith('_nCK'))} derived counts agree",
             bad or None, None)

    mr0_cl = _get(init, "mode_registers.MR0.cas_latency_cycles")
    if mr0_cl is None or cl is None:
        skip("J-CON-003", "missing MR0.cas_latency_cycles or CL_cycles")
    else:
        emit("J-CON-003", mr0_cl == cl,
             f"MR0.cas_latency_cycles={mr0_cl}, timing_model.CL_cycles={cl}",
             mr0_cl, cl)

    mr2_cwl = _get(init, "mode_registers.MR2.cas_write_latency_cycles")
    if mr2_cwl is None or cwl is None:
        skip("J-CON-004", "missing MR2.cas_write_latency_cycles or CWL_cycles")
    else:
        emit("J-CON-004", mr2_cwl == cwl,
             f"MR2.cas_write_latency_cycles={mr2_cwl}, timing_model.CWL_cycles={cwl}",
             mr2_cwl, cwl)

    return out


def audit_self_claims(spec: dict) -> list:
    """The spec's own $consistency_checks strings assert results with a check
    mark. Recompute the arithmetic they state and report any whose claim is
    contradicted — a spec generator can write a passing-looking string over a
    failing value."""
    issues = []
    checks = _get(spec, "timing_model.$consistency_checks") or {}
    for name, text in checks.items():
        # Pull "A == B" or "A >= B" arithmetic out of the prose, e.g.
        # "tRC == tRAS + tRP -> 48.75 == 35.0 + 13.75 [ok]"
        m = re.search(r"([\d.]+)\s*(==|>=|=)\s*([\d.]+)\s*([+*])\s*([\d.]+)", text)
        if m:
            lhs = float(m.group(1)); op = m.group(2)
            a, o, b = float(m.group(3)), m.group(4), float(m.group(5))
            rhs = a + b if o == "+" else a * b
            ok = abs(lhs - rhs) < TOL if op in ("==", "=") else lhs >= rhs - TOL
            if not ok:
                issues.append(f"{name}: claims '{text.strip()}' but "
                              f"{lhs} {op} {rhs} is false")
            continue
        m = re.search(r"([\d.]+)\s*(==|>=|=)\s*([\d.]+)\s*$", text.replace("✓", "").strip())
        if m:
            lhs, op, rhs = float(m.group(1)), m.group(2), float(m.group(3))
            ok = abs(lhs - rhs) < TOL if op in ("==", "=") else lhs >= rhs - TOL
            if not ok:
                issues.append(f"{name}: claims '{text.strip()}' but "
                              f"{lhs} {op} {rhs} is false")
    return issues


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", default=DEFAULT_SPEC)
    ap.add_argument("--json", help="write findings (agreed schema) to this path")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    with open(args.spec) as f:
        spec = json.load(f)
    with open(RULES_PATH) as f:
        rules = json.load(f)["rules"]

    results = check(spec, rules)
    rev = spec.get("revision", "unknown")

    npass = sum(1 for r in results if r.status == "pass")
    nfail = sum(1 for r in results if r.status == "fail")
    nskip = sum(1 for r in results if r.status == "skip")

    if not args.quiet:
        print(f"spec     : {os.path.relpath(args.spec, ROOT)}")
        print(f"revision : {rev}")
        print(f"standard : JESD79-3F\n")
        mark = {"pass": "PASS", "fail": "FAIL", "skip": "skip"}
        for r in results:
            flag = "  <-- VIOLATION" if r.status == "fail" else ""
            conf = "" if r.rule.get("confidence") == "high" else "  [verify vs standard]"
            print(f"  [{mark[r.status]:4}] {r.rule['id']:10} {r.rule['title']:44}{flag}{conf}")
            if r.status != "pass":
                print(f"          {r.detail}")

        claims = audit_self_claims(spec)
        print(f"\n  spec's own $consistency_checks: "
              f"{'all recomputed claims hold' if not claims else str(len(claims)) + ' CONTRADICTED'}")
        for c in claims:
            print(f"    {c}")

        print(f"\n{'='*74}")
        print(f"  {npass} pass · {nfail} fail · {nskip} skipped (data absent)")
        crit = [r for r in results if r.status == "fail"
                and r.rule["severity"] == "critical"]
        if crit:
            print(f"  {len(crit)} CRITICAL violation(s) — this spec is not "
                  f"JEDEC-conformant. RTL validated against it proves nothing.")
        elif nfail:
            print("  Violations found, none critical.")
        else:
            print("  Spec is conformant against every rule that could be checked.")
        print("=" * 74)

    if args.json:
        payload = [r.to_finding_schema(rev) for r in results if r.status == "fail"]
        with open(args.json, "w") as f:
            json.dump(payload, f, indent=2)
        if not args.quiet:
            print(f"\nwrote {len(payload)} finding(s) -> {args.json}")

    return 1 if nfail else 0


if __name__ == "__main__":
    sys.exit(main())
