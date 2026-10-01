#!/usr/bin/env python3
"""
validate_spec_stage.py — the spec-review stage of the Frontend pipeline
=======================================================================
Frontend2/scripts/full_pipeline.py runs a spec-validation stage right after
microarch synthesis and before Phase 1, through this contract:

    validate_spec(spec, compile_result=None) -> {"status": "PASS"|"FAIL",
                                                 "findings": [str, ...],
                                                 "validator": str}

This is Validation's implementation of that stage. It is the first point in
the loop where a problem goes UP (to the spec synthesis agent or to a person)
instead of down to a block generator. Everything it does is deterministic and
spec-as-data; nothing here knows the design's RTL.

What is checked, and what each outcome does:

  BLOCKING (status FAIL — the pipeline stops before Phase 1):
    * schema: every section Spec/llmmc_microarchitecture.schema.json requires
      is present, with the declared type; enum / pattern / minimum / maximum
      hold (the subset of JSON Schema this checker evaluates; nothing else is)
    * JEDEC: Validation/jedec/spec_conformance.py — JESD79-3 rules recomputed
      from the spec's numbers; the spec's own "[check]" claims re-derived
    * registers: the CSR map is self-consistent (unique offsets, fields inside
      the data width and not overlapping, reset values that fit) and the
      TIMING_* reset fields equal timing_model.$derived_cycles — the numbers
      the RTL will boot with must be the numbers the spec timed
    * compiler: microarch_compiler.compile_spec()'s own consistency checks,
      when the result is passed in, all pass
    * identity: the spec names a revision (every drop, report and finding is
      keyed on it)

  ADVISORY (status PASS, listed and routed, never silently dropped):
    * intake gaps: Validation/spec/completeness_rules.json — questions the
      spec leaves open (unmapped CSR reads, DM polarity, ...) that validation
      answers with pinned conventions until a person or the synthesis agent
      decides. Written to findings/outbox/intake_spec_gaps.json and
      findings/outbox/current/SPEC_REVIEW.json with requires_human_review.

Usage:
    python3 Validation/spec/validate_spec_stage.py --spec <path> [--compile-result <path>] [--json out]
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
V = os.path.join(ROOT, "Validation")
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(V, "jedec"))

SCHEMA_PATH = os.path.join(ROOT, "Spec", "llmmc_microarchitecture.schema.json")
OUTBOX = os.path.join(V, "findings", "outbox")
VALIDATOR = "Validation/spec/validate_spec_stage.py (schema + JESD79-3 + register map + intake gate)"


# --------------------------------------------------------------------------
# schema: required sections, declared types, enums (no jsonschema dependency)
# --------------------------------------------------------------------------

_TYPES = {"object": dict, "array": list, "string": str, "boolean": bool,
          "integer": int, "number": (int, float)}


def _schema_walk(node, value, path, out, depth=0):
    """A deliberately small subset of JSON Schema: required / properties /
    type / enum / pattern / minimum / maximum, recursively. Enough to refuse a spec with a missing section
    or a value outside its enum; anything the subset cannot express is not
    checked (and that is said, not hidden)."""
    if not isinstance(node, dict):
        return
    t = node.get("type")
    if t:
        types = t if isinstance(t, list) else [t]
        py = tuple(_TYPES[x] for x in types if x in _TYPES)
        if py and not isinstance(value, py):
            out.append(f"{path or '<root>'}: expected {'/'.join(types)}, got "
                       f"{type(value).__name__}")
            return
        if "integer" in types and "number" not in types and isinstance(value, bool):
            out.append(f"{path}: expected integer, got boolean")
            return
    if "enum" in node and value not in node["enum"]:
        out.append(f"{path}: {value!r} is not one of {node['enum']}")
    if "pattern" in node and isinstance(value, str) and not re.search(node["pattern"], value):
        out.append(f"{path}: {value!r} does not match pattern {node['pattern']!r}")
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        if "minimum" in node and value < node["minimum"]:
            out.append(f"{path}: {value} is below minimum {node['minimum']}")
        if "maximum" in node and value > node["maximum"]:
            out.append(f"{path}: {value} is above maximum {node['maximum']}")
    if isinstance(value, dict):
        for req in node.get("required", []):
            if req not in value:
                out.append(f"{path + '.' if path else ''}{req}: required section/field is missing")
        for k, sub in node.get("properties", {}).items():
            if k in value:
                _schema_walk(sub, value[k], f"{path + '.' if path else ''}{k}", out, depth + 1)
    elif isinstance(value, list) and isinstance(node.get("items"), dict):
        for i, item in enumerate(value):
            _schema_walk(node["items"], item, f"{path}[{i}]", out, depth + 1)


def check_schema(spec):
    try:
        with open(SCHEMA_PATH) as f:
            schema = json.load(f)
    except (OSError, ValueError) as e:
        return [f"schema unavailable ({e}); required sections not verified"]
    out = []
    _schema_walk(schema, spec, "", out)
    return out


# --------------------------------------------------------------------------
# register map
# --------------------------------------------------------------------------

def _bits(b):
    hi, _, lo = str(b).partition(":")
    hi = int(hi)
    lo = int(lo) if lo else hi
    return (hi, lo) if hi >= lo else (lo, hi)


def check_register_map(spec):
    rm = spec.get("csr_register_map")
    if not isinstance(rm, dict) or "registers" not in rm:
        return []
    out = []
    width = int(rm.get("data_width_bits", 32))
    seen = {}
    derived = (spec.get("timing_model") or {}).get("$derived_cycles") or {}
    for r in rm["registers"]:
        name = r.get("name", "?")
        try:
            off = int(str(r.get("offset")), 16)
        except (TypeError, ValueError):
            out.append(f"{name}: offset {r.get('offset')!r} is not a hex address")
            continue
        if off in seen:
            out.append(f"{name}: offset {r['offset']} is already {seen[off]}")
        seen[off] = name
        used = 0
        composed = 0
        for f in r.get("fields", []):
            try:
                hi, lo = _bits(f.get("bits"))
            except (TypeError, ValueError):
                out.append(f"{name}.{f.get('name')}: bits {f.get('bits')!r} unreadable")
                continue
            if hi >= width:
                out.append(f"{name}.{f.get('name')}: bits {f.get('bits')} exceed the "
                           f"{width}-bit data width")
            m = ((1 << (hi - lo + 1)) - 1) << lo
            if used & m:
                out.append(f"{name}.{f.get('name')}: bits {f.get('bits')} overlap another field")
            used |= m
            rst = f.get("reset_value", 0)
            try:
                rst = int(rst, 0) if isinstance(rst, str) else int(rst)
            except (TypeError, ValueError):
                out.append(f"{name}.{f.get('name')}: reset_value {f.get('reset_value')!r} unreadable")
                continue
            if rst >> (hi - lo + 1):
                out.append(f"{name}.{f.get('name')}: reset_value {rst:#x} does not fit "
                           f"{hi - lo + 1} bit(s)")
            composed |= (rst & ((1 << (hi - lo + 1)) - 1)) << lo
            # a timing field boots with the number the spec timed
            fn = f.get("name", "")
            if fn in derived and f.get("access", "").upper() in ("RW", "RO") and \
                    isinstance(derived[fn], (int, float)) and int(derived[fn]) != rst:
                out.append(f"{name}.{fn}: reset_value {rst} but timing_model.$derived_cycles."
                           f"{fn} = {derived[fn]} -- the RTL would boot with a timing the "
                           f"spec did not derive")
        rv = r.get("reset_value")
        if rv is not None and r.get("fields"):
            try:
                rv_int = int(rv, 0) if isinstance(rv, str) else int(rv)
                if rv_int != composed:
                    out.append(f"{name}: reset_value {rv} but its fields compose to "
                               f"{composed:#010x}")
            except (TypeError, ValueError):
                out.append(f"{name}: reset_value {rv!r} unreadable")
    return out


# --------------------------------------------------------------------------
# the stage
# --------------------------------------------------------------------------

def review(spec, compile_result=None):
    """Everything validate_spec() decides from, as structured data."""
    import spec_conformance as JC
    import spec_completeness as SCp

    blocking, advisory = [], []

    # identity
    if not spec.get("revision"):
        blocking.append("identity: the spec has no `revision`; every drop, report and finding "
                        "is keyed on it")

    # schema
    for s in check_schema(spec):
        blocking.append(f"schema: {s}")

    # JEDEC
    with open(JC.RULES_PATH) as f:
        rules = json.load(f)["rules"]
    jedec = JC.check(spec, rules)
    jedec_rows = []
    for r in jedec:
        jedec_rows.append({"id": r.rule["id"], "title": r.rule["title"], "status": r.status,
                           "severity": r.rule.get("severity"), "detail": r.detail})
        if r.status == "fail":
            (blocking if r.rule.get("severity") == "critical" else advisory).append(
                f"JEDEC {r.rule['id']} ({r.rule['title']}): {r.detail}")
    for c in JC.audit_self_claims(spec):
        blocking.append(f"JEDEC self-claim: {c}")

    # register map
    for s in check_register_map(spec):
        blocking.append(f"registers: {s}")

    # compiler's own checks
    if compile_result is not None and not compile_result.get("consistency_ok", True):
        failed = [c.get("name", "?") for c in compile_result.get("consistency_checks", [])
                  if not c.get("pass")]
        blocking.append(f"compiler: consistency check(s) failed: {', '.join(failed)}")

    # intake gaps (advisory, routed)
    with open(SCp.RULES) as f:
        crules = json.load(f)["rules"]
    pdefs = []
    if os.path.exists(SCp.PATH_DEFS):
        with open(SCp.PATH_DEFS) as f:
            pdefs = json.load(f)["paths"]
    gaps = []
    for r in crules:
        st, detail = SCp.check_rule(r, spec, pdefs)
        if st in ("gap", "invalid_value"):
            gaps.append({"id": r["id"], "status": st, "disposition": r.get("disposition"),
                         "question": r.get("question"), "detail": detail,
                         "require": r.get("require"), "options": r.get("options")})
            advisory.append(f"[gap:{r.get('disposition', 'decision')}] {r['id']}: {detail}")
            if st == "invalid_value":
                blocking.append(f"intake {r['id']}: {detail}")

    return {"blocking": blocking, "advisory": advisory, "jedec": jedec_rows, "gaps": gaps}


def validate_spec(spec, compile_result=None, spec_path=None, write=True):
    rev = review(spec, compile_result)
    status = "FAIL" if rev["blocking"] else "PASS"
    findings = rev["blocking"] + rev["advisory"]
    doc = {
        "$schema": "validation-spec-review/1",
        "status": status,
        "validator": VALIDATOR,
        "spec": os.path.relpath(spec_path, ROOT) if spec_path else None,
        "spec_revision": spec.get("revision"),
        "design_id": spec.get("design_id"),
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "blocking": rev["blocking"],
        "advisory": rev["advisory"],
        "jedec": rev["jedec"],
        "intake_gaps": rev["gaps"],
        "requires_human_review": any(g.get("disposition") == "decision" for g in rev["gaps"]),
        "note": ("FAIL stops the pipeline before Phase 1. A gap does not: validation judges "
                 "the RTL under a pinned convention and the question is carried here until "
                 "the spec answers it (the synthesis agent can answer most of them)."),
    }
    if write:
        os.makedirs(os.path.join(OUTBOX, "current"), exist_ok=True)
        with open(os.path.join(OUTBOX, "current", "SPEC_REVIEW.json"), "w") as f:
            json.dump(doc, f, indent=2)
        try:
            import spec_completeness as SCp
            with open(os.path.join(OUTBOX, "intake_spec_gaps.json"), "w") as f:
                json.dump({"$schema": "validation-findings/1", "spec_revision": spec.get("revision"),
                           "finding_count": len(rev["gaps"]),
                           "findings": SCp.findings_for(
                               [(next(r for r in json.load(open(SCp.RULES))["rules"] if r["id"] == g["id"]),
                                 g["status"], g["detail"]) for g in rev["gaps"]], spec)},
                          f, indent=2)
        except Exception:
            pass
    return {"status": status, "findings": findings, "validator": VALIDATOR, "review": doc}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", default=os.environ.get("VALIDATION_SPEC", os.path.join(
        HERE, "llmmc_microarchitecturespec_filled.json")))
    ap.add_argument("--compile-result", default=None,
                    help="microarch_compiler.compile_spec() result JSON, if available")
    ap.add_argument("--json", default=None, help="also write the full review here")
    args = ap.parse_args()
    with open(args.spec) as f:
        spec = json.load(f)
    cr = None
    if args.compile_result:
        with open(args.compile_result) as f:
            cr = json.load(f)
    res = validate_spec(spec, cr, spec_path=args.spec)
    rv = res["review"]
    print(f"  spec      : {os.path.relpath(args.spec, ROOT)}  rev {rv['spec_revision']}")
    print(f"  status    : {res['status']}   ({len(rv['blocking'])} blocking, "
          f"{len(rv['advisory'])} advisory)")
    print(f"  JEDEC     : {sum(1 for r in rv['jedec'] if r['status'] == 'pass')} pass / "
          f"{sum(1 for r in rv['jedec'] if r['status'] == 'fail')} fail / "
          f"{sum(1 for r in rv['jedec'] if r['status'] == 'skip')} skipped")
    for b in rv["blocking"]:
        print(f"    BLOCK  {b[:150]}")
    for a in rv["advisory"]:
        print(f"    note   {a[:150]}")
    print(f"  human     : {'yes -- open decisions listed above' if rv['requires_human_review'] else 'no'}")
    print(f"  wrote     : Validation/findings/outbox/current/SPEC_REVIEW.json")
    if args.json:
        with open(args.json, "w") as f:
            json.dump(rv, f, indent=2)
    return 0 if res["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
