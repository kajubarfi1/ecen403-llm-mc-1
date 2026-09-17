#!/usr/bin/env python3
"""
trace_extract.py — turn a simulation log into an observed transaction trace
============================================================================
The second half of the fuel line. Monitors print TXN lines into the Xcelium
log; this converts them into the .jsonl the scoreboard consumes.

    TXN csr write t=1250 addr=8 data=271c0b0b err=0
        -> {"iface":"csr","kind":"write","fields":{...},"seq":0,"time_ns":1250}

Deliberately strict about two things, both of which decide verdicts:

  * A malformed TXN line is an ERROR, never a skipped line. Silently dropping
    a transaction would make the scoreboard report a `missing` mismatch and
    blame the design for a parser bug. Extraction either produces the whole
    trace or says why it could not.
  * Fields are validated against the generated schema when one is supplied —
    an interface or field the schema does not define means the monitors and
    the schema have drifted apart, which is a regeneration problem, not a
    design finding.

`seq` is assigned by observation order, which is what the scoreboard aligns
on. `time_ns` is carried through for debugging only; the scoreboard never
compares it, because timing belongs to SVA.

Usage:
    python3 Validation/txn/trace_extract.py --log sim.log --out observed.jsonl
    python3 Validation/txn/trace_extract.py --log sim.log --out t.jsonl --schemas <path>
    python3 Validation/txn/trace_extract.py --log sim.log --summary
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

from txn_contract import Txn, save_trace, RESET_KIND

DEFAULT_SCHEMAS = os.path.join(HERE, "generated", "schemas.json")

# TXN <iface> <kind> t=<time> [<field>=<hex> ...]
TXN_RE = re.compile(r"^\s*TXN\s+(\w+)\s+(\w+)\s+t=(\d+)\s*(.*)$")
FIELD_RE = re.compile(r"(\w+)=([0-9a-fA-FxXzZ]+)")


class TraceError(Exception):
    """Extraction failed. Better than a quietly incomplete trace."""


def parse_line(line, lineno):
    """Parse one TXN line. Returns (iface, kind, time_ns, fields)."""
    m = TXN_RE.match(line)
    if not m:
        raise TraceError(f"line {lineno}: looks like a TXN line but does not "
                         f"match the monitor format: {line.strip()!r}")
    iface, kind, tstr, rest = m.groups()
    fields = {}
    for fname, fval in FIELD_RE.findall(rest):
        if any(c in fval.lower() for c in "xz"):
            # X/Z in an observed field means the DUT drove an unknown value on
            # a cycle the qualifier said a transaction completed. That is a
            # real finding, so record it rather than crashing or coercing to 0.
            fields[fname] = fval.lower()
        else:
            fields[fname] = int(fval, 16)
    leftover = FIELD_RE.sub("", rest).strip()
    if leftover:
        raise TraceError(f"line {lineno}: unparsed text {leftover!r} after "
                         f"fields — monitor format and extractor disagree.")
    return iface, kind, int(tstr), fields


def validate(iface, kind, fields, schemas, lineno):
    """Check the line against the generated schema, if one was supplied."""
    if schemas is None:
        return
    if iface not in schemas:
        raise TraceError(
            f"line {lineno}: interface {iface!r} is not in the generated "
            f"schemas ({sorted(schemas)}). Monitors and schemas have drifted — "
            f"re-run schema_gen.py and monitor_gen.py.")
    if kind == RESET_KIND:
        # Reserved: emitted by every monitor on reset assertion, carries no
        # fields, and is deliberately absent from the schema's kinds.
        if fields:
            raise TraceError(f"line {lineno}: {RESET_KIND!r} carries fields "
                             f"{sorted(fields)}; it must carry none.")
        return
    kinds = schemas[iface]["kinds"]
    if kind not in kinds:
        raise TraceError(
            f"line {lineno}: {iface} has no transaction kind {kind!r} "
            f"(schema defines {sorted(kinds)}).")
    expected = set(kinds[kind])
    got = set(fields)
    if got != expected:
        missing, extra = sorted(expected - got), sorted(got - expected)
        raise TraceError(
            f"line {lineno}: {iface}.{kind} field mismatch — "
            + (f"missing {missing} " if missing else "")
            + (f"unexpected {extra} " if extra else "")
            + "; regenerate monitors from the current schema.")


def extract(log_path, schemas=None):
    """Read a simulation log, return the observed transactions in order."""
    txns, errors = [], []
    with open(log_path, errors="replace") as f:
        for lineno, line in enumerate(f, 1):
            if "TXN " not in line:
                continue
            try:
                iface, kind, t, fields = parse_line(line, lineno)
                validate(iface, kind, fields, schemas, lineno)
            except TraceError as e:
                errors.append(str(e))
                continue
            txns.append(Txn(iface=iface, kind=kind, fields=fields,
                            seq=len(txns), time_ns=t))
    if errors:
        raise TraceError(
            f"{len(errors)} malformed TXN line(s) in "
            f"{os.path.basename(log_path)}:\n  " + "\n  ".join(errors[:10])
            + (f"\n  ... and {len(errors) - 10} more" if len(errors) > 10 else ""))
    return txns


def summarize(txns):
    from collections import Counter
    per = Counter(f"{t.iface}.{t.kind}" for t in txns)
    lines = [f"  {len(txns)} transaction(s)"]
    for k, n in sorted(per.items()):
        lines.append(f"    {k:24} {n}")
    if txns:
        lines.append(f"  time span: {txns[0].time_ns} .. {txns[-1].time_ns}")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True, help="Xcelium simulation log")
    ap.add_argument("--out", help="write observed trace here (.jsonl)")
    ap.add_argument("--schemas", default=DEFAULT_SCHEMAS,
                    help="validate against this schema file (use 'none' to skip)")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args()

    schemas = None
    if args.schemas and args.schemas.lower() != "none":
        with open(args.schemas) as f:
            schemas = json.load(f)["interfaces"]

    try:
        txns = extract(args.log, schemas)
    except TraceError as e:
        print(f"extraction failed:\n{e}", file=sys.stderr)
        return 1

    if not txns:
        print("no TXN lines found. Either the monitors are not bound into the "
              "simulation, or the run produced no completed transactions. "
              "This is not an empty pass — the scoreboard will report "
              "'unknown' for a trace like this.", file=sys.stderr)

    if args.summary or not args.out:
        print(summarize(txns))
    if args.out:
        save_trace(txns, args.out)
        print(f"wrote {len(txns)} transaction(s) -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
