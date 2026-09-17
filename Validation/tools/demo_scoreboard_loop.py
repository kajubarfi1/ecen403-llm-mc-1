#!/usr/bin/env python3
"""
demo_scoreboard_loop.py — the whole checking loop, offline
===========================================================
Proves the transaction-scoreboard path works end to end using the project's
REAL config_regs vector file, with no simulator, no cluster and no LLM call.
That is the point: the loop can be debugged and demonstrated before a single
minute of Olympus time is spent.

What it does:
  1. builds an observed trace the way a monitor would emit one, by reading
     the spec-derived register walk (Validation/sequences/register_walk.py)
  2. runs the scoreboard against a reference predictor -> expect pass
  3. corrupts one transaction's data          -> expect a `value` mismatch
  4. deletes one transaction                  -> expect a `missing` mismatch
  5. adds one the design never should produce -> expect `unexpected`

NOTE ON THE PREDICTOR USED HERE. CsrReferencePredictor below is a test
FIXTURE, not the delivered model. Its job is to exercise the scoreboard.
The delivered config_regs predictor will be agent-generated and graded
against the spec-derived conformance suite; this wrapper around the
deterministic spec register engine is the differential oracle that grades it.

Usage:
    python3 Validation/tools/demo_scoreboard_loop.py
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "refmodel"))

from txn_contract import Txn, TransactionPredictor
from scoreboard import Scoreboard
from spec_register_model import SpecRegisterModel

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
def walk_ops(spec):
    """(op, addr, wdata) rows from the spec-derived register walk — the same
    directed stimulus the live runners drive — instead of the legacy vector
    file. op: 0 reset, 1 read, 2 write."""
    import sys as _sys
    _sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
    import register_walk as RW
    with open(RW.SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(RW.CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    seq = RW.generate(spec, schemas, catalog)
    for st in seq["steps"]:
        if st["op"] == "reset":
            yield 0, 0, 0
        elif st["op"] == "drive":
            f = st["fields"]
            yield (2, f["addr"], f["data"]) if st["kind"] == "write" \
                else (1, f["addr"], 0)



class CsrReferencePredictor(TransactionPredictor):
    """Reference predictor for the CSR interface (scoreboard fixture).

    A read transaction on the bus implies an output transaction carrying the
    data that read should return. Writes change state and imply no output.
    Note what is absent: any notion of cycles, acks, or pipeline depth. The
    predictor says WHAT, never WHEN.
    """
    INPUT_IFACES = ("csr",)
    OUTPUT_IFACES = ("csr_rdata",)

    def __init__(self, spec):
        self.spec = spec
        self.model = SpecRegisterModel(spec["csr_register_map"])
        self.reset()

    def reset(self):
        self.model.reset()

    def process(self, txn):
        if txn.iface not in self.INPUT_IFACES:
            return []
        if txn.kind == "write":
            self.model.write(txn.fields["addr"], txn.fields["data"])
            return []
        if txn.kind == "read":
            _, data = self.model.read(txn.fields["addr"])
            return [Txn("csr_rdata", "data",
                        {"addr": txn.fields["addr"], "data": data})]
        if txn.kind == "reset":
            self.model.reset()
            return []
        return []

    def drain(self):
        return []


def build_trace_from_vectors(spec):
    """Synthesize the trace a monitor would emit for the register walk.

    Stimulus comes from the spec-derived register walk; observed read data
    comes from the deterministic spec register engine, i.e. a design that
    behaves exactly as the spec says — the clean baseline to then perturb.
    """
    ref = SpecRegisterModel(spec["csr_register_map"])
    trace, seq = [], 0

    def add(t):
        nonlocal seq
        t.seq = seq
        seq += 1
        trace.append(t)

    for op, addr, wdata in walk_ops(spec):
        if op == 0x00:
            ref.reset()
            add(Txn("csr", "reset", {}))
        elif op == 0x02:
            ref.write(addr, wdata)
            add(Txn("csr", "write", {"addr": addr, "data": wdata}))
        elif op == 0x01:
            add(Txn("csr", "read", {"addr": addr}))
            _, data = ref.read(addr)
            add(Txn("csr_rdata", "data", {"addr": addr, "data": data}))
        # inject opcodes drive hardware status pins; out of scope for this demo
    return trace


def show(label, res, expect):
    ok = res.status == expect
    print(f"\n  {label}")
    print(f"    {res.summary()}")
    for m in res.mismatches[:3]:
        print(f"      {m}")
    if len(res.mismatches) > 3:
        print(f"      ... and {len(res.mismatches) - 3} more")
    print(f"    expected {expect!r} -> {'OK' if ok else 'UNEXPECTED RESULT'}")
    return ok


def main() -> int:
    with open(SPEC_PATH) as f:
        spec = json.load(f)

    trace = build_trace_from_vectors(spec)
    reads = sum(1 for t in trace if t.iface == "csr" and t.kind == "read")
    print("=" * 70)
    print("  TRANSACTION SCOREBOARD — end-to-end, no simulator")
    print("=" * 70)
    print(f"  source stimulus: register walk derived from the spec's register map")
    print(f"  trace          : {len(trace)} transactions ({reads} bus reads)")

    def sb():
        return Scoreboard("exact", CsrReferencePredictor(spec), scope="config_regs")

    allok = True

    # 1. clean
    allok &= show("clean trace", sb().run(trace), "pass")

    # 2. corrupt one read's data
    bad = [Txn(t.iface, t.kind, dict(t.fields), t.seq) for t in trace]
    tgt = next(i for i, t in enumerate(bad) if t.iface == "csr_rdata")
    bad[tgt].fields["data"] ^= 0xDEAD
    allok &= show("one corrupted read value", sb().run(bad), "fail")

    # 3. drop one output
    dropped = [t for i, t in enumerate(trace) if i != tgt]
    res = sb().run(dropped)
    allok &= show("one output transaction dropped", res, "fail")
    kinds = {m.kind for m in res.mismatches}
    print(f"    mismatch kinds: {sorted(kinds)}  "
          f"(one dropped transaction should not cascade)")
    allok &= (len(res.mismatches) == 1)

    # 4. spurious extra output
    extra = list(trace)
    extra.insert(tgt + 1, Txn("csr_rdata", "data", {"addr": 0x99, "data": 0x1}))
    res = sb().run(extra)
    allok &= show("one spurious output added", res, "fail")

    # 5. findings emission
    res = sb().run(bad)
    findings = res.to_findings(spec_revision=spec.get("revision", "?"),
                               drop_id="demo")
    print(f"\n  findings emitted in the agreed schema: {len(findings)}")
    print("   ", json.dumps(findings[0], indent=2)[:340].replace("\n", "\n    "))

    print("\n" + "=" * 70)
    print("  loop verified offline" if allok else
          "  SOMETHING BEHAVED UNEXPECTEDLY — see above")
    print("=" * 70)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
