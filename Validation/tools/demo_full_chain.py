#!/usr/bin/env python3
"""
demo_full_chain.py — monitor -> extractor -> scoreboard, offline
=================================================================
Exercises the complete checking path with only the simulator stubbed:

    monitor $display format  ->  trace_extract.py  ->  scoreboard.py

Everything except Xcelium is the real code. The synthetic log is written in
exactly the format Validation/txn/generated/monitors/*.sv emit, so if the
generated monitors and the extractor ever drift apart, this demo breaks.

Stimulus is the spec-derived register walk (the same directed sequence the
live runners drive), including its unmapped-address probes.

NOTE ON THE PREDICTOR. ConfigRegsPredictor below is a test FIXTURE, not the
delivered model. Its job is to exercise the chain. The delivered predictor
will be agent-generated and graded against the spec-derived conformance
suite; the deterministic register engine it wraps is the differential oracle
that grades it.

Usage:
    python3 Validation/tools/demo_full_chain.py
"""

import json
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "refmodel"))

import trace_extract
from scoreboard import Scoreboard
from txn_contract import Txn, TransactionPredictor
from spec_register_model import SpecRegisterModel

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
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



class ConfigRegsPredictor(TransactionPredictor):
    """Consumes the CSR request stream, predicts the CSR response stream.

    The request/response split is what keeps the scoreboard's partition
    unambiguous: `csr` is what the host asked for, `csr_rsp` is what the
    design answered. Note what is absent — no cycles, no ack timing, no
    pipeline depth. The predictor says WHAT, never WHEN.
    """
    INPUT_IFACES = ("csr",)
    OUTPUT_IFACES = ("csr_rsp",)

    def __init__(self, spec):
        self.model = SpecRegisterModel(spec["csr_register_map"])
        self.reset()

    def reset(self):
        self.model.reset()

    def process(self, txn):
        if txn.iface not in self.INPUT_IFACES:
            return []
        addr = txn.fields["addr"]
        if txn.kind == "write":
            acked = self.model.write(addr, txn.fields["data"])
            return [Txn("csr_rsp", "write_ack",
                        {"addr": addr, "err": 0 if acked else 1})]
        if txn.kind == "read":
            acked, data = self.model.read(addr)
            return [Txn("csr_rsp", "read_data",
                        {"addr": addr, "data": data, "err": 0 if acked else 1})]
        return []

    def drain(self):
        return []


def synthesize_log(spec, path):
    """Write a simulation log in the generated monitors' exact format.

    Models a DUT that behaves per the spec — including returning an error on
    unmapped addresses, which the register map says is the correct response.
    That fidelity matters: an earlier version of this demo hardcoded err=0
    and the scoreboard correctly flagged 9 mismatches against the spec's own
    error semantics. The checker caught the fixture, which is the behaviour
    you want from a checker.
    """
    ref = SpecRegisterModel(spec["csr_register_map"])
    lines, t = ["xcelium> run"], 1000
    for op, addr, wdata in walk_ops(spec):
        t += 10
        if op == 0x00:
            ref.reset()
            # The monitors emit this on every reset assertion. Without it a
            # stateful predictor keeps state the DUT just cleared and
            # desynchronises permanently after the first one.
            lines.append(f"TXN csr reset t={t}")
        elif op == 0x02:
            acked = ref.write(addr, wdata)
            lines.append(f"TXN csr write t={t} addr={addr:0x} data={wdata:0x}")
            lines.append(f"TXN csr_rsp write_ack t={t} addr={addr:0x} "
                         f"err={0 if acked else 1:0x}")
        elif op == 0x01:
            acked, data = ref.read(addr)
            lines.append(f"TXN csr read t={t} addr={addr:0x}")
            lines.append(f"TXN csr_rsp read_data t={t} addr={addr:0x} "
                         f"data={data:0x} err={0 if acked else 1:0x}")
    lines.append("xmsim: *N,SIMEND: simulation complete")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


def show(label, res, expect):
    ok = res.status == expect
    print(f"\n  {label}")
    print(f"    {res.summary()}")
    for m in res.mismatches[:2]:
        print(f"      {m}")
    if len(res.mismatches) > 2:
        print(f"      ... and {len(res.mismatches) - 2} more")
    print(f"    expected {expect!r} -> {'OK' if ok else 'UNEXPECTED'}")
    return ok


def main() -> int:
    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]

    print("=" * 72)
    print("  MONITOR -> EXTRACTOR -> SCOREBOARD   (only Xcelium is stubbed)")
    print("=" * 72)

    log_path = tempfile.NamedTemporaryFile(suffix=".log", delete=False).name
    nlines = synthesize_log(spec, log_path)
    print(f"  synthetic sim log  : {nlines} lines, monitor $display format")

    # Real extractor, validating every line against the generated schema.
    txns = trace_extract.extract(log_path, schemas)
    print(trace_extract.summarize(txns))

    def sb():
        return Scoreboard("exact", ConfigRegsPredictor(spec), scope="config_regs")

    allok = True
    allok &= show("clean trace", sb().run(txns), "pass")

    bad = [Txn(t.iface, t.kind, dict(t.fields), t.seq) for t in txns]
    tgt = next(i for i, t in enumerate(bad) if t.kind == "read_data")
    bad[tgt].fields["data"] ^= 0xBEEF
    allok &= show("one corrupted read value", sb().run(bad), "fail")

    dropped = [t for i, t in enumerate(txns) if i != tgt]
    res = sb().run(dropped)
    allok &= show("one response never returned", res, "fail")
    allok &= (len(res.mismatches) == 1)
    print(f"    {len(res.mismatches)} finding for 1 dropped transaction "
          f"(alignment must not cascade)")

    # A malformed monitor line must stop extraction, not silently shrink the
    # trace — a dropped line would surface as a phantom `missing` mismatch
    # and blame the design for a parser bug.
    torn = log_path + ".torn"
    with open(log_path) as fi, open(torn, "w") as fo:
        for i, line in enumerate(fi):
            fo.write("TXN csr read tALTERED\n" if i == 5 else line)
    try:
        trace_extract.extract(torn, schemas)
        print("\n  malformed line     : NOT detected — extraction is too lenient")
        allok = False
    except trace_extract.TraceError:
        print("\n  malformed line     : extraction refused (correct — a silently "
              "short trace would blame the design)")

    os.unlink(log_path)
    os.unlink(torn)
    print("\n" + "=" * 72)
    print("  FULL CHAIN VERIFIED" if allok else "  SOMETHING BEHAVED UNEXPECTEDLY")
    print("=" * 72)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
