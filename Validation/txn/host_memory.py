#!/usr/bin/env python3
"""
host_memory.py — what the host wrote is what the host reads back, in order
================================================================================
The port's predictor answers a read with whatever the data path returns
next and the port's monitor attributes that response to the oldest read it
recorded: both assume responses come back in request order, so neither
could see the scheduler's FR-FCFS reordering reach the host (28 of 46 read
responses out of acceptance order on path_02, 2026-11-05, while the
design's own WB-009 tag assertion fired 66 times). This checker is
model-free: it keeps the memory image the host itself built with its
writes and, for every read response, compares the data with what the host
last wrote at the oldest outstanding read's address. A read of an address
the host never wrote is skipped (the DRAM stub's fill pattern is keyed on
the decoded row/bank/column, which the host does not know).

Usage:
    python3 Validation/txn/host_memory.py --trace observed.jsonl [--host wb --rsp wb_rsp]
Prints a scoreboard-style status line and one HOSTMEM line per mismatch.
"""
import argparse
import json
import sys


def _int(v):
    if isinstance(v, int):
        return v
    s = str(v)
    return int(s, 16) if not s.startswith("0x") else int(s, 16)


def check(trace, host="wb", rsp="wb_rsp", data_bits=32):
    txns = [json.loads(l) for l in open(trace) if l.strip()]
    txns.sort(key=lambda t: (t["time_ns"], 0 if t["iface"] == host else 1, t["seq"]))
    nbytes = data_bits // 8
    mask_all = (1 << data_bits) - 1
    mem, written, pending = {}, set(), []
    checked = skipped = 0
    mism = []
    idx = -1
    for t in txns:
        if t["iface"] == host and t["kind"] == "write":
            f = t["fields"]
            addr = _int(f["addr"]) & ~(nbytes - 1)
            data = _int(f["data"]) & mask_all
            sel = _int(f.get("sel", (1 << nbytes) - 1))
            old = mem.get(addr, 0)
            new = old
            for b in range(nbytes):
                if sel >> b & 1:
                    new = (new & ~(0xFF << (8 * b))) | (data & (0xFF << (8 * b)))
            mem[addr] = new & mask_all
            written.add(addr)
        elif t["iface"] == host and t["kind"] == "read":
            pending.append((_int(t["fields"]["addr"]) & ~(nbytes - 1), t["time_ns"]))
        elif t["iface"] == rsp and t["kind"] != "reset":
            idx += 1
            if not pending:
                mism.append(f"HOSTMEM {rsp}[{idx}] response with no read outstanding at t={t['time_ns']}")
                continue
            addr, t_acc = pending.pop(0)
            got = _int(t["fields"]["data"]) & mask_all
            if addr not in written:
                skipped += 1
                continue
            checked += 1
            exp = mem[addr]
            if got != exp:
                owner = next((a for a, v in mem.items() if v == got and a != addr), None)
                mism.append(f"HOSTMEM {rsp}[{idx}] addr=0x{addr:x} expected=0x{exp:x} observed=0x{got:x}"
                            + (f" (the data the host wrote at 0x{owner:x})" if owner is not None else "")
                            + f" read accepted t={t_acc} answered t={t['time_ns']}")
        elif t["iface"] == host and t["kind"] == "reset":
            mem, written, pending = {}, set(), []
    status = "fail" if mism else ("pass" if checked else "not_applicable")
    head = (f"scope=(host memory)  strategy=host_memory  status={status}  checked={checked} "
            f"skipped_unwritten={skipped} mismatches={len(mism)} outstanding_at_end={len(pending)}")
    return status, head, mism


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trace", required=True)
    ap.add_argument("--host", default="wb")
    ap.add_argument("--rsp", default="wb_rsp")
    ap.add_argument("--data-bits", type=int, default=32)
    a = ap.parse_args()
    status, head, mism = check(a.trace, a.host, a.rsp, a.data_bits)
    print(head)
    for m in mism[:40]:
        print("  " + m)
    if len(mism) > 40:
        print(f"  ... and {len(mism) - 40} more")
    return 0


if __name__ == "__main__":
    sys.exit(main())
