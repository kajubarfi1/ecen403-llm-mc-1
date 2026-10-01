#!/usr/bin/env python3
"""
check_data_integrity.py — end-to-end data integrity on the known-good design
==============================================================================
Two independent checks over one simulation log of UberDDR3 with our monitors
bound (uberddr3_wb_monitor.sv on the host port, uberddr3_pin_sva.sv at the
DRAM pins):

  1. HOST MEMORY MODEL. Every accepted Wishbone write updates a byte-
     addressable model (byte enables honoured); every read response must
     equal the model. This is the property the design exists to provide.
     Responses are paired to requests in order (Wishbone pipelined).

  2. HOST <-> PIN ADDRESS CONSISTENCY. Every accepted host request after
     calibration is mapped through the spec's address mapping
     ({row, bank, column}) and must correspond, in order, to a CAS command
     at the DRAM pins with that bank and column, issued while that bank's
     open row (tracked from ACT/PRE at the pins) is the mapped row. This
     ties the two observation points together: the controller not only
     returned the right data, it put every burst where the spec says it
     lives.

Usage:
    python3 Validation/refdesigns/uberddr3/check_data_integrity.py --log xrun.log \
        --spec builds/uberddr3_ddr3-667_x16_2lane_1rank/microarch_spec.json --json out.json
"""

import argparse
import json
import re
import sys

WB_REQ = re.compile(r"TXN wb request t=(\d+)(?:\.\d+)? ps addr=([0-9a-f]+) we=([01]) data=([0-9a-f]+) sel=([0-9a-f]+)")
# A write acknowledgement carries X on the read-data bus; accept x/z digits and let
# the pairing decide whether the data matters (it does only for reads).
WB_RSP = re.compile(r"TXN wb response t=(\d+)(?:\.\d+)? ps data=([0-9a-fxzXZ]+)")
PIN = re.compile(r"TXN ddr_cmd command t=(\d+)(?:\.\d+)? ps addr=([0-9a-f]+) bank=([0-9a-f]+) cmd=([0-9a-f]+)")
CALIB = re.compile(r"TXN wb calib_complete t=(\d+)")
ACT, PRE, WR, RD = 0x3, 0x2, 0x4, 0x5


def parse(log):
    reqs, rsps, pins, calib_t = [], [], [], None
    for line in open(log, errors="replace"):
        m = WB_REQ.search(line)
        if m:
            reqs.append((int(m.group(1)), int(m.group(2), 16), int(m.group(3)), int(m.group(4), 16), int(m.group(5), 16)))
            continue
        m = WB_RSP.search(line)
        if m:
            d = m.group(2).lower()
            rsps.append((int(m.group(1)), None if ("x" in d or "z" in d) else int(d, 16)))
            continue
        m = PIN.search(line)
        if m:
            pins.append((int(m.group(1)), int(m.group(2), 16), int(m.group(3), 16), int(m.group(4), 16)))
            continue
        m = CALIB.search(line)
        if m and calib_t is None:
            calib_t = int(m.group(1))
    return reqs, rsps, pins, calib_t


def memory_model(reqs, rsps, data_bytes):
    """Check 1. Walk requests in accept order, consuming responses in the
    same order (Wishbone pipelined, in-order completion): a write updates the
    model when it is encountered, a read is checked against the model AS IT
    STOOD when that read was accepted. Returns (reads, mismatches, unpaired)."""
    mem = {}
    mism = []
    n_reads = 0
    unpaired = 0
    ri = 0
    for t, addr, we, data, sel in reqs:
        if ri >= len(rsps):
            unpaired += 1
            rt, rdata = None, None
        else:
            rt, rdata = rsps[ri]
            ri += 1
        if we:
            for b in range(data_bytes):
                if (sel >> b) & 1:
                    mem[(addr, b)] = (data >> (8 * b)) & 0xFF
            continue
        n_reads += 1
        if rt is None:
            continue
        exp, known = 0, True
        for b in range(data_bytes):
            v = mem.get((addr, b))
            if v is None:
                known = False
                break
            exp |= v << (8 * b)
        if known and rdata != exp:
            mism.append({"t_req": t, "t_rsp": rt, "addr": hex(addr), "expected": hex(exp),
                         "actual": "X" if rdata is None else hex(rdata)})
    return n_reads, mism, unpaired


def address_check(reqs, pins, calib_t, row_bits, bank_bits, col_bits, burst_log2):
    """Check 2. Map host requests through {row,bank,col} and walk the pin CAS stream."""
    hosts = [(t, addr, we) for t, addr, we, _, _ in reqs if calib_t is None or t >= calib_t]
    cas = []
    row_open = {}
    for t, a, b, c in pins:
        if calib_t is not None and t < calib_t:
            continue
        if c == ACT:
            row_open[b] = a
        elif c == PRE:
            if a & (1 << 10):
                row_open.clear()
            else:
                row_open.pop(b, None)
        elif c in (WR, RD):
            cas.append((t, b, a & ~(1 << 10), row_open.get(b), c))
    col_field = col_bits - burst_log2
    errors = []
    j = 0
    matched = 0
    for t, addr, we in hosts:
        col = (addr & ((1 << col_field) - 1)) << burst_log2
        bank = (addr >> col_field) & ((1 << bank_bits) - 1)
        row = (addr >> (col_field + bank_bits)) & ((1 << row_bits) - 1)
        want = WR if we else RD
        # find the next CAS of the right kind (the controller may reorder writes vs reads? UberDDR3 does not)
        if j >= len(cas):
            errors.append({"t_host": t, "addr": hex(addr), "problem": "no CAS left at the pins"})
            break
        pt, pb, pcol, prow, pc = cas[j]
        j += 1
        if (pb, pcol, pc) != (bank, col, want) or prow != row:
            errors.append({"t_host": t, "addr": hex(addr), "expected": {"row": row, "bank": bank, "col": col, "cmd": "WR" if we else "RD"},
                           "pins": {"t": pt, "row_open": prow, "bank": pb, "col": pcol, "cmd": "WR" if pc == WR else "RD"}})
            if len(errors) > 20:
                break
        else:
            matched += 1
    return len(hosts), len(cas), matched, errors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True)
    ap.add_argument("--spec", required=True)
    ap.add_argument("--json")
    args = ap.parse_args()
    spec = json.load(open(args.spec))
    g = spec["memory_geometry"]
    row_bits, bank_bits, col_bits = int(g["row_bits"]), int(g["bank_bits"]), int(g["column_bits"])
    burst_log2 = int(g.get("burst_length", 8)).bit_length() - 1
    data_bytes = int(spec["host_interface"].get("data_width_bits", 128)) // 8

    reqs, rsps, pins, calib_t = parse(args.log)
    n_reads, mism, unpaired = memory_model(reqs, rsps, data_bytes)
    n_hosts, n_cas, matched, aerr = address_check(reqs, pins, calib_t, row_bits, bank_bits, col_bits, burst_log2)
    rep = {"$schema": "validation-data-integrity/1", "log": args.log, "spec_revision": spec.get("revision"),
           "host_requests": len(reqs), "host_responses": len(rsps), "host_writes": sum(1 for r in reqs if r[2]),
           "host_reads": n_reads, "unpaired_requests": unpaired, "calib_complete_ps": calib_t,
           "check1_memory_model": {"read_mismatches": len(mism), "samples": mism[:10]},
           "check2_host_pin_address": {"host_requests_after_calib": n_hosts, "cas_at_pins_after_calib": n_cas,
                                       "matched_in_order": matched, "errors": aerr[:10], "error_count": len(aerr)},
           "verdict": "pass" if not mism and not aerr and unpaired == 0 else "fail"}
    print(f"  host: {len(reqs)} requests ({rep['host_writes']} W / {n_reads} R), {len(rsps)} responses, {unpaired} unpaired")
    print(f"  check 1 memory model: {len(mism)} read mismatch(es)")
    print(f"  check 2 host<->pin address: {matched}/{n_hosts} host requests matched a CAS at the pins in order "
          f"({n_cas} CAS after calibration), {len(aerr)} error(s)")
    for e in aerr[:5]:
        print("    ", json.dumps(e))
    print(f"  verdict: {rep['verdict'].upper()}")
    if args.json:
        json.dump(rep, open(args.json, "w"), indent=2)
        print(f"  wrote {args.json}")
    return 0 if rep["verdict"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
