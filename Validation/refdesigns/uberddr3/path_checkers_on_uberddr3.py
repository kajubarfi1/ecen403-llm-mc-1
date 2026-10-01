#!/usr/bin/env python3
"""
path_checkers_on_uberddr3.py — run OUR path checkers on a design known to work
==============================================================================
The end-to-end path checkers need two streams only: requests accepted from
the host (cq_enq: row, bank, col, we) and commands at the DDR pins
(ddr_cmd). UberDDR3 has both, under different names:

  host    its Wishbone request, mapped through the spec's address mapping
          {row, bank, col/burst} — the same mapping check_data_integrity.py
          already verified against the pins
  pins    the adapter in uberddr3_pin_sva.sv already prints ddr_cmd in our
          encoding

So the agent-generated checkers (conservation: nothing dropped, nothing
invented; bank-state legality; refresh with banks open) can be run on a
design whose own self-check and an independent Micron model both pass. A
violation here is a false positive in our checker — or a JEDEC deviation
worth writing down.

Calibration traffic is the controller's own and has no host request behind
it: before calib_complete only the commands that change bank state
(ACT, PRE, REF) are kept, so the checker's bank tracking starts right.

Usage:
    python3 Validation/refdesigns/uberddr3/path_checkers_on_uberddr3.py --log <txn log>
"""
import argparse, glob, json, os, re, subprocess, sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
from txn_contract import (load_predictor_module, find_model_classes,  # noqa: E402
                          LegalityChecker, Txn)

SPEC = os.path.join(ROOT, "builds", "uberddr3_ddr3-667_x16_2lane_1rank", "microarch_spec.json")
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
OUT = os.path.join(ROOT, "Validation", "reports", "uberddr3")

WB = re.compile(r"TXN wb request t=(\d+)(?:\.\d+)? ps addr=([0-9a-f]+) we=([01])")
PIN = re.compile(r"TXN ddr_cmd command t=(\d+)(?:\.\d+)? ps addr=([0-9a-f]+) bank=([0-9a-f]+) cmd=([0-9a-f]+)")
CAL = re.compile(r"TXN wb calib_complete t=(\d+)")


def num(v):
    m = re.match(r"(\d+)'([bdh])([0-9a-fA-F_]+)", str(v))
    if m:
        return int(m.group(3).replace("_", ""), {"b": 2, "d": 10, "h": 16}[m.group(2)])
    return int(v)


def build_trace(log, spec, enc):
    g = spec["memory_geometry"]
    rb, bb, cb = int(g["row_bits"]), int(g["bank_bits"]), int(g["column_bits"])
    bl = int(g.get("burst_length", 8)).bit_length() - 1
    colf = cb - bl
    ev, calib = [], None
    for line in open(log, errors="replace"):
        m = CAL.search(line)
        if m:
            calib = int(m.group(1))
            continue
        m = WB.search(line)
        if m:
            t, a, we = int(m.group(1)), int(m.group(2), 16), int(m.group(3))
            ev.append((t, 0, "cq_enq", "enqueue",
                       {"row": (a >> (colf + bb)) & ((1 << rb) - 1),
                        "bank": (a >> colf) & ((1 << bb) - 1),
                        "col": (a & ((1 << colf) - 1)) << bl, "we": we}))
            continue
        m = PIN.search(line)
        if m:
            t, a, b, c = int(m.group(1)), int(m.group(2), 16), int(m.group(3), 16), int(m.group(4), 16)
            ev.append((t, 1, "ddr_cmd", "command", {"cmd": c, "addr": a, "bank": b}))
    state = {num(enc[k]) for k in ("ACT", "PRE", "REF") if k in enc}
    cas = {num(enc[k]) for k in ("RD", "WR")}
    nop = {num(enc[k]) for k in ("NOP", "DESL") if k in enc}
    out, dropped = [], 0
    for t, o, iface, kind, f in sorted(ev, key=lambda e: (e[0], e[1])):
        if iface == "ddr_cmd":
            if f["cmd"] in nop:
                continue
            if calib is not None and t < calib and f["cmd"] not in state:
                dropped += 1
                continue
            if f["cmd"] in cas:
                f = dict(f, addr=f["addr"] & ~(1 << 10))      # A10 = auto-precharge flag, not column
        elif calib is not None and t < calib:
            continue
        out.append(Txn(iface, kind, f, seq=len(out), time_ns=t // 1000))
    return out, calib, dropped


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True)
    ap.add_argument("--models", nargs="*", default=None)
    args = ap.parse_args()
    spec = json.load(open(SPEC))
    enc = {k: v for k, v in json.load(open(CATALOG))["interfaces"]["ddr_cmd"]
           ["command_encoding"].items() if not k.startswith("$")}
    trace, calib, dropped = build_trace(args.log, spec, enc)
    n_enq = sum(1 for t in trace if t.iface == "cq_enq")
    print(f"  trace: {len(trace)} txns ({n_enq} host requests, "
          f"{len(trace) - n_enq} pin commands; {dropped} calibration commands dropped; "
          f"calib at {calib} ps)")
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "path_trace.jsonl"), "w") as f:
        for t in trace:
            f.write(json.dumps({"iface": t.iface, "kind": t.kind, "fields": t.fields,
                                "seq": t.seq, "time_ns": t.time_ns}) + "\n")
    have = {"cq_enq", "ddr_cmd"}
    files = args.models or sorted(
        glob.glob(os.path.join(ROOT, "Validation", "predictors", "*_checker.py"))
        + glob.glob(os.path.join(ROOT, "Validation", "predictors", "second_opinion", "*_checker.py")))
    rows = []
    for fp in files:
        mod = load_predictor_module(fp)
        cls = find_model_classes(mod, LegalityChecker)
        if not cls:
            continue
        ins, outs = set(cls[0].INPUT_IFACES), set(cls[0].OUTPUT_IFACES)
        if not (outs <= have and (ins & have) and "ddr_cmd" in outs):
            continue
        m = cls[0](spec)
        m.reset()
        vs = []
        try:
            for t in trace:
                if t.iface in ins | outs:
                    vs += m.observe(t) or []
            vs += m.final() or []
            err = None
        except Exception as e:
            err = f"{type(e).__name__}: {e}"
        by = {}
        for v in vs:
            k = v.taxonomy_id or v.rule
            by.setdefault(k, {"count": 0, "first": str(v)[:220]})["count"] += 1
        absent = sorted(ins - have)
        rows.append({"model": os.path.relpath(fp, ROOT), "covers": list(cls[0].COVERS),
                     "streams_absent": absent, "violations": sum(x["count"] for x in by.values()),
                     "by_rule": by, "error": err})
        print(f"  {os.path.relpath(fp, os.path.join(ROOT, 'Validation', 'predictors')):52} "
              f"violations={rows[-1]['violations']}" + (f"  ERROR {err}" if err else "")
              + (f"  (no {absent} stream here)" if absent else ""))
        for k, x in by.items():
            print(f"      {k} x{x['count']}: {x['first'][:150]}")
    rep = {"$schema": "validation-known-good-path-checkers/1",
           "generated_utc": datetime.utcnow().isoformat() + "Z",
           "reference": "UberDDR3 + Micron DDR3 model", "spec": os.path.relpath(SPEC, ROOT),
           "host_requests": n_enq, "pin_commands": len(trace) - n_enq, "rows": rows}
    with open(os.path.join(OUT, "path_checkers_known_good.json"), "w") as f:
        json.dump(rep, f, indent=2)
    print("  wrote Validation/reports/uberddr3/path_checkers_known_good.json")
    bad = [r for r in rows if r["violations"] or r["error"]]
    for r in bad:
        print(f"VALIDATION_FAIL: {r['model']} reported {r['violations']} violation(s) "
              f"on the known-good design {r['error'] or ''}")
    if not rows:
        print("VALIDATION_FAIL: no checker was applicable")
        return 1
    if not bad:
        print(f"VALIDATION_PASS: {len(rows)} checker(s), 0 violations over "
              f"{n_enq} host requests and {len(trace) - n_enq} pin commands")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
