#!/usr/bin/env python3
"""
cex_triage.py — read a JasperGold counterexample VCD and print, per clock
cycle, what the host did and what came out on the DDR pins, so a
counterexample can be judged: did a LEGAL host drive the design into the
violation (a finding), or did the free inputs do something no Wishbone
master would (an assumption is missing)?

Usage:
    python3 Validation/formal/cex_triage.py cex_a_PROTO_001.vcd [--last 40]
"""
import argparse
import re
import sys

CMD = {0: "MRS", 1: "REF", 2: "PRE", 3: "ACT", 4: "WR", 5: "RD", 7: "NOP", 15: "DESL"}


def parse_vcd(path):
    """Minimal VCD reader: {signal_name: [(time, value_str)]} for scalar/vector vars."""
    ids, vals, scope = {}, {}, []
    t = 0
    with open(path, errors="replace") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("$scope"):
                scope.append(line.split()[2])
            elif line.startswith("$upscope"):
                scope.pop()
            elif line.startswith("$var"):
                p = line.split()
                code, name = p[3], p[4]
                ids.setdefault(code, []).append(".".join(scope + [name]))
            elif line.startswith("#"):
                t = int(line[1:])
            elif line[0] in "01xzXZ" and len(line) > 1 and not line.startswith("b"):
                code = line[1:]
                for n in ids.get(code, []):
                    vals.setdefault(n, []).append((t, line[0]))
            elif line[0] in "bB":
                v, code = line[1:].split()
                for n in ids.get(code, []):
                    vals.setdefault(n, []).append((t, v))
    return vals


def value_at(series, t):
    v = None
    for tt, vv in series:
        if tt > t:
            break
        v = vv
    return v


def as_int(v):
    if v is None or any(c in "xXzZ" for c in v):
        return None
    return int(v, 2)


def find(vals, suffix):
    for k in vals:
        if k.endswith(suffix):
            return k
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("vcd")
    ap.add_argument("--last", type=int, default=40, help="print only the last N cycles")
    ap.add_argument("--post", action="store_true", help="show values just AFTER each edge instead of before")
    a = ap.parse_args()
    vals = parse_vcd(a.vcd)
    clk = find(vals, ".clk")
    if not clk:
        sys.exit("no clk in VCD")
    edges = [t for t, v in vals[clk] if v == "1"]
    cols = {
        "cyc": find(vals, "free__wb_port__wb_cyc_i"), "stb": find(vals, "free__wb_port__wb_stb_i"),
        "we": find(vals, "free__wb_port__wb_we_i"), "adr": find(vals, "free__wb_port__wb_adr_i"),
        "sel": find(vals, "free__wb_port__wb_sel_i"), "stall": find(vals, "wb_port__wb_stall_o") or find(vals, ".wb_stall_o"),
        "ack": find(vals, "wb_port__wb_ack_o") or find(vals, ".wb_ack_o"),
        "cmd": find(vals, "cmd_gen__ddr_cmd") or find(vals, "u_cmd_gen.ddr_cmd"),
        "bank": find(vals, "cmd_gen__ddr_bank") or find(vals, "u_cmd_gen.ddr_bank"),
        "addr": find(vals, "cmd_gen__ddr_addr") or find(vals, "u_cmd_gen.ddr_addr"),
        "row_open": find(vals, "u_cmd_gen_sva.row_open"),
    }
    print(f"{len(edges)} clock cycles in trace; signals resolved: "
          + ", ".join(k for k, v in cols.items() if v))
    print(f"{'cyc':>4} | {'cyc':>3} {'stb':>3} {'we':>2} {'adr':>9} {'sel':>3} | {'stall':>5} {'ack':>3} | {'cmd':>4} {'bank':>4} {'addr':>6} | row_open")
    start = max(0, len(edges) - a.last)
    for i, t in enumerate(edges[start:], start):
        g = lambda k: (as_int(value_at(vals[cols[k]], t + 1 if a.post else t - 1)) if cols[k] else None)
        cmd = g("cmd")
        hx = lambda v, w: "-" if v is None else f"{v:0{w}x}"
        print(f"{i:>4} | {hx(g('cyc'),1):>3} {hx(g('stb'),1):>3} {hx(g('we'),1):>2} {hx(g('adr'),8):>9} {hx(g('sel'),1):>3} | "
              f"{hx(g('stall'),1):>5} {hx(g('ack'),1):>3} | {CMD.get(cmd, str(cmd)):>4} {hx(g('bank'),1):>4} {hx(g('addr'),4):>6} | "
              f"{'-' if g('row_open') is None else format(g('row_open'), '08b')}")


if __name__ == "__main__":
    main()
