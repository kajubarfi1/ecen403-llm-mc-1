#!/usr/bin/env python3
"""
generate_top.py — build a flat ddr3_controller top level from the block bundles.

This is an INTEGRATION SCAFFOLD, not a verified controller. It wires only the
connections the frontend actually declared (the `source` fields in the block
manifests). Every input with no declared source, and every output nothing
consumes, becomes a top-level port. While the frontend connectivity is
incomplete (see handoff/connectivity_worksheet.json) the result is a structurally
valid chip that builds end to end, but it is not functionally a memory
controller: data_path and calibration, for example, drive nothing internally.

Re-run this after the frontend backfills `source` fields; the wiring follows.

Port widths are computed from each block RTL declaration with that block
parameter values substituted, and cross-checked against the manifest width
(this is the check audit item 17 says nothing performs).

usage: python integration/generate_top.py [--out integration/ddr3_controller]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
import intake_agent as ia  # noqa: E402  (module lives in agents/)

TOP = "ddr3_controller"
CLK, RST = "clk", "rst_n"


def evaluate(expr: str, params: dict) -> int | None:
    """Numeric value of a width expression with the block parameters substituted."""
    e = expr
    for k, v in sorted(params.items(), key=lambda kv: -len(kv[0])):
        e = re.sub(rf"\b{re.escape(k)}\b", str(v), e)
    if not re.fullmatch(r"[\d\s+\-*/()]+", e or ""):
        return None
    try:
        return int(eval(e, {"__builtins__": {}}, {}))       # arithmetic only, no names left
    except Exception:
        return None


def declaration(parsed: dict | None, manifest_width, params: dict):
    """Return (packed, unpacked, bits, entries) for one port, numerically."""
    packed = unpacked = ""
    bits = entries = None
    if parsed:
        rng = parsed.get("range")
        if rng:
            m = re.match(r"\[\s*(.+?)\s*:\s*(.+?)\s*\]", rng)
            if m:
                hi, lo = evaluate(m.group(1), params), evaluate(m.group(2), params)
                if hi is not None and lo is not None:
                    packed, bits = f"[{hi}:{lo}]", abs(hi - lo) + 1
        m = re.search(r"\b\w+\s*\[\s*([^\]]+?)\s*\]\s*$", parsed.get("raw", ""))
        if m:
            n = evaluate(m.group(1), params)
            if n is not None:
                unpacked, entries = f"[{n}]", n
    mb = me = None
    if isinstance(manifest_width, int):
        mb = manifest_width
    elif isinstance(manifest_width, str) and "x" in manifest_width.lower():
        a, _, b = manifest_width.lower().partition("x")
        if a.isdigit() and b.isdigit():
            me, mb = int(a), int(b)
    if bits is None and mb:                     # fall back to the manifest
        bits = mb
        packed = f"[{mb - 1}:0]" if mb > 1 else ""
    if entries is None and me:
        entries, unpacked = me, f"[{me}]"
    return packed, unpacked, bits, entries, mb, me


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundles", type=Path, default=ROOT / "bundles")
    ap.add_argument("--out", type=Path, default=ROOT / "integration" / TOP)
    a = ap.parse_args()

    blocks, order = {}, []
    for d in sorted(a.bundles.iterdir()):
        if not d.is_dir():
            continue
        mf = next(iter(sorted(d.glob("*manifest*.json"))), None)
        if not mf:
            continue
        m = json.loads(mf.read_text())
        text = (d / m["file"]).read_text(errors="ignore")
        blob = ia.extract_ports_blob(text, m["module_name"])
        blocks[m["module_name"]] = {"dir": d, "m": m, "parsed": ia.parse_ports_from_blob(blob or ""),
                                    "params": m.get("parameters", {}), "src": d / m["file"]}
        order.append(m["module_name"])

    # every port, with a numeric declaration and a manifest cross-check
    ports, width_mismatch, unparsed = {}, [], []
    for b, info in blocks.items():
        for group, plist in info["m"]["ports"].items():
            for p in plist if isinstance(plist, list) else []:
                if not isinstance(p, dict) or not p.get("name"):
                    continue
                parsed = info["parsed"].get(p["name"])
                if parsed is None:
                    unparsed.append(f"{b}.{p['name']}")
                packed, unpacked, bits, entries, mb, me = declaration(parsed, p.get("width"), info["params"])
                if bits and mb and bits != mb:
                    width_mismatch.append(f"{b}.{p['name']}: RTL {bits} bits vs manifest {mb}")
                if entries and me and entries != me:
                    width_mismatch.append(f"{b}.{p['name']}: RTL {entries} entries vs manifest {me}")
                ports[(b, p["name"])] = {"dir": p.get("dir"), "group": group, "packed": packed,
                                         "unpacked": unpacked, "source": p.get("source")}

    # declared connections -> internal wires
    nets, consumed = {}, set()
    for (b, name), p in ports.items():
        if p["dir"] != "input" or not p["source"]:
            continue
        sb, _, sp = p["source"].partition(".")
        if (sb, sp) not in ports:
            continue
        nets[(sb, sp)] = f"w_{sb}__{sp}"
        consumed.add((sb, sp))

    def netname(b, name):
        p = ports[(b, name)]
        if p["dir"] == "input" and p["source"]:
            sb, _, sp = p["source"].partition(".")
            if (sb, sp) in nets:
                return nets[(sb, sp)]
        if p["dir"] == "output" and (b, name) in nets:
            return nets[(b, name)]
        return f"{b}_{name}"                     # promoted to a top-level pin

    top_in, top_out = [], []
    for (b, name), p in sorted(ports.items()):
        if name in (CLK, RST):
            continue
        if p["dir"] == "input" and not p["source"]:
            top_in.append((b, name))
        elif p["dir"] == "output" and (b, name) not in consumed:
            top_out.append((b, name))

    unwired = [b for b in order
               if any(x["dir"] == "output" for (bb, _), x in ports.items() if bb == b)
               and not any(bb == b for (bb, _) in consumed)]

    # ── emit ────────────────────────────────────────────────────────────────
    L = []
    L.append("// ddr3_controller — INTEGRATION SCAFFOLD, generated by integration/generate_top.py")
    L.append("//")
    L.append("// Wires ONLY the connections the frontend declared in the block manifests")
    L.append(f"// ({len(nets)} nets). Every other port is exposed at the top level, so this builds")
    L.append("// end to end but is NOT a functionally complete memory controller.")
    if unwired:
        L.append(f"// Blocks whose outputs nothing consumes yet: {', '.join(unwired)}")
    L.append("// Regenerate after the frontend backfills the `source` fields.")
    L.append("")
    L.append(f"module {TOP} (")
    decls = [f"    input  logic {CLK},", f"    input  logic {RST},"]
    for b, n in top_in:
        p = ports[(b, n)]
        decls.append(f"    input  logic {p['packed']:<12} {b}_{n}{p['unpacked']},")
    for b, n in top_out:
        p = ports[(b, n)]
        decls.append(f"    output logic {p['packed']:<12} {b}_{n}{p['unpacked']},")
    decls[-1] = decls[-1].rstrip(",")
    L += decls
    L.append(");")
    L.append("")
    L.append("    // ── internal nets (declared block-to-block connections) ──")
    for (sb, sp), w in sorted(nets.items()):
        p = ports[(sb, sp)]
        L.append(f"    logic {p['packed']:<12} {w}{p['unpacked']};")
    L.append("")
    for b in order:
        info = blocks[b]
        conns = []
        has_clk = (b, CLK) in ports
        if has_clk:
            conns.append(f".{CLK}({CLK})")
            if (b, RST) in ports:
                conns.append(f".{RST}({RST})")
        for (bb, n), p in sorted(ports.items()):
            if bb != b or n in (CLK, RST):
                continue
            conns.append(f".{n}({netname(b, n)})")
        L.append(f"    {b} u_{b} (")
        L += [f"        {c}," for c in conns[:-1]] + [f"        {conns[-1]}"]
        L.append("    );")
        L.append("")
    L.append("endmodule")

    a.out.mkdir(parents=True, exist_ok=True)
    (a.out / f"{TOP}.sv").write_text("\n".join(L) + "\n", encoding="utf-8")

    def entry(b, n, direction):
        p = ports[(b, n)]
        bits = 1
        if p["packed"]:
            hi, lo = (int(x) for x in p["packed"].strip("[]").split(":"))
            bits = abs(hi - lo) + 1
        w = bits
        if p["unpacked"]:
            w = f"{p['unpacked'].strip('[]')}x{bits}"
        return {"name": f"{b}_{n}", "width": w, "dir": direction}

    manifest = {
        "module_name": TOP,
        "kind": "top",
        "file": [f"{TOP}.sv"] + [f"../../bundles/{blocks[b]['dir'].name}/{blocks[b]['src'].name}" for b in order],
        "generated_by": "integration/generate_top.py",
        "scaffold": True,
        "note": "Integration scaffold: only frontend-declared connections are wired internally.",
        "dependencies": order,
        "parameters": {},
        # Yosys FSM extraction does not terminate on the flattened 11-block design
        # (>30 min at 100% CPU, no progress); each block alone passes it in seconds.
        "orfs_config": {"SYNTH_ARGS": "-nofsm"},
        "ports": {
            "clock_reset": [{"name": CLK, "width": 1, "dir": "input"}, {"name": RST, "width": 1, "dir": "input"}],
            "external_in": [entry(b, n, "input") for b, n in top_in],
            "external_out": [entry(b, n, "output") for b, n in top_out],
        },
    }
    (a.out / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print(f"wrote {a.out / (TOP + '.sv')} and manifest.json")
    print(f"  blocks instantiated      : {len(order)}")
    print(f"  internal nets (declared) : {len(nets)}")
    print(f"  top-level ports          : {len(top_in)} in + {len(top_out)} out + clk/rst_n")
    print(f"  blocks with no consumer  : {', '.join(unwired) or 'none'}")
    print(f"  ports not parsed from RTL: {len(unparsed)} {unparsed[:5]}")
    print(f"  width mismatches (RTL vs manifest): {len(width_mismatch)}")
    for w in width_mismatch[:8]:
        print(f"      {w}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
