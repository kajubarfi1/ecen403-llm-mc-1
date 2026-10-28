#!/usr/bin/env python3
"""
conservation.py — request conservation over an observed trace
================================================================================
The exact scoreboards judge what the design produced; this judges what it
never produced. A predictor that answers a read only once the downstream
completion arrives (wb_rsp completes_on dp_rd_rsp) predicts nothing for a
read the data path silently dropped, so every stage passes while the host
waits forever (path_02, 2026-10-28: 13 of 46 reads never answered). The
rules live in interface_catalog.json under `conservation` — data, one per
handoff edge: every `from` transaction must have produced `per_source` `to`
transactions by the end of the run, when both blocks are in the harness.

Usage:
    python3 Validation/txn/conservation.py --trace observed.jsonl \
        --blocks wb_port,addr_decoder,cmd_queue,scheduler,cmd_gen,data_path
Prints one scoreboard-style status line and one CONSERVE line per broken
rule; exit 0 whatever the verdict (the runner reads the lines).
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CATALOG = os.path.join(HERE, "interface_catalog.json")
SCHEMAS = os.path.join(HERE, "generated", "schemas.json")
SPEC_PATH = os.environ.get("VALIDATION_SPEC", os.path.join(
    ROOT, "Validation", "spec", "llmmc_microarchitecturespec_filled.json"))

_PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")


def spec_value(spec, dotted):
    cur = spec
    for part in dotted.split("."):
        if not isinstance(cur, dict) or part not in cur:
            raise KeyError(f"spec has no {dotted!r} (stopped at {part!r})")
        cur = cur[part]
    return cur


def resolve_count(per_source, spec):
    """1, an int, or {"$spec": "<arith over dotted spec paths>"} -> int."""
    if per_source is None:
        return 1
    if isinstance(per_source, int):
        return per_source
    expr = per_source["$spec"]
    subst = _PATH.sub(lambda m: str(spec_value(spec, m.group(0))), expr)
    if not re.fullmatch(r"[0-9\s\.\+\-\*/\(\)]+", subst):
        raise ValueError(f"per_source expression {expr!r} is not arithmetic over spec paths")
    val = eval(subst, {"__builtins__": {}}, {})  # digits and operators only
    if int(val) != val or int(val) < 1:
        raise ValueError(f"per_source {expr!r} = {val}: not a positive whole number")
    return int(val)


def _matches(txn, sel):
    if txn["kind"] == "reset":
        return False
    kinds = sel.get("kinds")
    if kinds and txn["kind"] not in kinds:
        return False
    for f, v in (sel.get("where") or {}).items():
        got = txn.get("fields", {}).get(f)
        try:
            if int(str(got), 0) != int(v):
                return False
        except (TypeError, ValueError):
            return False
    return True


def _sel_label(sel):
    s = sel["iface"]
    if sel.get("kinds"):
        s += "." + "|".join(sel["kinds"])
    if sel.get("where"):
        s += "[" + ",".join(f"{k}={v}" for k, v in sel["where"].items()) + "]"
    return s


def check(trace, blocks, catalog=None, schemas=None, spec=None):
    """-> (status, rows). status: pass | fail | not_applicable.
    rows: one dict per rule with status checked/broken/not_applicable."""
    catalog = catalog or json.load(open(CATALOG))
    schemas = schemas or json.load(open(SCHEMAS))["interfaces"]
    spec = spec or json.load(open(SPEC_PATH))
    blocks = set(blocks)
    txns = []
    with open(trace) as f:
        for line in f:
            line = line.strip()
            if line:
                txns.append(json.loads(line))
    rows = []
    for rule in catalog.get("conservation", {}).get("rules", []):
        fr, to = rule["from"], rule["to"]
        need = {schemas[fr["iface"]]["block"], schemas[to["iface"]]["block"]}
        row = {"id": rule["id"], "owner": rule["owner"], "from": _sel_label(fr),
               "to": _sel_label(to), "requirement": rule["requirement"],
               "taxonomy": rule.get("taxonomy"), "spec_ref": rule.get("spec_ref")}
        if not need <= blocks:
            row.update(status="not_applicable",
                       why=f"block(s) {sorted(need - blocks)} not in the harness")
            rows.append(row)
            continue
        per = resolve_count(rule.get("per_source"), spec)
        n_from = sum(1 for t in txns if t["iface"] == fr["iface"] and _matches(t, fr))
        n_to = sum(1 for t in txns if t["iface"] == to["iface"] and _matches(t, to))
        expected = n_from * per
        row.update(per_source=per, sources=n_from, expected=expected, observed=n_to)
        if n_to == expected:
            row["status"] = "checked"
        elif n_to < expected:
            row.update(status="broken", lost=expected - n_to)
        else:
            row.update(status="broken", extra=n_to - expected)
        rows.append(row)
    checked = [r for r in rows if r["status"] != "not_applicable"]
    if not checked:
        return "not_applicable", rows
    return ("fail" if any(r["status"] == "broken" for r in checked) else "pass"), rows


def render(status, rows):
    checked = [r for r in rows if r["status"] != "not_applicable"]
    broken = [r for r in rows if r["status"] == "broken"]
    out = [f"scope=(conservation)  strategy=conservation  status={status}  "
           f"rules={len(checked)} checked, {len(broken)} broken, "
           f"{len(rows) - len(checked)} not applicable"]
    for r in broken:
        if "lost" in r:
            what = (f"lost={r['lost']} of={r['expected']} from={r['from']} to={r['to']} "
                    f"observed={r['observed']}"
                    + (f" per_source={r['per_source']}" if r["per_source"] != 1 else ""))
        else:
            what = (f"extra={r['extra']} of={r['expected']} from={r['from']} to={r['to']} "
                    f"observed={r['observed']}")
        out.append(f"  CONSERVE {r['id']} owner={r['owner']} {what} | {r['requirement']}")
    for r in rows:
        if r["status"] == "not_applicable":
            out.append(f"  (not applicable) {r['id']}: {r['why']}")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trace", required=True)
    ap.add_argument("--blocks", required=True, help="comma-separated instantiated blocks")
    ap.add_argument("--json", help="also write the rows here")
    a = ap.parse_args()
    status, rows = check(a.trace, [b for b in a.blocks.split(",") if b])
    print(render(status, rows))
    if a.json:
        with open(a.json, "w") as f:
            json.dump({"status": status, "rules": rows}, f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
