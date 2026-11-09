#!/usr/bin/env python3
"""
address_order.py — same-address requests reach the memory in host order
================================================================================
The scheduler may reorder commands across addresses (fr_fcfs); it may not
reorder two requests to the SAME word address when one of them is a write,
or the host reads stale data (read-after-write), the new data (write-after-
read) or keeps the older word (write-after-write). host_memory.py sees only
the consequence at the host port and blames the port; this check sees the
issue order and names the block that reordered (path_18, drop 2a18a7929dce,
2026-11-09: the read of 0x17fb2260 reached DDR 40 ns before the older write).

Model-free and data-driven: the catalog's `ordering.rules` name the request
stream (host order; address, direction, the tag the port assigned) and the
issue stream (commands by direction and tag). A command pairs with the
oldest un-issued request of its direction and tag; at that moment every
older un-issued request to the same word address with a write on either
side is a violation.

Usage:
    python3 Validation/txn/address_order.py --trace observed.jsonl --blocks a,b [--data-bits 32]
Prints a status line and one ADDRORDER line per violation.
"""
import argparse
import json
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")


def _int(v):
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, int):
        return v
    s = str(v).strip()
    if s in ("True", "False"):
        return int(s == "True")
    return int(s, 16)


def load_rules(catalog_path=CATALOG):
    with open(catalog_path) as f:
        doc = json.load(f)
    return doc.get("ordering", {}).get("rules", []), doc["interfaces"]


class NotCheckable(Exception):
    """The trace lacks a field the rule pairs on (monitors generated before
    the catalog declared it): no verdict, never a pass."""


def check_rule(txns, rule, data_bits=32):
    """-> (checked, unpaired, [violation lines]) for one rule over a sorted trace."""
    rq, iss = rule["request"], rule["issue"]
    for t in txns:
        if t["iface"] == rq["iface"] and t["kind"] != "reset":
            missing = [k for k in (rq["addr"], rq["we"], rq["aux"]) if k not in t["fields"]]
            if missing:
                raise NotCheckable(f"{rq['iface']} carries no {'/'.join(missing)} field in this trace "
                                   f"(monitors regenerated before the catalog declared it)")
            break
    for t in txns:
        if t["iface"] == iss["iface"] and t["kind"] in iss["kind_we"]:
            if iss["aux"] not in t["fields"]:
                raise NotCheckable(f"{iss['iface']} carries no {iss['aux']} field in this trace")
            break
    kind_we = {k: int(v) for k, v in iss["kind_we"].items()}
    nbytes = max(1, data_bits // 8)
    outstanding = []            # host order: dicts of un-issued requests
    checked = unpaired = 0
    lines = []
    for t in txns:
        if t["iface"] == rq["iface"] and t["kind"] == "reset":
            outstanding = []
        elif t["iface"] == rq["iface"] and t["kind"] != "reset":
            f = t["fields"]
            r = {"we": _int(f[rq["we"]]), "addr": _int(f[rq["addr"]]) & ~(nbytes - 1),
                 "aux": _int(f[rq["aux"]]), "t": t["time_ns"], "tainted": False}
            # the tag is the request's identity downstream; a second
            # un-issued request with the same direction and tag makes the
            # pairing ambiguous and, in a tag-indexed buffer, overwrites the
            # older word (path_07, 2a18a7929dce). Both are tainted: no
            # ordering verdict is drawn from either.
            for o in outstanding:
                if o["we"] == r["we"] and o["aux"] == r["aux"]:
                    kind = "write" if r["we"] else "read"
                    tr = rule.get("tag_reuse", {})
                    lines.append(f"ADDRORDER {rule['id']}_TAG_REUSE owner={tr.get('owner', rule['owner'])} "
                                 f"addr=0x{r['addr']:x} {kind} accepted t={r['t']} reuses tag {r['aux']} of the "
                                 f"older {kind} accepted t={o['t']} to 0x{o['addr']:x} still unissued")
                    o["tainted"] = r["tainted"] = True
            outstanding.append(r)
        elif t["iface"] == iss["iface"] and t["kind"] in kind_we:
            we = kind_we[t["kind"]]
            aux = _int(t["fields"][iss["aux"]])
            i = next((k for k, r in enumerate(outstanding) if r["we"] == we and r["aux"] == aux), None)
            if i is None:
                unpaired += 1
                continue
            r = outstanding.pop(i)
            checked += 1
            kind = "write" if we else "read"
            for o in outstanding[:i]:
                if o["addr"] == r["addr"] and (o["we"] or r["we"]) and not (o["tainted"] or r["tainted"]):
                    okind = "write" if o["we"] else "read"
                    lines.append(f"ADDRORDER {rule['id']} owner={rule['owner']} addr=0x{r['addr']:x} "
                                 f"{kind} accepted t={r['t']} issued t={t['time_ns']} ahead of the older "
                                 f"{okind} accepted t={o['t']} still unissued")
    return checked, unpaired, lines


def check(trace, blocks, rules, interfaces, data_bits=32):
    """-> (status, head, lines). not_applicable when no rule names two
    interfaces whose blocks are both in the harness."""
    txns = [json.loads(l) for l in open(trace) if l.strip()]
    # In one cycle a command's issue frees a tag before a new request takes
    # it (pop then push, the buffer's same-cycle handshake): issue events
    # sort ahead of request events at equal time so that is not a reuse.
    issue_ifaces = {r["issue"]["iface"] for r in rules}
    txns.sort(key=lambda t: (t["time_ns"], 0 if t["iface"] in issue_ifaces else 1, t["seq"]))
    blocks = set(blocks)
    applicable = [r for r in rules
                  if interfaces.get(r["request"]["iface"], {}).get("block") in blocks
                  and interfaces.get(r["issue"]["iface"], {}).get("block") in blocks]
    if not applicable:
        return "not_applicable", "scope=(address order)  strategy=address_order  status=not_applicable  rules=0", []
    checked = unpaired = 0
    lines, uncheckable = [], []
    for r in applicable:
        try:
            c, u, ls = check_rule(txns, r, data_bits)
        except NotCheckable as e:
            uncheckable.append(f"{r['id']}: {e}")
            continue
        checked += c
        unpaired += u
        lines += ls
    if uncheckable and not lines:
        status = "unknown"
    else:
        status = "fail" if lines else ("pass" if checked else "not_applicable")
    head = (f"scope=(address order)  strategy=address_order  status={status}  rules={len(applicable)} "
            f"checked={checked} unpaired={unpaired} violations={len(lines)}"
            + (f"  uncheckable={len(uncheckable)} ({'; '.join(uncheckable)})" if uncheckable else ""))
    return status, head, lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trace", required=True)
    ap.add_argument("--blocks", required=True, help="comma-separated blocks in the harness")
    ap.add_argument("--data-bits", type=int, default=32)
    ap.add_argument("--catalog", default=CATALOG)
    a = ap.parse_args()
    rules, ifs = load_rules(a.catalog)
    status, head, lines = check(a.trace, a.blocks.split(","), rules, ifs, a.data_bits)
    print(head)
    for l in lines[:40]:
        print("  " + l)
    if len(lines) > 40:
        print(f"  ... and {len(lines) - 40} more")
    return 0


if __name__ == "__main__":
    sys.exit(main())
