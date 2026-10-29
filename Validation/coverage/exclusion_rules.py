#!/usr/bin/env python3
"""
exclusion_rules.py — coverage exclusions as rules over the spec, not numbers
================================================================================
An exclusion in coverage/exclusions.json names WHY a set of toggle bits can
never be reached; the bits themselves are derived here, against the spec and
the drop under judgement, each time the exclusions are applied. A literal
bit list would freeze one spec's values into the file (the first draft did,
2026-10-29: counter bits computed from the golden tRCD and stored as
[4, 5, 6, 7]); under a spec whose counter loads 20 those bits are reachable
and the exclusion would hide them. The approval therefore covers the rule.

`bits` is "all", or one rule:
    {"above_max": "<arith over spec paths>", "width": W}
        bits ceil(log2(max + 1)) .. W-1: a W-bit counter that never loads
        more than max.  Arithmetic: + - * / ( ) ceil() floor() log2() and
        dotted spec paths (data_path_mapping.host_width_bits).
    {"low_bits": "<arith>"}            bits 0 .. n-1
    {"reserved_of": "REGISTER"}        the register map's 'reserved' field range
    {"address_bits_unused": true}      word-stride low bits and the bits above
                                       the highest mapped offset
`signals` is a list, or {"undriven_inputs_of": "<block>", "plus": [...]}:
the block's manifest inputs that the integration map neither connects nor
ties (E-ABSENT), plus named registers those inputs alone can set.
"""
import json
import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
SPEC_PATH = os.environ.get("VALIDATION_SPEC", os.path.join(
    ROOT, "Validation", "spec", "llmmc_microarchitecturespec_filled.json"))
IMAP = os.path.join(ROOT, "Validation", "structural", "integration_map.json")

_PATH = re.compile(r"(?<![\w.])[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)+")
_FUNCS = {"ceil": math.ceil, "floor": math.floor, "log2": lambda x: math.log2(x)}


class RuleError(Exception):
    pass


def spec_value(spec, dotted):
    cur = spec
    for part in dotted.split("."):
        if not isinstance(cur, dict) or part not in cur:
            raise RuleError(f"spec has no {dotted!r} (stopped at {part!r})")
        cur = cur[part]
    if not isinstance(cur, (int, float)) or isinstance(cur, bool):
        raise RuleError(f"spec {dotted!r} is {cur!r}, not a number")
    return cur


def spec_expr(spec, expr):
    """A number from arithmetic over dotted spec paths."""
    subst = _PATH.sub(lambda m: repr(spec_value(spec, m.group(0))), str(expr))
    if not re.fullmatch(r"[0-9\s\.\+\-\*/\(\),a-z]+", subst) or re.search(r"[a-z]+", re.sub(r"ceil|floor|log2", "", subst)):
        raise RuleError(f"exclusion expression {expr!r} is not arithmetic over spec paths")
    return eval(subst, {"__builtins__": {}}, dict(_FUNCS))


def register(spec, name):
    for r in spec.get("csr_register_map", {}).get("registers", []):
        if r.get("name") == name:
            return r
    raise RuleError(f"register map has no register {name!r}")


def _field_range(f):
    b = str(f.get("bits") or f.get("bit_range") or "")
    if ":" in b:
        hi, lo = (int(x) for x in b.split(":"))
    else:
        hi = lo = int(b)
    return list(range(lo, hi + 1))


def resolve_bits(rule, spec):
    """-> list of bit indices, or "all"."""
    if rule == "all":
        return "all"
    if not isinstance(rule, dict):
        raise RuleError(f"bits must be \"all\" or a rule object, not a literal list ({rule!r}): "
                        f"a literal freezes one spec's values into the file")
    if "above_max" in rule:
        mx = spec_expr(spec, rule["above_max"])
        w = int(rule.get("width", 8))
        lo = math.ceil(math.log2(mx + 1)) if mx >= 0 else 0
        return list(range(lo, w))
    if "low_bits" in rule:
        n = int(round(spec_expr(spec, rule["low_bits"])))
        return list(range(0, n))
    if "reserved_of" in rule:
        reg = register(spec, rule["reserved_of"])
        bits = []
        for f in reg.get("fields", []):
            if f.get("name") == "reserved" and f.get("access", "RO") == "RO":
                bits += _field_range(f)
        return sorted(bits)
    if rule.get("address_bits_unused"):
        rm = spec["csr_register_map"]
        stride = int(rm.get("data_width_bits", 32)) // 8
        offs = [int(str(r["offset"]), 16) for r in rm["registers"] if "offset" in r]
        width = int(rm.get("address_width_bits", 8))
        low = list(range(0, int(math.log2(stride))))
        top = max(offs) if offs else 0
        high = list(range(top.bit_length(), width))
        return low + high
    raise RuleError(f"unknown bits rule {sorted(rule)}")


def undriven_inputs(block, imap=None, manifest_ports=None):
    """The block's manifest inputs with no source connection and no tie."""
    imap = imap if imap is not None else json.load(open(IMAP))
    if manifest_ports is None:
        sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))
        import rtl_drop as RD
        manifest_ports = RD.manifest_ports(block)
    driven = {c["to"].split(".", 1)[1] for c in imap.get("connections", []) if c["to"].startswith(block + ".")}
    for key in ("ties", "standalone_ties"):
        for k in imap.get(key, {}):
            if k.startswith(block + ".") and not k.startswith("$"):
                driven.add(k.split(".", 1)[1])
    for k, v in imap.get("expr_glue", {}).items() if isinstance(imap.get("expr_glue"), dict) else []:
        if k.startswith(block + "."):
            driven.add(k.split(".", 1)[1])
    # a port the interface catalog observes or drives (a host bus, a CSR bus)
    # is an external boundary, driven by the environment, never "undriven"
    external = catalog_ports(block)
    ins = [n for n, p in manifest_ports.items() if p.get("dir", "input") == "input"
           and n not in ("clk", "rst_n") and n not in driven and n not in external]
    return sorted(ins)


_IDENT = re.compile(r"[A-Za-z_]\w*")


def catalog_ports(block, catalog=None):
    """Every port of `block` the interface catalog names: fields, qualifier,
    kind_select, pending.push, drive signals."""
    if catalog is None:
        with open(os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")) as f:
            catalog = json.load(f).get("interfaces", {})
    ports = set()
    for e in catalog.values():
        # only streams the ENVIRONMENT drives into the block (a catalog drive
        # block: the host bus, the CSR bus). `role` is the predictor's
        # input/output partition, not this: a status stream another block
        # feeds is role request too, and its ports are what this rule judges
        if e.get("block") != block or not e.get("drive"):
            continue
        for kinds in e.get("kinds", {}).values():
            for v in kinds.values():
                ports.add(v["port"] if isinstance(v, dict) else v)
        for expr in (e.get("qualifier"), (e.get("kind_select") or {}).get("expr"),
                     (e.get("pending") or {}).get("push")):
            if expr:
                ports |= set(_IDENT.findall(expr))
        drv = e.get("drive") or {}
        for k in ("assert", "release_on_accept", "hold_across_run"):
            ports |= set(drv.get(k, []))
        for lst in (drv.get("assert_by_kind") or {}).values():
            ports |= set(lst)
        ports |= set((drv.get("hold") or {}).keys())
    return ports


def resolve_signals(sig, imap=None, manifest_ports=None):
    if isinstance(sig, list):
        return list(sig)
    if isinstance(sig, dict) and "undriven_inputs_of" in sig:
        return undriven_inputs(sig["undriven_inputs_of"], imap, manifest_ports) + list(sig.get("plus", []))
    raise RuleError(f"signals must be a list or {{undriven_inputs_of}} ({sig!r})")


def resolve(excl, spec, imap=None, manifest_ports=None):
    """A concrete copy of the exclusion for this spec and drop."""
    out = dict(excl)
    out["signals"] = resolve_signals(excl["signals"], imap, manifest_ports)
    out["bits"] = resolve_bits(excl.get("bits", "all"), spec)
    return out
