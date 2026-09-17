#!/usr/bin/env python3
"""
validate_bundles.py — system-level validation of a bundle set.

intake_agent.py validates one bundle in isolation. This validates the *set*:
the connectivity contract that the top-level elaborator depends on. It answers
the question intake cannot — "do these blocks actually compose into a
controller?" — and it is the natural home for the inbound validation gate.

Checks, in order:

  SCH-*  each manifest against schema/manifest.schema.json
  SET-*  set-level structure (duplicate modules, at most one `top`)
  NET-*  every port `source` resolves to a real output on a real block
  WID-*  the two ends of every declared edge agree on width
  GAP-*  an unsourced input that name-matches an existing output — a probable
         missed edge, which would otherwise be silently promoted to a chip pin
  DEP-*  `dependencies` agrees with the sources actually declared

GAP findings are warnings, not errors: an unsourced input is legal (that is how
a top-level pin is expressed) but one that collides with an existing output name
is far more likely to be an omission than a coincidence, and the failure mode is
silent — a net that should have been internal becomes an external pin and the
controller is quietly wrong.

Exit codes match intake_agent.py:
  0 -> PASS
  1 -> PASS_WITH_WARNINGS
  2 -> FAIL

Usage:
  python schema/validate_bundles.py --bundles_root bundles
  python schema/validate_bundles.py --bundles_root bundles --json report.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

SCHEMA_PATH = Path(__file__).resolve().parent / "manifest.schema.json"


@dataclass
class Finding:
    severity: str          # ERROR | WARNING | INFO
    code: str
    owner: str             # frontend | backend  (see intake findings item 28)
    message: str
    fix: str


def add(lst: List[Finding], sev: str, code: str, owner: str, msg: str, fix: str) -> None:
    lst.append(Finding(sev, code, owner, msg, fix))


# ── manifest discovery (same preference order as intake_agent.py) ────────────

def find_manifest(bundle_dir: Path) -> Optional[Path]:
    direct = bundle_dir / "manifest.json"
    if direct.exists():
        return direct
    for pattern in ("*_manifest.json", "*manifest*.json"):
        hits = sorted(bundle_dir.glob(pattern), key=lambda p: len(p.name))
        if hits:
            return hits[0]
    return None


def resolve_width(width: Any) -> Optional[int]:
    """Mirror of intake_agent._resolve_width, so both agree on what a width is."""
    if isinstance(width, bool):
        return None
    if isinstance(width, int):
        return width if width > 0 else None
    if isinstance(width, str):
        w = width.strip()
        if "x" in w.lower():
            a, _, b = w.lower().partition("x")
            if a.isdigit() and b.isdigit():
                total = int(a) * int(b)
                return total if total > 0 else None
            return None
        if w.isdigit():
            return int(w) if int(w) > 0 else None
    return None


def iter_ports(manifest: Dict[str, Any]):
    """Yield (group, port_dict) for every well-formed port entry."""
    for group, plist in (manifest.get("ports") or {}).items():
        if not isinstance(plist, list):
            continue
        for p in plist:
            if isinstance(p, dict) and isinstance(p.get("name"), str):
                yield group, p


# ── schema validation (optional dependency) ─────────────────────────────────

def validate_schema(manifests: Dict[str, Dict[str, Any]], findings: List[Finding]) -> bool:
    try:
        import jsonschema
    except ImportError:
        add(findings, "WARNING", "SCH-000", "backend",
            "jsonschema not installed — per-manifest schema validation skipped.",
            "pip install jsonschema (add it to requirements.txt).")
        return False

    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    validator = jsonschema.Draft202012Validator(schema)
    for name, manifest in manifests.items():
        for err in sorted(validator.iter_errors(manifest), key=lambda e: list(e.path)):
            loc = "/".join(str(x) for x in err.path) or "<root>"
            add(findings, "ERROR", "SCH-010", "frontend",
                f"{name}: manifest violates schema at {loc}: {err.message}",
                "Regenerate the manifest so it conforms to schema/manifest.schema.json.")
    return True


# ── set-level checks ────────────────────────────────────────────────────────

def validate_set(manifests: Dict[str, Dict[str, Any]], findings: List[Finding]) -> Dict[str, Any]:
    """Cross-bundle checks. Returns the derived connectivity facts."""

    # module_name -> bundle dir, for source resolution
    module_owner: Dict[str, str] = {}
    for name, m in manifests.items():
        mod = m.get("module_name")
        if not isinstance(mod, str):
            continue
        if mod in module_owner:
            add(findings, "ERROR", "SET-010", "frontend",
                f"module_name '{mod}' declared by both '{module_owner[mod]}' and '{name}'.",
                "Module names must be unique across the bundle set.")
        else:
            module_owner[mod] = name

    tops = [n for n, m in manifests.items() if m.get("kind") == "top"]
    if len(tops) > 1:
        add(findings, "ERROR", "SET-020", "frontend",
            f"More than one bundle declares kind='top': {sorted(tops)}.",
            "Exactly one bundle may be the structural top level.")

    # outputs, keyed by module_name
    outputs: Dict[str, Dict[str, Dict[str, Any]]] = {}
    for name, m in manifests.items():
        mod = m.get("module_name")
        if not isinstance(mod, str):
            continue
        outputs[mod] = {
            p["name"]: p for g, p in iter_ports(m) if p.get("dir") == "output"
        }

    edges: List[Dict[str, Any]] = []
    consumed: set[Tuple[str, str]] = set()
    unsourced: List[Tuple[str, str]] = []

    for name, m in manifests.items():
        mod = m.get("module_name")
        if m.get("kind") == "top":
            continue  # the top level's ports are chip pins by definition
        declared_deps: set[str] = set()

        for group, p in iter_ports(m):
            if p.get("dir") != "input":
                continue
            src = p.get("source")

            if not src:
                if group != "clock_reset":
                    unsourced.append((mod, p["name"]))
                continue

            src_mod, _, src_port = src.partition(".")
            declared_deps.add(src_mod)

            # NET — does the reference resolve?
            if src_mod not in outputs:
                add(findings, "ERROR", "NET-010", "frontend",
                    f"{mod}.{p['name']}: source '{src}' names module "
                    f"'{src_mod}', which is not in the bundle set.",
                    "Fix the source reference or add the missing bundle.")
                continue
            if src_port not in outputs[src_mod]:
                add(findings, "ERROR", "NET-011", "frontend",
                    f"{mod}.{p['name']}: source '{src}' names port "
                    f"'{src_port}', which is not an output of '{src_mod}'.",
                    "Fix the source reference or the producing block's port list.")
                continue

            # WID — do the ends agree?
            dst_w = resolve_width(p.get("width"))
            src_w = resolve_width(outputs[src_mod][src_port].get("width"))
            if dst_w is not None and src_w is not None and dst_w != src_w:
                add(findings, "ERROR", "WID-010", "frontend",
                    f"Width mismatch on {src} (w={src_w}) -> "
                    f"{mod}.{p['name']} (w={dst_w}).",
                    "Make the producing and consuming port widths agree.")

            consumed.add((src_mod, src_port))
            edges.append({
                "from": {"module": src_mod, "port": src_port},
                "to":   {"module": mod,     "port": p["name"]},
                "width": dst_w,
            })

        # DEP — does `dependencies` match reality?
        if "dependencies" in m:
            stated = set(m["dependencies"]) if isinstance(m["dependencies"], list) else set()
            if stated != declared_deps:
                missing, extra = declared_deps - stated, stated - declared_deps
                bits = []
                if missing:
                    bits.append(f"used but not listed: {sorted(missing)}")
                if extra:
                    bits.append(f"listed but unused: {sorted(extra)}")
                add(findings, "WARNING", "DEP-010", "frontend",
                    f"{mod}: dependencies disagree with declared sources — {'; '.join(bits)}.",
                    "Regenerate `dependencies` from the port source fields.")

    # GAP — an unsourced input whose name matches an existing output
    producers: Dict[str, List[str]] = {}
    for src_mod, ports in outputs.items():
        for port_name in ports:
            producers.setdefault(port_name, []).append(src_mod)

    gaps = []
    for mod, port_name in unsourced:
        cands = [b for b in producers.get(port_name, []) if b != mod]
        if cands:
            gaps.append({"module": mod, "port": port_name, "candidates": sorted(cands)})
            add(findings, "WARNING", "GAP-010", "frontend",
                f"{mod}.{port_name} has no source but '{port_name}' is an output of "
                f"{', '.join(sorted(cands))} — probable missing connection.",
                f"Add \"source\": \"{sorted(cands)[0]}.{port_name}\", or confirm it is "
                f"intentionally a top-level pin.")

    top_inputs = [f"{m}.{p}" for m, p in unsourced
                  if not [b for b in producers.get(p, []) if b != m]]
    top_outputs = [f"{mod}.{pn}" for mod, ports in outputs.items()
                   for pn in ports if (mod, pn) not in consumed]

    # Per-block worksheet: the unfilled slots in the connectivity contract.
    # This is what the frontend team fills in — for each entry, decide whether
    # it is an internal edge (add a `source`) or a genuine top-level chip pin.
    worksheet: Dict[str, Any] = {}
    for name, m in manifests.items():
        mod = m.get("module_name")
        if not isinstance(mod, str) or m.get("kind") == "top":
            continue
        ins = [
            {"port": p["name"], "width": resolve_width(p.get("width")), "group": g}
            for g, p in iter_ports(m)
            if p.get("dir") == "input" and not p.get("source") and g != "clock_reset"
        ]
        dangling = [
            {"port": pn, "width": resolve_width(pp.get("width"))}
            for pn, pp in outputs.get(mod, {}).items() if (mod, pn) not in consumed
        ]
        worksheet[mod] = {
            "bundle_dir":         name,
            "unsourced_inputs":   sorted(ins, key=lambda x: x["port"]),
            "unconsumed_outputs": sorted(dangling, key=lambda x: x["port"]),
            "outputs_total":      len(outputs.get(mod, {})),
            "outputs_consumed":   len(outputs.get(mod, {})) - len(dangling),
        }

    return {
        "declared_edges":         len(edges),
        "distinct_producer_ports": len({(e["from"]["module"], e["from"]["port"]) for e in edges}),
        "modules":                sorted(module_owner),
        "top_bundle":             tops[0] if len(tops) == 1 else None,
        "internal_edges":         edges,
        "gaps":                   gaps,
        "top_level_inputs":       sorted(top_inputs),
        "top_level_outputs":      sorted(top_outputs),
        "worksheet":              worksheet,
    }


# ── main ────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Validate a DDR3 bundle set as a system.")
    ap.add_argument("--bundles_root", type=Path, default=Path("bundles"),
                    help="Directory containing one subdirectory per bundle.")
    ap.add_argument("--json", type=Path, default=None,
                    help="Write the full machine-readable report here.")
    ap.add_argument("--worksheet", type=Path, default=None,
                    help="Write just the connectivity worksheet here — the per-block list of "
                         "unsourced inputs and unreferenced outputs for the frontend team to fill in.")
    args = ap.parse_args()

    if not args.bundles_root.exists():
        print(f"ERROR: bundles root not found: {args.bundles_root}", file=sys.stderr)
        return 2

    findings: List[Finding] = []
    manifests: Dict[str, Dict[str, Any]] = {}

    for entry in sorted(args.bundles_root.iterdir()):
        if not entry.is_dir():
            continue
        mpath = find_manifest(entry)
        if not mpath:
            continue
        try:
            manifests[entry.name] = json.loads(mpath.read_text(encoding="utf-8"))
        except Exception as e:
            add(findings, "ERROR", "SCH-001", "frontend",
                f"{entry.name}: manifest is not valid JSON: {e}",
                "Fix the JSON and re-export from the frontend.")

    if not manifests:
        print(f"ERROR: no bundles with a manifest found under {args.bundles_root}",
              file=sys.stderr)
        return 2

    validate_schema(manifests, findings)
    facts = validate_set(manifests, findings)

    errors = [f for f in findings if f.severity == "ERROR"]
    warnings = [f for f in findings if f.severity == "WARNING"]
    status = "FAIL" if errors else ("PASS_WITH_WARNINGS" if warnings else "PASS")

    # ── console report ──────────────────────────────────────────────────────
    print("=" * 68)
    print("  DDR3 BUNDLE SET VALIDATION")
    print("=" * 68)
    print(f"  bundles            : {len(manifests)}")
    print(f"  top-level bundle   : {facts['top_bundle'] or '(none — see §4.1)'}")
    print(f"  internal nets      : {len(facts['internal_edges'])}")
    print(f"  probable gaps      : {len(facts['gaps'])}")
    print(f"  top-level pins     : {len(facts['top_level_inputs'])} in / "
          f"{len(facts['top_level_outputs'])} out")
    print("-" * 68)

    for group, label in ((errors, "ERRORS"), (warnings, "WARNINGS")):
        if not group:
            continue
        print(f"\n  {label} ({len(group)})")
        for f in group:
            print(f"    [{f.code}] ({f.owner}) {f.message}")
            print(f"        fix: {f.fix}")

    print("\n" + "=" * 68)
    print(f"  STATUS : {status}")
    print("=" * 68)

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps({
            "status": status,
            "errors": [asdict(f) for f in errors],
            "warnings": [asdict(f) for f in warnings],
            "facts": facts,
        }, indent=2), encoding="utf-8")
        print(f"  report    -> {args.json}")

    if args.worksheet:
        ws = facts["worksheet"]
        slots = sum(len(b["unsourced_inputs"]) + len(b["unconsumed_outputs"])
                    for b in ws.values())
        args.worksheet.parent.mkdir(parents=True, exist_ok=True)
        args.worksheet.write_text(json.dumps({
            "_README": (
                "Connectivity worksheet for the DDR3 bundle set. For every entry below, decide: "
                "is this an internal edge or a top-level chip pin? For an internal edge, add "
                "\"source\": \"<producing_module>.<port>\" to the input port in its manifest. For a "
                "chip pin, leave it as-is — an input with no source is promoted to a top-level port. "
                "Regenerate with: python schema/validate_bundles.py --bundles_root bundles "
                "--worksheet handoff/connectivity_worksheet.json"
            ),
            "generated_from":          str(args.bundles_root),
            "declared_edges":          facts["declared_edges"],
            "distinct_producer_ports": facts["distinct_producer_ports"],
            "slots_to_fill":           slots,
            "blocks":                  ws,
        }, indent=2), encoding="utf-8")
        print(f"  worksheet -> {args.worksheet}   ({slots} slots to fill)")

    return {"PASS": 0, "PASS_WITH_WARNINGS": 1, "FAIL": 2}[status]


if __name__ == "__main__":
    raise SystemExit(main())
