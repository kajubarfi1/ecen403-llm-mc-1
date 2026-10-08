#!/usr/bin/env python3
"""
integration_map_gen.py — derive the integration map from manifest `source`
===========================================================================
The block-to-block wiring used by every chain harness used to be a hand-
written list of 71 edges (`integration_map.json`). The Frontend's manifests
now say the same thing: a consumer port carries `"source": "<block>.<port>"`.
One source of truth, so this tool builds the map FROM the manifests and keeps
by hand only what a manifest cannot say:

  * `connections` that the manifests do not (yet) declare — every one is a
    finding against the Frontend (a consumer port with no `source`), and the
    override becomes redundant (and is reported as such) the moment the
    manifest gains the field;
  * `glue` (registered re-timing), `expr_glue` (an input computed from several
    ports), `ties`, `requires` (support-block closure) and `stubs` — each
    already carries its own `why`.

Where a manifest declares a direct `source` for a port that the design cannot
actually drive directly (the port is the target of glue or expression glue),
the glue wins and the manifest's claim is filed as a finding: the generator
emitted a wiring statement the RTL does not honour.

Every derived edge is checked: the producer block and port must exist in the
drop, the producer must be an output, the consumer an input, and the widths
must agree. A violation stops generation — an integration map that names a
port the drop does not have is worse than none.

Usage:
    python3 Validation/structural/integration_map_gen.py             # write the map
    python3 Validation/structural/integration_map_gen.py --check     # exit 1 if the map on disk is stale
    python3 Validation/structural/integration_map_gen.py --findings Validation/findings/outbox/integration_map_findings.json
"""

import argparse
import datetime
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

MAP_PATH = os.path.join(HERE, "integration_map.json")
OVERRIDES_PATH = os.path.join(HERE, "integration_overrides.json")
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SPEC_PATH = os.environ.get("VALIDATION_SPEC", SPEC_PATH)   # the spec the drop was generated from, when it is not the default


class MapError(Exception):
    pass


def load_manifests(blocks):
    """{block: {port: {width, dir, group, source?}}} straight from the drop's
    manifests (rtl_drop.manifest_ports drops `source`, so read the files)."""
    import rtl_drop as RD
    out = {}
    for b in blocks:
        try:
            mf = RD.manifest_file(b)
        except RD.DropError:
            # a phase-partial drop: the block is reported absent, never
            # substituted; edges that name it are left for the drop that
            # brings it (validate_drop --partial decides what may run)
            load_manifests.missing.append(b)
            continue
        with open(mf) as f:
            m = json.load(f)
        ports = {}
        for group, plist in m.get("ports", {}).items():
            for p in plist:
                ports[p["name"]] = {"width": p["width"], "dir": p["dir"],
                                    "group": group, "source": p.get("source"),
                                    "source_expr": p.get("source_expr")}
        out[b] = ports
    return out


load_manifests.missing = []


def blocks_in_order():
    with open(PATH_DEFS) as f:
        return list(json.load(f)["blocks"].keys())


def derive(manifests, blocks):
    derive.deferred = []
    derive.inconsistent = []
    """Edges the manifests declare, in block order then manifest port order,
    plus the problems found on the way."""
    edges, errors = [], []
    derive.declared_expr = {}
    for b in blocks:
        for name, p in manifests[b].items():
            src = p.get("source")
            if p.get("source_expr"):
                # The manifest declares the input as an expression of other
                # blocks' ports (Frontend, 2026-10-08: `source_expr`, with
                # `source` its first term). That is the driver; no direct
                # edge is derived from the first term.
                derive.declared_expr[f"{b}.{name}"] = p["source_expr"]
                continue
            if not src:
                continue
            if p["dir"] != "input":
                errors.append(f"{b}.{name} carries a source but is an {p['dir']}")
                continue
            if "." not in src:
                errors.append(f"{b}.{name}: source {src!r} is not <block>.<port>")
                continue
            pb, pp = src.split(".", 1)
            if pb not in manifests:
                if pb in load_manifests.missing:
                    # absent block: the edge waits for it, but stays visible
                    # so a standalone harness knows this input is a cut edge
                    derive.deferred.append({"from": src, "to": f"{b}.{name}",
                                            "waits_for": pb})
                    continue
                errors.append(f"{b}.{name}: source block {pb!r} is not in the drop")
                continue
            prod = manifests[pb].get(pp)
            if prod is None:
                errors.append(f"{b}.{name}: source port {src} does not exist")
                continue
            if prod["dir"] != "output":
                errors.append(f"{b}.{name}: source {src} is an {prod['dir']}, not an output")
                continue
            if str(prod["width"]) != str(p["width"]):
                # a real edge the design cannot carry: filed, kept out of the
                # wiring (a harness never silently truncates or zero-extends),
                # and every path across it is blocked until a drop fixes it
                derive.inconsistent.append({"from": src, "to": f"{b}.{name}",
                                            "from_width": prod["width"], "to_width": p["width"]})
                continue
            edges.append({"from": src, "to": f"{b}.{name}"})
    return edges, errors


def build(manifests, blocks, ov):
    """Assemble the map. Returns (map, report)."""
    derived, errors = derive(manifests, blocks)
    if errors:
        raise MapError("manifest source fields are inconsistent with the drop:\n  "
                       + "\n  ".join(errors))

    # Ports the design drives through glue / expression glue: a manifest's
    # direct source there is superseded and filed.
    glued = {}
    for g in ov.get("glue", []):
        for t in g["to"]:
            glued[t] = ("glue", g["from"], g.get("why", ""))
    for e in ov.get("expr_glue", []):
        glued[e["to"]] = ("expr_glue", e["expr"], e.get("why", ""))
    # Expressions the manifests declare themselves win over our overrides: an
    # override for the same port is redundant (housekeeping), and the harness
    # builds the glue from the manifest's expression.
    declared = getattr(derive, "declared_expr", {})
    redundant_expr = [{"from": glued[t][1], "to": t, "kind": "expr_glue"}
                      for t in declared if t in glued]
    for t, expr in declared.items():
        glued[t] = ("expr_glue", expr, "declared by the manifest (source_expr)")
    expr_glue = ([e for e in ov.get("expr_glue", []) if e["to"] not in declared]
                 + [{"to": t, "expr": expr, "declared_by": "manifest"} for t, expr in declared.items()])
    superseded, kept = [], []
    for c in derived:
        if c["to"] in glued:
            kind, drv, why = glued[c["to"]]
            superseded.append({**c, "superseded_by": kind, "driver": drv, "why": why})
        else:
            kept.append(c)

    # Overrides: edges the manifests lack. Redundant ones are reported.
    have = {(c["from"], c["to"]) for c in kept}
    redundant, overrides, deferred = list(redundant_expr), [], []
    for c in ov.get("connections", []):
        key = (c["from"], c["to"])
        if key in have:
            redundant.append(c)
            continue
        cb, cp = c["to"].split(".", 1)
        fb, fp = c["from"].split(".", 1)
        if cb in load_manifests.missing or fb in load_manifests.missing:
            deferred.append({"from": c["from"], "to": c["to"],
                             "waits_for": cb if cb in load_manifests.missing else fb})
            continue
        for blk, prt, want in ((cb, cp, "input"), (fb, fp, "output")):
            if blk not in manifests or prt not in manifests[blk]:
                raise MapError(f"override {c['from']} -> {c['to']}: {blk}.{prt} is not in the drop")
            if manifests[blk][prt]["dir"] != want:
                raise MapError(f"override {c['from']} -> {c['to']}: {blk}.{prt} is not an {want}")
        if str(manifests[cb][cp]["width"]) != str(manifests[fb][fp]["width"]):
            raise MapError(f"override {c['from']} -> {c['to']}: widths differ")
        overrides.append({"from": c["from"], "to": c["to"]})
        have.add(key)

    # Consumer inputs the manifests leave without a source, grouped by block,
    # so the finding names exactly the ports the Frontend should stamp.
    missing = {}
    # Glue-driven ports are excluded: the design gives them no single source,
    # so the manifest cannot name one; that gap is filed by the glue's own
    # finding (see its `why`), not here.
    driven = {c["to"] for c in kept} | {c["to"] for c in overrides}
    for b in blocks:
        for name, p in manifests[b].items():
            ref = f"{b}.{name}"
            if p["dir"] != "input" or p.get("source"):
                continue
            if ref in driven and ref not in glued:
                missing.setdefault(b, []).append(name)

    imap = {
        "$schema": "validation-integration-map/2",
        "$comment": ov.get("$comment", ""),
        "$provenance": (
            "GENERATED by Validation/structural/integration_map_gen.py — do not edit. "
            "`connections` come from the consumer ports' `source` fields in the "
            "drop's manifests, plus the edges in integration_overrides.json that "
            "the manifests do not yet declare (each one is a filed finding). glue, "
            "expr_glue, ties, requires and stubs are carried from the overrides "
            "file verbatim: they are what a manifest cannot express."),
        "$derivation": {
            "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "manifest_edges": len(kept),
            "manifest_expressions": declared,
            "override_edges": len(overrides),
            "superseded_manifest_sources": superseded,
            "override_connections": overrides,
            "deferred_until_block_arrives": deferred,
            "redundant_overrides": [{"from": c["from"], "to": c["to"]} for c in redundant],
            "consumer_ports_without_source": missing,
        },
        "connections": kept + overrides,
        "glue": ov.get("glue", []),
        "ties": ov.get("ties", {}),
        "standalone_ties": ov.get("standalone_ties", {}),
        "deferred_connections": getattr(derive, "deferred", []) + deferred,
        "inconsistent_connections": getattr(derive, "inconsistent", []),
        "requires": ov.get("requires", {}),
        "expr_glue": expr_glue,
        "stubs": ov.get("stubs", []),
    }
    report = {"inconsistent": getattr(derive, "inconsistent", []),
              "manifest_edges": len(kept), "override_edges": len(overrides),
              "superseded": superseded, "redundant": redundant, "missing": missing}
    return imap, report


def _width_blame(edge):
    """Which end departs from the spec, by the width rules (data). Both ends
    are candidates when no rule decides."""
    try:
        sys.path.insert(0, HERE)
        import width_conformance as WC
        with open(SPEC_PATH) as f:
            spec = json.load(f)
        with open(os.path.join(HERE, "width_rules.json")) as f:
            rules = json.load(f)
        bad = {f"{r['block']}.{r['port']}" for r in WC.check(spec, rules) if r["state"] == "mismatch"}
        spec_w = {f"{r['block']}.{r['port']}": (r["expected"], r["spec_path"]) for r in WC.check(spec, rules)
                  if r["state"] in ("ok", "mismatch")}
    except Exception:
        bad, spec_w = set(), {}
    owners = [e.partition(".")[0] for e in (edge["from"], edge["to"]) if e in bad]
    ref = next((spec_w[e][1] for e in (edge["from"], edge["to"]) if e in spec_w), None)
    exp = next((spec_w[e][0] for e in (edge["from"], edge["to"]) if e in spec_w), None)
    if not owners:
        owners = [edge["from"].partition(".")[0], edge["to"].partition(".")[0]]
    return owners, ref, exp


def to_findings(report, spec_rev):
    out = []
    for e in report.get("inconsistent", []):
        owners, ref, exp = _width_blame(e)
        out.append({
            "source": "validation", "target": "frontend", "kind": "width_mismatch",
            "scope": owners[0], "owner_candidates": owners, "severity": "critical",
            "spec_revision": spec_rev,
            "title": f"{e['from']} is {e['from_width']} bits but drives {e['to']}, "
                     f"which is {e['to_width']}",
            "detail": (f"The manifests declare {e['to']} is driven by {e['from']}, and their "
                       f"widths differ ({e['from_width']} -> {e['to_width']}). The wire cannot "
                       f"be made; every path that crosses it is blocked until the drop agrees "
                       f"with itself."
                       + (f" The spec fixes this width: {ref} = {exp}, so the block(s) that "
                          f"depart from it own the fix: {', '.join(owners)}." if ref else
                          " The spec does not fix this width; either end may be the one to change.")),
            "evidence": {**e, "spec_path": ref, "spec_value": exp},
            "spec_ref": ref,
            "status": "open",
        })
    for blk, ports in sorted(report["missing"].items()):
        out.append({
            "source": "validation", "target": "frontend", "kind": "manifest_gap",
            "scope": blk, "severity": "minor", "spec_revision": spec_rev,
            "title": f"{blk} manifest declares no `source` on {len(ports)} consumer "
                     f"port(s) the design wires",
            "detail": (f"Ports {', '.join(ports)} are inputs that the integrated design "
                       f"drives from another block, but the manifest does not say from "
                       f"where. Validation carries these edges by hand in "
                       f"integration_overrides.json; the backend's set gate lists them as "
                       f"unresolved slots. Add `\"source\": \"<block>.<port>\"` to each."),
            "evidence": {"block": blk, "ports": ports},
            "status": "open",
        })
    for s in report["superseded"]:
        out.append({
            "source": "validation", "target": "frontend", "kind": "manifest_wrong_source",
            "scope": s["to"].split(".")[0], "severity": "major", "spec_revision": spec_rev,
            "title": f"{s['to']} declares source {s['from']}, but the design needs "
                     f"{s['superseded_by']}",
            "detail": (f"The manifest says {s['to']} is driven directly by {s['from']}. "
                       f"It is not: {s['why']} Driver used: {s['driver']}. Either the "
                       f"RTL should consume {s['from']} as declared, or the manifest "
                       f"should name what drives it."),
            # The contract, stated, because an agent answered the sentence
            # above by writing prose into `source` (2026-10-08), which the
            # map generator refuses: a source is a port or nothing.
            "fix": (f"A manifest `source` is \"<block>.<port>\" naming a port that exists "
                    f"in the drop, never free text. Preferred: make the RTL match the "
                    f"manifest -- have {s['from'].split('.')[0]} drive {s['from']} so "
                    f"{s['to']} is connected as declared. Otherwise set "
                    f"\"source\": \"{s['driver']}\" (the port that drives it in the design today"
                    + (", through registered glue the harness supplies" if s["superseded_by"] == "glue"
                       else ", through an expression the harness supplies")
                    + ")."),
            "evidence": {"consumer": s["to"], "declared_source": s["from"],
                         "driver": s["driver"], "kind": s["superseded_by"]},
            "status": "open",
        })
    for c in report["redundant"]:
        out.append({
            "source": "validation", "target": "validation", "kind": "housekeeping",
            "scope": c["to"].split(".")[0], "severity": "minor", "spec_revision": spec_rev,
            "title": f"override {c['from']} -> {c['to']} is now declared by the manifest",
            "detail": "Remove it from integration_overrides.json.",
            "evidence": c, "status": "open",
        })
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="do not write; exit 1 if integration_map.json is stale")
    ap.add_argument("--findings", help="write manifest-gap findings here")
    ap.add_argument("--out", default=MAP_PATH)
    args = ap.parse_args()

    blocks = blocks_in_order()
    with open(OVERRIDES_PATH) as f:
        ov = json.load(f)
    manifests = load_manifests(blocks)
    if load_manifests.missing:
        print(f"  partial drop: no manifest for {', '.join(load_manifests.missing)}; "
              f"their edges are deferred")
        blocks = [b for b in blocks if b in manifests]
    try:
        imap, report = build(manifests, blocks, ov)
        imap["$derivation"]["blocks_missing_from_drop"] = list(load_manifests.missing)
    except MapError as e:
        print(f"  integration map NOT generated: {e}", file=sys.stderr)
        return 1

    def stable(m):
        m = dict(m); d = dict(m["$derivation"]); d.pop("generated_utc", None)
        m["$derivation"] = d
        return json.dumps(m, sort_keys=True)

    if args.check:
        try:
            with open(args.out) as f:
                on_disk = json.load(f)
        except FileNotFoundError:
            on_disk = {}
        if on_disk.get("$derivation") is None or stable(on_disk) != stable(imap):
            print("  integration_map.json is STALE relative to the manifests + overrides; "
                  "rerun integration_map_gen.py")
            return 1
        print(f"  integration_map.json is current ({report['manifest_edges']} manifest "
              f"edge(s) + {report['override_edges']} override(s))")
        return 0

    with open(args.out, "w") as f:
        json.dump(imap, f, indent=2)
        f.write("\n")
    print(f"  wrote {os.path.relpath(args.out, ROOT)}: {report['manifest_edges']} edge(s) "
          f"from manifests + {report['override_edges']} from overrides; "
          f"{len(report['superseded'])} manifest source(s) superseded by glue; "
          f"{sum(len(v) for v in report['missing'].values())} consumer port(s) in "
          f"{len(report['missing'])} block(s) without a source; "
          f"{len(report['redundant'])} redundant override(s)")
    if args.findings:
        with open(SPEC_PATH) as f:
            rev = json.load(f).get("revision")
        fs = to_findings(report, rev)
        os.makedirs(os.path.dirname(os.path.abspath(args.findings)), exist_ok=True)
        with open(args.findings, "w") as f:
            json.dump({"$schema": "validation-findings/1",
                       "generated_by": "integration_map_gen.py",
                       "findings": fs}, f, indent=2)
        print(f"  wrote {len(fs)} finding(s) -> {os.path.relpath(args.findings, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
