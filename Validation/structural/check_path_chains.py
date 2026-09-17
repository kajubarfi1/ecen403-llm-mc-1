#!/usr/bin/env python3
"""
check_path_chains.py — can each composed path actually be built as a chain?
============================================================================
A composed path's predictor is the composition of its stages' predictors.
That only works if the stages actually connect: every stage must consume a
stream the previous stage produces. This validates that BEFORE anyone burns
an LLM call or a simulation on a chain that silently drops everything at the
first broken hop.

Sits beside connectivity_checker.py and width_conformance.py, one level up:
connectivity asks "are the ports wired", width asks "are they the right
shape", this asks "do the declared transaction streams compose".

Stage fusion: some blocks cannot stand alone as a stage — cmd_queue has no
output stream (its outputs are 16-deep queue STATE), and bank_tracker's
outputs are per-bank state. In a chain those blocks fuse with the block that
turns their state back into a stream: [cmd_queue+scheduler] is one stage
whose input is cq_enq and whose output is sched_cmd. The fusion is reported
explicitly, because a fused stage needs a JOINT predictor and someone has to
know to build one.

Aliases: sched_cmd and sched_in are one stream under two names (the same
wires, observed from either end); `same_stream_as` in the catalog declares
that, and a hop across the alias counts as connected.

Usage:
    python3 Validation/structural/check_path_chains.py
    python3 Validation/structural/check_path_chains.py --path path_01_write_cmd
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
SCHEMAS = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
PATHS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
PREDICTORS = os.path.join(ROOT, "Validation", "predictors")


def load():
    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    with open(PATHS) as f:
        paths = json.load(f)["paths"]
    return catalog, paths


def produces(block, catalog):
    return sorted({i for i, d in catalog.items()
                   if (d["block"] == block and d.get("role") == "response")
                   or block in d.get("producers", [])})


def consumes(block, catalog):
    return sorted({i for i, d in catalog.items()
                   if (d["block"] == block and d.get("role") == "request")
                   or block in d.get("consumers", [])})


def connected(out_streams, in_streams, catalog):
    """Streams linking a producer set to a consumer set, aliases included."""
    links = []
    for o in out_streams:
        # None must never enter the name set: with two non-aliased streams,
        # `alias(i) in {o, None}` is True for every pair, which linked
        # everything to everything and made BROKEN unreportable. A checker
        # that cannot fail is not a checker.
        names = {o}
        o_alias = catalog.get(o, {}).get("same_stream_as")
        if o_alias:
            names.add(o_alias)
        for i in in_streams:
            i_alias = catalog.get(i, {}).get("same_stream_as")
            if i in names or (i_alias is not None and i_alias in names):
                links.append((o, i))
    return links


def build_stages(blocks, catalog):
    """Fuse blocks into stages: a stage ends at the first block that produces
    a stream. Returns (stages, error) where each stage is
    {blocks, inputs, outputs}."""
    stages, run = [], []
    for b in blocks:
        run.append(b)
        outs = sorted({o for blk in run for o in produces(blk, catalog)})
        if outs:
            ins = sorted({i for blk in run for i in consumes(blk, catalog)})
            stages.append({"blocks": list(run), "inputs": ins, "outputs": outs})
            run = []
    if run:
        return stages, (f"trailing block(s) {run} produce no stream — the "
                        f"chain has no way to observe what they did")
    return stages, None


def stage_kind(stage, catalog):
    """What artifact does this stage need? The catalog decides, as data:

    autonomous  every output stream is time-driven (e.g. a refresh timer).
                An order-only predictor cannot know how many events occur, so
                the stream is OBSERVED and fed downstream; its pacing is SVA's
                job. No predictor is required — requiring one would demand an
                artifact that cannot be correct.
    invariant   some output stream is order-nondeterministic under the spec's
                policy (e.g. FR-FCFS). Exact stream comparison is unsound, so
                the stage needs an agent-generated invariant CHECKER (graded
                by LegalityCheckerGate), not an exact predictor.
    exact       otherwise: an exact transaction predictor.
    """
    outs = stage["outputs"]
    if outs and all(catalog.get(o, {}).get("autonomous") for o in outs):
        return "autonomous"
    if any(catalog.get(o, {}).get("order_nondeterministic") for o in outs):
        return "invariant"
    return "exact"


def stage_artifact(stage, kind):
    if kind == "autonomous":
        return None
    base = "_".join(stage["blocks"])
    suffix = "_checker.py" if kind == "invariant" else "_predictor.py"
    return os.path.join(PREDICTORS, base + suffix)


def check_path(p, catalog):
    blocks = p["blocks"]
    stages, err = build_stages(blocks, catalog)
    report = {"id": p["id"], "strategy": p["check_strategy"],
              "stages": stages, "hops": [], "chains": err is None,
              "error": err, "missing_predictors": []}
    if err:
        return report

    for a, b in zip(stages, stages[1:]):
        links = connected(a["outputs"], b["inputs"], catalog)
        report["hops"].append({
            "from": a["blocks"], "to": b["blocks"],
            "links": links, "ok": bool(links)})
        if not links:
            report["chains"] = False

    for st in stages:
        kind = stage_kind(st, catalog)
        st["kind"] = kind
        artifact = stage_artifact(st, kind)
        if artifact is None or os.path.exists(artifact):
            continue
        name = "+".join(st["blocks"])
        what = ("invariant checker" if kind == "invariant"
                else "predictor")
        joint = (" (JOINT stage — the fused blocks share state and need one "
                 "model together)" if len(st["blocks"]) > 1 else "")
        report["missing_predictors"].append(
            f"{name}: {what} ({os.path.basename(artifact)}){joint}")
    return report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", help="check one path id")
    ap.add_argument("--all-strategies", action="store_true",
                    help="also report non-composed paths")
    args = ap.parse_args()

    catalog, paths = load()
    targets = [p for p in paths
               if (args.path and p["id"] == args.path)
               or (not args.path and (args.all_strategies
                                      or p["check_strategy"] == "composed"))]
    if not targets:
        print(f"no path matches", file=sys.stderr)
        return 2

    all_ok, missing = True, set()
    for p in targets:
        r = check_path(p, catalog)
        mark = "CHAINS" if r["chains"] else "BROKEN"
        print(f"\n  {r['id']}  [{r['strategy']}]  {mark}")
        for st in r["stages"]:
            tag = "+".join(st["blocks"])
            note = {"autonomous": "  (autonomous — observed, SVA owns pacing)",
                    "invariant": "  (order-nondeterministic — invariant "
                                 "checker, not exact predictor)",
                    }.get(st.get("kind"), "")
            print(f"      stage [{tag}]  in={st['inputs'] or '—'} "
                  f"out={st['outputs'] or '—'}{note}")
        for h in r["hops"]:
            link = ", ".join(f"{o}->{i}" for o, i in h["links"]) or "NO LINK"
            flag = "" if h["ok"] else "   <-- BROKEN HOP"
            print(f"      {'+'.join(h['from'])} => {'+'.join(h['to'])}: "
                  f"{link}{flag}")
        if r["error"]:
            print(f"      ERROR: {r['error']}")
        if r["missing_predictors"]:
            for m in r["missing_predictors"]:
                print(f"      needs predictor: {m}")
                missing.add(m)
        all_ok &= r["chains"]

    verdict = ("every checked path chains structurally" if all_ok
               else "some paths do not chain — fix the catalog hops above")
    print(f"\n  {verdict}")
    if missing:
        print(f"  stage predictors still to generate: {len(missing)}")
        for m in sorted(missing):
            print(f"    {m}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
