#!/usr/bin/env python3
"""
file_scope_findings.py — run a scope's checking and file what it found
=======================================================================
Ties the pieces together for one scope: load the observed trace, replay it
through the accepted predictor, classify the disagreements, and write the
result to the versioned outbox for the owning subsystem to pick up.

    observed.jsonl + accepted predictor
        -> scoreboard
        -> deterministic classification
        -> Validation/findings/outbox/<spec_revision>/<scope>_findings.json

Usage:
    python3 Validation/findings/file_scope_findings.py --scope config_regs
"""

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))

from txn_contract import (load_trace, load_predictor_module, find_model_classes,
                          TransactionPredictor, strategy_for_scope)
from scoreboard import Scoreboard
import findings as F

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--trace")
    ap.add_argument("--predictor")
    ap.add_argument("--rtl-drop", default="PHASE1RTL@local")
    args = ap.parse_args()

    scope = args.scope
    trace_path = args.trace or os.path.join(
        ROOT, "Validation", "txn", "generated", f"{scope}_observed.jsonl")
    pred_path = args.predictor or os.path.join(
        ROOT, "Validation", "predictors", f"{scope}_predictor.py")

    for p in (trace_path, pred_path):
        if not os.path.exists(p):
            print(f"missing: {p}", file=sys.stderr)
            return 2

    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]

    trace = load_trace(trace_path)
    strategy = strategy_for_scope(scope, PATH_DEFS, default="exact")
    cls = find_model_classes(load_predictor_module(pred_path),
                             TransactionPredictor)[0]
    result = Scoreboard(strategy, cls(spec), scope=scope).run(trace)

    print(f"  scope     : {scope}")
    print(f"  trace     : {len(trace)} transactions")
    print(f"  predictor : {cls.__name__}")
    print(f"  verdict   : {result.summary()}\n")

    found = F.find_observation_gaps(trace, catalog, scope)
    found += F.classify_mismatches(result.mismatches, spec, schemas, scope)

    if not found:
        print("  no findings — nothing to route.")
        return 0

    dest = F.file_findings(found, spec.get("revision", "unknown"),
                           args.rtl_drop, scope)

    for f in found:
        owner, why = F.ROUTING[f.kind]
        print(f"  [{f.kind}] -> {owner}   ({f.occurrences} occurrence(s))")
        print(f"      {f.title}")
        print(f"      {why}")
        if f.vplan_items:
            print(f"      vplan: {', '.join(f.vplan_items)}")
        if f.question:
            print(f"      QUESTION: {f.question[:160]}...")
        print()

    print(f"  filed -> {os.path.relpath(dest, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
