#!/usr/bin/env python3
"""
oracle_agreement.py — do independent checks of the same rule agree, run by run?
===============================================================================
Several rules are watched by more than one oracle built a different way:

  rule        an agent-generated checker reading the transaction trace
  assertion   a generated SVA property counting cycles on the pins
  formal      the same property under JasperGold (all inputs, not one run)

On any one simulation the checker and the assertion for the same taxonomy id
should either both fire or both stay silent. Where exactly one fires, one of
them is wrong (or they define the rule differently) and the run is listed.
Rules with a single oracle are listed too: that is where a second one would
add the most.

Usage:
    python3 Validation/agreement/oracle_agreement.py
"""
import glob, json, os, re, sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
V = os.path.join(ROOT, "Validation")
sys.path.insert(0, os.path.join(V, "faults"))
sys.path.insert(0, os.path.join(V, "txn"))
from seed_faults import signature  # noqa: E402
from txn_contract import load_predictor_module, find_model_classes, LegalityChecker  # noqa: E402

DIRS = ["reports/paths", "reports/repairs/baseline"] + sorted(
    os.path.relpath(d, V) for d in glob.glob(os.path.join(V, "reports", "repairs", "R*"))
    if os.path.isdir(d))
OUT = os.path.join(V, "reports", "oracle_agreement.json")


def main() -> int:
    rule_ids = set()
    for f in glob.glob(os.path.join(V, "predictors", "*_checker.py")):
        c = find_model_classes(load_predictor_module(f), LegalityChecker)
        if c:
            rule_ids |= set(c[0].COVERS)
    sva_ids = set()
    for f in glob.glob(os.path.join(V, "sva", "generated", "*_sva.sv")):
        sva_ids |= {a[2:] for a in re.findall(r"\b(a_[A-Z]+_\d+)\s*:", open(f).read())}
    formal = {}
    for f in sorted(glob.glob(os.path.join(V, "reports", "formal", "*.json"))):
        for p in json.load(open(f)).get("results", []):
            if p.get("short", "").startswith("a_"):
                formal[p["short"][2:]] = p.get("status")

    rows = []
    for tid in sorted(rule_ids | sva_ids):
        oracles = [o for o, have in (("rule", tid in rule_ids), ("assertion", tid in sva_ids),
                                     ("formal", tid in formal)) if have]
        both = agree_fire = agree_silent = 0
        split = []
        if tid in rule_ids and tid in sva_ids:
            for d in DIRS:
                for rp in sorted(glob.glob(os.path.join(V, d, "*_report.json"))):
                    rep = json.load(open(rp))
                    if rep.get("derived_from"):
                        continue
                    # only runs whose checkers include this rule
                    covers = set()
                    for s in rep.get("stages", []):
                        if s.get("model") and os.path.exists(s["model"]) and s["model"].endswith("_checker.py"):
                            c = find_model_classes(load_predictor_module(s["model"]), LegalityChecker)
                            covers |= set(c[0].COVERS) if c else set()
                    if tid not in covers:
                        continue
                    sig = signature(os.path.join(V, d), rep["path"]) or {}
                    r, a = sig.get(f"id:{tid}", 0), sig.get(f"assert:a_{tid}", 0)
                    both += 1
                    if r and a:
                        agree_fire += 1
                    elif not r and not a:
                        agree_silent += 1
                    else:
                        split.append({"run": f"{d}/{rep['path']}", "rule": r, "assertion": a})
        rows.append({"id": tid, "oracles": oracles, "formal": formal.get(tid),
                     "runs_compared": both, "both_fire": agree_fire,
                     "both_silent": agree_silent, "split": split})
    print(f"  {'id':12} oracles                   formal        runs  both-fire both-silent split")
    for r in rows:
        print(f"  {r['id']:12} {'+'.join(r['oracles']):25} {str(r['formal'] or '-'):13} "
              f"{r['runs_compared']:>4} {r['both_fire']:>9} {r['both_silent']:>11} {len(r['split']):>5}")
        for s in r["split"][:4]:
            print(f"      split: {s['run']}  rule={s['rule']} assertion={s['assertion']}")
    single = [r["id"] for r in rows if len([o for o in r["oracles"] if o != "formal"]) == 1
              and "formal" not in r["oracles"]]
    print(f"  single-oracle rules (no second opinion of any kind): {single}")
    with open(OUT, "w") as f:
        json.dump({"$schema": "validation-oracle-agreement/1",
                   "generated_utc": datetime.utcnow().isoformat() + "Z",
                   "rows": rows, "single_oracle": single}, f, indent=2)
    print(f"  wrote {os.path.relpath(OUT, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
