#!/usr/bin/env python3
"""
model_agreement.py — do two independently generated models agree on real traces?
================================================================================
Runs the primary model (predictors/) and its second opinion
(predictors/second_opinion/) on every recorded trace that carries the
scope's input streams, and compares what they say:

  predictor   the predicted output transactions, stream by stream, in order
  checker     the set of violations (taxonomy id + the transaction blamed)

Agreement is weak evidence (same spec, same model family). A DISAGREEMENT
means at least one model is wrong about the spec, and it is found without
any reference design: the first differing transaction is printed with both
answers so it can be settled against the spec clause.

Usage:
    python3 Validation/agreement/model_agreement.py
"""
import argparse, collections, glob, json, os, sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
from txn_contract import (load_trace, load_predictor_module, find_model_classes,  # noqa: E402
                          TransactionPredictor, LegalityChecker)
import scoreboard as SB  # noqa: E402

PRIMARY = os.path.join(ROOT, "Validation", "predictors")
SECOND = os.path.join(PRIMARY, "second_opinion")
SPEC = os.path.join(ROOT, "Validation", "spec", "llmmc_microarchitecturespec_filled.json")
SPEC = os.environ.get("VALIDATION_SPEC", SPEC)   # the spec the drop was generated from, when it is not the default
OUT = os.path.join(ROOT, "Validation", "reports", "model_agreement.json")
TRACE_GLOBS = ["Validation/reports/paths/*_observed.jsonl",
               "Validation/reports/repairs/*/*_observed.jsonl"]


def load_model(path, spec):
    mod = load_predictor_module(path)
    for base in (TransactionPredictor, LegalityChecker):
        cls = find_model_classes(mod, base)
        if cls:
            return cls[0](spec), ("predictor" if base is TransactionPredictor else "checker")
    raise SystemExit(f"no model class in {path}")


def clean(trace):
    return [t for t in trace if t.kind != "reset"
            and not any(v is None for v in t.fields.values())]


def run_predictor(m, trace):
    m.reset()
    out = []
    for t in trace:
        if t.iface in m.INPUT_IFACES:
            out += m.process(t) or []
    out += m.drain() or []
    by = collections.defaultdict(list)
    for t in out:
        t = SB._apply_dont_care(t) if hasattr(SB, "_apply_dont_care") else t
        by[t.iface].append((t.kind, tuple(sorted(t.fields.items()))))
    return by


def run_checker(m, trace):
    m.reset()
    ifs = set(m.INPUT_IFACES) | set(m.OUTPUT_IFACES)
    vs = []
    for t in trace:
        if t.iface in ifs:
            vs += m.observe(t) or []
    vs += m.final() or []
    c = collections.Counter()
    first = {}
    for v in vs:
        tid = v.taxonomy_id or v.rule
        seq = v.txns[0].seq if v.txns else -1
        c[(tid, seq)] += 1
        first.setdefault(tid, str(v)[:200])
    return c, first


def compare_pred(a, b):
    diffs = []
    for iface in sorted(set(a) | set(b)):
        la, lb = a.get(iface, []), b.get(iface, [])
        n = sum(1 for x, y in zip(la, lb) if x != y) + abs(len(la) - len(lb))
        if n:
            i = next((k for k, (x, y) in enumerate(zip(la, lb)) if x != y),
                     min(len(la), len(lb)))
            diffs.append({"iface": iface, "differing": n, "of": max(len(la), len(lb)),
                          "first_index": i,
                          "primary": _fmt(la[i]) if i < len(la) else "(nothing)",
                          "second": _fmt(lb[i]) if i < len(lb) else "(nothing)"})
    return diffs


def _fmt(x):
    kind, fields = x
    return kind + " " + " ".join(f"{k}={v:#x}" if isinstance(v, int) else f"{k}={v}"
                                 for k, v in fields)


def compare_chk(a, b):
    """Per rule id: a disagreement is a different NUMBER of violations. Two
    checkers that file the same count under a rule but blame different
    witness transactions (one points at the command, the other at the
    request that asked for the row) agree about the design; that is
    recorded as `attribution_differs`, not as a disagreement (2026-10-08:
    SCHED_004 110 vs 110 on 15 traces had counted as 15 disagreements)."""
    (ca, fa), (cb, fb) = a, b
    ids = sorted({k[0] for k in ca} | {k[0] for k in cb})
    diffs = []
    for tid in ids:
        sa = {k for k in ca if k[0] == tid}
        sb = {k for k in cb if k[0] == tid}
        if sa == sb:
            continue
        na, nb = sum(ca[k] for k in sa), sum(cb[k] for k in sb)
        if na == nb:
            diffs.append({"id": tid, "attribution_differs": True, "count": na,
                          "primary_example": fa.get(tid), "second_example": fb.get(tid)})
            continue
        diffs.append({"id": tid, "primary_only": len(sa - sb),
                      "second_only": len(sb - sa), "both": len(sa & sb),
                      "primary_count": na, "second_count": nb,
                      "primary_example": fa.get(tid), "second_example": fb.get(tid)})
    return diffs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope")
    args = ap.parse_args()
    with open(SPEC) as f:
        spec = json.load(f)
    traces = sorted({p for g in TRACE_GLOBS for p in glob.glob(os.path.join(ROOT, g))})
    loaded = {p: clean(load_trace(p)) for p in traces}
    rows = []
    for f2 in sorted(glob.glob(os.path.join(SECOND, "*.py"))):
        name = os.path.basename(f2)
        f1 = os.path.join(PRIMARY, name)
        scope = name.rsplit("_", 1)[0]
        if (args.scope and scope != args.scope) or not os.path.exists(f1):
            continue
        m1, kind = load_model(f1, spec)
        m2, _ = load_model(f2, spec)
        ran = agree = 0
        disagreements, attribution = [], []
        for p, tr in loaded.items():
            if not any(t.iface in m1.INPUT_IFACES for t in tr):
                continue
            try:
                if kind == "predictor":
                    d = compare_pred(run_predictor(m1, tr), run_predictor(m2, tr))
                else:
                    d = compare_chk(run_checker(m1, tr), run_checker(m2, tr))
            except Exception as e:
                d = [{"error": f"{type(e).__name__}: {e}"}]
            ran += 1
            subst = [x for x in d if not x.get("attribution_differs")]
            if subst:
                disagreements.append({"trace": os.path.relpath(p, ROOT), "diffs": subst})
            else:
                agree += 1
                if d:
                    attribution.append({"trace": os.path.relpath(p, ROOT), "diffs": d})
        rows.append({"scope": scope, "kind": kind, "traces": ran, "agree": agree,
                     "disagree": ran - agree, "attribution_only": len(attribution),
                     "disagreements": disagreements[:6], "attribution": attribution[:3]})
    print(f"  {'scope':34} kind       traces agree disagree  (attribution-only)")
    for r in rows:
        print(f"  {r['scope']:34} {r['kind']:10} {r['traces']:>5} {r['agree']:>5} {r['disagree']:>8}  {r.get('attribution_only', 0):>6}")
        for d in r["disagreements"][:1]:
            for x in d["diffs"][:3]:
                if "error" in x:
                    print(f"      ERROR {x['error']}")
                elif "iface" in x:
                    print(f"      {x['iface']}: {x['differing']}/{x['of']} differ; first at [{x['first_index']}]")
                    print(f"         primary: {x['primary'][:110]}")
                    print(f"         second : {x['second'][:110]}")
                else:
                    print(f"      {x['id']}: primary only {x['primary_only']}, second only {x['second_only']}, both {x['both']}")
                    print(f"         primary: {(x['primary_example'] or '-')[:110]}")
                    print(f"         second : {(x['second_example'] or '-')[:110]}")
    with open(OUT, "w") as f:
        json.dump({"$schema": "validation-model-agreement/1",
                   "generated_utc": datetime.utcnow().isoformat() + "Z",
                   "traces": len(traces), "rows": rows}, f, indent=2)
    print(f"  wrote {os.path.relpath(OUT, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
