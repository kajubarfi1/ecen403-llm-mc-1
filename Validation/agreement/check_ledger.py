#!/usr/bin/env python3
"""
check_ledger.py — for every check: has it been seen to FIRE, and to stay SILENT?
=================================================================================
A check is trustworthy once it has done both: killed something that was
wrong, and stayed quiet on something that was right. This gathers the
evidence that already exists, per check, and says where it is missing.

Checks
  assertion   every generated a_<ID> (sva/generated)
  rule        every (checker model, rule id) pair — COVERS of each checker
  predictor   every exact predictor

FIRED (it can catch a fault)
  seeded      reports/faults/fault_matrix.json — a seeded design fault it detected
  repaired    reports/repairs/repair_matrix.json — it fired on the drop and went
              silent when that defect alone was repaired: a true positive
  formal-cex  a JasperGold counterexample for the property
  gate        accepted by a gate whose violating traces it caught (synthetic)

SILENT (it does not fire on correct behaviour)
  known-good  UberDDR3 + Micron model: assertions at the pins, path checkers
              on its host/pin streams
  repaired    it passed on real traffic through the repaired copy of the drop
  passing     it passes on a path of the current drop
  proven      JasperGold proved the property for all inputs
  agreement   an independently generated second model agrees on every trace
  gate        silent on the gate's legal traces (synthetic)

`gate` evidence is synthetic and `agreement` is correlated, so neither
closes a cell on its own: a check is CLOSED only with non-synthetic evidence
on both sides. A check that fired on the known-good design is a FALSE
POSITIVE and is listed first.

Usage:
    python3 Validation/agreement/check_ledger.py
"""
import glob, json, os, re, subprocess, sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
V = os.path.join(ROOT, "Validation")
sys.path.insert(0, os.path.join(V, "txn"))
from txn_contract import (load_predictor_module, find_model_classes,  # noqa: E402
                          TransactionPredictor, LegalityChecker)
OUT = os.path.join(V, "reports", "check_ledger.json")


def load(p, d=None):
    try:
        with open(p) as f:
            return json.load(f)
    except Exception:
        return d


def models():
    out = []
    for f in sorted(glob.glob(os.path.join(V, "predictors", "*.py"))):
        mod = load_predictor_module(f)
        name = os.path.basename(f)[:-3]
        c = find_model_classes(mod, LegalityChecker)
        if c:
            out.append((name, "checker", list(c[0].COVERS), f))
            continue
        c = find_model_classes(mod, TransactionPredictor)
        if c:
            out.append((name, "predictor", [], f))
    return out


def stage_results(report_dir):
    """{model_name: [(path, verdict, summary, stage_dict)]} from path reports."""
    out = {}
    for f in sorted(glob.glob(os.path.join(report_dir, "*_report.json"))):
        r = load(f, {})
        if r.get("derived_from"):
            continue
        for s in r.get("stages", []):
            if not s.get("model"):
                continue
            name = os.path.basename(s["model"])[:-3]
            out.setdefault(name, []).append((r["path"], s["verdict"], s.get("summary", ""),
                                             s, r.get("observed_trace")))
    return out


def rule_ids_fired(stage, trace):
    """Rule ids a failing checker stage reported (full scoreboard output)."""
    if not trace or not os.path.exists(os.path.join(ROOT, trace)):
        text = "\n".join(stage.get("detail", []))
    else:
        r = subprocess.run(["python3", "Validation/txn/scoreboard.py", "--scope", stage["scope"],
                            "--strategy", "invariant", "--trace", trace, "--model", stage["model"]],
                           cwd=ROOT, capture_output=True, text=True)
        text = r.stdout
    return set(re.findall(r"^\s*([A-Z]+_\d{3})\b", text, re.M))


def main() -> int:
    fm = load(os.path.join(V, "reports", "faults", "fault_matrix.json"), {"rows": []})
    rm = load(os.path.join(V, "reports", "repairs", "repair_matrix.json"), {"rows": []})
    kg = load(sorted(glob.glob(os.path.join(V, "reports", "uberddr3", "known_good_*.json")))[-1], {}) \
        if glob.glob(os.path.join(V, "reports", "uberddr3", "known_good_*.json")) else {}
    kgp = load(os.path.join(V, "reports", "uberddr3", "path_checkers_known_good.json"), {"rows": []})
    ag = load(os.path.join(V, "reports", "model_agreement.json"), {"rows": []})
    # formal: best verdict per property across runs. A proof under an
    # abstraction (stopat) is sound and counts; a cex under one may be
    # spurious (the runner marks it with a note) and is not evidence
    formal, formal_note = {}, {}
    rank = {"proven": 3, "bounded_proven": 2, "cex": 1, "undetermined": 0}
    for f in sorted(glob.glob(os.path.join(V, "reports", "formal", "*.json"))):
        doc = load(f, {})
        abstracted = bool(doc.get("abstractions"))
        for p in doc.get("results", []):
            s = p.get("short", "")
            if not s.startswith("a_"):
                continue
            st = p.get("status")
            if st == "cex" and p.get("note"):
                continue
            if rank.get(st, -1) > rank.get(formal.get(s), -1):
                formal[s] = st
                formal_note[s] = (" (" + ", ".join(a["stopat"] for a in doc["abstractions"])
                                  + " cut)") if abstracted else ""
    pins = set(re.findall(r"\b(a_[A-Z]+_\d+)\s*:", open(os.path.join(
        V, "refdesigns", "uberddr3", "generated", "cmd_gen_sva_pins.sv")).read())) \
        if os.path.exists(os.path.join(V, "refdesigns", "uberddr3", "generated", "cmd_gen_sva_pins.sv")) else set()

    # --- fired evidence -----------------------------------------------------
    seeded = {}
    for r in fm["rows"]:
        if not r.get("killed"):
            continue
        for k in list(r.get("new", {})) + list(r.get("grew", {})) + list(r.get("fewer_matched", {})):
            seeded.setdefault(k, []).append(r["fault"])
    repaired_fired = {}
    for r in rm["rows"]:
        for k in list(r.get("silenced_expected", {})) + list(r.get("silenced_other", {})):
            repaired_fired.setdefault(k, set()).add(r["repair"])

    repairs = sorted({r["repair"] for r in rm["rows"] if not r.get("error")})
    top = repairs[-1] if repairs else None
    rep_stage = stage_results(os.path.join(V, "reports", "repairs", top)) if top else {}
    cur_stage = stage_results(os.path.join(V, "reports", "paths"))
    agree = {r["scope"]: r for r in ag["rows"]}

    rows = []

    def add(kind, name, check, fired, silent, fp=None, note=""):
        hard_f = [x for x in fired if not x.startswith("gate")]
        hard_s = [x for x in silent if not x.startswith(("gate", "agreement"))]
        status = ("FALSE POSITIVE" if fp else
                  "closed" if hard_f and hard_s else
                  "fires only" if hard_f else
                  "silent only" if hard_s else "synthetic only")
        rows.append({"kind": kind, "model": name, "check": check, "fired": fired,
                     "silent": silent, "false_positive": fp, "status": status, "note": note})

    # assertions
    for f in sorted(glob.glob(os.path.join(V, "sva", "generated", "*_sva.sv"))):
        for a in re.findall(r"\b(a_[A-Z]+_\d+(?:_\w+)?)\s*:", open(f).read()):
            fired, silent = [], []
            if f"assert:{a}" in seeded:
                fired.append("seeded: " + ", ".join(sorted(set(seeded[f"assert:{a}"]))[:2]))
            if f"assert:{a}" in repaired_fired:
                fired.append("repaired: " + ", ".join(sorted(repaired_fired[f"assert:{a}"])))
            if formal.get(a) == "cex":
                fired.append("formal-cex")
            if kg.get("sanity_mutation", {}).get("observed", {}).get(a):
                fired.append("seeded: UberDDR3 spec mutation")
            if a in pins and kg.get("our_assertion_failures") == 0:
                silent.append(f"known-good: UberDDR3, {kg.get('commands_observed')} commands")
            if formal.get(a) in ("proven", "bounded_proven"):
                silent.append(formal[a].replace("_", " ") + formal_note.get(a, ""))
            add("assertion", os.path.basename(f)[:-3], a, fired, silent)

    # models
    kgrows = {os.path.basename(r["model"])[:-3]: r for r in kgp["rows"]
              if "second_opinion" not in r["model"]}
    for name, kind, covers, path in models():
        scope = name.rsplit("_", 1)[0]
        a = agree.get(scope)
        ag_ev = ([f"agreement: second model, {a['agree']}/{a['traces']} traces"]
                 if a and a["traces"] and a["disagree"] == 0 else [])
        ag_note = (f"second model DISAGREES on {a['disagree']}/{a['traces']} traces"
                   if a and a["disagree"] else "")
        if kind == "predictor":
            stage = scope
            fired, silent = ["gate"], ["gate"] + ag_ev
            for k in (f"stage:{stage}", f"matched:{stage}"):
                if k in seeded:
                    fired.append("seeded: " + ", ".join(sorted(set(seeded[k]))[:2]))
                    break
            for label, table in (("repaired", rep_stage), ("passing", cur_stage)):
                ok = [p for p, v, s, _, _ in table.get(name, []) if v == "pass"]
                if ok:
                    m = re.search(r"matched=(\d+)/(\d+)", next(
                        s for p, v, s, _, _ in table[name] if v == "pass"))
                    silent.append(f"{label}: {len(ok)} path(s)"
                                  + (f", e.g. {m.group(0)}" if m else ""))
            add("predictor", name, "exact prediction", fired, silent, note=ag_note)
            continue
        for rid in covers:
            fired, silent, fp = ["gate"], ["gate"] + ag_ev, None
            if f"id:{rid}" in seeded:
                fired.append("seeded: " + ", ".join(sorted(set(seeded[f"id:{rid}"]))[:2]))
            if f"id:{rid}" in repaired_fired:
                fired.append("repaired: " + ", ".join(sorted(repaired_fired[f"id:{rid}"])))
            k = kgrows.get(name)
            if k and not k.get("error"):
                if rid in k["by_rule"]:
                    fp = f"fires {k['by_rule'][rid]['count']}x on UberDDR3: {k['by_rule'][rid]['first'][:140]}"
                else:
                    silent.append(f"known-good: UberDDR3, {kgp.get('host_requests')} requests")
            for label, table in (("repaired", rep_stage), ("passing", cur_stage)):
                n = 0
                for p, v, s, st, tr in table.get(name, []):
                    if v == "pass" or (v == "fail" and rid not in rule_ids_fired(st, tr)):
                        n += 1
                if n:
                    silent.append(f"{label}: {n} path(s)")
            add("rule", name, rid, fired, silent, fp, ag_note)

    order = {"FALSE POSITIVE": 0, "synthetic only": 1, "fires only": 2, "silent only": 3, "closed": 4}
    rows.sort(key=lambda r: (order[r["status"]], r["kind"], r["model"], r["check"]))
    tally = {}
    for r in rows:
        tally[r["status"]] = tally.get(r["status"], 0) + 1
    print(f"  {len(rows)} checks: " + ", ".join(f"{v} {k}" for k, v in sorted(tally.items(), key=lambda x: order[x[0]])))
    for r in rows:
        if r["status"] == "closed":
            continue
        print(f"  {r['status']:15} {r['kind']:9} {r['model'][:34]:34} {r['check']}")
        if r["false_positive"]:
            print(f"      {r['false_positive'][:150]}")
        if r["note"]:
            print(f"      {r['note']}")
    with open(OUT, "w") as f:
        json.dump({"$schema": "validation-check-ledger/1",
                   "generated_utc": datetime.utcnow().isoformat() + "Z",
                   "repair_stack": repairs, "tally": tally, "rows": rows}, f, indent=2)
    print(f"  wrote {os.path.relpath(OUT, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
