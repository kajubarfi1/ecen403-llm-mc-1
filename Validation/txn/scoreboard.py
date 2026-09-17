#!/usr/bin/env python3
"""
scoreboard.py — compare what the design did against what should have happened
==============================================================================
The checking engine. Deterministic infrastructure: agent-generated models flow
THROUGH it, they never produce it, because this is the thing that decides
pass/fail.

Input is ONE observed trace — monitors emit every transaction they see on
every bound interface, inputs and outputs mixed in observation order. The
scoreboard partitions that stream using the model's declared interfaces, then
dispatches on the scope's check_strategy:

  exact / composed   replay observed INPUT transactions through the
                     predictor; align its predicted OUTPUT stream against the
                     observed one
  invariant          no prediction; run the whole stream through a
                     LegalityChecker and collect Violations
  observe            the scoreboard has no opinion — monitors and SVA carry
                     the scope entirely

Two deliberate design choices:

  * Timing is never compared. A Txn's time_ns is informational; alignment is
    by order alone. "When" belongs to SVA. This is what lets a predictor be
    derived from the spec without knowing RTL pipeline depths (audit V-06) and
    removes any need for a tolerance window (V-17).

  * Alignment is a diff, not a zip. Walking two lists in lockstep reports one
    real defect as a cascade of false ones the moment a transaction is missing.
    Sequence alignment separates the three distinct failures — wrong value,
    missing output, unexpected output — which is the difference between a
    triage-able report and noise.

Nothing here passes without evidence: a run in which nothing was compared
reports `unknown`, never `pass` (the shape of audit finding V-02).
"""

import difflib
import json
import os
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from txn_contract import (Txn, Violation, TransactionPredictor, LegalityChecker,
                          CHECK_STRATEGIES, STRATEGY_NEEDS_MODEL, RESET_KIND)


# =============================================================================
# Results
# =============================================================================

@dataclass
class Mismatch:
    """One disagreement between prediction and observation."""
    kind: str                       # value | missing | unexpected
    iface: str
    index: int                      # position within that interface's stream
    predicted: Optional[Txn] = None
    observed: Optional[Txn] = None

    def __str__(self):
        if self.kind == "value":
            return (f"{self.iface}[{self.index}] value: "
                    f"predicted {self.predicted} but observed {self.observed}")
        if self.kind == "missing":
            return (f"{self.iface}[{self.index}] missing: predicted "
                    f"{self.predicted} but the design produced nothing")
        return (f"{self.iface}[{self.index}] unexpected: the design produced "
                f"{self.observed} with nothing predicted")

    def to_dict(self):
        return {"kind": self.kind, "iface": self.iface, "index": self.index,
                "predicted": self.predicted.to_dict() if self.predicted else None,
                "observed": self.observed.to_dict() if self.observed else None}


@dataclass
class ScoreboardResult:
    scope: str = ""
    waived_fields: int = 0
    waivers_applied: dict = field(default_factory=dict)
    strategy: str = "exact"
    status: str = "unknown"         # pass | fail | unknown | not_applicable
    reason: str = ""
    predicted_count: int = 0
    observed_count: int = 0
    matched: int = 0
    mismatches: List[Mismatch] = field(default_factory=list)
    violations: List[Violation] = field(default_factory=list)

    @property
    def failed(self):
        return self.status == "fail"

    def summary(self) -> str:
        parts = [f"scope={self.scope or '?'}", f"strategy={self.strategy}",
                 f"status={self.status}"]
        if self.strategy in ("exact", "composed"):
            parts.append(f"matched={self.matched}/{self.predicted_count}")
            if self.waived_fields:
                parts.append(f"WAIVED={self.waived_fields} field comparison(s)")
            by = {}
            for m in self.mismatches:
                by[m.kind] = by.get(m.kind, 0) + 1
            if by:
                parts.append(" ".join(f"{k}={v}" for k, v in sorted(by.items())))
        if self.violations:
            parts.append(f"violations={len(self.violations)}")
        if self.reason:
            parts.append(f"({self.reason})")
        return "  ".join(parts)

    def to_findings(self, spec_revision="unknown", drop_id="unknown") -> list:
        """Emit in the team's agreed cross-subsystem finding schema."""
        out = []
        for m in self.mismatches:
            out.append({
                "source": "validation", "target": "frontend",
                "kind": "rtl_bug",           # triage may reclassify
                "scope": self.scope, "severity": "critical",
                "spec_revision": spec_revision, "rtl_drop": drop_id,
                "detail": str(m), "evidence": m.to_dict(),
                "status": "open",
            })
        for v in self.violations:
            out.append({
                "source": "validation", "target": "frontend",
                "kind": "rtl_bug", "scope": self.scope,
                "severity": v.severity, "taxonomy_id": v.taxonomy_id,
                "spec_revision": spec_revision, "rtl_drop": drop_id,
                "detail": str(v), "evidence": v.to_dict(),
                "status": "open",
            })
        return out


# =============================================================================
# Composition (the `composed` strategy)
# =============================================================================

class CompositePredictor(TransactionPredictor):
    """Chain predictors so one block's outputs are the next block's inputs.

    This is what makes feed-forward paths work without a bespoke whole-path
    model: given per-block predictors, the path predictor is their composition.
    Only valid where the blocks form a pipeline — a feedback loop cannot be
    composed this way, which is exactly why those scopes use `invariant`.
    """

    def __init__(self, stages: List[TransactionPredictor], aliases=None):
        if not stages:
            raise ValueError("CompositePredictor needs at least one stage")
        self.stages = stages
        # Two catalog names may denote ONE stream observed from either end
        # (scheduler.cmd_* and cmd_gen.sched_* are the same wires). The
        # catalog declares that as same_stream_as; between stages the name is
        # rewritten so a producer under one name feeds a consumer under the
        # other. Without this, the handoff silently drops every transaction.
        self.aliases = dict(aliases or {})
        self.INPUT_IFACES = tuple(stages[0].INPUT_IFACES)
        self.OUTPUT_IFACES = tuple(stages[-1].OUTPUT_IFACES)

    def _for_stage(self, txn, stage):
        if txn.iface in stage.INPUT_IFACES:
            return txn
        alias = self.aliases.get(txn.iface)
        if alias and alias in stage.INPUT_IFACES:
            return Txn(alias, txn.kind, dict(txn.fields), txn.seq, txn.time_ns)
        return txn

    def reset(self):
        for s in self.stages:
            s.reset()

    def process(self, txn: Txn) -> List[Txn]:
        current = [txn]
        for stage in self.stages:
            nxt = []
            for t in current:
                nxt.extend(stage.process(self._for_stage(t, stage)))
            current = nxt
            if not current:
                break
        return current

    def drain(self) -> List[Txn]:
        # Drain in order: each stage's leftovers still feed the stages after it.
        current = []
        for i, stage in enumerate(self.stages):
            produced = list(current)
            current = []
            for t in produced:
                current.extend(stage.process(self._for_stage(t, stage)))
            current.extend(stage.drain())
        return current


# =============================================================================
# Alignment
# =============================================================================

def align(predicted: List[Txn], observed: List[Txn], iface: str) -> tuple:
    """Align two ordered transaction streams. Returns (matched, mismatches).

    Uses sequence alignment rather than lockstep comparison so a single
    missing transaction does not cascade into a mismatch on every subsequent
    one. difflib works on the hashable key() — everything except seq/time.
    """
    pk = [t.key() for t in predicted]
    ok = [t.key() for t in observed]
    sm = difflib.SequenceMatcher(a=pk, b=ok, autojunk=False)

    matched = 0
    mismatches: List[Mismatch] = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            matched += (i2 - i1)
        elif tag == "replace":
            # Pair them up positionally; any surplus on either side is a
            # missing or unexpected transaction rather than a wrong value.
            n = min(i2 - i1, j2 - j1)
            for k in range(n):
                mismatches.append(Mismatch("value", iface, i1 + k,
                                           predicted[i1 + k], observed[j1 + k]))
            for k in range(n, i2 - i1):
                mismatches.append(Mismatch("missing", iface, i1 + k,
                                           predicted=predicted[i1 + k]))
            for k in range(n, j2 - j1):
                mismatches.append(Mismatch("unexpected", iface, j1 + k,
                                           observed=observed[j1 + k]))
        elif tag == "delete":
            for k in range(i1, i2):
                mismatches.append(Mismatch("missing", iface, k,
                                           predicted=predicted[k]))
        elif tag == "insert":
            for k in range(j1, j2):
                mismatches.append(Mismatch("unexpected", iface, k,
                                           observed=observed[k]))
    return matched, mismatches


def align_keyed(predicted: List[Txn], observed: List[Txn], iface: str,
                key_field: str) -> tuple:
    """Alignment for interfaces where reorder is legal: match on a field
    (an address or tag) rather than position. Used where the spec permits a
    design to answer out of order."""
    from collections import defaultdict
    pend = defaultdict(list)
    for t in predicted:
        pend[t.fields.get(key_field)].append(t)

    matched = 0
    mismatches: List[Mismatch] = []
    for idx, o in enumerate(observed):
        k = o.fields.get(key_field)
        bucket = pend.get(k)
        if not bucket:
            mismatches.append(Mismatch("unexpected", iface, idx, observed=o))
            continue
        p = bucket.pop(0)
        if p.key() == o.key():
            matched += 1
        else:
            mismatches.append(Mismatch("value", iface, idx, predicted=p, observed=o))
    for k, bucket in pend.items():
        for p in bucket:
            mismatches.append(Mismatch("missing", iface, -1, predicted=p))
    return matched, mismatches


def _apply_waivers(waiverset, predicted, observed):
    """Drop waived fields from BOTH streams before alignment.

    Removing the field from both sides is what makes this an exclusion rather
    than a tolerance: the comparison still demands exact equality on
    everything that remains, and a waived field cannot mask a disagreement in
    a neighbouring one."""
    n = 0

    def strip(txns):
        nonlocal n
        out = []
        for t in txns:
            waived = waiverset.waived_fields(t)
            if not waived:
                out.append(t)
                continue
            n += len(waived)
            out.append(Txn(t.iface, t.kind,
                           {k: v for k, v in t.fields.items() if k not in waived},
                           t.seq, t.time_ns))
        return out

    stripped_pred = strip(predicted)
    half = n
    stripped_obs = strip(observed)
    # n counted strips on both streams; a comparison is one pair, so report
    # the observed-side count — the number of checks actually given up.
    return stripped_pred, stripped_obs, n - half


# =============================================================================
# The scoreboard
# =============================================================================

class Scoreboard:
    """Compare an observed trace against a model, per the scope's strategy.

    reorder_keys: {iface: field_name} for interfaces where the design may
    legally answer out of order. Omitted interfaces are matched in order.
    """

    def __init__(self, strategy: str = "exact", model=None, scope: str = "",
                 reorder_keys: Optional[Dict[str, str]] = None,
                 waivers=None):
        if strategy not in CHECK_STRATEGIES:
            raise ValueError(f"unknown strategy {strategy!r}; "
                             f"expected one of {list(CHECK_STRATEGIES)}")
        self.strategy = strategy
        self.model = model
        self.scope = scope
        self.reorder_keys = reorder_keys or {}
        # Declared, attributed exclusions from comparison. A waived field is
        # not compared — and is reported as waived, never folded into the
        # matched count, because a waived check is one the design did not pass.
        self.waivers = waivers

        need = STRATEGY_NEEDS_MODEL[strategy]
        if need == "predictor" and not isinstance(model, TransactionPredictor):
            raise TypeError(f"strategy {strategy!r} needs a TransactionPredictor, "
                            f"got {type(model).__name__}")
        if need == "checker" and not isinstance(model, LegalityChecker):
            raise TypeError(f"strategy {strategy!r} needs a LegalityChecker, "
                            f"got {type(model).__name__}")

    # -- main entry -----------------------------------------------------------

    def run(self, trace: List[Txn]) -> ScoreboardResult:
        r = ScoreboardResult(scope=self.scope, strategy=self.strategy)

        if self.strategy == "observe":
            r.status = "not_applicable"
            r.reason = ("autonomous scope: monitors and SVA carry the check, "
                        "the scoreboard has nothing to compare")
            r.observed_count = len(trace)
            return r

        if not trace:
            r.status = "unknown"
            r.reason = "empty trace — nothing was observed, so nothing was checked"
            return r

        # X-valued observations: the design drove an unknown onto a monitored
        # field. That is a defect in its own right (uninitialised state
        # escaping to an interface), reported here — and the transaction is
        # withheld from the model, which can do nothing meaningful with a
        # value that does not exist.
        xs = [t for t in trace if any(v is None for v in t.fields.values())]
        if xs:
            modeled = (set(self.model.INPUT_IFACES)
                       | set(self.model.OUTPUT_IFACES)) if self.model else None
            for t in xs:
                if modeled is not None and t.iface not in modeled:
                    continue
                bad = [k for k, v in t.fields.items() if v is None]
                r.violations.append(Violation(
                    rule="x_value",
                    detail=f"{t.iface}.{t.kind} seq={t.seq} carries "
                           f"X/Z on {bad} — the design drove an undefined "
                           f"value onto a monitored interface",
                    taxonomy_id="DATA_001", txns=[t]))
            trace = [t for t in trace if t not in xs]

        if self.strategy == "invariant":
            out = self._run_invariant(trace, r)
        else:
            out = self._run_predictive(trace, r)
        if r.violations and out.status == "pass":
            out.status = "fail"
        return out

    # -- invariant ------------------------------------------------------------

    def _run_invariant(self, trace, r):
        self.model.reset()
        for t in trace:
            if t.kind == RESET_KIND:
                self.model.reset()
                continue
            out = self.model.observe(t)
            if out:
                r.violations.extend(out)
        r.violations.extend(self.model.final() or [])
        r.observed_count = len(trace)

        seen = {t.iface for t in trace}
        # A checker is relevant if the trace touches EITHER side it models: a
        # full-controller checker may declare only output streams (it judges
        # the command stream's legality, consuming no inputs), and requiring
        # input traffic would report those runs as 'unknown' forever.
        modeled = set(self.model.INPUT_IFACES) | set(self.model.OUTPUT_IFACES)
        if not (seen & modeled):
            r.status = "unknown"
            r.reason = (f"no transactions on any interface this checker models "
                        f"({sorted(modeled)}); observed {sorted(seen)}")
            return r

        r.status = "fail" if r.violations else "pass"
        if r.status == "pass":
            r.reason = f"{len(trace)} transactions, no rule broken"
        return r

    # -- exact / composed -----------------------------------------------------

    def _run_predictive(self, trace, r):
        ins = set(self.model.INPUT_IFACES)
        outs = set(self.model.OUTPUT_IFACES)

        # Reset events are control, not data: they re-initialise the model and
        # are never compared. Handling them here rather than in each model
        # means no generated predictor can forget to.
        observed_in = [t for t in trace
                       if t.iface in ins or t.kind == RESET_KIND]
        observed_out = [t for t in trace
                        if t.iface in outs and t.kind != RESET_KIND]

        if not [t for t in observed_in if t.kind != RESET_KIND]:
            r.status = "unknown"
            r.reason = (f"no transactions on the model's input interfaces "
                        f"{sorted(ins)}; observed {sorted({t.iface for t in trace})}. "
                        f"Either the monitors are not bound or the schema names "
                        f"disagree with the model's declaration.")
            return r

        # Replay
        self.model.reset()
        predicted: List[Txn] = []
        n_resets = 0
        for t in observed_in:
            if t.kind == RESET_KIND:
                self.model.reset()
                n_resets += 1
                continue
            produced = self.model.process(t)
            if produced:
                predicted.extend(produced)
        predicted.extend(self.model.drain() or [])
        for i, t in enumerate(predicted):
            t.seq = i

        r.predicted_count = len(predicted)
        r.observed_count = len(observed_out)

        # Nothing on either side means nothing was checked. Do not call that a
        # pass — an empty comparison is the classic vacuous success.
        if not predicted and not observed_out:
            r.status = "unknown"
            r.reason = (f"{len(observed_in)} input transaction(s) replayed, but "
                        f"neither the model nor the design produced any output "
                        f"on {sorted(outs)} — nothing was compared")
            return r

        if self.waivers is not None:
            predicted, observed_out, n_waived = _apply_waivers(
                self.waivers, predicted, observed_out)
            r.waived_fields = n_waived
            r.waivers_applied = dict(self.waivers.used)

        # Compare per interface: distinct interfaces interleave freely in the
        # trace, but each one is individually ordered.
        for iface in sorted(outs):
            p = [t for t in predicted if t.iface == iface]
            o = [t for t in observed_out if t.iface == iface]
            if not p and not o:
                continue
            key = self.reorder_keys.get(iface)
            if key:
                m, mm = align_keyed(p, o, iface, key)
            else:
                m, mm = align(p, o, iface)
            r.matched += m
            r.mismatches.extend(mm)

        r.status = "fail" if r.mismatches else "pass"
        if r.status == "pass":
            r.reason = f"{r.matched} output transaction(s) matched"
        return r


# =============================================================================
# CLI
# =============================================================================

def _load_model(path: str, spec: dict, strategy: str):
    from txn_contract import load_predictor_module, find_model_classes
    base = (TransactionPredictor
            if STRATEGY_NEEDS_MODEL[strategy] == "predictor" else LegalityChecker)
    mod = load_predictor_module(path)
    classes = find_model_classes(mod, base)
    if len(classes) != 1:
        raise SystemExit(f"expected exactly one {base.__name__} in {path}, "
                         f"found {[c.__name__ for c in classes]}")
    return classes[0](spec)


def main() -> int:
    import argparse
    from txn_contract import load_trace, strategy_for_scope

    root = os.path.abspath(os.path.join(HERE, "..", ".."))
    ap = argparse.ArgumentParser(description="Run the transaction scoreboard")
    ap.add_argument("--scope", required=True)
    ap.add_argument("--trace", required=True, help="observed .jsonl trace")
    ap.add_argument("--model", help="predictor/checker .py (not needed for observe)")
    ap.add_argument("--strategy", help="override path_definitions.json")
    ap.add_argument("--spec", default=os.path.join(
        root, "Validation", "spec", "llmmc_microarchitecturespec_filled.json"))
    ap.add_argument("--findings", help="write findings JSON here")
    args = ap.parse_args()

    with open(args.spec) as f:
        spec = json.load(f)
    strategy = args.strategy or strategy_for_scope(
        args.scope, os.path.join(root, "Validation", "spec",
                                 "path_definitions.json"))

    model = None
    if STRATEGY_NEEDS_MODEL[strategy] is not None:
        if not args.model:
            raise SystemExit(f"strategy {strategy!r} requires --model")
        files = [m.strip() for m in args.model.split(",") if m.strip()]
        if len(files) > 1:
            if strategy not in ("composed", "exact"):
                raise SystemExit(f"multiple models only make sense for a "
                                 f"composed chain, not {strategy!r}")
            stages = [_load_model(f, spec, "exact") for f in files]
            cat_path = os.path.join(os.path.dirname(HERE),
                                    "txn", "interface_catalog.json")
            with open(os.path.join(HERE, "interface_catalog.json")) as f:
                cat = json.load(f)["interfaces"]
            aliases = {n: d["same_stream_as"] for n, d in cat.items()
                       if d.get("same_stream_as")}
            model = CompositePredictor(stages, aliases=aliases)
        else:
            model = _load_model(files[0], spec, strategy)

    # Approved waivers ALWAYS apply on the CLI path: a waiver is a recorded
    # team decision, and a run that ignores it re-reports mismatches the team
    # already dispositioned. (An early version never loaded them here, so the
    # first transaction-pipeline cluster run re-flagged the 11 unmapped-read
    # data values that W-001 had already waived as VP_CSR_006.) Waived checks
    # are reported as WAIVED, never as passes.
    waiver_path = os.path.join(root, "Validation", "waivers", "waivers.json")
    waivers = None
    if os.path.exists(waiver_path):
        sys.path.insert(0, os.path.join(root, "Validation", "waivers"))
        from waivers import WaiverSet
        waivers = WaiverSet.load(waiver_path, scope=args.scope,
                                 spec_revision=spec.get("revision"))

    sb = Scoreboard(strategy=strategy, model=model, scope=args.scope,
                    waivers=waivers)
    result = sb.run(load_trace(args.trace))

    print(result.summary())
    for m in result.mismatches[:20]:
        print(f"  {m}")
    if len(result.mismatches) > 20:
        print(f"  ... and {len(result.mismatches) - 20} more")
    for v in result.violations[:20]:
        print(f"  {v}")

    if args.findings:
        with open(args.findings, "w") as f:
            json.dump(result.to_findings(spec.get("revision", "unknown")), f, indent=2)
        print(f"\nwrote findings -> {args.findings}")

    return 1 if result.status == "fail" else 0


if __name__ == "__main__":
    sys.exit(main())
