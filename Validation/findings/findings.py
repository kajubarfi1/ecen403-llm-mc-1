#!/usr/bin/env python3
"""
findings.py — classify scoreboard mismatches and file them up the chain
=========================================================================
The scoreboard reports that prediction and observation disagree. It does not
know WHY, and it must not guess: an RTL bug, a spec gap, a testbench bug, a
predictor bug and an unmonitored input stream all look identical in a diff,
and they have five different owners.

This module does the part of triage that is DETERMINISTIC — classifications
the evidence settles on its own, with no LLM and no judgement:

  spec_gap
      Prediction and observation agree that the access is exceptional (the
      status/error field matches) but disagree on a data field, AND the spec
      contains no definition of that data for that condition. Neither side is
      wrong; the specification did not say. This is a question for whoever
      owns the spec, not a defect for whoever wrote the RTL.

  observation_gap
      The scope has an interface in the catalog that produced no transactions
      in the trace. A predictor cannot model an input it never sees, so any
      mismatch downstream of it is unattributable until the stream is
      captured.

Anything the rules cannot settle is emitted as `unclassified` and routed to
human/LLM triage. Guessing a kind would send a finding to the wrong owner,
which is worse than admitting the classifier could not tell.

Findings are written to a versioned outbox stamped with the spec revision and
RTL drop they were found against, because a finding is only meaningful
against the inputs that produced it.
"""

import json
import os
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from typing import List, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))

OUTBOX = os.path.join(HERE, "outbox")

# Where each kind of finding goes. The routing is the integration contract:
# a finding that cannot name its owner cannot be acted on.
ROUTING = {
    "spec_gap":         ("spec_owner", "The specification does not define this "
                                       "behaviour; it must say, or the item stays blocked."),
    "rtl_bug":          ("frontend",   "The design disagrees with what the spec requires."),
    "observation_gap":  ("validation", "Our own instrumentation is incomplete; "
                                       "no conclusion about the design is possible here."),
    "predictor_bug":    ("validation", "The generated model is wrong; regenerate it."),
    "tb_bug":           ("validation", "The stimulus or harness is at fault."),
    "unclassified":     ("triage",     "Evidence did not settle the owner."),
}


@dataclass
class Finding:
    kind: str
    scope: str
    title: str
    detail: str
    severity: str = "major"
    target: str = "triage"
    source: str = "validation"
    spec_revision: str = "unknown"
    rtl_drop: str = "unknown"
    vplan_items: List[str] = field(default_factory=list)
    question: Optional[str] = None          # for spec_gap: what must be decided
    evidence: List[dict] = field(default_factory=list)
    occurrences: int = 1
    status: str = "open"

    def to_dict(self):
        d = asdict(self)
        d["routing_reason"] = ROUTING.get(self.kind, ROUTING["unclassified"])[1]
        return d


# =============================================================================
# Spec interrogation (all spec-driven, nothing about this design hardcoded)
# =============================================================================

def _register_map(spec):
    for val in spec.values():
        if isinstance(val, dict) and isinstance(val.get("registers"), list):
            regs = val["registers"]
            if regs and "fields" in regs[0]:
                return val
    return None


def _mapped_offsets(spec):
    rm = _register_map(spec)
    if not rm:
        return set()
    return {int(str(r["offset"]), 0) for r in rm["registers"]}


def _spec_defines(spec, *terms):
    """Does the spec say anything about these concepts at all?"""
    blob = json.dumps(spec).lower()
    return any(t.lower() in blob for t in terms)


def _status_fields(schemas, iface, kind):
    """Field names on this transaction kind that carry status rather than
    payload — an error or acknowledgement indication."""
    fields = schemas.get(iface, {}).get("kinds", {}).get(kind, {})
    return {f for f in fields if f in ("err", "error", "ack", "resp", "status")}


# =============================================================================
# Deterministic classification
# =============================================================================

def classify_mismatches(mismatches, spec, schemas, scope):
    """Group scoreboard mismatches into findings using rules the evidence
    settles. Returns a list of Finding."""
    mapped = _mapped_offsets(spec)
    undefined_response, unresolved = [], []

    for m in mismatches:
        p, o = m.predicted, m.observed
        if m.kind != "value" or p is None or o is None:
            unresolved.append(m)
            continue

        status = _status_fields(schemas, o.iface, o.kind)
        agree_status = all(p.fields.get(f) == o.fields.get(f) for f in status)
        differing = {f for f in set(p.fields) | set(o.fields)
                     if p.fields.get(f) != o.fields.get(f)}

        # Rule: exceptional access, both sides agree it is exceptional, they
        # differ only on payload, the address is outside the register map, and
        # the spec never defines what such an access returns.
        addr = o.fields.get("addr")
        exceptional = status and any(o.fields.get(f) for f in status)
        if (agree_status and exceptional and differing <= {"data"}
                and addr is not None and addr not in mapped
                and not _spec_defines(spec, "unmapped", "unimplemented",
                                      "decode_error", "undefined address")):
            undefined_response.append(m)
        else:
            unresolved.append(m)

    findings = []

    if undefined_response:
        observed_vals = sorted({m.observed.fields.get("data")
                                for m in undefined_response})
        predicted_vals = sorted({m.predicted.fields.get("data")
                                 for m in undefined_response})
        addrs = sorted({m.observed.fields.get("addr") for m in undefined_response})
        findings.append(Finding(
            kind="spec_gap",
            scope=scope,
            severity="major",
            target=ROUTING["spec_gap"][0],
            title="Read data for an unmapped register address is undefined",
            occurrences=len(undefined_response),
            detail=(
                f"{len(undefined_response)} reads to addresses outside the "
                f"register map disagreed on returned data. Both the design and "
                f"the spec-derived model agree the access is exceptional (the "
                f"error indication matches on every one), so this is not a "
                f"disagreement about whether the access fails. They differ only "
                f"on the data accompanying the error: the design returns "
                f"{', '.join(hex(v) for v in observed_vals)}, the model returns "
                f"{', '.join(hex(v) for v in predicted_vals)}. The model reads "
                f"the specification literally, and the specification does not "
                f"state what data an unmapped read returns — the terms "
                f"'unmapped', 'unimplemented', 'decode_error' and 'undefined "
                f"address' do not appear in it. Neither implementation is "
                f"wrong; the specification did not decide."),
            question=(
                "What must a read of an unmapped CSR address return on the data "
                "bus? Options: (a) the design's current 0xDEADBEEF, recorded in "
                "the spec as the defined response; (b) zero; (c) explicitly "
                "'don't care', in which case validation must exclude the data "
                "field from comparison for errored accesses. Any of the three "
                "is actionable; silence is not."),
            vplan_items=["VP_CSR_006"],
            evidence=[{
                "addresses": [hex(a) for a in addrs],
                "design_returns": [hex(v) for v in observed_vals],
                "model_returns": [hex(v) for v in predicted_vals],
                "error_indication_agrees": True,
                "example": str(undefined_response[0]),
            }],
        ))

    if unresolved:
        findings.append(Finding(
            kind="unclassified",
            scope=scope,
            severity="major",
            target=ROUTING["unclassified"][0],
            title=f"{len(unresolved)} mismatch(es) the deterministic rules could not classify",
            occurrences=len(unresolved),
            detail=("These disagreements did not match any rule that settles an "
                    "owner from evidence alone. They need triage before being "
                    "routed; sending them to a subsystem on a guess would waste "
                    "that subsystem's time and hide the real fault."),
            evidence=[{"mismatch": str(m)} for m in unresolved[:20]],
        ))

    return findings


def find_observation_gaps(trace, catalog, scope):
    """Interfaces the catalog says this scope has, that produced nothing."""
    expected = {i for i, d in catalog.items() if d["block"] == scope}
    seen = {t.iface for t in trace}
    silent = sorted(expected - seen)
    if not silent:
        return []
    return [Finding(
        kind="observation_gap",
        scope=scope,
        severity="major",
        target=ROUTING["observation_gap"][0],
        title=f"{len(silent)} declared interface(s) produced no transactions",
        occurrences=len(silent),
        detail=(f"The interface catalog declares {sorted(expected)} for this "
                f"scope, but {silent} appear nowhere in the trace. Either the "
                f"monitors were not bound, the qualifier never fired, or the "
                f"stimulus never exercised them. Until this is resolved, any "
                f"mismatch that depends on those inputs is unattributable — a "
                f"model cannot be faulted for not predicting an input it was "
                f"never shown."),
        evidence=[{"declared": sorted(expected), "observed": sorted(seen),
                   "silent": silent}],
    )]


# =============================================================================
# Filing
# =============================================================================

def file_findings(findings, spec_revision, rtl_drop, scope, outbox=OUTBOX):
    """Write findings to the versioned outbox. Returns the path."""
    for f in findings:
        f.spec_revision = spec_revision
        f.rtl_drop = rtl_drop
        if f.target == "triage" and f.kind in ROUTING:
            f.target = ROUTING[f.kind][0]

    dest_dir = os.path.join(outbox, spec_revision)
    os.makedirs(dest_dir, exist_ok=True)
    dest = os.path.join(dest_dir, f"{scope}_findings.json")
    payload = {
        "$schema": "validation-findings/1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "scope": scope,
        "spec_revision": spec_revision,
        "rtl_drop": rtl_drop,
        "finding_count": len(findings),
        "by_target": {t: sum(1 for f in findings if f.target == t)
                      for t in sorted({f.target for f in findings})},
        "findings": [f.to_dict() for f in findings],
    }
    with open(dest, "w") as f:
        json.dump(payload, f, indent=2)
    return dest
