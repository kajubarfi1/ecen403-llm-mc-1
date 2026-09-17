#!/usr/bin/env python3
"""
waivers.py — declared, attributed, expiring exclusions from comparison
=======================================================================
Sometimes a field genuinely must not be compared: the specification declares
it undefined, or a decision is pending and the team has agreed to proceed
without it. That is legitimate. What is not legitimate is quietly widening a
checker until a disagreement stops appearing — which is how the previous flow
ended up with a +/-2-cycle tolerance window that could not catch the
single-cycle violations the spec calls critical (audit finding V-17).

A waiver here is the honest version of the same act. Four properties make it
so, and all four are enforced:

  * NAMED OWNER. approved_by is required and must not be empty. An anonymous
    waiver is an unattributed decision to stop checking something.
  * A REASON, not a restatement. Required, and separate from the title.
  * TIED TO A SPEC REVISION. A waiver applies to the revision it was granted
    against. When the spec changes, it expires and must be re-argued — the
    change may be exactly the decision that resolves it.
  * NARROW. A waiver excludes one field of one transaction kind, optionally
    only under a stated condition. There is no way to express "ignore this
    interface" or "allow a tolerance".

And one property enforced by the reporting, not the data: a waived item is
reported as WAIVED. It never counts as a pass. Coverage of a waived vplan
item is coverage the design did not earn.

Usage:
    from waivers import WaiverSet
    w = WaiverSet.load()
    w.applies(txn, "data")          -> the waiver, or None
"""

import json
import os
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from typing import Dict, List, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DEFAULT_PATH = os.path.join(HERE, "waivers.json")


class WaiverError(Exception):
    """A waiver that cannot be trusted is worse than no waiver."""


@dataclass
class Waiver:
    id: str
    scope: str
    iface: str
    kind: str
    field_name: str
    reason: str
    approved_by: str
    spec_revision: str
    approved_utc: str = ""
    when: Dict[str, int] = field(default_factory=dict)
    vplan_items: List[str] = field(default_factory=list)
    pending_spec_change: bool = False
    resolves_when: str = ""

    def validate(self):
        for required in ("id", "scope", "iface", "kind", "field_name",
                         "reason", "approved_by", "spec_revision"):
            if not getattr(self, required):
                raise WaiverError(
                    f"waiver {self.id or '(no id)'}: {required!r} is required. "
                    f"A waiver without one is an unattributed decision to stop "
                    f"checking something.")
        if len(self.reason) < 30:
            raise WaiverError(
                f"waiver {self.id}: reason is too short to be a reason "
                f"({self.reason!r}). State why not comparing this field is "
                f"correct, not what is being skipped.")

    def matches(self, txn, field_name, scope, spec_revision):
        if field_name != self.field_name:
            return False
        if txn.iface != self.iface or txn.kind != self.kind:
            return False
        if scope != self.scope:
            return False
        if spec_revision != self.spec_revision:
            return False                     # expired against a new spec
        for k, v in self.when.items():
            if txn.fields.get(k) != v:
                return False
        return True


class WaiverSet:
    def __init__(self, waivers: List[Waiver], scope=None, spec_revision=None):
        self.waivers = waivers
        self.scope = scope
        self.spec_revision = spec_revision
        self.used = {}                       # id -> times applied

    @classmethod
    def load(cls, path=DEFAULT_PATH, scope=None, spec_revision=None):
        if not os.path.exists(path):
            return cls([], scope, spec_revision)
        with open(path) as f:
            raw = json.load(f)
        ws = []
        for entry in raw.get("waivers", []):
            w = Waiver(**entry)
            w.validate()
            ws.append(w)
        return cls(ws, scope, spec_revision)

    def applies(self, txn, field_name) -> Optional[Waiver]:
        for w in self.waivers:
            if w.matches(txn, field_name, self.scope, self.spec_revision):
                self.used[w.id] = self.used.get(w.id, 0) + 1
                return w
        return None

    def waived_fields(self, txn) -> set:
        """Field names on this transaction that are waived from comparison.

        Records usage: `unused()` is only a trustworthy signal if every path
        that consumes a waiver marks it used. Otherwise a live waiver reports
        as dead and someone withdraws a check that was doing work."""
        hit = set()
        for w in self.waivers:
            if w.matches(txn, w.field_name, self.scope, self.spec_revision):
                hit.add(w.field_name)
                self.used[w.id] = self.used.get(w.id, 0) + 1
        return hit

    # -- reporting ---------------------------------------------------------

    def expired(self, spec_revision):
        """Waivers granted against a different spec revision. These do NOT
        apply, and their vplan items go back to unproven."""
        return [w for w in self.waivers if w.spec_revision != spec_revision]

    def unused(self):
        """Waivers that never fired. Either the condition no longer occurs —
        in which case the waiver should be withdrawn — or it is written
        wrongly and is silently protecting nothing."""
        return [w for w in self.waivers if w.id not in self.used]

    def summary(self):
        lines = []
        for w in self.waivers:
            n = self.used.get(w.id, 0)
            state = f"applied {n}x" if n else "NEVER APPLIED"
            lines.append(f"    {w.id}  {w.iface}.{w.kind}.{w.field_name}"
                         f"{'  when ' + str(w.when) if w.when else ''}"
                         f"   [{state}]  approved by {w.approved_by}")
            if w.pending_spec_change:
                lines.append(f"        PENDING SPEC CHANGE: {w.resolves_when}")
        return "\n".join(lines)


def grant(path=DEFAULT_PATH, **kw):
    """Add a waiver, validating it first."""
    w = Waiver(approved_utc=datetime.now(timezone.utc).isoformat(), **kw)
    w.validate()
    data = {"$schema": "validation-waivers/1", "waivers": []}
    if os.path.exists(path):
        with open(path) as f:
            data = json.load(f)
    if any(x["id"] == w.id for x in data["waivers"]):
        raise WaiverError(f"waiver {w.id} already exists")
    data["waivers"].append(asdict(w))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(data, f, indent=2)
    return w
