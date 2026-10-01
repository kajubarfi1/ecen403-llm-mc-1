"""
Ingest for the Frontend Orchestrator: turns whatever the other subsystems
dropped on disk into one normalized list of findings, each tagged with the
stage it belongs to.

Sources (all optional, all merged):
  - Validation outbox: <outbox>/current/ (HANDOFF_CONTRACT.md §4; HANDOFF.json,
    findings_v2.json, retry_instructions.json, DROP_STATUS.json), falling back to
    <outbox>/<spec_revision>/latest -> <drop>/findings_v2.json
    (RTL defects, owner_module set) and any <spec_revision>/*_findings.json
    / <outbox>/*.json whose entries carry target == "spec" (spec gaps).
  - .md files (hand-off notes, triage reports) anywhere under the given
    dirs -- not parsed, only listed; the orchestrator LLM reads them on
    demand via read_md.
"""
from __future__ import annotations

import json
from pathlib import Path

# module -> phase. Code is ground truth (calibration is Phase 2).
MODULE_PHASE = {
    "init_fsm": 1, "config_regs": 1, "wb_port": 1,
    "addr_decoder": 2, "bank_tracker": 2, "refresh_ctrl": 2, "calibration": 2,
    "cmd_queue": 3, "scheduler": 3, "cmd_gen": 3,
    "data_path": 4,
}
# Phases that have an automated fix agent today.
FIXABLE_PHASES = (1, 2)


def _norm(raw: dict, origin: str) -> dict:
    target = raw.get("target") or ("spec" if raw.get("kind") == "spec_gap" else "rtl")
    module = raw.get("owner_module") or raw.get("module")
    return {
        "id": raw.get("id") or f"{raw.get('scope', 'spec')}/{raw.get('title', '')[:60]}",
        "target": target,                                   # "spec" | "rtl"
        "module": module,
        "phase": MODULE_PHASE.get(module),
        "scope": raw.get("scope"),                          # spec section, spec-stage only
        "severity": raw.get("severity"),
        "title": raw.get("title") or raw.get("check_id"),
        "detail": raw.get("detail") or raw.get("requirement"),
        "expected": raw.get("expected"),
        "actual": raw.get("actual"),
        "anchor": raw.get("anchor"),
        "origin": origin,
        "raw": raw,                                         # verbatim, for forwarding
    }


def _load_json(p: Path):
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


def load_findings(outbox: Path, spec_revision: str | None = None) -> dict:
    """Returns {"drop", "spec_revision", "findings": [...], "md_files": [...],
    "raw_retry": {module: [failed_check, ...]}}."""
    outbox = Path(outbox)
    findings, md_files = [], []
    drop = None
    revs = [d for d in sorted(outbox.iterdir()) if d.is_dir()] if outbox.is_dir() else []
    if spec_revision:
        revs = [d for d in revs if d.name == spec_revision]
    rev_dir = revs[0] if revs else None

    handoff = None
    cur = outbox / "current"
    if (cur / "HANDOFF.json").is_file():
        # Contract (Validation/findings/HANDOFF_CONTRACT.md §4): current/ is
        # always the newest result; its HANDOFF.json names the drop it judged.
        handoff = _load_json(cur / "HANDOFF.json") or {}
        drop = handoff.get("drop_id")
        d = _load_json(cur / "findings_v2.json") or {}
        findings += [_norm(f, "current/findings_v2.json") for f in d.get("findings", [])]
        rev_dir = outbox / handoff["spec_revision"] if (outbox / handoff.get("spec_revision", "")).is_dir() else rev_dir
    elif rev_dir:
        latest = rev_dir / "latest"
        drop = latest.read_text().strip() if latest.is_file() else None
        if drop and (rev_dir / drop / "findings_v2.json").is_file():
            d = _load_json(rev_dir / drop / "findings_v2.json") or {}
            findings += [_norm(f, f"{rev_dir.name}/{drop}/findings_v2.json")
                         for f in d.get("findings", [])]

    # Blocking spec-review findings (schema / JESD79-3 / register map) from
    # Validation's spec-review stage: spec-stage findings like any other.
    review = _load_json(cur / "SPEC_REVIEW.json") if handoff is not None or (cur / "SPEC_REVIEW.json").is_file() else None
    for i, b in enumerate((review or {}).get("blocking", [])):
        scope = b.split(":", 1)[1].strip().split(".")[0] if ":" in b else None
        findings.append(_norm({"id": f"spec_review/blocking/{i}: {b[:70]}", "target": "spec",
                               "kind": "spec_review_blocking", "scope": scope, "severity": "blocking",
                               "title": b, "detail": b, "spec_revision": (review or {}).get("spec_revision")},
                              "current/SPEC_REVIEW.json"))

    # Spec-gap style files live beside the drop dirs and at the outbox root.
    for p in list(outbox.glob("*.json")) + (list(rev_dir.glob("*_findings.json")) if rev_dir else []):
        d = _load_json(p)
        if isinstance(d, dict) and isinstance(d.get("findings"), list):
            for f in d["findings"]:
                if f.get("target") == "spec" or f.get("kind") == "spec_gap":
                    findings.append(_norm(f, p.name))

    # De-dupe on (id, origin-independent).
    seen, uniq = set(), []
    for f in findings:
        k = (f["target"], f["id"])
        if k not in seen:
            seen.add(k)
            uniq.append(f)

    raw_retry, extra = {}, {}
    rpath = (cur / "retry_instructions.json") if handoff else (
        rev_dir / drop / "retry_instructions.json" if rev_dir and drop else None)
    r = (_load_json(rpath) or {}) if rpath else {}
    for m, v in (r.get("retry_instructions") or {}).items():
        raw_retry[m] = v.get("failed_checks", [])
    if r:
        extra = {"untested_in_this_drop": r.get("untested_in_this_drop", []),
                 "requires_human_review": r.get("requires_human_review"),
                 "status": r.get("status")}
    drop_status = _load_json(cur / "DROP_STATUS.json") if handoff else None

    # .md hand-off notes: beside the outbox (Validation/findings/*.md) and
    # anywhere under it. Never recurse upward from the outbox's parent.
    if outbox.is_dir():
        md_files += sorted(str(p) for p in outbox.rglob("*.md"))
        md_files += sorted(str(p) for p in outbox.parent.glob("*.md"))
    return {"drop": drop, "spec_revision": rev_dir.name if rev_dir else None,
            "handoff": handoff, "drop_status": drop_status, **extra,
            "findings": uniq, "md_files": sorted(set(md_files)), "raw_retry": raw_retry}
