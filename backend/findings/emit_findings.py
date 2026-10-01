#!/usr/bin/env python3
"""Turn backend sign-off failures into findings the frontend can act on.

The backend has always produced verdicts: "STA FAIL, WNS -0.915 ns". That tells the
backend owner the block is slow. It tells the frontend nothing they can change - not
which path, not which signal, not what to do. For the three-subsystem pipeline the
backend has to stop terminating and start participating: a failure must come back as
a routable record naming an owner module, the evidence, and a suggested fix.

Records follow Validation's `validation-findings/2` envelope
(Validation/findings/emit_findings.py) so all three subsystems speak one language.

Five fields are backend decisions pending agreement with Validation; each is marked
PENDING below. They are additive, so a consumer that ignores them still works.

usage:
  emit_findings.py --design scheduler --report <6_finish.rpt> --period 5.0 \
                   --rtl Frontend2/OutputFolders/PHASE3RTL/scheduler.sv [--outbox DIR]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

SCHEMA = "validation-findings/2"

# PENDING(1): `kind`. Validation hardcodes "rtl_defect"; the backend needs to say what
# sort of failure this is. Additive to their vocabulary, not a redefinition.
KIND_TIMING = "timing_defect"

# PENDING(2): severity. Backend findings are ERROR/WARNING/INFO; Validation uses a
# rules file defaulting to "major". Missing a hard spec target is "critical".
SEVERITY_MISSED_TARGET = "critical"

# A standard-cell instance on a timing path. Used to count logic depth, which is what
# distinguishes "one slow path" from "this block is structurally too deep".
CELL_RE = re.compile(r"sky130_fd_sc_hd__(?!clkbuf|buf_|inv_)\w+")
BUF_RE = re.compile(r"sky130_fd_sc_hd__(buf_|clkbuf)")


def find_repo(start: Path) -> Optional[Path]:
    """Nearest enclosing git repository, or None.

    The backend may sit inside the team repo or beside it as a working copy. The
    drop stamp is how a finding is tied to a code state, so it is worth locating
    rather than assuming.
    """
    for d in [start, *start.parents]:
        if (d / ".git").exists():
            return d
    return None


def git_head(repo: Path) -> Optional[str]:
    try:
        return subprocess.run(["git", "-C", str(repo), "rev-parse", "--short", "HEAD"],
                              capture_output=True, text=True, timeout=10).stdout.strip() or None
    except Exception:
        return None


def parse_timing_report(path: Path) -> Dict[str, Any]:
    """Failing paths and the design-wide slack totals from an ORFS 6_finish.rpt.

    Returns {"wns_ns", "tns_ns", "paths": [...]}. A path carries its endpoints, slack,
    logic depth and the arrival/required split. Paths are reported worst first, which
    is the order report_checks emits them.
    """
    text = path.read_text(errors="ignore")
    wns = tns = None
    m = re.search(r"^wns max ([-\d.]+)", text, re.M)
    if m:
        wns = float(m.group(1))
    m = re.search(r"^tns max ([-\d.]+)", text, re.M)
    if m:
        tns = float(m.group(1))

    paths: List[Dict[str, Any]] = []
    # Split on Startpoint so each chunk is one reported path.
    for chunk in re.split(r"(?=Startpoint:)", text):
        if "slack (VIOLATED)" not in chunk:
            continue
        sp = re.search(r"Startpoint:\s*(\S+)(?:\s*\((.*?)\))?", chunk)
        ep = re.search(r"Endpoint:\s*(\S+)", chunk)
        sl = re.search(r"([-\d.]+)\s+slack \(VIOLATED\)", chunk)
        if not (sp and ep and sl):
            continue
        arrival = re.search(r"([\d.]+)\s+data arrival time", chunk)
        required = re.search(r"([\d.]+)\s+data required time", chunk)
        group = re.search(r"Path Group:\s*(\S+)", chunk)
        paths.append({
            "startpoint": sp.group(1),
            "startpoint_kind": (sp.group(2) or "register").strip(),
            "endpoint": ep.group(1),
            "slack_ns": float(sl.group(1)),
            "logic_levels": len(CELL_RE.findall(chunk)),
            "buffers": len(BUF_RE.findall(chunk)),
            "arrival_ns": float(arrival.group(1)) if arrival else None,
            "required_ns": float(required.group(1)) if required else None,
            "path_group": group.group(1) if group else None,
        })
    # report_checks prints the worst path more than once (once for -path_delay max,
    # again under its path group), so the same path arrives twice. Counting it twice
    # would overstate how many endpoints are failing, which is the number that says
    # whether this is one bad path or a structural problem.
    seen, unique = set(), []
    for p in paths:
        key = (p["startpoint"], p["endpoint"], round(p["slack_ns"], 4))
        if key not in seen:
            seen.add(key)
            unique.append(p)
    unique.sort(key=lambda p: p["slack_ns"])
    return {"wns_ns": wns, "tns_ns": tns, "paths": unique}


def timing_finding(design: str, period_ns: float, parsed: Dict[str, Any],
                   rtl_path: Optional[str], repro: str, drop: Dict[str, Any],
                   mechanism: Optional[str] = None,
                   suggested_fix: Optional[str] = None) -> Optional[Dict[str, Any]]:
    """One finding for a block that misses its clock target. None if it closed."""
    wns, paths = parsed.get("wns_ns"), parsed.get("paths") or []
    if wns is None or wns >= 0:
        return None
    worst = paths[0] if paths else None
    tns = parsed.get("tns_ns")

    # TNS far exceeding WNS means many endpoints fail, not one outlier. That is the
    # difference between nudging a path and restructuring the block, so it belongs in
    # the finding rather than being left for the reader to work out.
    spread = None
    if tns is not None and wns and wns < 0:
        ratio = abs(tns) / abs(wns)
        spread = ("many endpoints failing, not a single outlier"
                  if ratio > 3 else "concentrated on the worst path")

    # The endpoint carries a synthesis-generated suffix (cmd_row[5]$_DFFE_PN0P_).
    # That name changes when the block is re-synthesised, so an id built from it
    # would not match itself across drops and lifecycle tracking would silently
    # break. Key on the RTL signal; the full instance stays in the evidence.
    signal = worst["endpoint"].split("$")[0] if worst else None
    check_id = f"TIMING/{signal}" if signal else "TIMING/unknown"
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    return {
        "schema": SCHEMA,
        "id": f"{design}/{check_id}",
        "kind": KIND_TIMING,                       # PENDING(1)
        "check_id": check_id,
        "taxonomy_id": "TIMING_001",
        "detectors": ["sta:opensta:setup"],
        "owner_module": design,
        "owner_candidates": [design],
        "severity": SEVERITY_MISSED_TARGET,        # PENDING(2)
        "confidence": "observed",
        "title": f"{design}: does not close timing at {period_ns} ns",
        "requirement": f"{design} must close timing at the clock period of {period_ns} ns "
                       f"({round(1000.0 / period_ns)} MHz)",
        "spec_ref": "clocking_model.controller_clock_period_ns",
        "expected": f"slack >= 0 ns at a {period_ns} ns period",
        "actual": (f"WNS {wns:+.3f} ns"
                   + (f", TNS {tns:+.3f} ns" if tns is not None else "")
                   + (f", Fmax {1000.0 / (period_ns - wns):.2f} MHz" if period_ns - wns > 0 else "")),
        "detector": "sta:opensta:setup",
        # PENDING(3): Validation anchors to file and line. The backend can name the
        # file but not the line - synthesis does not preserve it - so line is omitted
        # rather than guessed.
        "anchor": ([{"file": rtl_path}] if rtl_path else []),
        "mechanism": mechanism,
        "paths": [],
        "occurrences": len(paths),
        # PENDING(4): no field in the schema carries a remedy, and every backend check
        # has one. Added here because it is the most actionable part of the record.
        "suggested_fix": suggested_fix,
        "evidence": {
            "worst_path": worst,
            "wns_ns": wns, "tns_ns": tns,
            "failing_paths_reported": len(paths),
            "spread": spread,
        },
        "repro": {"command": repro},
        "drop": drop,
        "introduced_in": None,
        "first_seen": drop.get("git_head"),
        "last_seen": drop.get("git_head"),
        "resolved_in": None,
        "status": "open",
        "generated_utc": now,
        "related_manual_findings": [],
    }


def write_outbox(findings: List[Dict[str, Any]], outbox: Path, drop: Dict[str, Any]) -> Path:
    """Write a drop and update `latest`, carrying lifecycle from the previous drop.

    A finding the previous drop carried as open and this drop no longer raises is
    recorded as resolved, so the outbox is a ledger rather than a snapshot. Without
    this an orchestrator cannot tell a fixed defect from one that was never re-tested.
    """
    rev = drop.get("spec_revision") or "unknown"
    head = drop.get("git_head") or "nohead"
    prev: Dict[str, Any] = {}
    latest = outbox / rev / "latest"
    if latest.exists():
        try:
            prev_path = outbox / rev / latest.read_text(encoding="utf-8").strip() / "findings_v2.json"
            if prev_path.exists():
                for f in json.loads(prev_path.read_text(encoding="utf-8")).get("findings", []):
                    prev[f["id"]] = f
        except Exception:
            prev = {}

    current = {f["id"] for f in findings}
    for f in findings:
        old = prev.get(f["id"])
        if old:                       # seen before: keep its history
            f["first_seen"] = old.get("first_seen", f["first_seen"])
            f["introduced_in"] = old.get("introduced_in")
    resolved = []
    for fid, old in prev.items():
        if fid not in current and old.get("status") == "open":
            old = dict(old, status="resolved", resolved_in=head, last_seen=old.get("last_seen"))
            resolved.append(old)

    d = outbox / rev / head
    d.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": SCHEMA,
        "drop": drop,
        "spec_revision": rev,
        "generated_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "producer": "backend",
        "finding_count": len(findings),
        "findings": findings,
        "resolved": resolved,
    }
    out = d / "findings_v2.json"
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    (outbox / rev / "latest").write_text(head + "\n", encoding="utf-8")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--design", required=True)
    ap.add_argument("--report", required=True, type=Path, help="ORFS 6_finish.rpt")
    ap.add_argument("--period", required=True, type=float, help="clock period in ns")
    ap.add_argument("--rtl", default=None, help="RTL path for the anchor")
    ap.add_argument("--repro", default=None)
    ap.add_argument("--outbox", type=Path, default=Path(__file__).resolve().parent / "outbox")
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--spec-revision", default="golden_ddr3_1600k_x8_2lane_1rank")
    ap.add_argument("--mechanism", default=None)
    ap.add_argument("--suggested-fix", default=None)
    ap.add_argument("--print-only", action="store_true")
    a = ap.parse_args()

    parsed = parse_timing_report(a.report)
    repo = find_repo(a.repo.resolve())
    head = git_head(repo) if repo else None
    if not head:
        print(f"FINDINGS WARNING: no git repo above {a.repo} - the drop stamp will be "
              f"incomplete, so this finding cannot be tied to a code state. "
              f"Pass --repo pointing into the team checkout.")
    drop = {"git_head": head, "spec_revision": a.spec_revision}
    repro = a.repro or f"pipeline_batch.py --bundle_dirs bundles/{a.design}"
    f = timing_finding(a.design, a.period, parsed, a.rtl, repro, drop,
                       a.mechanism, a.suggested_fix)
    if not f:
        print(f"FINDINGS {a.design}: timing closed, nothing to emit "
              f"(WNS {parsed.get('wns_ns')})")
        return 0
    if a.print_only:
        print(json.dumps(f, indent=2))
        return 0
    out = write_outbox([f], a.outbox, drop)
    w = f["evidence"]["worst_path"]
    print(f"FINDINGS emitted {f['id']}  owner={f['owner_module']}  severity={f['severity']}")
    if w:
        print(f"FINDINGS worst path {w['startpoint']} -> {w['endpoint']}  "
              f"slack={w['slack_ns']:+.3f}ns  levels={w['logic_levels']}")
    print(f"FINDINGS wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
