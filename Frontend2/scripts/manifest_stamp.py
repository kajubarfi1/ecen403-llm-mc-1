#!/usr/bin/env python3
"""
Drop stamp helper -- shared by every generator's generate_manifest().

Validation's regression history (`introduced_in`/`resolved_in`,
Validation/structural/rtl_drop.py) is only as trustworthy as the commit a
manifest was generated under. Today Validation recovers that commit itself
by inspecting the repo; this emits it directly on every manifest instead,
per Validation/findings/HANDOFF_FRONTEND_2026-09-24.md ask #5 (C1).
"""

import subprocess
from datetime import datetime, timezone


def _git_commit() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=5,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass
    return "unknown"


def stamp(spec: dict) -> dict:
    """Returns {"git_commit", "spec_revision", "generated_utc",
    "clock_period_ns"?} to merge into a generate_manifest() return value.

    clock_period_ns comes straight from the spec's own clocking_model --
    per TOP_LEVEL_SPEC_2026-09-24.md section 4, this was missing on all 11
    block manifests, which meant every backend timing result reported so
    far was against a target the backend invented (10.0 ns / 100 MHz
    default), not one the spec actually requires.
    """
    out = {
        "git_commit": _git_commit(),
        "spec_revision": spec.get("revision", "unknown"),
        "generated_utc": datetime.now(timezone.utc).isoformat(),
    }
    period = spec.get("clocking_model", {}).get("controller_clock_period_ns")
    if period is not None:
        out["clock_period_ns"] = period
    return out
