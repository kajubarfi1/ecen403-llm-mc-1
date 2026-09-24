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
    """Returns {"git_commit", "spec_revision", "generated_utc"} to merge
    into a generate_manifest() return value."""
    return {
        "git_commit": _git_commit(),
        "spec_revision": spec.get("revision", "unknown"),
        "generated_utc": datetime.now(timezone.utc).isoformat(),
    }
