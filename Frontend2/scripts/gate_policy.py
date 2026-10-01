"""
gate_policy.py -- a SKIPPED gate is not a passed gate.

Lint and sim run on Olympus over SSH. When SSH is unavailable (no
OLYMPUS_USER / OLYMPUS_KEY, auth failure, paramiko missing) those gates
return status "SKIPPED". The pipelines used to route SKIPPED to success, so a
run with no verification at all looked identical to a clean one -- and
Validation's flow reads those reports. Now SKIPPED fails closed.

Set ALLOW_SKIPPED_GATES=1 to proceed deliberately without verification
(e.g. offline development). The pipelines then record the skipped gates in
their final report and mark it PASS_UNVERIFIED, not PASS.
"""
import os


def skipped_allowed() -> bool:
    return os.environ.get("ALLOW_SKIPPED_GATES", "").strip().lower() in ("1", "true", "yes")


def gate_passes(status) -> bool:
    """True only for a real PASS, or SKIPPED when explicitly allowed."""
    if status == "PASS":
        return True
    return status == "SKIPPED" and skipped_allowed()
