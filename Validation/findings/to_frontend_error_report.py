#!/usr/bin/env python3
"""
to_frontend_error_report.py — our retry package in the Frontend's own shape
===========================================================================
The Frontend's phase validation agents (Frontend2/scripts/Phase{1,2}/
phase{N}_validation_agent.py) repair a generator from
VALIDATIONREPORT/phase{N}_error_report.json: `failure_stage` must be
BEHAVIORAL_SIMULATION and each failing module carries
    sim_result.modules[<module>] = {status: "FAIL", test_count, pass_count,
                                    fail_lines: [...], assertion_errors: [...]}
which the agent pastes into its prompt. This writes that report, per phase,
from retry_instructions.json: one "test" per failed check, its name the
check id and requirement, its fail line the expected/actual with the source
anchor and reproduction, assertion-type checks under assertion_errors. The
agent then sees exactly what a sim failure would have told it, with the
spec requirement and the anchor added.

Usage:
    python3 Validation/findings/to_frontend_error_report.py --retry <retry_instructions.json> \\
        --drop <frontend output dir> [--phases phases.json]
Returns the phases written (one report each), as JSON on stdout.
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

# the Frontend's phase -> modules map; flow.py passes its own copy
DEFAULT_PHASES = {1: ["init_fsm", "config_regs", "wb_port"],
                  2: ["addr_decoder", "bank_tracker", "refresh_ctrl", "calibration"],
                  3: ["cmd_queue", "scheduler", "cmd_gen"],
                  4: ["data_path"]}


def _lines(check):
    """What the agent will read for one failed check: the requirement, the
    expected/actual, where in the RTL it is, how to see it again."""
    out = [f"[{check['id']}] {check.get('name') or ''}".rstrip()]
    out.append(f"  expected: {check.get('expected')}")
    out.append(f"  actual:   {check.get('actual')}")
    if check.get("spec_ref"):
        out.append(f"  spec:     {check['spec_ref']}")
    # anchors: a line when the producer has one (simulation), a signal with
    # its bit and role when it does not (the backend's timing paths name an
    # endpoint and a startpoint register, never a line)
    for a in (check.get("anchor") or [])[:3]:
        where = a.get("file") or "?"
        if a.get("line") is not None:
            where += f":{a['line']}"
        sig = a.get("signal") or ""
        if sig and a.get("bit") is not None:
            sig += f"[{a['bit']}]"
        if sig and a.get("role"):
            sig += f" ({a['role']})"
        out.append(f"  at {where}  {sig}  {str(a.get('text') or '')[:80]}".rstrip())
    if check.get("fix"):
        out.append(f"  fix hypothesis: {check['fix']}")
    rep = check.get("repro") or {}
    cmd = rep.get("cmd") or rep.get("command") if isinstance(rep, dict) else (rep if isinstance(rep, str) else None)
    if cmd:
        out.append(f"  repro: {cmd}")
    occ = check.get("occurrences")
    if occ:
        paths = ", ".join(check.get("paths") or [])[:120]
        out.append(f"  occurrences: {occ}" + (f" on {paths}" if paths else ""))
    return out


def write_error_reports(retry, drop, phases=None):
    phases = phases or DEFAULT_PHASES
    ri = retry["retry_instructions"]
    written = {}
    for n, mods in phases.items():
        n = int(n)
        failing = [m for m in mods if m in ri]
        if not failing:
            continue
        modules = {}
        for m in failing:
            checks = ri[m]["failed_checks"]
            fail_lines, asserts = [], []
            for c in checks:
                target = asserts if str(c["id"]).startswith(("TIMING_", "PROTO_", "INIT_", "CAL_", "REF_")) \
                    and any(d.startswith("assert") or "sva" in d for d in c.get("detectors", []) or []) \
                    else fail_lines
                target.extend(_lines(c))
            modules[m] = {"status": "FAIL",
                          "test_count": len(checks), "pass_count": 0,
                          "fail_lines": fail_lines, "assertion_errors": asserts,
                          "source": "Validation (spec-derived checks on the integrated drop), "
                                    "not the phase testbench"}
        rep = {"status": "FAIL", "pipeline": f"phase{n}",
               "failure_stage": "BEHAVIORAL_SIMULATION",
               "failed_modules": failing,
               "requires_human_review": bool(retry.get("requires_human_review")),
               "generated_by": "Validation/findings/to_frontend_error_report.py",
               "generated_utc": datetime.now(timezone.utc).isoformat(),
               "validation_drop": retry.get("drop"),
               "spec_revision": retry.get("spec_revision"),
               "sim_result": {"status": "FAIL", "modules": modules},
               "note": ("Written by Validation from retry_instructions.json so the phase "
                        "validation agent can repair the generator: each 'test' is one failed "
                        "spec-derived check with its expected/actual, source anchor and "
                        "reproduction. The phase's own testbench passed; the integrated drop "
                        "did not.")}
        vdir = os.path.join(drop, "VALIDATIONREPORT")
        os.makedirs(vdir, exist_ok=True)
        p = os.path.join(vdir, f"phase{n}_error_report.json")
        with open(p, "w") as f:
            json.dump(rep, f, indent=2)
        written[n] = p
    return written


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--retry", required=True)
    ap.add_argument("--drop", required=True)
    ap.add_argument("--phases", help="JSON {phase: [modules]} (default: the Frontend2 map)")
    args = ap.parse_args()
    with open(args.retry) as f:
        retry = json.load(f)
    phases = None
    if args.phases:
        with open(args.phases) as f:
            phases = {int(k): v for k, v in json.load(f).items()}
    written = write_error_reports(retry, args.drop, phases)
    print(json.dumps({str(k): os.path.relpath(v, ROOT) for k, v in written.items()}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
