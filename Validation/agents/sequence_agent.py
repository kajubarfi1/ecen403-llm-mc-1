#!/usr/bin/env python3
"""
sequence_agent.py — generate stimulus aimed at named coverage holes
====================================================================
Replaces vector_gen_agent.py, and inverts what it was for.

The old agent produced a hex vector file in which each line carried both the
stimulus AND the expected response, precomputed by the reference model. That
made the stimulus file the oracle, which is why the flow could report 228/228
passing while assertions were firing: the answers were computed by the same
chain that produced the questions.

Here stimulus carries no answers at all. A sequence is a list of transactions
to drive; what should happen is the predictor's job and when is SVA's. That
separation is what lets stimulus be judged on a completely different axis:

    a sequence is good if COVERAGE MOVES.

Which makes this the most defensible use of an LLM in the whole subsystem.
Choosing which corner of a timing constraint to probe is genuinely
underdetermined — there is no algorithm that enumerates interesting stimulus —
and the metric that grades the answer is functional coverage against a
spec-derived vplan, which the model cannot influence. A wrong predictor lies
about the design; a wrong sequence costs one simulation.

The prompt carries the measured holes, not a general instruction to "get good
coverage": "cp_trcd_spacing is at 33%, the at_minimum bin was never hit, and
the minimum is 3 cycles" is a concrete, checkable goal.

Usage:
    python3 Validation/agents/sequence_agent.py --scope cmd_gen
    python3 Validation/agents/sequence_agent.py --scope cmd_gen --dry-run
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))

import sequence_contract as SC
from llm_client import call_llm, strip_fences
sys.path.insert(0, os.path.join(ROOT, "Validation", "sva"))
from sva_gen import cycles_for

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
ROLLUP_PATH = os.path.join(ROOT, "Validation", "reports", "coverage_rollup.json")
OUT_DIR = os.path.join(ROOT, "Validation", "sequences", "generated")


def open_holes(rollup_path, scope_hint=None, limit=12):
    """Coverage items that are measured and short of goal, or never measured.

    A hole is only useful to an agent if it is CONCRETE. Each entry carries
    the vplan requirement text and, where the plan knows it, the target that
    was missed — which turns 'improve coverage' into 'drive tRCD to exactly
    its minimum'."""
    if not os.path.exists(rollup_path):
        return []
    with open(rollup_path) as f:
        roll = json.load(f)
    holes = []
    for item in roll["items"]:
        if item["status"] not in ("partial", "not_measured"):
            continue
        for cov in item.get("coverage", []):
            if cov["state"] == "met":
                continue
            holes.append({
                "vplan_item": item["id"],
                "requirement": item["title"],
                "coverpoint": cov["name"],
                "measured_percent": cov.get("measured"),
                "goal": cov.get("goal"),
                "bins": cov.get("bins"),
                "state": cov["state"],
            })
    holes.sort(key=lambda h: (h["measured_percent"] is None,
                              h["measured_percent"] or 0))
    return holes[:limit]


def enrich(holes, vplan_path, spec, rules_path):
    """Attach requirement text AND the already-converted cycle counts.

    The agent is NOT asked to convert nanoseconds to cycles. It was doing that
    arithmetic against the wrong clock — dividing by tCK (1.25ns, the DDR
    clock) instead of the controller period (5.0ns), producing 11 cycles where
    tRCD needs 3. Both numbers appear in the spec and 11 is the more salient
    one, so the ambiguity was ours, not the model's.

    The same conversion the assertions and covergroups use is applied here, so
    the agent receives a target it can act on directly. Deterministic code
    does the arithmetic; the model chooses which corner to probe."""
    with open(vplan_path) as f:
        items = {i["id"]: i for i in json.load(f)["items"]}
    with open(rules_path) as f:
        rules = json.load(f)
    params = {r["param"].lower(): r["param"]
              for r in rules["min_separation_rules"] + rules["window_rules"]}

    for h in holes:
        it = items.get(h["vplan_item"], {})
        h["requirement_text"] = it.get("requirement", "")
        if it.get("failure_ref"):
            h["failure_ref"] = it["failure_ref"]
        pt = h["coverpoint"].split(".")[-1]
        if pt.startswith("cp_") and pt.endswith("_spacing"):
            key = pt[3:-8]
            param = params.get(key)
            if param:
                try:
                    n, ns, period = cycles_for(spec, param)
                except Exception:
                    continue
                h["timing_parameter"] = param
                h["target_separation_cycles"] = n
                h["required_idle_cycles"] = n - 1
                h["how_to_hit_at_minimum"] = (
                    f"drive the first command, then "
                    f"{{\"op\":\"idle\",\"cycles\":{n - 1}}}, then drive the "
                    f"second command to the SAME bank"
                    if n > 1 else
                    "drive the two commands on consecutive steps with no idle "
                    "between them")
    return holes


def assemble_prompt(scope, spec, schemas, catalog, holes, prior_failures=None):
    drivable = {i: schemas[i] for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == scope}
    if not drivable:
        raise SC.SequenceError(
            f"scope {scope!r} has no interface with role 'request' in the "
            f"catalog, so there is nothing to drive. Add its stimulus surface.")

    enc = {i: catalog[i].get("command_encoding", {}) for i in drivable}
    period = spec["clocking_model"]["controller_clock_period_ns"]

    prompt = f"""You are writing STIMULUS for hardware verification. Your job is
to choose what to try, so that specific coverage holes get closed.

You are NOT deciding what correct behaviour is. Another model predicts the
expected response and assertions check timing; your sequence carries no
expected values. A sequence is judged by one thing only: does the coverage it
produces close the holes below.

=== WHAT YOU MAY DRIVE ===

These are the stimulus interfaces of scope '{scope}'. Drive only these.

{json.dumps(drivable, indent=2)}

Command encodings for these interfaces (use the NUMBER, not the name):

{json.dumps(enc, indent=2)}

=== THE COVERAGE HOLES TO CLOSE ===

Each entry is a real measurement from a real simulation. `at_minimum` bins
are the ones that matter: a sequence that always leaves slack satisfies a
timing constraint without ever testing it.

{json.dumps(holes, indent=2)}

=== TIMING CONTEXT ===

Do NOT convert nanoseconds to cycles yourself. Every hole above that needs a
boundary already carries the answer:

    target_separation_cycles  how many cycles must separate the two commands
    required_idle_cycles      the exact `idle` value to use between them
    how_to_hit_at_minimum     the two steps, spelled out

Use those numbers directly. The controller clock period is {period}ns, but you
should not need it — the conversion has been done for you, against the correct
clock.

=== OUTPUT FORMAT ===

Return ONE JSON object, nothing else:

{{
  "name": "short_snake_case_name",
  "targets": ["VP_TIME_004", "..."],        // vplan ids this aims to cover
  "rationale": "one or two sentences on how the steps close those holes",
  "steps": [
    {{"op": "reset"}},
    {{"op": "drive", "iface": "<one of the above>", "kind": "<a kind>",
      "fields": {{ ... exactly the schema's field names, integer values ... }}}},
    {{"op": "idle", "cycles": 2}},
    ...
  ]
}}

Rules:
  - `idle` is how you control SPACING, and spacing is what the timing bins
    measure. A drive occupies exactly one cycle.

    WORKED EXAMPLE — read this carefully, it is the most common mistake.
    Coverage measures the cycle count at the SECOND command, counting the
    first command's cycle as 0. To make a RD land exactly 3 cycles after an
    ACT (so the counter reads 3, hitting the at_minimum bin for tRCD):

        {{"op":"drive", ...ACT...}}     <- occupies cycle 0
        {{"op":"idle",  "cycles": 2}}   <- covers cycles 1 and 2
        {{"op":"drive", ...RD...}}      <- lands on cycle 3   CORRECT

    Using "cycles": 3 there would place the RD on cycle 4, which lands in
    above_minimum and leaves at_minimum unhit. The rule is:

        idle cycles = (target separation) - 1

    Both commands must also address the SAME bank for a same-bank constraint
    (tRCD, tRP, tRAS, tRC, tWR, tRTP); use a DIFFERENT bank for tRRD.
  - Every field of the driven kind must be present, as a non-negative integer
    that fits the field width.
  - Prefer several short, clearly-aimed passages over one long one, and reset
    between passages that must not interfere.
  - Legal stimulus only: do not deliberately violate a timing constraint. The
    goal is to reach the minimum legal spacing, not to break the rule.

Return ONLY the JSON object."""

    if prior_failures:
        prompt += f"""

=== YOUR PREVIOUS ATTEMPT WAS REJECTED ===

{chr(10).join('  - ' + f for f in prior_failures)}

Fix all of these and return the corrected JSON object in full."""
    return prompt


def generate(scope, retries=3, dry_run=False):
    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]

    holes = enrich(open_holes(ROLLUP_PATH),
                   os.path.join(ROOT, "Validation", "vplan", "vplan.json"),
                   spec,
                   os.path.join(ROOT, "Validation", "sva", "sva_rules.json"))
    if not holes:
        print("  no open coverage holes in the rollup — run coverage first, or "
              "everything the vplan asks for is already covered.")
        return 1

    print(f"  scope        : {scope}")
    print(f"  open holes   : {len(holes)}")
    for h in holes[:5]:
        pct = "never measured" if h["measured_percent"] is None \
            else f"{h['measured_percent']}%"
        print(f"    {h['coverpoint']:34} {pct:>15}  ({h['vplan_item']})")
    if len(holes) > 5:
        print(f"    ... and {len(holes) - 5} more")

    drivable = {i for i, d in catalog.items() if d.get("role") == "request"}
    failures = None
    for attempt in range(1, retries + 2):
        prompt = assemble_prompt(scope, spec, schemas, catalog, holes, failures)
        if dry_run:
            print("\n" + prompt[:2200] + "\n  ... [truncated]")
            return 0
        print(f"\n  attempt {attempt}: prompt {len(prompt):,} chars"
              + (f", repairing {len(failures)} fault(s)" if failures else ""))

        raw = strip_fences(call_llm([{"role": "user", "content": prompt}],
                                    max_tokens=16000))
        try:
            seq = json.loads(raw)
        except ValueError as e:
            failures = [f"the response is not valid JSON: {e}. Return one JSON "
                        f"object and nothing else — no prose, no fences."]
            print(f"    REJECTED: {failures[0][:110]}")
            continue

        failures = SC.validate(seq, schemas, drivable)
        if failures:
            print(f"    REJECTED: {len(failures)} fault(s)")
            for f in failures[:4]:
                print(f"      {f[:150]}")
            continue

        os.makedirs(OUT_DIR, exist_ok=True)
        dest = os.path.join(OUT_DIR, f"{scope}_{seq['name']}.json")
        seq["_provenance"] = {
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "spec_revision": spec.get("revision"),
            "model": os.environ.get("ANTHROPIC_MODEL", "(client default)"),
            "attempts": attempt,
            "aimed_at": [h["coverpoint"] for h in holes],
            "note": ("Stimulus only — carries no expected values. Judged by "
                     "whether the coverage it produces closes the targeted "
                     "holes, a metric the generating model cannot influence."),
        }
        SC.save(seq, dest)
        print(f"\n  ACCEPTED on attempt {attempt}")
        print(f"  {SC.summarize(seq)}")
        if seq.get("rationale"):
            print(f"  rationale: {seq['rationale'][:200]}")
        print(f"  wrote {os.path.relpath(dest, ROOT)}")
        return 0

    print(f"\n  GAVE UP after {retries + 1} attempts.")
    return 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--retries", type=int, default=3)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    try:
        return generate(args.scope, args.retries, args.dry_run)
    except SC.SequenceError as e:
        print(f"  {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
