#!/usr/bin/env python3
"""
random_sequence.py — the control arm for the coverage-closure experiment
=========================================================================
Constrained-random stimulus, generated with no knowledge of which coverage
holes are open. This is what a conventional DV flow does, and it is the only
honest baseline for the claim "the agent improved coverage": without it,
coverage going up proves only that more simulation happened.

Fairness is the whole point of this file, so the constraints are deliberate:

  * Same step format, same schema, same interfaces as the agent's output, so
    the identical driver codegen and harness run both arms.
  * Same budget — matched drive count and comparable sequence length. An arm
    allowed more stimulus would win for the wrong reason.
  * Legal stimulus only. Random commands with random spacing would trip
    illegal bins and produce assertion failures, which is a different
    experiment (does random find bugs?) than the one being run (does
    targeting close coverage?).
  * Seeded, so a reported result can be reproduced.

What it deliberately does NOT do is read the coverage rollup. That asymmetry
IS the independent variable.
"""

import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

# Spacing drawn from a plausible operating range. The minimum legal separation
# for the tightest constraint is 1 cycle and the widest is tRFC at 32, so a
# uniform draw over this range is what an unguided constrained-random test
# would produce — it can reach a boundary, but only by chance.
IDLE_RANGE = (1, 12)


def generate(schemas, catalog, scope, n_drives=19, seed=0, only_kinds=None):
    """A legal, unguided sequence with the same shape as an agent's."""
    rng = random.Random(seed)
    drivable = [i for i, d in catalog.items()
                if d.get("role") == "request" and d["block"] == scope]
    if not drivable:
        raise SystemExit(f"no stimulus interface for scope {scope!r}")
    iface = drivable[0]
    kinds = schemas[iface]["kinds"]
    if only_kinds:
        kinds = {k: v for k, v in kinds.items() if k in only_kinds}
        if not kinds:
            raise SystemExit(f"{iface!r} has none of the kinds {only_kinds}; "
                             f"it has {sorted(schemas[iface]['kinds'])}")
    enc = {k: v for k, v in catalog[iface].get("command_encoding", {}).items()
           if not k.startswith("$")}

    # Only commands that make sense as stimulus; NOP would drive nothing.
    cmds = [v for k, v in enc.items() if k != "NOP"] or [1]

    steps = [{"op": "reset"}]
    for _ in range(n_drives):
        # Draw the kind per drive: an interface with reads and writes must
        # see both, or read-back checking never runs.
        kind = rng.choice(sorted(kinds))
        fields = kinds[kind]
        vals = {}
        for fname, info in fields.items():
            w = info["width"]
            if fname == "type":
                vals[fname] = rng.choice(cmds)
            elif isinstance(w, int):
                # keep values modest so they are plausible rather than extreme
                vals[fname] = rng.randrange(0, min(1 << w, 64))
            else:
                vals[fname] = 0
        steps.append({"op": "drive", "iface": iface, "kind": kind,
                      "fields": vals})
        steps.append({"op": "idle", "cycles": rng.randint(*IDLE_RANGE)})

    return {
        "name": f"random_seed{seed}",
        "targets": [],          # the control aims at nothing, by construction
        "rationale": (f"Constrained-random control (seed {seed}). Generated "
                      f"without reading the coverage rollup; the absence of "
                      f"targeting is the independent variable."),
        "steps": steps,
        "_provenance": {"arm": "control", "seed": seed,
                        "reads_coverage": False},
    }


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--drives", type=int, default=19)
    ap.add_argument("--out", required=True)
    ap.add_argument("--kinds", help="comma-separated kinds to restrict to "
                    "(e.g. 'write' when the read-return path is absent)")
    args = ap.parse_args()

    with open(os.path.join(ROOT, "Validation/txn/generated/schemas.json")) as f:
        schemas = json.load(f)["interfaces"]
    with open(os.path.join(ROOT, "Validation/txn/interface_catalog.json")) as f:
        catalog = json.load(f)["interfaces"]

    seq = generate(schemas, catalog, args.scope, args.drives, args.seed,
                   only_kinds=set(args.kinds.split(",")) if args.kinds else None)
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(seq, f, indent=2)
    n_drive = sum(1 for s in seq["steps"] if s["op"] == "drive")
    print(f"  {seq['name']}: {len(seq['steps'])} steps, {n_drive} drives -> "
          f"{os.path.relpath(args.out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
