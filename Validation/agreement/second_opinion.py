#!/usr/bin/env python3
"""
second_opinion.py — an independently generated second model per scope
=====================================================================
A model accepted by its gate is known to be right on the gate's synthetic
traces. Whether it is right on real waveforms is a different question, and
with no correct RTL to run it on, the cheapest evidence is a second model
written independently from the same spec: where the two agree on a real
trace nothing is proved, but where they DISAGREE at least one of them is
wrong, and that is found without any reference design.

This drives the ordinary predictor agent (same spec, same schemas, same
gate, same no-RTL rule) with a differently framed prompt, and writes the
result to predictors/second_opinion/ — never over the primary model.
Both models come from the same LLM family, so their errors are correlated:
agreement is weak evidence, disagreement is strong evidence.

Usage:
    python3 Validation/agreement/second_opinion.py --scope cmd_gen
    python3 Validation/agreement/second_opinion.py --all
"""
import argparse, glob, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
import predictor_agent as PA  # noqa: E402

OUT = os.path.join(ROOT, "Validation", "predictors", "second_opinion")

PREAMBLE = """INDEPENDENT SECOND IMPLEMENTATION.
Another engineer has already written a model for this scope; you have not
seen it and must not try to guess it. Yours will be run against theirs on
recorded traces, and every difference will be investigated, so derive each
behaviour from the specification itself rather than from convention:
  - for every output field, find the spec clause that determines it; where
    the spec is silent, choose the behaviour the applicable standard
    (JESD79-3 for DDR3 pins, Wishbone B4 for the host bus) requires and say
    so in a comment that names the clause;
  - prefer a table-driven structure (one table per decision the spec makes)
    over nested conditionals;
  - do not assume a field is zero, all-ones or 'don't care' unless the spec
    or the standard says so.

"""


def primary_scopes():
    out = []
    for f in sorted(glob.glob(os.path.join(PA.OUT_DIR, "*.provenance.json"))):
        name = os.path.basename(f)[:-len(".provenance.json")]
        out.append(name.rsplit("_", 1)[0])
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--retries", type=int, default=3)
    args = ap.parse_args()
    scopes = primary_scopes() if args.all else [args.scope]
    if not scopes or scopes == [None]:
        ap.error("--scope or --all")

    PA.OUT_DIR = OUT
    a0, c0 = PA.assemble_prompt, PA.assemble_checker_prompt
    PA.assemble_prompt = lambda *a, **k: _pre(a0(*a, **k))
    PA.assemble_checker_prompt = lambda *a, **k: _pre(c0(*a, **k))
    rc = 0
    for s in scopes:
        print(f"\n=== second opinion: {s}")
        try:
            r = PA.generate(s, args.retries, False)
        except Exception as e:
            print(f"  FAILED: {type(e).__name__}: {e}")
            r = 2
        rc = rc or r
    return rc


def _pre(p):
    if isinstance(p, list):
        return [PREAMBLE + p[0]] + p[1:]
    return PREAMBLE + p


if __name__ == "__main__":
    sys.exit(main())
