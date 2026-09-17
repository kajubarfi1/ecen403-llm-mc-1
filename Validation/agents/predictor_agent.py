#!/usr/bin/env python3
"""
predictor_agent.py — generate a transaction predictor, then earn its acceptance
================================================================================
Replaces refmodel_agent.py. Same role in the flow (the agent that produces the
model against which the design is checked), fundamentally different contract.

What changed, and why each change exists:

  * TRANSACTION-LEVEL, not cycle-level. The old agent had to implement
    step(**signals) -> dict, advancing one clock at a time, which forced it to
    know the RTL's pipeline depth. Its prompt therefore carried a section
    headed "CRITICAL — RTL PIPELINE LATENCY (from RTL source inspection)" that
    told the model when cmd_gen registers its outputs. A model told what the
    design does cannot independently check that design (audit finding V-06),
    and when its predictions still drifted the checker was widened to a
    +/-2-cycle tolerance (V-17), which cannot catch a one-cycle violation.
    A predictor says WHAT happens and in what order; SVA says WHEN.

  * NO RTL IN THE PROMPT. Enforced, not merely intended: assemble_prompt()
    is built only from the spec, the generated schemas, and the contract, and
    a self-check refuses to send a prompt that mentions RTL files or paths.

  * GRADED BY A GATE IT NEVER SEES. The old agent wrote its own self-test and
    was accepted when its own test printed "ALL TESTS PASSED" (V-05). Here the
    model is graded by Validation/gates/predictor_gates.py, whose expectations
    are composed from the spec independently. Gate failures are fed back into
    the prompt verbatim, because they are written as repair instructions.

  * NO GATE MEANS NO ACCEPTANCE. If no behavioural gate applies to a scope,
    the agent reports the model as UNGATED and exits non-zero rather than
    signing it off on structural checks alone. Silence is not evidence.

Usage:
    python3 Validation/agents/predictor_agent.py --scope config_regs
    python3 Validation/agents/predictor_agent.py --scope config_regs --dry-run
    python3 Validation/agents/predictor_agent.py --scope config_regs --retries 4
"""

import argparse
import json
import os
import re
import sys
import tempfile
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "gates"))

from txn_contract import (contract_check, load_predictor_module,
                          find_model_classes, TransactionPredictor,
                          LegalityChecker, STRATEGY_NEEDS_MODEL,
                          strategy_for_scope)
import predictor_gates
from llm_client import call_llm, strip_fences

SPEC_PATH = os.path.join(ROOT, "Validation", "spec",
                         "llmmc_microarchitecturespec_filled.json")
SCHEMA_PATH = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
CATALOG_PATH = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
CONTRACT_PATH = os.path.join(ROOT, "Validation", "txn", "txn_contract.py")
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
STAGE_RULES = os.path.join(ROOT, "Validation", "gates",
                           "stage_invariant_rules.json")
OUT_DIR = os.path.join(ROOT, "Validation", "predictors")

# Substrings that would mean RTL leaked into the prompt. The whole point of
# the rebuild is that the predictor is derived from the spec alone.
RTL_LEAK_MARKERS = [".sv", "always_ff", "always_comb", "posedge", "localparam",
                    "endmodule", "PHASE1RTL", "reg [", "wire "]


class PredictorAgentError(Exception):
    pass


# =============================================================================
# Prompt assembly
# =============================================================================

def contract_excerpt(want="predictor"):
    """The contract, quoted verbatim from the file the gate enforces.

    Quoting the real source rather than a paraphrase means the prompt cannot
    drift from what contract_check() actually requires."""
    src = open(CONTRACT_PATH).read()
    if want == "checker":
        # A checker constructs Violation objects, so the excerpt must include
        # the dataclass itself — without it the model guesses the constructor
        # (Violation(message=...)) and every attempt dies on a TypeError.
        v_start = src.rindex("@dataclass", 0, src.index("class Violation"))
        v_end = src.index("# ====", v_start)
        start = src.index("class LegalityChecker")
        end = src.index("# ====", start)
        return (src[v_start:v_end].rstrip() + "\n\n\n"
                + src[start:end].rstrip())
    start = src.index("class TransactionPredictor")
    end = src.index("class LegalityChecker")
    return src[start:end].rstrip()


def stage_entry(scope):
    """The stage-checker declaration for this scope, or None.

    Composed-path stages whose output stream is order-nondeterministic
    (declared in stage_invariant_rules.json) are generated as LegalityCheckers
    rather than predictors. The stage entry supplies the interface sets and
    the invariant ids the checker must cover; the grading TRACES stay in the
    gate and are never shown to the agent.
    """
    if not os.path.exists(STAGE_RULES):
        return None
    with open(STAGE_RULES) as f:
        return json.load(f)["stages"].get(scope)


def scope_interfaces(scope, catalog, schemas):
    """Interfaces belonging to this scope, split into inputs and outputs.

    A scope named after a block gets that block's interfaces. Request streams
    (those carrying an address or a valid payload the host drives) are inputs;
    response streams are outputs. The split is by direction of the fields'
    ports, so it holds for any design.
    """
    # `mine` may legitimately be empty: a block like addr_decoder owns no
    # ports that form an interface, yet consumes and produces shared streams
    # declared on its neighbours. The error case is having NEITHER own
    # interfaces NOR stream declarations, checked after both are gathered.
    mine = {i: d for i, d in catalog.items() if d["block"] == scope}

    # Role is declared in the catalog, not inferred from port directions: a
    # response stream commonly carries the address that was requested, and
    # that port is a DUT input. Inferring would misclassify it.
    #
    # A stream also belongs to more than one block: the catalog's `block` is
    # the port owner, but `producers`/`consumers` name the other blocks on the
    # same wires. addr_decoder owns no interface of its own, yet it consumes
    # `req` and produces `cq_enq` — without honouring those declarations, a
    # middle-of-the-chain block looks unpredictable when it is actually the
    # easiest stage of all.
    ins = sorted(set(
        [i for i, d in mine.items() if d.get("role") == "request"]
        + [i for i, d in catalog.items() if scope in d.get("consumers", [])]))
    outs = sorted(set(
        [i for i, d in mine.items() if d.get("role") == "response"]
        + [i for i, d in catalog.items() if scope in d.get("producers", [])]))
    # An aliased pair (same_stream_as) is ONE stream under two names; keep a
    # single canonical name per side or the composite would double-count it.
    def dedupe(names):
        keep = []
        for n in sorted(names):
            alias = catalog.get(n, {}).get("same_stream_as")
            if alias and alias in keep:
                continue
            keep.append(n)
        return keep
    ins, outs = dedupe(ins), dedupe(outs)

    if not mine and not ins and not outs:
        raise PredictorAgentError(
            f"scope {scope!r} owns no interfaces and no stream in the catalog "
            f"names it as a producer or consumer. Known blocks: "
            f"{sorted({d['block'] for d in catalog.values()})}. Declare its "
            f"streams before generating for it.")

    unroled = sorted(i for i, d in mine.items() if "role" not in d)
    if unroled:
        raise PredictorAgentError(
            f"interfaces {unroled} have no 'role' in interface_catalog.json. "
            f"Mark each as 'request' (driven into the block) or 'response' "
            f"(produced by it) — a predictor consumes the first and predicts "
            f"the second.")
    if not ins or not outs:
        have = "no request stream" if not ins else "no response stream"
        raise PredictorAgentError(
            f"scope {scope!r} has {have}: requests={ins or '—'}, "
            f"responses={outs or '—'}. Exact prediction needs both — input "
            f"transactions to drive the model and output transactions to "
            f"compare against. A scope shaped like this is verified by "
            f"check_strategy 'invariant' or 'observe' instead, where "
            f"assertions and legality rules do the checking.")
    return ins, outs


def _encoding_section(stage):
    """The command encoding a stage checker must decode — or, for a stage
    with no command stream (event ordering only), a note saying so. The
    stage entry's own `$note` rides along: it carries the field semantics
    (e.g. an MRS command's bank field is the mode-register number) that the
    schemas alone do not state."""
    parts = []
    if stage.get("command_iface"):
        enc = {k: v for k, v in
               _catalog()[stage["encoding_iface"]]["command_encoding"].items()
               if not k.startswith("$")}
        parts.append(f"The command field '{stage['command_field']}' on "
                     f"'{stage['command_iface']}' uses this encoding:\n\n"
                     f"{json.dumps(enc, indent=2)}")
    else:
        parts.append("This stage carries no command stream: the invariants are "
                     "pure ordering between the events above.")
    if stage.get("$note"):
        parts.append(f"Stage note: {stage['$note']}")
    return "\n\n".join(parts)


def assemble_checker_prompt(scope, spec, schemas, stage, prior_failures=None):
    """Prompt for a stage invariant CHECKER (LegalityChecker).

    The checker gets the invariant ids and their requirement prose — those
    restate the spec's failure_taxonomy plus the proposed scheduler
    extensions, which the model may see. The legal/violating grading traces
    stay in the gate.
    """
    ins, outs = stage["input_ifaces"], stage["output_ifaces"]
    sub = {i: schemas[i] for i in ins + outs}
    invariants = "\n".join(
        f"  {r['id']}: {r['requirement']}" for r in stage["rules"])

    parts = [f"""You are writing a LEGALITY CHECKER for the validation of a
hardware design. The stage you are checking ({' + '.join(stage['blocks'])})
emits a command stream with more than one legal ordering, so its behaviour is
checked by INVARIANTS over what was observed, not by predicting one exact
output sequence.

You are given the specification and the transaction schemas. You are NOT given
the design's source. Assert what the spec REQUIRES of any implementation.

=== THE CONTRACT YOUR CLASS MUST SATISFY ===

{contract_excerpt('checker')}

=== THE TRANSACTION SCHEMAS FOR THIS STAGE ===

Your INPUT_IFACES must be exactly: {tuple(ins)}
Your OUTPUT_IFACES must be exactly: {tuple(outs)}

Field names below are the exact keys in Txn.fields.

{json.dumps(sub, indent=2)}

{_encoding_section(stage)}

=== THE INVARIANTS YOUR CHECKER MUST DETECT (COVERS must be exactly these) ===

{invariants}

=== THE SPECIFICATION ===

{json.dumps(spec, indent=2)}

=== REQUIREMENTS ===

1. Write ONE class subclassing LegalityChecker. Import with:
       from txn_contract import LegalityChecker, Txn, Violation
2. __init__(self, spec) takes the spec dict as its only argument. Read every
   constant you need from it (e.g. refresh policy limits) — no literals.
3. COVERS must be exactly the invariant ids listed above. Each detection
   returns a Violation with taxonomy_id set to the matching id.
4. observe(txn) consumes one transaction (input or output stream, in observed
   order) and returns a list of Violation, usually empty. It must not raise
   on any transaction the schemas permit.
5. final() reports end-of-trace rules: requests never issued, refreshes never
   serviced. It is called exactly once, after the last transaction.
6. Do NOT model clock cycles or timing — a checker sees order, not cycles.
7. Do not report a violation on behaviour the spec permits: several command
   orderings are legal, and a checker that fires on correct behaviour is
   worse than no checker.
8. No file I/O, no network, no imports beyond the standard library and
   txn_contract.

Return ONLY the Python module. No explanation, no markdown fences."""]

    if prior_failures:
        parts.append(f"""

=== YOUR PREVIOUS ATTEMPT WAS REJECTED ===

An acceptance suite derived independently from the same specification found
the problems below. Fix all of them. Do not change anything that was not
faulted.

{chr(10).join('  - ' + f for f in prior_failures)}

Return the corrected module in full.""")
    return "".join(parts)


def _catalog():
    with open(CATALOG_PATH) as f:
        return json.load(f)["interfaces"]


def assemble_prompt(scope, spec, schemas, catalog, strategy, prior_failures=None):
    ins, outs = scope_interfaces(scope, catalog, schemas)
    sub = {i: schemas[i] for i in ins + outs}

    parts = [
        f"""You are writing a TRANSACTION PREDICTOR for the validation of a
hardware design. It is a reference model: an independent implementation of
what the SPECIFICATION says must happen, used to check a separate
implementation of the same spec.

You are given the specification and the transaction schemas. You are NOT given
the design's source, and you must not guess at it. Model what the spec
REQUIRES, not what an implementation might do. If the spec is silent on
something, model the most literal reading and do not invent behaviour.

=== THE CONTRACT YOUR CLASS MUST SATISFY ===

{contract_excerpt()}

=== THE TRANSACTION SCHEMAS FOR THIS SCOPE ===

Your INPUT_IFACES must be exactly: {tuple(ins)}
Your OUTPUT_IFACES must be exactly: {tuple(outs)}

Field names below are the exact keys that appear in Txn.fields. Use these
names; the scoreboard compares on them.

{json.dumps(sub, indent=2)}

=== THE SPECIFICATION ===

{json.dumps(spec, indent=2)}

=== REQUIREMENTS ===

1. Write ONE class subclassing TransactionPredictor. Import it with:
       from txn_contract import TransactionPredictor, Txn
2. __init__(self, spec) takes the spec dict as its only argument. Read every
   constant you need from it. Do not hardcode register offsets, reset values,
   field positions, or timing numbers as literals — a different spec must
   produce different behaviour from the same code.
3. process(txn) returns a list of Txn. Return [] for any transaction on an
   interface you do not model; it must not raise on unknown input.
4. Emitted Txn objects set iface and kind from the schemas above and carry
   exactly the fields the schema lists for that kind.
5. Do NOT model clock cycles, latency, acknowledgement timing or pipeline
   depth. Ordering is expressed by the order you emit; timing is checked
   elsewhere.
6. reset() must return the model to its power-on state, including re-reading
   reset values from the spec.
7. No file I/O, no network, no imports beyond the standard library and
   txn_contract.

Return ONLY the Python module. No explanation, no markdown fences."""
    ]

    if prior_failures:
        parts.append(f"""

=== YOUR PREVIOUS ATTEMPT WAS REJECTED ===

An acceptance suite derived independently from the same specification found
the problems below. Each names a concrete disagreement between your model and
what the spec requires. Fix all of them. Do not change anything that was not
faulted.

{chr(10).join('  - ' + f for f in prior_failures)}

Return the corrected module in full.""")
    return "".join(parts)


def assert_no_rtl(prompt):
    """Refuse to send a prompt carrying design implementation detail.

    This is the V-06 guard made mechanical. A predictor told what the RTL does
    is not an independent check of that RTL, and the failure is invisible —
    the model and the design agree, and the agreement proves nothing."""
    spec_blob = open(SPEC_PATH).read()
    leaked = []
    for marker in RTL_LEAK_MARKERS:
        if marker in prompt and marker not in spec_blob:
            leaked.append(marker)
    if leaked:
        raise PredictorAgentError(
            f"prompt contains RTL implementation markers {leaked}. A predictor "
            f"must be derived from the spec alone.")


# =============================================================================
# Grading
# =============================================================================

def evaluate(path, spec, schemas, strategy):
    """Structural gate, then behavioural gate. Returns (failures, gate_name)."""
    structural = contract_check(path, spec, strategy)
    if structural:
        return structural, None

    mod = load_predictor_module(path)
    base = (TransactionPredictor
            if STRATEGY_NEEDS_MODEL[strategy] == "predictor" else LegalityChecker)
    cls = find_model_classes(mod, base)[0]

    gate = predictor_gates.select_gate(cls, spec, schemas)
    if gate is None:
        return [], None                     # caller must treat this as UNGATED
    try:
        try:
            return gate.grade(cls(spec), spec, schemas), gate.name
        except TypeError:
            with open(CATALOG_PATH) as f:
                cat = json.load(f)["interfaces"]
            return gate.grade(cls(spec), spec, schemas, cat), gate.name
    except predictor_gates.GateNotApplicable as e:
        return [], None
    except Exception as e:
        return [f"the model raised {type(e).__name__} while being graded: {e}. "
                f"It must handle every transaction the schema permits."], gate.name


# =============================================================================
# Main loop
# =============================================================================

def generate(scope, retries=3, dry_run=False, verbose=True):
    with open(SPEC_PATH) as f:
        spec = json.load(f)
    with open(SCHEMA_PATH) as f:
        schemas = json.load(f)["interfaces"]
    with open(CATALOG_PATH) as f:
        catalog = json.load(f)["interfaces"]

    stage = stage_entry(scope)
    if stage is not None:
        strategy = "invariant"
        ins, outs = stage["input_ifaces"], stage["output_ifaces"]
    else:
        strategy = strategy_for_scope(scope, PATH_DEFS, default="exact")
        if STRATEGY_NEEDS_MODEL[strategy] is None:
            print(f"  scope {scope!r} has strategy {strategy!r} — no model is "
                  f"needed; monitors and assertions carry this scope.")
            return 0
        ins, outs = scope_interfaces(scope, catalog, schemas)
    if verbose:
        print(f"  scope      : {scope}")
        print(f"  strategy   : {strategy}")
        print(f"  inputs     : {ins}")
        print(f"  outputs    : {outs}")

    failures, attempts = None, []
    for attempt in range(1, retries + 2):
        if stage is not None:
            prompt = assemble_checker_prompt(scope, spec, schemas, stage,
                                             failures)
        else:
            prompt = assemble_prompt(scope, spec, schemas, catalog, strategy,
                                     failures)
        assert_no_rtl(prompt)
        if verbose:
            print(f"\n  attempt {attempt}: prompt {len(prompt):,} chars"
                  + (f", repairing {len(failures)} fault(s)" if failures else ""))
        if dry_run:
            print("\n" + prompt[:1500] + "\n  ... [truncated]")
            return 0

        code = strip_fences(call_llm([{"role": "user", "content": prompt}],
                                     max_tokens=16000))
        tmp = tempfile.NamedTemporaryFile("w", suffix=".py", delete=False)
        tmp.write(code)
        tmp.close()

        failures, gate_name = evaluate(tmp.name, spec, schemas, strategy)
        attempts.append({"attempt": attempt, "failures": len(failures),
                         "gate": gate_name})

        if failures:
            if verbose:
                print(f"    REJECTED by {gate_name or 'contract check'}: "
                      f"{len(failures)} fault(s)")
                for f in failures[:4]:
                    print(f"      {f[:150]}")
                if len(failures) > 4:
                    print(f"      ... and {len(failures) - 4} more")
            os.unlink(tmp.name)
            continue

        if gate_name is None:
            print(f"\n  UNGATED: the model passes the structural contract, but "
                  f"no behavioural gate applies to scope {scope!r}.")
            print(f"  Refusing to accept it. A model no spec-derived suite has "
                  f"graded is not evidence of anything —")
            print(f"  add a gate in Validation/gates/predictor_gates.py that "
                  f"applies to this scope's shape.")
            os.unlink(tmp.name)
            return 2

        # accepted
        os.makedirs(OUT_DIR, exist_ok=True)
        kind = "checker" if stage is not None else "predictor"
        dest = os.path.join(OUT_DIR, f"{scope}_{kind}.py")
        with open(dest, "w") as f:
            f.write(code if code.endswith("\n") else code + "\n")
        os.unlink(tmp.name)

        prov = {
            "scope": scope, "strategy": strategy,
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "spec_revision": spec.get("revision"),
            "model": os.environ.get("ANTHROPIC_MODEL", "(client default)"),
            "accepted_by_gate": gate_name,
            "attempts": attempts,
            "input_ifaces": ins, "output_ifaces": outs,
            "note": ("Generated from the spec and transaction schemas only; no "
                     "RTL was supplied to the model. Accepted by a gate whose "
                     "expectations are composed from the same spec by code the "
                     "model never saw."),
        }
        with open(os.path.join(OUT_DIR, f"{scope}_{kind}.provenance.json"), "w") as f:
            json.dump(prov, f, indent=2)

        if verbose:
            print(f"\n  ACCEPTED on attempt {attempt} by gate {gate_name!r}")
            print(f"  wrote {os.path.relpath(dest, ROOT)}")
        return 0

    print(f"\n  GAVE UP after {retries + 1} attempts; {len(failures)} fault(s) "
          f"remain. This is a generation failure, not a design finding — the "
          f"design has not been judged.")
    return 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", required=True)
    ap.add_argument("--retries", type=int, default=3)
    ap.add_argument("--dry-run", action="store_true",
                    help="assemble and show the prompt without calling the LLM")
    args = ap.parse_args()
    try:
        return generate(args.scope, args.retries, args.dry_run)
    except PredictorAgentError as e:
        print(f"  {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
