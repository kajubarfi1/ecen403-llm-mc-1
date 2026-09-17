#!/usr/bin/env python3
"""
txn_contract.py — the transaction vocabulary and the predictor contract
========================================================================
The foundation of the transaction-scoreboard architecture. Two things live
here and nothing else:

  Txn                    the unit of observation and prediction
  TransactionPredictor   the ABC every AGENT-GENERATED reference model
                         must implement

Division of labor (project rule): the LLM agent generates the predictor;
this file is deterministic infrastructure. The agent never edits it — the
contract is quoted verbatim into the agent's prompt, and contract_check()
is the first gate of its generate-validate-repair loop.

Design decisions the contract enforces:
  * Transaction-level only. A predictor sees and emits Txn objects — no
    clocks, no cycle counts, no pin values. "What happens, in what order"
    is the model's job; "when" belongs to SVA; "did we exercise it" belongs
    to coverage. This is what removes the need for RTL knowledge in the
    generation prompt (audit V-06) and for tolerance windows in the checker
    (V-17).
  * Spec-agnostic. Nothing here names a register, a field, or a DDR
    command. Interface names and field sets come from the generated schema
    (schema_gen.py), which is derived from whatever spec is loaded.
"""

import importlib.util
import inspect
import json
import os
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Dict, List, Optional


# =============================================================================
# The transaction
# =============================================================================

@dataclass
class Txn:
    """One observed or predicted transaction.

    iface   interface name from the generated schema (e.g. "csr", "req")
    kind    transaction kind within that interface (e.g. "read", "write")
    fields  field name -> integer value, per the schema's field list
    seq     monotonic observation index within its trace (order matters;
            absolute time does not)
    time_ns optional simulator timestamp — informational only. Predictors
            MUST NOT read it and the scoreboard MUST NOT compare it.
    """
    iface: str
    kind: str
    fields: Dict[str, int] = field(default_factory=dict)
    seq: int = -1
    time_ns: Optional[int] = None

    def key(self):
        """Identity used for comparison: everything except seq/time."""
        return (self.iface, self.kind, tuple(sorted(self.fields.items())))

    def __str__(self):
        fs = " ".join(f"{k}={v:#x}" if isinstance(v, int) else f"{k}={v}"
                      for k, v in sorted(self.fields.items()))
        return f"[{self.iface}.{self.kind} {fs}]"

    # ---- serialization (trace files are .jsonl of these) ----

    def to_dict(self):
        d = {"iface": self.iface, "kind": self.kind, "fields": self.fields,
             "seq": self.seq}
        if self.time_ns is not None:
            d["time_ns"] = self.time_ns
        return d

    @classmethod
    def from_dict(cls, d):
        return cls(iface=d["iface"], kind=d["kind"],
                   # A monitor can sample an unknown ('x'/'z' bits): the design drove an
        # undefined value. No integer represents that honestly, so it loads
        # as None — the scoreboard reports such transactions as defects and
        # never feeds them to a model.
        fields={k: (int(v) if not (isinstance(v, str)
                                   and any(c in v.lower() for c in "xz"))
                    else None)
                for k, v in d.get("fields", {}).items()},
                   seq=int(d.get("seq", -1)), time_ns=d.get("time_ns"))


def load_trace(path: str) -> List[Txn]:
    """Read a .jsonl trace file into Txn objects, in file order."""
    out = []
    with open(path) as f:
        for i, line in enumerate(f):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            t = Txn.from_dict(json.loads(line))
            if t.seq < 0:
                t.seq = i
            out.append(t)
    return out


def save_trace(txns: List[Txn], path: str):
    with open(path, "w") as f:
        for t in txns:
            f.write(json.dumps(t.to_dict()) + "\n")


# =============================================================================
# Violations (the legality-envelope result type)
# =============================================================================

@dataclass
class Violation:
    """One broken rule, found by observation rather than by prediction.

    Where a predictor says "the output should have been X", a checker says
    "whatever the output was, it broke rule R". That distinction is what makes
    full-controller validation possible: an FR-FCFS scheduler with refresh
    interleaving has many legal command orderings, so predicting one exact
    sequence would fail against correct RTL. Legality is checkable where
    equality is not.
    """
    rule: str                       # short id, e.g. "no_starvation"
    detail: str                     # human-readable, names the actual values
    severity: str = "critical"      # critical | major | minor
    taxonomy_id: str = ""           # spec failure_taxonomy id, when one applies
    txns: list = field(default_factory=list)   # the transactions involved

    def __str__(self):
        where = " ".join(str(t) for t in self.txns[:3])
        return f"{self.rule}: {self.detail}{(' @ ' + where) if where else ''}"

    def to_dict(self):
        return {"rule": self.rule, "detail": self.detail,
                "severity": self.severity, "taxonomy_id": self.taxonomy_id,
                "txns": [t.to_dict() for t in self.txns]}


# =============================================================================
# Check strategies
# =============================================================================
# Which shape of checking a scope uses. Read from path_definitions.json rather
# than inferred from a scope name, so a new design picks its strategy from data.
#
#   exact     one predictor; scoreboard compares predicted vs observed exactly
#   composed  several predictors chained (one block's outputs are the next
#             block's inputs); still an exact comparison at the end
#   invariant no prediction — a LegalityChecker asserts rules over the observed
#             stream. For feedback loops and end-to-end paths where many
#             orderings are legal
#   observe   no model at all — monitors plus SVA carry the whole check. For
#             autonomous FSMs that nothing drives

CHECK_STRATEGIES = ("exact", "composed", "invariant", "observe")

# A reserved transaction kind, emitted by every monitor when the DUT's reset
# asserts. It is not a bus transaction: it is the event that tells a stateful
# model the design just cleared its state. Without it a predictor keeps state
# the DUT has dropped and diverges for the rest of the run — silently, which
# is the worst way to be wrong. The scoreboard consumes these itself so that
# no generated model has to remember to handle them.
RESET_KIND = "reset"

STRATEGY_NEEDS_MODEL = {"exact": "predictor", "composed": "predictor",
                        "invariant": "checker", "observe": None}


# =============================================================================
# The predictor contract
# =============================================================================

class TransactionPredictor(ABC):
    """What an agent-generated reference model must be.

    Lifecycle: construct with the spec dict -> reset() -> process() once per
    observed INPUT transaction, in observed order -> drain() at end of trace.

    The predicted output stream is the concatenation of every list returned
    by process() and drain(), in call order. The scoreboard compares that
    stream against the OBSERVED output trace.

    Rules the gate enforces (contract_check) and the prompt states:
      * __init__(self, spec: dict) — the ONLY configuration input is the
        spec. No RTL paths, no file reads, no environment.
      * process() must accept any Txn on its declared input interfaces and
        ignore (return []) transactions on interfaces it does not model.
      * Emitted Txns carry no seq/time — ordering is implied by emission
        order; the infrastructure assigns seq.
      * Deterministic: same input stream => same output stream.
    """

    #: interface names this predictor consumes / produces. The generated
    #: model must override these with names from the schema.
    INPUT_IFACES: tuple = ()
    OUTPUT_IFACES: tuple = ()

    @abstractmethod
    def __init__(self, spec: dict):
        ...

    @abstractmethod
    def reset(self) -> None:
        """Return all modeled state to its power-on values."""

    @abstractmethod
    def process(self, txn: Txn) -> List[Txn]:
        """Consume one observed input transaction; return the output
        transactions it implies (possibly none, possibly several)."""

    @abstractmethod
    def drain(self) -> List[Txn]:
        """Outputs still pending after the last input (e.g. buffered
        responses). Called exactly once, at end of trace."""


class LegalityChecker(ABC):
    """What an agent-generated model must be for `invariant` scopes.

    COVERS declares which failure_taxonomy ids this checker is responsible
    for detecting. It is not documentation: the gate grades the checker by
    synthesising a trace that violates each declared id and requiring
    detection. A checker that claims nothing is graded on nothing, so an
    empty COVERS is rejected — claiming less is not a way to pass.

    The counterpart to TransactionPredictor. It never says what SHOULD have
    happened; it says which rules what DID happen broke. Use it wherever the
    correct output is a set rather than a value:

      * feedback loops (scheduler <-> bank_tracker) — no entry/exit to predict
        across, but bank state must stay consistent and no illegal command may
        be issued for the current state
      * end-to-end and full-controller paths — many legal command orderings,
        but data integrity, liveness, row-hit priority and refresh bounds all
        still hold

    Lifecycle mirrors the predictor: reset() -> observe() per transaction, in
    observed order -> final() once at end of trace. Timing rules belong in SVA,
    not here; a checker sees order, not cycles.
    """

    INPUT_IFACES: tuple = ()
    OUTPUT_IFACES: tuple = ()
    COVERS: tuple = ()          # failure_taxonomy ids this checker detects

    @abstractmethod
    def __init__(self, spec: dict):
        ...

    @abstractmethod
    def reset(self) -> None:
        """Return all tracked state to power-on."""

    @abstractmethod
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction (input OR output — a checker sees
        both sides). Return any rules it broke, usually none."""

    @abstractmethod
    def final(self) -> List[Violation]:
        """End-of-trace rules: liveness and completeness. Requests still
        outstanding here are exactly what a starvation check reports."""


# =============================================================================
# Loading and gating generated predictors
# =============================================================================

def load_predictor_module(path: str):
    spec = importlib.util.spec_from_file_location(
        os.path.splitext(os.path.basename(path))[0], path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def find_model_classes(mod, base):
    """Subclasses of `base` defined in this module (excluding the base)."""
    return [obj for _, obj in inspect.getmembers(mod, inspect.isclass)
            if issubclass(obj, base) and obj is not base]


def find_predictor_class(mod):
    """The module must define exactly one TransactionPredictor subclass."""
    return find_model_classes(mod, TransactionPredictor)


def contract_check(path: str, spec: dict, strategy: str = "exact") -> List[str]:
    """Structural gate for an agent-generated model file.

    `strategy` selects which contract applies (see CHECK_STRATEGIES):
    exact/composed require a TransactionPredictor, invariant requires a
    LegalityChecker, observe requires no model at all.

    Returns a list of violations (empty = pass). These strings are fed back to
    the agent verbatim in its repair loop, so they are written to be
    actionable, not merely true.
    """
    if strategy not in CHECK_STRATEGIES:
        return [f"unknown check strategy {strategy!r}; "
                f"expected one of {list(CHECK_STRATEGIES)}"]

    want = STRATEGY_NEEDS_MODEL[strategy]
    if want is None:
        return []          # 'observe' scopes have nothing to gate

    base = TransactionPredictor if want == "predictor" else LegalityChecker
    errors = []
    try:
        mod = load_predictor_module(path)
    except SyntaxError as e:
        return [f"file does not parse: line {e.lineno}: {e.msg}"]
    except Exception as e:
        return [f"file does not import: {type(e).__name__}: {e}"]

    classes = find_model_classes(mod, base)
    other = find_model_classes(
        mod, LegalityChecker if want == "predictor" else TransactionPredictor)
    if len(classes) == 0:
        if other:
            return [f"this scope uses strategy {strategy!r}, which requires a "
                    f"subclass of {base.__name__}, but the file defines "
                    f"{[c.__name__ for c in other]} "
                    f"({'LegalityChecker' if want == 'predictor' else 'TransactionPredictor'})."]
        return [f"no subclass of {base.__name__} found. The model class must "
                f"inherit from txn_contract.{base.__name__}."]
    if len(classes) > 1:
        return [f"exactly one {base.__name__} subclass is allowed, "
                f"found {len(classes)}: {[c.__name__ for c in classes]}"]
    cls = classes[0]

    # A predictor with no inputs can predict nothing, so both sides are
    # required. A CHECKER may legitimately consume nothing: a feedback-loop
    # checker judges only the command stream the loop emits (its stage
    # declares input_ifaces: []). What no model may do is declare nothing at
    # all.
    if want == "predictor":
        if not cls.INPUT_IFACES:
            errors.append(f"{cls.__name__}.INPUT_IFACES is empty — declare "
                          f"the schema interface names this model consumes.")
        if not cls.OUTPUT_IFACES:
            errors.append(f"{cls.__name__}.OUTPUT_IFACES is empty — declare "
                          f"the schema interface names this model produces.")
    elif not cls.INPUT_IFACES and not cls.OUTPUT_IFACES:
        # A checker may watch only inputs (a liveness checker over
        # requests) or only outputs (a loop's command stream); it just
        # cannot watch nothing.
        errors.append(f"{cls.__name__} declares no interfaces at all; a "
                      f"checker observing nothing checks nothing.")

    try:
        inst = cls(spec)
    except Exception as e:
        return errors + [f"{cls.__name__}(spec) failed to construct: "
                         f"{type(e).__name__}: {e}. __init__ must accept the "
                         f"spec dict as its only argument."]

    try:
        inst.reset()
    except Exception as e:
        errors.append(f"reset() raised {type(e).__name__}: {e}")

    unknown = Txn(iface="__nonexistent__", kind="noop")
    if want == "predictor":
        try:
            out = inst.process(unknown)
            if out != []:
                errors.append("process() must return [] for transactions on "
                              f"interfaces it does not model; got {out!r}.")
        except Exception as e:
            errors.append(f"process() must ignore unknown interfaces, but "
                          f"raised {type(e).__name__}: {e}")
        try:
            out = inst.drain()
            if not isinstance(out, list):
                errors.append(f"drain() must return a list, got "
                              f"{type(out).__name__}")
        except Exception as e:
            errors.append(f"drain() raised {type(e).__name__}: {e}")
    else:
        try:
            out = inst.observe(unknown)
            if not isinstance(out, list):
                errors.append(f"observe() must return a list of Violation, got "
                              f"{type(out).__name__}")
            elif out:
                errors.append("observe() must return [] for transactions on "
                              f"interfaces it does not model; got {out!r}.")
        except Exception as e:
            errors.append(f"observe() must ignore unknown interfaces, but "
                          f"raised {type(e).__name__}: {e}")
        try:
            out = inst.final()
            if not isinstance(out, list):
                errors.append(f"final() must return a list of Violation, got "
                              f"{type(out).__name__}")
            elif out and not all(isinstance(v, Violation) for v in out):
                errors.append("final() must return Violation objects; got "
                              f"{[type(v).__name__ for v in out]}")
        except Exception as e:
            errors.append(f"final() raised {type(e).__name__}: {e}")

    return errors


# =============================================================================
# Reading a scope's strategy from path_definitions.json
# =============================================================================

def strategy_for_scope(scope: str, path_defs_path: str,
                       default: str = "exact") -> str:
    """Which checking shape this scope uses. Read from data, never inferred
    from the scope's name, so a new design carries its own answer."""
    try:
        with open(path_defs_path) as f:
            defs = json.load(f)
    except (OSError, ValueError):
        return default
    for p in defs.get("paths", []):
        if p.get("id") == scope:
            strat = p.get("check_strategy", default)
            return strat if strat in CHECK_STRATEGIES else default
    return default
