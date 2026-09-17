#!/usr/bin/env python3
"""
sequence_contract.py — what a generated stimulus sequence is, and its gate
===========================================================================
The other half of the agent's job. The predictor says what SHOULD happen; a
sequence decides what to TRY. They are graded completely differently, and the
difference is the point:

    a predictor must be RIGHT   -> graded by spec-derived acceptance tests,
                                   because a wrong one lies about the design
    a sequence need only be INTERESTING -> graded by whether coverage moved,
                                   because a bad one costs a simulation

That asymmetry is why stimulus is the most defensible thing to hand an LLM.
Choosing which corner of a timing constraint to probe is genuinely
underdetermined — there is no algorithm for it — and the metric that judges
the answer (functional coverage against a spec-derived vplan) is one the
model cannot influence.

A sequence is a list of steps at TRANSACTION level, never SystemVerilog. The
agent writes intent; deterministic codegen turns it into a driver. That keeps
timing, sampling and protocol mechanics out of the model's hands for exactly
the reason the monitors are generated rather than prompted.

Steps:
    {"op": "reset"}                       assert reset, then release
    {"op": "drive", "iface": ..., "kind": ..., "fields": {...}}
    {"op": "idle",  "cycles": N}          N cycles with no stimulus

`idle` is not filler: it is how a sequence controls SPACING, and spacing is
what the timing coverage bins measure. A sequence with no idles can never hit
an at_minimum bin except by accident.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

VALID_OPS = ("reset", "drive", "idle")
MAX_STEPS = 4000            # a runaway sequence wastes cluster time
MAX_IDLE = 2000


class SequenceError(Exception):
    """Rejection reasons are fed back to the agent verbatim, so they are
    written as repair instructions rather than observations."""


IDENT = __import__("re").compile(r"^[A-Za-z_][A-Za-z0-9_$]*$")


def _manifest_width(block, port):
    """Width of a port not in any schema (e.g. a held byte-enable), from the
    block's newest manifest — the design's own declaration."""
    import glob
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{block}_manifest.json"),
                             recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    for mp in paths[:1]:
        with open(mp) as f:
            for group in json.load(f)["ports"].values():
                for p in group:
                    if p["name"] == port:
                        return p["width"]
    raise SequenceError(
        f"drive declaration names port {port!r}, but block {block!r}'s "
        f"manifest has no such port.")


def stimulus_ports(iface, catalog, schemas):
    """The signals a driver of this interface owns and observes.

    Shared by driver_gen.py (which emits the driver) and harness_gen.py
    (which instantiates it), so the two cannot disagree about the port list.

    Returns {"outputs": {port: width}, "inputs": {port: 1}}.

    Two driving styles, decided by catalog data:

      * `drive` declaration present — a handshake bus. The observation
        qualifier involves a completion signal the DUT owns (csr is observed
        on csr_ack_o), so the driver asserts the declared request signals,
        waits for `complete`, and never touches the qualifier expression.
      * no declaration — a valid-style stream whose qualifier is a single
        DUT input the driver asserts directly. Anything else (an expression,
        or a DUT output) is refused loudly: driving an observation qualifier
        is how a testbench ends up fighting the DUT for a net.
    """
    cat, sch = catalog[iface], schemas[iface]
    outs, ins = {}, {}
    for kind, fields in sch["kinds"].items():
        for info in fields.values():
            outs[info["port"]] = info["width"]

    drv = cat.get("drive")
    if drv:
        for sig in drv.get("assert", []):
            outs[sig] = 1
        for kind, sigs in drv.get("assert_by_kind", {}).items():
            for sig in sigs:
                outs[sig] = 1
        for sig in drv.get("hold", {}):
            if sig not in outs:
                outs[sig] = _manifest_width(cat["block"], sig)
        if drv.get("complete"):
            ins[drv["complete"]] = 1
    else:
        q = cat["qualifier"]
        if not IDENT.match(q):
            raise SequenceError(
                f"interface {iface!r} has qualifier {q!r}, which is an "
                f"expression, so a driver cannot assert it. Declare how to "
                f"initiate a transaction with a 'drive' block in "
                f"interface_catalog.json (assert / assert_by_kind / "
                f"complete).")
        outs[q] = 1

    ks = cat.get("kind_select")
    if ks:
        outs[ks["expr"]] = 1
    return {"outputs": outs, "inputs": ins}


def validate(seq, schemas, drivable_ifaces, require_targets=True):
    """Structural gate. Returns a list of actionable failure strings.

    This checks only that the sequence is RUNNABLE and non-trivial. Whether it
    is any GOOD is decided by coverage after it runs — the honest gate for
    stimulus, and one the model cannot game.
    """
    errs = []
    if not isinstance(seq, dict):
        return [f"a sequence must be a JSON object, got {type(seq).__name__}"]

    required = ("name", "targets", "steps") if require_targets else ("name", "steps")
    for key in required:
        if key not in seq:
            errs.append(f"missing required key {key!r}. 'targets' must list the "
                        f"vplan item ids this sequence is trying to cover, so a "
                        f"coverage change can be attributed to it.")
    if errs:
        return errs

    steps = seq["steps"]
    if not isinstance(steps, list) or not steps:
        return ["'steps' must be a non-empty list."]
    if len(steps) > MAX_STEPS:
        return [f"{len(steps)} steps exceeds the {MAX_STEPS} limit; a sequence "
                f"this long is a regression, not a targeted stimulus."]

    n_drive = 0
    for i, st in enumerate(steps):
        where = f"step {i}"
        if not isinstance(st, dict) or "op" not in st:
            errs.append(f"{where}: each step must be an object with an 'op'.")
            continue
        op = st["op"]
        if op not in VALID_OPS:
            errs.append(f"{where}: unknown op {op!r}; valid ops are "
                        f"{list(VALID_OPS)}.")
            continue

        if op == "idle":
            n = st.get("cycles")
            if not isinstance(n, int) or n < 1:
                errs.append(f"{where}: 'idle' needs a positive integer "
                            f"'cycles', got {n!r}.")
            elif n > MAX_IDLE:
                errs.append(f"{where}: idle of {n} cycles exceeds {MAX_IDLE}.")
            continue

        if op == "drive":
            n_drive += 1
            iface, kind = st.get("iface"), st.get("kind")
            if iface not in drivable_ifaces:
                errs.append(
                    f"{where}: cannot drive {iface!r}. Only these interfaces "
                    f"are stimulus surfaces for this scope: "
                    f"{sorted(drivable_ifaces)}. A response interface is "
                    f"produced by the design, not driven into it.")
                continue
            kinds = schemas[iface]["kinds"]
            if kind not in kinds:
                errs.append(f"{where}: {iface} has no kind {kind!r}; "
                            f"schema defines {sorted(kinds)}.")
                continue
            want = set(kinds[kind])
            got = set(st.get("fields", {}))
            if got != want:
                missing, extra = sorted(want - got), sorted(got - want)
                errs.append(
                    f"{where}: {iface}.{kind} fields "
                    + (f"missing {missing} " if missing else "")
                    + (f"unexpected {extra} " if extra else "")
                    + f"— drive exactly {sorted(want)}.")
                continue
            for fname, val in st["fields"].items():
                if not isinstance(val, int) or val < 0:
                    errs.append(f"{where}: field {fname!r} must be a "
                                f"non-negative integer, got {val!r}.")
                    continue
                width = kinds[kind][fname]["width"]
                if isinstance(width, int) and val >= (1 << width):
                    errs.append(
                        f"{where}: field {fname!r} = {val} does not fit in "
                        f"{width} bit(s) (max {(1 << width) - 1}).")

    if n_drive == 0:
        errs.append("the sequence drives nothing — it contains no 'drive' "
                    "steps, so it cannot exercise the design.")

    if require_targets and not seq.get("targets"):
        errs.append("'targets' is empty. Name the vplan item ids this sequence "
                    "aims to cover; an untargeted sequence cannot be credited "
                    "with a coverage change.")
    if not require_targets and seq.get("targets"):
        errs.append("this sequence was validated as an untargeted control but "
                    "declares targets. A control that aims at holes is not a "
                    "control — it is the treatment.")
    return errs


def load(path):
    with open(path) as f:
        return json.load(f)


def save(seq, path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(seq, f, indent=2)


def summarize(seq):
    steps = seq.get("steps", [])
    n_drive = sum(1 for s in steps if s.get("op") == "drive")
    n_idle = sum(1 for s in steps if s.get("op") == "idle")
    cycles = sum(s.get("cycles", 0) for s in steps if s.get("op") == "idle")
    return (f"{seq.get('name','(unnamed)')}: {len(steps)} step(s) "
            f"({n_drive} drive, {n_idle} idle covering {cycles} cycle(s)), "
            f"targets {seq.get('targets', [])}")
