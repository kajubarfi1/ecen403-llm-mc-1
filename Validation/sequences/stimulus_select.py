#!/usr/bin/env python3
"""
stimulus_select.py — one place that decides how a path is stimulated
=====================================================================
run_path.py and vmanager_session.py used to each carry their own copy of
"which block is the entry, which generator makes the sequence, how long to
run". They drifted (vManager picked the entry by looking for 'csr' in the
path id) and the status paths had no stimulus at all. This module is the
single source:

  entry_block(pdef, blocks, catalog, imap)
      the path's first block with a drivable request stream that is not fed
      from inside the chain; None means the path is autonomous (runs from
      reset with no driver — the init and calibration paths).

  generate_sequence(pdef, entry, out, seed, drives, override)
      writes the sequence file using the generator the path declares
      (stimulus_generator: register_walk / status_poll / refresh_stress) or
      the default: a register walk for a CSR entry at seed 1, constrained
      random otherwise.

  window(pdef, cli_settle)
      cycles to simulate after the driver finishes (settle_cycles), or the
      whole observation window for an autonomous path (window_cycles).
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)

DEFAULT_WINDOW = 150_000     # past the ~140k-cycle boot of the present design
DEFAULT_SETTLE = 64


def _run(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=ROOT)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def internal_sinks(imap):
    """Ports already driven inside the chain: a driver on them would fight
    the design or dangle."""
    s = {c["to"] for c in imap["connections"]}
    s |= {t for g in imap.get("glue", []) for t in g["to"]}
    s |= {e["to"] for e in imap.get("expr_glue", [])}
    s |= {t for st in imap.get("stubs", []) for t in st.get("outputs", {}).values()}
    return s


def drivable(block, catalog, schemas, sinks):
    import sequence_contract as SC
    for name, d in catalog.items():
        if d.get("role") != "request" or d["block"] != block:
            continue
        if not ("drive" in d or d["qualifier"].isidentifier()):
            continue
        try:
            sp = SC.stimulus_ports(name, catalog, schemas)
        except Exception:
            continue
        if any(f"{block}.{p}" in sinks for p in sp["outputs"]):
            continue
        return True
    return False


def entry_block(pdef, blocks, catalog, schemas, imap, override=None):
    """The block whose request stream the sequence drives, or None for an
    autonomous path. The path's OWN blocks are tried first (a CSR path is
    driven at the CSR even though wb_port rides along in the support
    closure); wb_port is the fallback only when the path declares stimulus
    and none of its blocks can take it."""
    if override:
        return override
    sinks = internal_sinks(imap)
    for b in pdef["blocks"]:
        if drivable(b, catalog, schemas, sinks):
            return b
    if pdef.get("stimulus_kinds") or pdef.get("stimulus_generator"):
        return "wb_port" if "wb_port" in blocks else None
    return None


def generator_for(pdef, entry, seed):
    g = pdef.get("stimulus_generator")
    if g:
        return g
    if entry == "config_regs" and seed == 1:
        return "register_walk"
    return "random"


def generate_sequence(pdef, entry, out, seed=1, drives=19, override=None,
                      kinds=None):
    """Write the path's stimulus to `out`; returns (rc, output, generator)."""
    gen = override or generator_for(pdef, entry, seed)
    if kinds is None:
        kinds = ",".join(pdef.get("stimulus_kinds", ["write"]))
    if gen == "register_walk":
        cmd = f"python3 Validation/sequences/register_walk.py --out {out}"
    elif gen == "status_poll":
        win = pdef.get("window_cycles", DEFAULT_WINDOW)
        cmd = (f"python3 Validation/sequences/status_poll.py --window {win} "
               f"--out {out}")
    elif gen == "refresh_stress":
        cmd = (f"python3 Validation/sequences/refresh_stress.py --seed {seed} "
               f"--drives {max(drives, 600)} --out {out}")
    elif gen == "burst":
        cmd = f"python3 Validation/sequences/burst.py --seed {seed} --out {out}"
    elif gen == "random":
        cmd = (f"python3 Validation/closure/random_sequence.py --scope {entry} "
               f"--seed {seed} --drives {drives} --kinds {kinds} --out {out}")
    else:
        return 2, f"unknown stimulus_generator {gen!r} on {pdef['id']}", gen
    rc, text = _run(cmd)
    return rc, text, gen


def window(pdef, autonomous, cli_settle=None):
    """Cycles the harness keeps simulating: the whole window for an
    autonomous path, the post-driver drain otherwise. A CLI value that is
    not the default overrides the path's declaration."""
    if cli_settle is not None and cli_settle != DEFAULT_SETTLE:
        return cli_settle
    if autonomous:
        return pdef.get("window_cycles", DEFAULT_WINDOW)
    return pdef.get("settle_cycles", DEFAULT_SETTLE)
