#!/usr/bin/env python3
"""
rtl_drop.py — the one place that says which RTL is under validation
====================================================================
Nine tools used to find a block's RTL and manifest the same way: the newest
`<block>.sv` anywhere under Frontend/. That was fine while the Frontend tree
held exactly one copy of each block. After the September drop it also holds
demo copies with deliberate bugs, failed attempts and per-trial directories,
and "newest anywhere" resolved five of eleven blocks to a failed attempt —
silently. A validation flow that cannot say which design it validated has
proved nothing.

This module resolves every block through the roots declared in
Validation/spec/rtl_drop.json, in order, and nowhere else:

  rtl_file(block)        the block's RTL in the first root that has it
  manifest_file(block)   its manifest, preferring the drop's consolidated
                         (lint) copy over the per-phase one
  manifest_ports(block)  {port: {"width", "dir", "group"}} from that manifest
  missing(blocks)        blocks no root provides — reported, never substituted
  stamp(blocks)          what was resolved, from where, at which git commit;
                         goes into every run report so a verdict names the
                         design it judged

Usage (as a check):
    python3 Validation/structural/rtl_drop.py            # resolve every catalog block
"""

import glob
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CONFIG = os.path.join(ROOT, "Validation", "spec", "rtl_drop.json")
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")


class DropError(Exception):
    """A block the declared drop does not provide. Never guess a substitute."""


def _config():
    with open(CONFIG) as f:
        return json.load(f)


def roots():
    """Absolute drop roots, in priority order. Missing roots are skipped so
    a config listing a snapshot that is not checked out still works."""
    # VALIDATION_RTL_DROP_ROOTS overrides the config for one process tree:
    # the seeded-fault suite points a run at a mutated copy of the drop
    # without touching the declared roots. The stamp records which root was
    # used, so a mutant run can never be mistaken for a real one.
    env = os.environ.get("VALIDATION_RTL_DROP_ROOTS")
    declared = env.split(os.pathsep) if env else _config()["roots"]
    out = []
    for r in declared:
        p = os.path.realpath(r if os.path.isabs(r) else os.path.join(ROOT, r))
        if os.path.isdir(p):
            out.append(p)
    return out


def _find(block, pattern):
    """First root with a match; within that root, prefer the paths the
    config lists, then the newest copy. Returns (path, root) or (None, None)."""
    pref = _config().get("manifest_dirs_preferred", [])
    for root in roots():
        hits = glob.glob(os.path.join(root, "**", pattern), recursive=True)
        if not hits:
            continue
        for d in pref:
            for h in hits:
                if os.path.relpath(h, root).startswith(d + os.sep):
                    return h, root
        hits.sort(key=lambda p: (-os.path.getmtime(p), p))
        return hits[0], root
    return None, None


def rtl_file(block):
    p, _ = _find(block, f"{block}.sv")
    if not p:
        raise DropError(
            f"no {block}.sv in the declared RTL drop "
            f"({', '.join(os.path.relpath(r, ROOT) for r in roots())}). "
            f"The block is missing from the drop — request it from the "
            f"Frontend or add a snapshot root in Validation/spec/rtl_drop.json.")
    return p


def manifest_file(block):
    p, _ = _find(block, f"{block}_manifest.json")
    if not p:
        raise DropError(
            f"no {block}_manifest.json in the declared RTL drop "
            f"({', '.join(os.path.relpath(r, ROOT) for r in roots())}).")
    return p


def manifest_ports(block):
    with open(manifest_file(block)) as f:
        m = json.load(f)
    out = {}
    for group, plist in m.get("ports", {}).items():
        for p in plist:
            out[p["name"]] = {"width": p["width"], "dir": p["dir"],
                              "group": group}
    return out


def missing(blocks):
    out = []
    for b in blocks:
        try:
            rtl_file(b)
            manifest_file(b)
        except DropError:
            out.append(b)
    return out


def _git_head():
    try:
        r = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                           capture_output=True, text=True)
        return r.stdout.strip() or None
    except Exception:
        return None


def stamp(blocks):
    """Which files were validated, from which root, at which commit."""
    out = {"git_head": _git_head(),
           "roots": [os.path.relpath(r, ROOT) for r in roots()],
           "blocks": {}}
    for b in blocks:
        entry = {}
        for key, fn in (("rtl", rtl_file), ("manifest", manifest_file)):
            try:
                entry[key] = os.path.relpath(fn(b), ROOT)
            except DropError:
                entry[key] = None
        out["blocks"][b] = entry
    return out


def main() -> int:
    with open(CATALOG) as f:
        blocks = sorted({d["block"] for d in json.load(f)["interfaces"].values()})
    st = stamp(blocks)
    print(f"  drop roots : {', '.join(st['roots']) or 'NONE PRESENT'}")
    print(f"  git head   : {st['git_head']}\n")
    bad = 0
    for b, e in st["blocks"].items():
        ok = e["rtl"] and e["manifest"]
        bad += not ok
        print(f"  {'ok     ' if ok else 'MISSING'} {b:13} "
              f"{e['rtl'] or '—':52} {e['manifest'] or '—'}")
    print(f"\n  {len(blocks) - bad}/{len(blocks)} block(s) resolved"
          + (f"; missing: {[b for b, e in st['blocks'].items() if not (e['rtl'] and e['manifest'])]}"
             if bad else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
