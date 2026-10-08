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
import hashlib
import json
import re
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


def _same(paths):
    """True when every file has identical content."""
    with open(paths[0], "rb") as f:
        ref = f.read()
    for q in paths[1:]:
        with open(q, "rb") as f:
            if f.read() != ref:
                return False
    return True


def _find(block, pattern):
    """First root with a match; within that root, prefer the directories the
    config lists (`manifest_dirs_preferred` for manifests, `rtl_dirs_preferred`
    for RTL). Several copies that are byte-identical are one file. Several
    copies that DIFFER and none in a preferred directory is an ambiguous
    drop: refused, never settled by file age -- the age heuristic once
    resolved five blocks to a failed attempt, and on 2026-10-01 it picked
    between a phase output and a top-level assembly generated from two
    different specs. Returns (path, root) or (None, None)."""
    cfg = _config()
    # manifests: the consolidated lint copies first, then the phase
    # directories (the same preference as the RTL -- a repair agent that
    # drops a regenerated manifest at the drop root must not make the phase
    # copy ambiguous, 2026-10-07)
    pref = (cfg.get("manifest_dirs_preferred", []) + cfg.get("rtl_dirs_preferred", [])
            if pattern.endswith("_manifest.json") else cfg.get("rtl_dirs_preferred", []))
    for root in roots():
        hits = sorted(glob.glob(os.path.join(root, "**", pattern), recursive=True))
        if not hits:
            continue
        for d in pref:
            for h in hits:
                if os.path.relpath(h, root).startswith(d + os.sep):
                    return h, root
        if len(hits) > 1 and not _same(hits):
            raise DropError(
                f"{block}: {len(hits)} differing copies of {pattern} under "
                f"{os.path.relpath(root, ROOT)} ({', '.join(os.path.relpath(h, root) for h in hits)}) "
                f"and none is in a preferred directory. Declare which layout is the drop "
                f"(rtl_dirs_preferred / manifest_dirs_preferred in Validation/spec/rtl_drop.json); "
                f"a differing copy is never chosen by age.")
        return hits[0], root
    return None, None


_SPEC_STAMP = re.compile(r"^//\s*Spec:\s*(\S+)\s+rev\s+(\S+)", re.M)


def spec_stamp(block):
    """(design_id, revision) the generator stamped on the block: the manifest's
    `design_id`/`spec_revision` first, else the RTL header's `// Spec:` line,
    else (None, None)."""
    try:
        with open(manifest_file(block)) as f:
            m = json.load(f)
        if m.get("spec_revision"):
            return m.get("design_id"), m["spec_revision"]
    except (DropError, OSError, ValueError):
        pass
    try:
        with open(rtl_file(block), errors="replace") as f:
            head = f.read(4000)
    except DropError:
        return None, None
    m = _SPEC_STAMP.search(head)
    return (m.group(1), m.group(2)) if m else (None, None)


def shipped_spec():
    """The spec the drop ships beside its RTL (generated_spec.json in a
    root), as (path, revision), or (None, None)."""
    for root in roots():
        p = os.path.join(root, "generated_spec.json")
        if os.path.exists(p):
            try:
                with open(p) as f:
                    return p, json.load(f).get("revision")
            except (OSError, ValueError):
                return p, None
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


PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")


def all_blocks():
    """Every block of the design (path_definitions.json `blocks`, 11 today).
    The interface catalog names only the blocks that own an interface (9:
    addr_decoder and bank_tracker consume and produce shared streams), so it
    is not the list a drop is identified by -- a drop id that ignored two
    blocks let an addr_decoder change keep its id (Lehana, 2026-10-01)."""
    try:
        with open(PATH_DEFS) as f:
            return sorted(json.load(f)["blocks"])
    except (OSError, ValueError, KeyError):
        return _catalog_blocks()


def _catalog_blocks():
    with open(CATALOG) as f:
        return sorted({d["block"] for d in json.load(f)["interfaces"].values()})


def frontend_commits(blocks=None):
    """{block: git_commit the Frontend's manifest records}, blocks without
    one omitted."""
    out = {}
    for b in blocks or all_blocks():
        try:
            with open(manifest_file(b)) as f:
                c = json.load(f).get("git_commit")
            if c:
                out[b] = c
        except (DropError, OSError, ValueError):
            pass
    return out


def drop_id(blocks=None):
    """The drop's identity, which names its reports and its outbox folder.

    It is a hash of the drop's OWN files -- EVERY block's RTL and manifest
    (all_blocks(): the 11 of path_definitions.json, not only the 9 the
    interface catalog names), in block order -- so it depends on nothing outside the drop: not on
    this repo's HEAD, not on the Frontend's, not on when the files were
    written. The same files always get the same id; one changed byte is a
    new drop. The Frontend can compute it from the files it just wrote
    (sha256 over `<block>.sv` then `<block>_manifest.json` contents, blocks
    sorted, first 12 hex digits) and match it against the result it reads
    back. Blocks the drop lacks contribute nothing, so a partial drop and
    the complete drop it grows into are different ids, as they should be.
    """
    h = hashlib.sha256()
    n = 0
    for b in sorted(blocks or all_blocks()):
        for fn in (rtl_file, manifest_file):
            try:
                p = fn(b)
            except DropError:
                continue
            with open(p, "rb") as f:
                h.update(b.encode())
                # line endings are the checkout's, not the drop's: a Windows
                # clone gets CRLF from git and computed ec49d485ca8d where
                # the Frontend published 4b86c7cd3705 (backend, 2026-10-08)
                h.update(f.read().replace(b"\r\n", b"\n"))
                n += 1
    return h.hexdigest()[:12] if n else "empty"


# What a regeneration changes without changing the design: the RTL header's
# generation timestamp and the manifest's provenance fields. Everything else
# in a file is design.
VOLATILE_RTL_LINE = re.compile(rb"^\s*//\s*Generated\b.*$")
VOLATILE_MANIFEST_KEYS = ("generated_utc", "git_commit", "generated_by", "generator_version")


def design_id(blocks=None):
    """The DESIGN's identity: `drop_id` with the volatile parts out -- RTL
    lines that only carry the generation timestamp, manifest keys that only
    carry provenance (VOLATILE_*). Two drops with equal design ids are the
    same design regenerated (a7cd3cb93546 vs 4b86c7cd3705: RTL byte-identical
    but for `// Generated:`); a changed design id is a changed design. The
    drop id still names the files and the reports; this answers "did the
    design change", which a stale-drop check keyed on the drop id cannot."""
    h = hashlib.sha256()
    n = 0
    for b in sorted(blocks or all_blocks()):
        try:
            p = rtl_file(b)
        except DropError:
            p = None
        if p:
            with open(p, "rb") as f:
                lines = [l for l in f.read().replace(b"\r\n", b"\n").split(b"\n")
                         if not VOLATILE_RTL_LINE.match(l)]
            h.update(b.encode())
            h.update(b"\n".join(lines))
            n += 1
        try:
            p = manifest_file(b)
        except DropError:
            p = None
        if p:
            try:
                with open(p) as f:
                    m = json.load(f)
                for k in VOLATILE_MANIFEST_KEYS:
                    m.pop(k, None)
                canon = json.dumps(m, sort_keys=True, separators=(",", ":")).encode()
            except ValueError:
                with open(p, "rb") as f:
                    canon = f.read().replace(b"\r\n", b"\n")
            h.update(b.encode())
            h.update(canon)
            n += 1
    return h.hexdigest()[:12] if n else "empty"


def stamp(blocks):
    """Which files were validated, from which root, at which commit."""
    # the drop's identity is the WHOLE drop's hash, whichever blocks this run
    # used (a per-path stamp over a subset gave every path a different id and
    # the emitter named the outbox after the first report it read, 2026-10-08)
    whole = drop_id()
    out = {"git_head": whole,                    # the drop's identity: a content hash (see drop_id); key kept for every reader
           "drop_id": whole,
           "design_id": design_id(),            # the design's identity: timestamps and provenance left out (see design_id)
           "blocks_used": sorted(blocks),
           "validated_at": _git_head(),          # informational only: this repo's HEAD, if any
           "frontend_commits": frontend_commits(blocks),   # informational: what the manifests record
           "roots": [os.path.relpath(r, ROOT) for r in roots()],
           "blocks": {}}
    for b in blocks:
        entry = {}
        for key, fn in (("rtl", rtl_file), ("manifest", manifest_file)):
            try:
                entry[key] = os.path.relpath(fn(b), ROOT)
            except DropError as e:
                entry[key] = None
                entry["error"] = str(e)
        entry["spec_revision"] = spec_stamp(b)[1] if entry.get("rtl") else None
        out["blocks"][b] = entry
    sp, rev = shipped_spec()
    out["shipped_spec"] = {"path": os.path.relpath(sp, ROOT) if sp else None, "revision": rev}
    return out


def main() -> int:
    blocks = all_blocks()
    st = stamp(blocks)
    print(f"  drop roots : {', '.join(st['roots']) or 'NONE PRESENT'}")
    n_gen = len(set(st["frontend_commits"].values()))
    print(f"  drop id    : {st['drop_id']}  (sha256 of the drop's RTL + manifests"
          + (f"; the manifests record {n_gen} generation commits" if n_gen > 1 else "") + ")")
    print(f"  validator  : HEAD {st['validated_at'] or '(no git)'}\n")
    bad = 0
    for b, e in st["blocks"].items():
        ok = e["rtl"] and e["manifest"]
        bad += not ok
        tag = "ok     " if ok else ("AMBIG  " if "differing copies" in e.get("error", "") else "MISSING")
        print(f"  {tag} {b:13} {e['rtl'] or '—':52} {e['manifest'] or '—'}"
              + (f"  [spec {e['spec_revision']}]" if e.get("spec_revision") else ""))
        if not ok and e.get("error"):
            print(f"          {e['error'][:150]}")
    if st["shipped_spec"]["path"]:
        print(f"\n  drop ships spec: {st['shipped_spec']['path']} rev {st['shipped_spec']['revision']}")
    print(f"\n  {len(blocks) - bad}/{len(blocks)} block(s) resolved"
          + (f"; missing: {[b for b, e in st['blocks'].items() if not (e['rtl'] and e['manifest'])]}"
             if bad else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
