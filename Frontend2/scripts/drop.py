"""
drop.py -- the Frontend's side of Validation/findings/HANDOFF_CONTRACT.md.

  compute_drop_id(root)      the drop's content-hash identity (contract §2).
                             Own implementation, deliberately not imported
                             from Validation; verified equal to
                             Validation/structural/rtl_drop.py:drop_id().
  spec_consistency(root)     every manifest's spec_revision must equal the
                             shipped generated_spec.json's revision; a block
                             from another revision is "foreign" and Validation
                             will block every path through it (contract §1).
  ship_spec(spec, root)      writes <root>/generated_spec.json (contract §1).
  read_handoff(outbox, id)   reads outbox/current/HANDOFF.json and says whether
                             it is about THIS drop (contract §4).
"""
from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path

RTL_DIRS = ("PHASE1RTL", "PHASE2RTL", "PHASE3RTL", "PHASE4RTL")


def _block_files(root: Path) -> dict:
    """{block: (sv_path, manifest_path)} from the phase directories only
    (TOPRTL copies are never the drop). First phase dir with the file wins."""
    blocks = {}
    for d in RTL_DIRS:
        for m in sorted((root / d).glob("*_manifest.json")) if (root / d).is_dir() else []:
            name = m.name[: -len("_manifest.json")]
            blocks.setdefault(name, {})
    for name in blocks:
        for kind, fn in (("sv", f"{name}.sv"), ("manifest", f"{name}_manifest.json")):
            for d in RTL_DIRS:
                p = root / d / fn
                if p.is_file():
                    blocks[name][kind] = p
                    break
    return blocks


CATALOG = Path(__file__).resolve().parents[2] / "Validation" / "txn" / "interface_catalog.json"


def catalog_blocks() -> list | None:
    """The blocks Validation's drop_id covers. The contract says "each
    block", but Validation/structural/rtl_drop.py:drop_id() hashes only the
    blocks in its interface catalog (today 9 of 11: no addr_decoder or
    bank_tracker), so matching its id means using the same set. None when
    the catalog isn't on disk (then every block in the drop is hashed)."""
    try:
        return sorted({d["block"] for d in json.loads(CATALOG.read_text())["interfaces"].values()})
    except Exception:
        return None


def compute_drop_id(root, blocks=None) -> str:
    h, n = hashlib.sha256(), 0
    have = _block_files(Path(root))
    blocks = blocks or catalog_blocks() or sorted(have)
    for b in sorted(blocks):
        if b not in have:
            continue
        for kind in ("sv", "manifest"):
            p = have[b].get(kind)
            if p:
                h.update(b.encode())
                h.update(p.read_bytes())
                n += 1
    return h.hexdigest()[:12] if n else "empty"


def ship_spec(spec_path, root) -> Path:
    dest = Path(root) / "generated_spec.json"
    if not (dest.exists() and dest.samefile(spec_path)):
        shutil.copyfile(spec_path, dest)
    return dest


def spec_consistency(root) -> dict:
    """{"spec_revision", "foreign": {block: revision}, "ok": bool}"""
    root = Path(root)
    sp = root / "generated_spec.json"
    rev = json.loads(sp.read_text()).get("revision") if sp.is_file() else None
    foreign = {}
    for b, f in _block_files(root).items():
        mrev = json.loads(f["manifest"].read_text()).get("spec_revision") if "manifest" in f else None
        if rev and mrev != rev:
            foreign[b] = mrev
    return {"spec_revision": rev, "foreign": foreign, "ok": bool(rev) and not foreign}


def read_handoff(outbox, drop_id: str) -> dict:
    """outbox/current/HANDOFF.json plus whether it matches `drop_id`."""
    p = Path(outbox) / "current" / "HANDOFF.json"
    if not p.is_file():
        return {"present": False, "matches": False}
    h = json.loads(p.read_text())
    return {"present": True, "matches": h.get("drop_id") == drop_id, "handoff": h}


def revision_mismatches(root, spec_path, phases=RTL_DIRS) -> dict:
    """{block: spec_revision} for every block in `phases` whose manifest says it
    was generated from a different spec revision than `spec_path`'s. One
    generation = one spec (HANDOFF_FRONTEND_2026-10-01.md §1): a drop built
    from two specs has no single contract and Validation blocks every path
    across the seam."""
    want = json.loads(Path(spec_path).read_text()).get("revision")
    out = {}
    for d in phases:
        for m in sorted((Path(root) / d).glob("*_manifest.json")) if (Path(root) / d).is_dir() else []:
            rev = json.loads(m.read_text()).get("spec_revision")
            if rev != want:
                out[m.name[: -len("_manifest.json")]] = rev
    return out


def top_copy_mismatches(root) -> list:
    """TOPRTL copies that differ from the phase output they claim to be."""
    root, bad = Path(root), []
    for b, f in _block_files(root).items():
        top = root / "TOPRTL" / f"{b}.sv"
        if "sv" in f and top.is_file() and top.read_bytes() != f["sv"].read_bytes():
            bad.append(b)
    return bad
