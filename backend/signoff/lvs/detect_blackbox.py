#!/usr/bin/env python3
"""Find library cells whose extracted layout and vendor CDL disagree on device count.

SkyWater's GDS for some standard cells splits a series branch into two transistors
where its own CDL draws one, so LVS compares them as unequal and the whole top-level
comparison is Skipped. Those cells have to be compared by pin connectivity instead
(`blank_circuit` in the deck).

The list used to be hardcoded, so it only ever contained cells that had already
broken a run. On 2026-09-24 a `scheduler` build at 5 ns picked `a21boi_2` and
`o211a_4` — two gates no earlier run had used — and LVS failed in a way that looks
identical to a real design defect. This detects the condition instead of enumerating
it, and records the evidence for each cell it adds.

A cell is added only when it has devices in BOTH files and the counts differ. A zero
count in the layout means the cell is already black-boxed (or absent), which is not
evidence of anything.

usage:
  detect_blackbox.py --extracted extracted.cir --reference reference.cdl [--apply]
"""
from __future__ import annotations

import argparse
import json
import re
from datetime import date
from pathlib import Path
from typing import Dict, List

HERE = Path(__file__).resolve().parent
LIST_FILE = HERE / "blackbox_cells.txt"
EVIDENCE_FILE = HERE / "blackbox_cells.json"

SUBCKT = re.compile(r"^\.SUBCKT\s+(\S+)", re.IGNORECASE)
ENDS = re.compile(r"^\.ENDS", re.IGNORECASE)
DEVICE = re.compile(r"^[MX]\S*", re.IGNORECASE)
PREFIX = "sky130_fd_sc_hd__"


def device_counts(path: Path) -> Dict[str, int]:
    """Devices per subcircuit, keyed by lowercase cell name."""
    counts: Dict[str, int] = {}
    name, n = None, 0
    for line in path.read_text(errors="ignore").splitlines():
        line = line.strip()
        m = SUBCKT.match(line)
        if m:
            name, n = m.group(1).lower(), 0
            continue
        if name and ENDS.match(line):
            counts[name] = n
            name = None
            continue
        if name and DEVICE.match(line):
            n += 1
    return counts


def read_list(path: Path = LIST_FILE) -> List[str]:
    if not path.exists():
        return []
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            out.append(line)
    return out


def detect(extracted: Path, reference: Path, known: List[str]) -> List[Dict]:
    """Cells that disagree and are not already black-boxed."""
    lay, ref = device_counts(extracted), device_counts(reference)
    known_set = {k.lower() for k in known}
    found = []
    for cell, ref_n in sorted(ref.items()):
        if not cell.startswith(PREFIX):
            continue
        base = cell[len(PREFIX):]
        if base in known_set:
            continue
        lay_n = lay.get(cell)
        # Both must actually have devices. A 0 in the layout means already
        # black-boxed or not extracted, which proves nothing about the cell.
        if not lay_n or not ref_n or lay_n == ref_n:
            continue
        found.append({"cell": base, "layout_devices": lay_n, "cdl_devices": ref_n,
                      "delta": lay_n - ref_n, "discovered": date.today().isoformat()})
    return found


def apply(found: List[Dict], known: List[str],
          list_file: Path = LIST_FILE, evidence_file: Path = EVIDENCE_FILE) -> None:
    """Append to the list and record why each cell is on it.

    `list_file` is a parameter because sign-off mounts this directory read-only:
    inside the container the merged list has to be written to the writable output
    mount and handed to the deck via `-rd blackbox_list=...`.
    """
    list_file.parent.mkdir(parents=True, exist_ok=True)
    list_file.write_text(
        "# Library cells compared by pin connectivity only (blank_circuit in the deck).\n"
        "# SkyWater's GDS splits series branches its own CDL draws as single devices,\n"
        "# so a transistor-level comparison of these cells can never match.\n"
        "# Maintained by detect_blackbox.py - see blackbox_cells.json for the evidence.\n"
        "# ASCII only: the deck reads this from Ruby, whose default encoding is US-ASCII.\n"
        + "\n".join(known + [f["cell"] for f in found]) + "\n", encoding="utf-8")

    evidence = {}
    if evidence_file.exists():
        try:
            evidence = json.loads(evidence_file.read_text(encoding="utf-8"))
        except Exception:
            evidence = {}
    for f in found:
        evidence[f["cell"]] = f
    evidence_file.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n",
                             encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--extracted", type=Path, required=True)
    ap.add_argument("--reference", type=Path, required=True)
    ap.add_argument("--apply", action="store_true",
                    help="Add what is found to the list and record the evidence.")
    ap.add_argument("--list-out", type=Path, default=None,
                    help="Where to write the merged list. Defaults to blackbox_cells.txt "
                         "beside this script; sign-off passes a writable path because it "
                         "mounts this directory read-only.")
    a = ap.parse_args()

    known = read_list()
    found = detect(a.extracted, a.reference, known)
    for f in found:
        print(f"BLACKBOX-DETECT {f['cell']} layout={f['layout_devices']} "
              f"cdl={f['cdl_devices']} delta={f['delta']:+d}")
    if found and a.apply:
        out_list = a.list_out or LIST_FILE
        apply(found, known, out_list,
              out_list.parent / "blackbox_cells.json" if a.list_out else EVIDENCE_FILE)
        print(f"BLACKBOX-DETECT applied={len(found)} total={len(known) + len(found)} "
              f"list={out_list}")
        if a.list_out:
            # The run can use this, but it dies with the container. Say what to keep.
            print("BLACKBOX-DETECT PERSIST add to signoff/lvs/blackbox_cells.txt: "
                  + " ".join(f["cell"] for f in found))
    elif not found:
        print(f"BLACKBOX-DETECT none (known={len(known)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
