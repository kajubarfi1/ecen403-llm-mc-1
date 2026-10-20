#!/usr/bin/env python3
"""
install_sky130_models.py — put the sky130_fd_sc_hd simulation models on Olympus
================================================================================
The backend's netlists (6_final.v) instantiate sky130_fd_sc_hd standard
cells. To run a netlist through the validation paths, Xcelium needs the
cells' functional models. Olympus has no sky130 PDK, so the models the
netlists need (Validation/refdesigns/sky130: the open-PDK cells, mirrored
in the PDK's own layout so their relative includes resolve) are installed
once under ~/cadence_agent_work/sky130/ with a file list run_path.py
references with `-F`.

    python3 Validation/tools/install_sky130_models.py            # install + smoke test
    python3 Validation/tools/install_sky130_models.py --check    # is it there?

The smoke test compiles backend/outputs/wb_port/6_final.v against the
library: a netlist that elaborates is the proof the install is usable.
"""

import argparse
import glob
import os
import sys
import tarfile
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
sys.path.insert(0, HERE)
LIB = os.path.join(ROOT, "Validation", "refdesigns", "sky130")
REMOTE = "cadence_agent_work/sky130"          # under $HOME
SMOKE = os.path.join(ROOT, "backend", "outputs", "wb_port", "6_final.v")

# what run_path.py adds to xrun for a netlist block; kept here so the two
# agree (functional models, zero unit delay, the installed file list)
XRUN_NETLIST_ARGS = "+define+FUNCTIONAL +define+UNIT_DELAY= -F $HOME/{remote}/cells.f".format(remote=REMOTE)


PDK_RAW = "https://raw.githubusercontent.com/google/skywater-pdk-libs-sky130_fd_sc_hd/main/"
NETLIST_GLOB = os.path.join(ROOT, "backend", "outputs", "*", "6_final.v")


def library_cells():
    """Every sky130_fd_sc_hd module the mirrored library defines."""
    import re
    have = set()
    for f in glob.glob(os.path.join(LIB, "**", "*.v"), recursive=True):
        with open(f, errors="replace") as fh:
            have |= set(re.findall(r"^\s*module\s+(sky130_fd_sc_hd__\w+)", fh.read(), re.M))
    return have


def cells_used(netlists):
    import re
    used = set()
    for n in netlists:
        with open(n, errors="replace") as fh:
            used |= set(re.findall(r"^\s*(sky130_fd_sc_hd__\w+)\s+\S+\s*\(", fh.read(), re.M))
    return used


def fetch_missing(netlists=None, quiet=False):
    """Mirror from the open PDK every cell the netlists instantiate that the
    library lacks (a drive strength the last build did not use, usually:
    23 on the 10-15 rebuild, ha_4 on the 10-20 one), with the base and
    functional model of a new family and the UDP primitives those include.
    Returns the cells fetched; raises if one cannot be fetched, because a
    netlist that does not elaborate is not a verdict."""
    import re
    import shutil
    import subprocess
    netlists = netlists or sorted(glob.glob(NETLIST_GLOB))
    have = library_cells()
    missing = sorted(cells_used(netlists) - have)
    if not missing:
        return []
    dl = tempfile.mkdtemp(prefix="sky130_dl_")

    def fetch(rel):
        dst = os.path.join(dl, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        r = subprocess.run(["curl", "-sf", "-o", dst, PDK_RAW + rel], capture_output=True)
        return r.returncode == 0

    want = []
    for cell in missing:
        fam = re.sub(r"_\d+$", "", cell[len("sky130_fd_sc_hd__"):])
        want.append(f"cells/{fam}/{cell}.v")
        if not os.path.isdir(os.path.join(LIB, "cells", fam)):
            want += [f"cells/{fam}/sky130_fd_sc_hd__{fam}.v", f"cells/{fam}/sky130_fd_sc_hd__{fam}.functional.v"]
    got, queue = [], list(dict.fromkeys(want))
    while queue:
        rel = queue.pop(0)
        if rel in got:
            continue
        if not fetch(rel):
            raise SystemExit(f"could not fetch {PDK_RAW}{rel} for the missing cell models {missing}")
        got.append(rel)
        with open(os.path.join(dl, rel), errors="replace") as fh:
            incs = re.findall(r"`include\s+\"([^\"]+)\"", fh.read())
        for inc in incs:
            if inc.endswith((".pp.v", ".behavioral.v")):
                continue            # only functional, no-power-pin models are compiled
            if glob.glob(os.path.join(LIB, "**", inc), recursive=True) or any(g.endswith("/" + inc) for g in got):
                continue
            if "udp" in inc:
                queue.append(f"models/{inc.replace('sky130_fd_sc_hd__', '').split('.')[0]}/{inc}")
            else:
                queue.append(f"cells/{os.path.basename(os.path.dirname(rel))}/{inc}")
    for rel in got:
        dst = os.path.join(LIB, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy(os.path.join(dl, rel), dst)
    if not quiet:
        print(f"  fetched {len(got)} file(s) from the open PDK for {len(missing)} missing cell(s): "
              + ", ".join(c.replace("sky130_fd_sc_hd__", "") for c in missing))
    return missing


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-smoke", action="store_true")
    ap.add_argument("--no-fetch", action="store_true",
                    help="do not mirror cells the backend's netlists use and the library lacks")
    args = ap.parse_args()
    if not args.check and not args.no_fetch:
        fetch_missing()
    from sim_runner import CadenceSSHAgent
    from run_path import load_password          # the same credential source every path run uses
    a = CadenceSSHAgent()
    a.connect(password=load_password())
    try:
        home = a._head_exec("echo $HOME")["stdout"].strip()
        rdir = f"{home}/{REMOTE}"
        if args.check:
            r = a._head_exec(f"test -s {rdir}/cells.f && wc -l < {rdir}/cells.f || echo missing")
            print(f"  {rdir}: {r['stdout'].strip()} cell file(s)")
            return 0 if "missing" not in r["stdout"] else 1
        wrappers = sorted(glob.glob(os.path.join(LIB, "cells", "*", "sky130_fd_sc_hd__*_[0-9]*.v")))
        if not wrappers:
            print(f"no cell models under {os.path.relpath(LIB, ROOT)}")
            return 1
        tgz = os.path.join(tempfile.gettempdir(), "sky130_models.tgz")
        with tarfile.open(tgz, "w:gz") as t:
            t.add(LIB, arcname="sky130")
        a.upload_file(tgz, "sky130_models.tgz")
        a._head_exec(f"rm -rf {rdir} && tar xzf {home}/cadence_agent_work/sky130_models.tgz "
                     f"-C {home}/cadence_agent_work")
        # the file list: an include directory per cell (Xcelium searches
        # +incdir+, not the including file's directory, and the models'
        # `../../models/...` includes resolve relative to those), then every
        # sized wrapper (each includes its base cell and functional model;
        # the UDP models come in through those includes)
        cell_dirs = sorted({os.path.basename(os.path.dirname(w)) for w in wrappers})
        listing = ("\n".join(f"+incdir+{rdir}/cells/{d}" for d in cell_dirs) + "\n"
                   + "\n".join(f"{rdir}/cells/{os.path.basename(os.path.dirname(w))}/{os.path.basename(w)}"
                                for w in wrappers) + "\n")
        a._head_exec(f"cat > {rdir}/cells.f << 'EOF'\n{listing}EOF")
        print(f"  installed {len(wrappers)} cell model(s), {len(cell_dirs)} include dir(s) -> {rdir}  (cells.f)")
        if args.no_smoke or not os.path.exists(SMOKE):
            return 0
        a.upload_file(SMOKE, "sky130/smoke_netlist.v")
        cmd = (f"cd {rdir} && xrun -sv -compile -timescale 1ns/1ps -clean "
               f"+define+FUNCTIONAL +define+UNIT_DELAY= -F {rdir}/cells.f smoke_netlist.v 2>&1 | tail -4")
        r = a.srun(cmd, timeout=600)
        out = r.get("stdout", "")
        ok = "*E" not in out and "*F" not in out
        print("  smoke test (wb_port netlist compiles against the library): " + ("OK" if ok else "FAILED"))
        for l in out.strip().splitlines()[-4:]:
            print("    " + l[:140])
        return 0 if ok else 1
    finally:
        a.disconnect()


if __name__ == "__main__":
    sys.exit(main())
