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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-smoke", action="store_true")
    args = ap.parse_args()
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
