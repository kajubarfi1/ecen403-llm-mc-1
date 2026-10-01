#!/usr/bin/env python3
"""
run_formal.py — one command: prove the generated SVA on the composed command path
================================================================================
  1. generate   chain_formal.sv for the path (chain_harness_gen.py --formal):
                the path's blocks wired per the integration map, host inputs and
                DRAM data free, CSR/status tied at the spec's reset values
  2. package    the drop's RTL for those blocks + the generated SVA and bind
  3. run        JasperGold in batch on an Olympus compute node (Slurm), with
                a prove time limit and trace-length cap
  4. report     parse the RESULTS table into reports/formal/jg_<path>_<head>.json
                (status, engine, bound per property) and keep the raw report

Counterexample triage is separate (formal/cex_triage.py on exported VCDs);
this tool records statuses, it does not decide what a CEX means.

Usage:
    python3 Validation/tools/run_formal.py                       # path_01_write_cmd closure
    python3 Validation/tools/run_formal.py --path path_04_scheduler_bank_loop --time 30m
"""
import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))

FORMAL_DIR = os.path.join(ROOT, "Validation", "formal")
REPORTS = os.path.join(ROOT, "Validation", "reports", "formal")
SVA = os.path.join(ROOT, "Validation", "sva", "generated")
JG_BIN = "/opt/coe/cadence/JASPERGOLD240/bin"

TCL = """clear -all
analyze -sv12 -f files.f
elaborate -top chain_formal
{stopat}clock clk
reset -expression {{!rst_n}}
set_prove_time_limit {time}
set_max_trace_length {trace}
prove -all
report -summary
report -all -file report_all.txt -force
exit
"""


def sh(cmd):
    r = subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True, text=True)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def parse_results(text):
    """Rows of the RESULTS table: name, result, engine, bound, time."""
    rows = []
    for line in text.splitlines():
        m = re.match(r"\[\d+\]\s+(\S+)\s+(\w+)\s+(\S+)\s+(\S+(?: - \S+)?)\s+([\d.]+ s)?", line)
        if m:
            name = m.group(1)
            rows.append({"property": name, "short": name.split(".")[-1], "status": m.group(2),
                         "engine": m.group(3), "bound": m.group(4), "time": m.group(5)})
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", default="path_01_write_cmd")
    ap.add_argument("--time", default="20m", help="JasperGold prove time limit")
    ap.add_argument("--trace", type=int, default=200, help="max trace length")
    ap.add_argument("--remote-dir", default="~/formal/auto")
    ap.add_argument("--stopat", action="append", default=[], metavar="HIER.SIG",
                    help="cut this signal free (JasperGold stopat) -- e.g. a wait counter "
                         "whose 100k-cycle spans no bounded engine can cross. Proofs under "
                         "a cut are sound (over-approximation); a cex may be spurious and "
                         "is marked so in the report")
    args = ap.parse_args()
    import rtl_drop as RD
    head = RD._git_head() or "unknown"

    # 1. formal top
    os.makedirs(FORMAL_DIR, exist_ok=True)
    rc, out = sh(f"python3 Validation/structural/chain_harness_gen.py --path {args.path} "
                 f"--formal --outdir {FORMAL_DIR}")
    print(out.strip())
    if rc != 0:
        return 1
    top = os.path.join(FORMAL_DIR, "chain_formal.sv")
    blocks = re.search(r"// Blocks\s*:\s*(.*)", open(top).read()).group(1).split(", ")

    # 2. package
    pkg = tempfile.mkdtemp(prefix="formal_pkg_")
    files = []
    for b in blocks:
        p = RD.rtl_file(b)
        shutil.copy(p, pkg)
        files.append(os.path.basename(p))
    # every generated assertion module for the blocks in the top: the
    # command-path SVA on cmd_gen, the init group on init_fsm, ordering
    # groups on blocks without a command stream
    for b in blocks:
        for sfx in ("_sva.sv", "_sva_bind.sv", "_order_sva.sv", "_order_sva_bind.sv"):
            f = b + sfx
            if os.path.exists(os.path.join(SVA, f)):
                shutil.copy(os.path.join(SVA, f), pkg)
                files.append(f)
    shutil.copy(top, pkg)
    files.append("chain_formal.sv")
    with open(os.path.join(pkg, "files.f"), "w") as f:
        f.write("\n".join(files) + "\n")
    with open(os.path.join(pkg, "run.tcl"), "w") as f:
        stop = "".join(f"stopat {sig}\n" for sig in args.stopat)
        f.write(TCL.format(time=args.time, trace=args.trace, stopat=stop))
    tgz = os.path.join(tempfile.gettempdir(), "formal_pkg.tgz")
    with tarfile.open(tgz, "w:gz") as t:
        t.add(pkg, arcname="pkg")

    # 3. run
    from sim_runner import CadenceSSHAgent
    a = CadenceSSHAgent()
    a.connect()
    try:
        a.upload_file(tgz, "formal_pkg.tgz")
        rd = args.remote_dir
        a._head_exec(f"mkdir -p {rd} && rm -rf {rd}/pkg && tar xzf ~/cadence_agent_work/formal_pkg.tgz -C {rd}")
        script = (f"export PATH={JG_BIN}:$PATH; cd {rd}/pkg && rm -rf jgproj && "
                  f"jg -batch -tcl run.tcl -proj jgproj -allow_unsupported_OS > jg.log 2>&1; "
                  f"echo jg_exit_$?; grep -c '' report_all.txt 2>/dev/null")
        a._head_exec(f"cat > {rd}/run.sh << 'EOF'\n#!/bin/bash\n{script}\nEOF")
        print(f"  JasperGold on Olympus ({args.time} limit, trace {args.trace}) ...")
        r = a.srun(f"bash {rd}/run.sh", timeout=3600)
        print("  " + r["stdout"].strip().splitlines()[-1] if r["stdout"].strip() else "  (no output)")
        a._head_exec(f"cp {rd}/pkg/report_all.txt ~/cadence_agent_work/jg_report_all.txt")
        os.makedirs(REPORTS, exist_ok=True)
        raw = os.path.join(REPORTS, f"jg_{args.path}_{head}{'_abs' if args.stopat else ''}_report.txt")
        a.download_file("jg_report_all.txt", raw)
    finally:
        a.disconnect()

    # 4. report
    text = open(raw, errors="replace").read()
    rows = parse_results(text)
    asserts = [r for r in rows if r["short"].startswith("a_") and ":" not in r["short"]]
    covers = [r for r in rows if r["short"].startswith("c_")]
    summ = {s: sum(1 for r in asserts if r["status"] == s) for s in ("proven", "cex", "undetermined", "bounded_proven")}
    if args.stopat:
        for r in asserts:
            if r["status"] == "cex":
                r["note"] = ("cex found with " + ", ".join(args.stopat) + " cut free; may be "
                             "spurious -- the timing this property depends on is graded by simulation")
    sva_files = [f for f in files if "_sva" in f]
    tag = "_abs" if args.stopat else ""
    rep = {"$schema": "validation-formal/1", "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "tool": "JasperGold (Olympus)", "drop": head, "path": args.path, "blocks": blocks,
           "top": os.path.relpath(top, ROOT),
           "assertions_files": ["Validation/sva/generated/" + f for f in sva_files],
           "abstractions": [{"stopat": sig, "effect": "signal driven free; proofs remain sound, "
                             "cex may be spurious"} for sig in args.stopat],
           "prove_time_limit": args.time, "max_trace_length": args.trace,
           "summary": {"assertions": len(asserts), **summ, "covers": len(covers),
                       "covered": sum(1 for r in covers if r["status"] == "covered")},
           "results": asserts + covers, "raw_report": os.path.relpath(raw, ROOT)}
    out = os.path.join(REPORTS, f"jg_{args.path}_{head}{tag}.json")
    with open(out, "w") as f:
        json.dump(rep, f, indent=2)
    print(f"  assertions: {len(asserts)}  proven={summ['proven']} cex={summ['cex']} undetermined={summ['undetermined']}"
          f"  | covers {rep['summary']['covered']}/{len(covers)}")
    for r in asserts:
        print(f"    {r['short']:22} {r['status']:12} bound={r['bound']}"
              + ("   (may be spurious under stopat)" if r.get("note") else ""))
    print(f"  wrote {os.path.relpath(out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
