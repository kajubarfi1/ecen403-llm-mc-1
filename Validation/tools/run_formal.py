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

def _py(cmd):
    """Run our own tools with THIS interpreter, never whatever `python3` is
    first on PATH: a venv invoked by absolute path otherwise loses its
    packages in every subprocess (Frontend handoff 2026-10-15, 2a)."""
    return re.sub(r"^python3 ", sys.executable + " ", cmd) if isinstance(cmd, str) else cmd

sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))

FORMAL_DIR = os.path.join(ROOT, "Validation", "formal")
REPORTS = os.path.join(ROOT, "Validation", "reports", "formal")
SVA = os.path.join(ROOT, "Validation", "sva", "generated")
JG_BIN = "/opt/coe/cadence/JASPERGOLD240/bin"

TCL = """clear -all
analyze -sv12 -f files.f
elaborate -top chain_formal
clock clk
reset -expression {{!rst_n}}
{stopat}set_prove_time_limit {time}
{trace_line}prove -all
report -summary
report -all -file report_all.txt -force
exit
"""


def override_bind(bind_path, sva_path, params):
    """Rewrite `bind <block> <mod> <inst> (.*);` as `bind <block> <mod> #(.P(v), ...)
    <inst> (.*);` for the parameters that <mod> declares."""
    with open(sva_path) as f:
        declared = set(re.findall(r"parameter\s+int\s+(\w+)", f.read()))
    use = {k: v for k, v in params.items() if k in declared}
    if not use:
        return
    with open(bind_path) as f:
        text = f.read()
    m = re.search(r"^(bind\s+\w+\s+\w+)(\s+\w+\s*\(\.\*\);)", text, re.M)
    if not m:
        raise SystemExit(f"{bind_path}: no `bind <block> <mod> <inst> (.*);` line to override")
    plist = ", ".join(f".{k}({v})" for k, v in use.items())
    with open(bind_path, "w") as f:
        f.write(text[:m.start()] + f"{m.group(1)} #({plist}){m.group(2)}" + text[m.end():])


def sh(cmd):
    r = subprocess.run(_py(cmd), shell=True, cwd=ROOT, capture_output=True, text=True)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def signoff_bars(spec, params):
    """The bounded-proof bar of SIGNOFF §6, per property: twice the bound
    that property's own assertion uses, in cycles (a --sva-param override,
    as in a scaled run, replaces the spec's value for that rule). Returns
    {rule_id: bar} plus "*": twice the longest of them, for properties
    whose bound is not derived here. A single bar from the longest bound
    (tREFI's 14 040) was the wrong yardstick for an obligation bounded at
    184 cycles explored to 2 948 (REF_001, 2026-10-22)."""
    sys.path.insert(0, os.path.join(ROOT, "Validation", "sva"))
    import sva_gen as SG
    with open(os.path.join(ROOT, "Validation", "sva", "sva_rules.json")) as f:
        rules = json.load(f)
    bars = {}
    for r in rules.get("max_interval_rules", []):
        try:
            _n, _ns, _p, _m, bound = SG.interval_bound(spec, r)
        except SG.SvaGenError:
            continue
        bars[r["id"]] = 2 * int(params.get(f"{r['id']}_BOUND", bound))
    for r in rules.get("min_separation_rules", []) + rules.get("window_rules", []):
        try:
            n, _ns, _p = SG.cycles_for(spec, r["param"])
        except SG.SvaGenError:
            continue
        bars[r["id"]] = 2 * n
    for grp in rules.get("signal_groups", []):
        for r in grp.get("liveness_rules", []):
            try:
                bound = SG.liveness_bound(spec, r["bound"])
            except (SG.SvaGenError, KeyError):
                continue
            bars[r["id"]] = 2 * int(params.get(f"{r['id']}_BOUND", bound))
    bars["*"] = max(bars.values()) if bars else 0
    return bars


def signoff_bar(spec, params):
    """The global bar (twice the longest bound); kept for callers that want one number."""
    return signoff_bars(spec, params)["*"]


def classify_bounded(asserts, bars):
    """An `undetermined` result whose explored bound meets the signoff bar
    for THAT property is recorded as bounded_proven at that bound (SIGNOFF
    §6: bounded to at least twice the property's own timing bound).
    JasperGold itself only says undetermined; the bar is ours and is
    written into the row. `bars` is {rule_id: bar, "*": global}; an int is
    taken as the global bar."""
    if isinstance(bars, int):
        bars = {"*": bars}
    for r in asserts:
        if r.get("status") != "undetermined":
            continue
        try:
            depth = int(str(r.get("bound", "")).split()[0])
        except ValueError:
            continue
        rid = r.get("short", "").replace("a_", "", 1)
        bar = bars.get(rid, bars.get("*", 0))
        if bar and depth >= bar:
            r["status"] = "bounded_proven"
            r["bounded_bar"] = bar
            r["note"] = (r.get("note", "") + f" bounded proof: no counterexample to depth {depth}, "
                         f"signoff bar {bar} (2 x this property's bound under these parameters)").strip()
    return asserts


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
    ap.add_argument("--trace", type=int, default=None,
                    help="JasperGold max_trace_length; none by default. Not just a cap on "
                         "counterexample length: the whole proof shuts down when a bounded "
                         "engine reaches it (2026-10-20: 300 stopped after 12 s, 2000 after "
                         "2 min, every open property undetermined at that bound), so the "
                         "time limit governs unless a cap is asked for")
    ap.add_argument("--remote-dir", default="~/formal/auto")
    ap.add_argument("--assume", action="append", default=[], metavar="EXPR",
                    help="constrain a signal (JasperGold assume), e.g. a configuration "
                         "register cut free with --stopat and assumed at a scaled value "
                         "so a bounded engine can cross the interval it governs")
    ap.add_argument("--sva-param", action="append", default=[], metavar="NAME=VALUE",
                    help="override a parameter of the generated assertion modules in the "
                         "bind (e.g. TIMING_012_BOUND=258 beside an assumed tREFI); the "
                         "report records it as an abstraction")
    ap.add_argument("--stopat", action="append", default=[], metavar="HIER.SIG",
                    help="cut this signal free (JasperGold stopat) -- e.g. a wait counter "
                         "whose 100k-cycle spans no bounded engine can cross. Proofs under "
                         "a cut are sound (over-approximation); a cex may be spurious and "
                         "is marked so in the report")
    args = ap.parse_args()
    import rtl_drop as RD
    head = RD.drop_id()

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
    params = dict(kv.split("=", 1) for kv in args.sva_param)
    for b in blocks:
        for sfx in ("_sva.sv", "_sva_bind.sv", "_order_sva.sv", "_order_sva_bind.sv"):
            f = b + sfx
            if os.path.exists(os.path.join(SVA, f)):
                shutil.copy(os.path.join(SVA, f), pkg)
                files.append(f)
                if params and sfx.endswith("_bind.sv"):
                    override_bind(os.path.join(pkg, f), os.path.join(pkg, f.replace("_bind", "")), params)
    shutil.copy(top, pkg)
    files.append("chain_formal.sv")
    with open(os.path.join(pkg, "files.f"), "w") as f:
        f.write("\n".join(files) + "\n")
    with open(os.path.join(pkg, "run.tcl"), "w") as f:
        stop = "".join(f"stopat {sig}\n" for sig in args.stopat)
        stop += "".join(f"assume -name asm_{i} {{{e}}}\n" for i, e in enumerate(args.assume))
        trace_line = f"set_max_trace_length {args.trace}\n" if args.trace else ""
        f.write(TCL.format(time=args.time, trace_line=trace_line, stopat=stop))
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
        print(f"  JasperGold on Olympus ({args.time} limit, trace {args.trace or 'unlimited'}) ...")
        r = a.srun(f"bash {rd}/run.sh", timeout=3600)
        print("  " + r["stdout"].strip().splitlines()[-1] if r["stdout"].strip() else "  (no output)")
        a._head_exec(f"cp {rd}/pkg/report_all.txt ~/cadence_agent_work/jg_report_all.txt")
        # what JasperGold said about the cuts and assumptions: a stopat on a
        # name it cannot resolve, or an assume it rejects, is silent in the
        # results table (the scaled tREFI run of 2026-10-20 ran 48 s with
        # "Global Stopats: <none>" and every property undetermined)
        if args.stopat or args.assume:
            r2 = a._head_exec(f"grep -n -i 'stopat\\|assume\\|ERROR' {rd}/pkg/jg.log | head -20")
            txt = r2["stdout"] if isinstance(r2, dict) else str(r2)
            for l in txt.strip().splitlines():
                print("    jg: " + l.strip()[:150])
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
    with open(os.environ.get("VALIDATION_SPEC", os.path.join(ROOT, "Validation", "spec",
                             "llmmc_microarchitecturespec_filled.json"))) as f:
        bars = signoff_bars(json.load(f), params)
    bar = bars["*"]
    classify_bounded(asserts, bars)
    summ = {s: sum(1 for r in asserts if r["status"] == s) for s in ("proven", "cex", "undetermined", "bounded_proven")}
    abstracted = bool(args.stopat or args.assume or args.sva_param)
    if abstracted:
        what = ", ".join(args.stopat + [f"assume {e}" for e in args.assume] + args.sva_param)
        for r in asserts:
            if r["status"] == "cex":
                r["note"] = (f"cex found under abstraction ({what}); may be spurious -- the "
                             f"timing this property depends on is graded by simulation")
    sva_files = [f for f in files if "_sva" in f]
    tag = "_abs" if abstracted else ""
    rep = {"$schema": "validation-formal/1", "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "tool": "JasperGold (Olympus)", "drop": head, "design_id": RD.design_id(),
           # the proof is about THESE blocks: a later drop that changes only
           # other blocks keeps it (emit_findings compares this against the
           # current drop's design id over the same block list)
           "blocks_design_id": RD.design_id(blocks),
           "path": args.path, "blocks": blocks,
           "top": os.path.relpath(top, ROOT),
           "assertions_files": ["Validation/sva/generated/" + f for f in sva_files],
           "abstractions": ([{"stopat": sig, "effect": "signal driven free; proofs remain sound, "
                              "cex may be spurious"} for sig in args.stopat]
                            + [{"assume": e, "effect": "constrains the free signal; a proof holds "
                                "for the assumed configuration only"} for e in args.assume]
                            + [{"sva_param": kv, "effect": "assertion bound scaled to match the "
                                "assumed configuration"} for kv in args.sva_param]),
           "prove_time_limit": args.time, "max_trace_length": args.trace,
           "bounded_bar_cycles": bar, "bounded_bars": bars,
           "summary": {"assertions": len(asserts), **summ, "covers": len(covers),
                       "covered": sum(1 for r in covers if r["status"] == "covered")},
           "results": asserts + covers, "raw_report": os.path.relpath(raw, ROOT)}
    out = os.path.join(REPORTS, f"jg_{args.path}_{head}{tag}.json")
    with open(out, "w") as f:
        json.dump(rep, f, indent=2)
    print(f"  assertions: {len(asserts)}  proven={summ['proven']} bounded={summ['bounded_proven']} "
          f"cex={summ['cex']} undetermined={summ['undetermined']}  | covers {rep['summary']['covered']}/{len(covers)}"
          f"  (bounded bars: per property, longest {bar} cycles)")
    for r in asserts:
        print(f"    {r['short']:22} {r['status']:12} bound={r['bound']}"
              + ("   (may be spurious under stopat)" if r.get("note") else ""))
    print(f"  wrote {os.path.relpath(out, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
