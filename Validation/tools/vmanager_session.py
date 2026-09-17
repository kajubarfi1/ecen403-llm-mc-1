#!/usr/bin/env python3
"""
vmanager_session.py — package the path regression as a vManager session
========================================================================
Olympus has Cadence vManager 22.03 (/opt/coe/cadence/VMANAGER). This
generates everything it needs to run and display the path regression
natively: a session directory with all generated collateral (harnesses,
drivers, monitors, stubs, RTL) plus a .vsif whose tests are the same xrun
invocations run_path.py performs.

What vManager gives you on top of our tooling:
  * regression sessions — launch all paths, watch runs live, rerun failures
  * native coverage aggregation — it reads the cov_work UCD/UCM databases
    our -covtest flags produce, merged across runs
  * failure triage — *E,ASRTST assertion failures (the design's embedded
    SVA) are exactly what its failure scanner classifies

What it deliberately does NOT show: transaction-scoreboard verdicts, gate
acceptances, findings and waivers. Those live outside coverage databases and
simulation logs — Validation/reports/dashboard.html is their cockpit. The
two views are complementary: vManager answers "did the sims run, what did
coverage and assertions say"; the dashboard answers "does the design meet
the spec".

Usage (from the repo root):
    python3 Validation/tools/vmanager_session.py            # all paths
    python3 Validation/tools/vmanager_session.py --upload   # + push to Olympus

Then on Olympus (needs X forwarding: ssh -X or -Y):
    export PATH=/opt/coe/cadence/VMANAGER/tools.lnx86/bin:$PATH
    cd ~/vmanager_session
    vmanager -gui &
    # Regressions -> Launch -> select llmmc_paths.vsif
"""

import argparse
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))

SESSION = os.path.join(ROOT, "Validation", "reports", "vmanager_session")
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")
MON_DIR = os.path.join(ROOT, "Validation", "txn", "generated", "monitors")
SEQ_GEN = os.path.join(ROOT, "Validation", "sequences", "generated")

# Paths that run as simulations. The exact hop paths are judged by stage
# models inside these runs and add no distinct stimulus, so they are not
# separate sim tests.
RUNNABLE = ["path_01_write_cmd", "path_02_read_cmd", "path_03_read_return",
            "path_12_csr_timing_to_scheduling",
            "path_13_csr_refresh_to_scheduling", "path_18_full_write",
            "path_04_scheduler_bank_loop", "path_05_scheduler_refresh_loop",
            "path_19_row_conflict", "path_20_refresh_preempt",
            "path_08_init_to_cal", "path_09_init_to_refresh",
            "path_14_status_init", "path_15_status_cal",
            "path_16_status_refresh", "path_17_full_boot"]


FLT_CONTENT = """# xcelium.flt — classify Xcelium log messages for vm_scan.pl.
# vManager 22.03 ships no xrun filter (only shell.flt / vm.flt); this one
# follows the add_filter syntax documented in vmgr/runner/bin/vm.flt.

add_filter ('xrun_assert', 4,
            '\\*E,ASRTST[^\\n]*Assertion\\s+([\\w.$]+)\\s+has failed',
            failure('1', 'assertion', '$1', 'error', 'embedded SVA assertion failed')
           );

add_filter ('xrun_error', 5,
            '^(xmsim|xmelab|xmvlog|xrun):\\s*\\*E,(\\w+)([^\\n]*)\\n',
            failure('1', '$1', '$2', 'error', '$3')
           );

add_filter ('xrun_fatal', 5,
            '^(xmsim|xmelab|xmvlog|xrun):\\s*\\*F,(\\w+)([^\\n]*)\\n',
            failure('1', '$1', '$2', 'fatal', '$3')
           );

add_filter ('harness_timeout', 6,
            '^(HARNESS_TIMEOUT[^\\n]*)\\n',
            failure('1', 'harness', 'TIMEOUT', 'error', '$1')
           );
"""


def run_local(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True,
                       cwd=ROOT)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def prepare(path_id, tdir, pdefs, imap, seed=1, drives=19, test_name=None):
    """Generate this path's collateral into its test directory and return
    the xrun command that runs it (mirrors run_path.py)."""
    import chain_harness_gen as CHG

    pdef = pdefs[path_id]
    sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
    import stimulus_select as SS
    with open(os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")) as f:
        catalog = json.load(f)["interfaces"]
    with open(os.path.join(ROOT, "Validation", "txn", "generated",
                           "schemas.json")) as f:
        schemas = json.load(f)["interfaces"]
    blocks = CHG.block_closure(pdef["blocks"], imap)

    # Entry, generator and window come from stimulus_select — the same
    # decisions run_path.py makes, so a vManager test IS the run_path run.
    observe = pdef["check_strategy"] == "observe"
    entry = None if observe else SS.entry_block(pdef, blocks, catalog, schemas, imap)
    autonomous = entry is None
    settle = SS.window(pdef, autonomous)
    if not autonomous and settle == SS.DEFAULT_SETTLE:
        settle = 300                # regression drain: a little more slack

    files = []
    if autonomous:
        os.makedirs(tdir, exist_ok=True)
        rc, out = run_local(
            f"python3 Validation/structural/chain_harness_gen.py "
            f"--path {path_id} --settle {settle} --outdir {tdir}")
    else:
        # Own filename, ALWAYS regenerated: reusing run_path.py's
        # "{path}_seed1.json" pulled in its read+write stimulus, which drives
        # the known-broken read-return path through every chain — including
        # paths whose subject is bank state or refresh service. Their
        # assertions then drown in 334 wb_port read failures and the
        # property under test is never exercised. The read path has its own
        # paths (02, 03, 18) where that bug is reported.
        seq = os.path.join(SEQ_GEN, f"{path_id}_vm_s{seed}.json")
        rc0, out0, gen = SS.generate_sequence(pdef, entry, seq, seed=seed,
                                              drives=drives)
        if rc0 != 0:
            raise SystemExit(f"{path_id}: stimulus generation failed\n{out0[-300:]}")
        os.makedirs(tdir, exist_ok=True)
        rc, out = run_local(
            f"python3 Validation/sequences/driver_gen.py --sequence {seq} "
            f"--outdir {tdir}")
        rc2, out2 = run_local(
            f"python3 Validation/structural/chain_harness_gen.py "
            f"--path {path_id} --sequence {seq} --settle {settle} "
            f"--outdir {tdir}")
        rc, out = rc or rc2, out + out2
    if rc != 0:
        raise SystemExit(f"{path_id}: collateral generation failed\n{out[-400:]}")

    import glob as g
    for b in blocks:
        rtl = sorted(g.glob(os.path.join(ROOT, "Frontend", "**", f"{b}.sv"),
                            recursive=True), key=lambda p: -os.path.getmtime(p))
        files.append(rtl[0])
    files += [os.path.join(ROOT, s["source"]) for s in imap.get("stubs", [])
              if s.get("when_block") in blocks]
    # driver + harness were generated straight into tdir; only the rest is copied

    # per-run bind subset + monitors
    lines, mods = [], set()
    for l in open(os.path.join(MON_DIR, "monitors_bind.sv")):
        parts = l.split()
        if len(parts) >= 3 and parts[0] == "bind" and parts[1] in blocks:
            lines.append(l)
            mods.add(parts[2])
    bind = os.path.join(tdir, "binds.sv")
    os.makedirs(tdir, exist_ok=True)
    with open(bind, "w") as f:
        f.write("".join(lines))
    files += [os.path.join(MON_DIR, f)
              for f in (m.replace("_monitor", "") + "_monitor.sv"
                        for m in mods)]
    files.append(os.path.join(ROOT, "Validation", "coverage", "cov_conf.ccf"))
    # generated covergroups / assertions for the instantiated blocks
    gen = os.path.join(ROOT, "Validation", "sva", "generated")
    for b in blocks:
        for sfx in ("_fcov.sv", "_fcov_bind.sv", "_coverage.sv",
                    "_coverage_bind.sv", "_sva.sv", "_sva_bind.sv"):
            if os.path.exists(os.path.join(gen, b + sfx)):
                files.append(os.path.join(gen, b + sfx))

    for f in files:
        shutil.copy(f, tdir)

    # driver + harness were generated directly into tdir (not copied), so
    # they are added to the compile list here.
    local_sv = ["chain_harness.sv"] + ([] if autonomous else ["seq_driver.sv"])
    for n in local_sv:
        if not os.path.exists(os.path.join(tdir, n)):
            raise SystemExit(f"{path_id}: expected generated {n} in {tdir}")
    names = " ".join(sorted([os.path.basename(f) for f in files
                             if f.endswith(".sv")] + local_sv))
    return (f"/opt/coe/cadence/XCELIUM240/tools/bin/xrun "
            f"-sv -access +rwc -timescale 1ns/1ps "
            f"-coverage A -covoverwrite -covfile cov_conf.ccf "
            f"-covtest {test_name or path_id} {names} binds.sv -top chain_harness")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--upload", action="store_true",
                    help="scp the session directory to Olympus")
    ap.add_argument("--drives", type=int, default=19,
                    help="transactions per stimulus sequence (default 19: "
                         "enough to prove plumbing, far too few for "
                         "coverage)")
    ap.add_argument("--seeds", type=int, default=1,
                    help="sequences per stimulated path; >1 packages one "
                         "test per seed (observe paths have no stimulus and "
                         "run once)")
    args = ap.parse_args()

    with open(PATH_DEFS) as f:
        pdefs = {p["id"]: p for p in json.load(f)["paths"]}
    with open(os.path.join(ROOT, "Validation", "structural",
                           "integration_map.json")) as f:
        imap = json.load(f)

    if os.path.exists(SESSION):
        shutil.rmtree(SESSION)
    os.makedirs(SESSION)

    tests = []
    for pid in RUNNABLE:
        strat = pdefs[pid]["check_strategy"]
        seeds = [1] if (strat == "observe" or args.seeds <= 1) \
            else list(range(1, args.seeds + 1))
        for sd in seeds:
            name = pid if len(seeds) == 1 else f"{pid}_s{sd}"
            tdir = os.path.join(SESSION, name)
            cmd = prepare(pid, tdir, pdefs, imap, seed=sd,
                          drives=args.drives, test_name=name)
            tests.append((name, strat, cmd))
            print(f"  packaged {name}")

    vsif = os.path.join(SESSION, "llmmc_paths.vsif")
    with open(vsif, "w") as f:
        f.write('session llmmc_paths {\n'
                '    top_dir: $ENV(HOME)/vmanager_session/vm_results;\n'
                '    drm: serial local;\n'
                '};\n\n')
        for strat in ("composed", "invariant", "observe"):
            group = [t for t in tests if t[1] == strat]
            if not group:
                continue
            f.write(f'group {strat} {{\n')
            for pid, _, cmd in group:
                f.write(f'    test {pid} {{\n'
                        f'        run_script: "cd $ENV(HOME)/vmanager_session/{pid} '
                        f'&& {cmd}";\n'
                        f'        scan_script: "env '
                        f'PATH=/opt/coe/cadence/XCELIUM240/tools.lnx86/bin:'
                        f'/opt/coe/cadence/XCELIUM240/tools/bin:$ENV(PATH) '
                        f'vm_scan.pl '
                        f'/opt/coe/cadence/XCELIUM240/tools.lnx86/bin/cdns_sim.flt '
                        f'$ENV(HOME)/vmanager_session/xcelium.flt";\n'
                        f'        timeout: 1800;\n'
                        f'    }};\n')
            f.write('};\n\n')

    with open(os.path.join(SESSION, "README.txt"), "w") as f:
        f.write(__doc__)
    with open(os.path.join(SESSION, "xcelium.flt"), "w") as f:
        f.write(FLT_CONTENT)
    print(f"\n  session -> {os.path.relpath(SESSION, ROOT)}")
    print(f"  vsif    -> {os.path.relpath(vsif, ROOT)}  "
          f"({len(tests)} test(s))")

    if args.upload:
        # The session is a directory tree; scp -r preserves it, and the
        # ssh config sim_runner uses knows the host details.
        import sim_runner as SR
        host = SR.SSH_CONFIG["hostname"]
        user = SR.SSH_CONFIG["username"]
        port = SR.SSH_CONFIG.get("port", 22)
        cmd = (f"scp -P {port} -r {SESSION} {user}@{host}:~/")
        print(f"  uploading: {cmd}")
        rc = subprocess.call(cmd, shell=True)
        if rc != 0:
            print("  upload failed — run the scp command above by hand")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
