#!/usr/bin/env python3
"""
run_path.py — run one integration path end-to-end through the chain harness
============================================================================
The path-level counterpart of rerun_scope.py. One command:

    stimulus on the path's entry stream
      -> chain_harness_gen.py   the generated multi-block integration harness
      -> xrun on Olympus        every block of the path (plus support
                                closure), every monitor bound
      -> trace_extract.py       one log -> one multi-interface trace
      -> per-stage judgment     exact stages against their gate-accepted
                                predictors, order-nondeterministic stages
                                against their invariant checkers, autonomous
                                stages left to SVA
      -> path-level checker     for invariant paths (and any composed path
                                that has one): the full-chain legality rules

The per-stage split is the point: intermediate streams are monitored, so a
composed path is judged hop by hop from what actually crossed each boundary,
not by predicting through a nondeterministic scheduler.

Usage:
    python3 Validation/tools/run_path.py --path path_01_write_cmd
    python3 Validation/tools/run_path.py --path path_19_row_conflict --settle 4000
"""

import argparse
import getpass
import glob
import json
import os
import subprocess
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "agents"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))

from sim_runner import CadenceSSHAgent
import check_path_chains as CPC

CCF = os.path.join(ROOT, "Validation", "coverage", "cov_conf.ccf")
CATALOG = os.path.join(ROOT, "Validation", "txn", "interface_catalog.json")
MON_DIR = os.path.join(ROOT, "Validation", "txn", "generated", "monitors")
SEQ_GEN = os.path.join(ROOT, "Validation", "sequences", "generated")
PREDICTORS = os.path.join(ROOT, "Validation", "predictors")
PATH_DEFS = os.path.join(ROOT, "Validation", "spec", "path_definitions.json")


def load_password():
    pw = os.environ.get("OLYMPUS_PASSWORD")
    if pw:
        return pw
    env = os.path.join(ROOT, "Validation", "setup.env")
    if os.path.exists(env):
        for line in open(env):
            if line.strip().startswith("OLYMPUS_PASSWORD"):
                val = line.split("=", 1)[1].strip().strip('"').strip("'")
                if val:
                    return val
    return getpass.getpass("Olympus password: ")


def run_local(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True,
                       cwd=ROOT)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def rtl_file(block):
    paths = sorted(glob.glob(os.path.join(ROOT, "Frontend", "**",
                                          f"{block}.sv"), recursive=True),
                   key=lambda p: -os.path.getmtime(p))
    return paths[0] if paths else None


def generated_checkers(blocks):
    """Generated covergroup and SVA modules (plus their bind files) for the
    given blocks — only those that exist."""
    gen = os.path.join(ROOT, "Validation", "sva", "generated")
    out = []
    for b in blocks:
        for suffix in ("_fcov.sv", "_fcov_bind.sv", "_coverage.sv",
                       "_coverage_bind.sv", "_sva.sv", "_sva_bind.sv"):
            p = os.path.join(gen, b + suffix)
            if os.path.exists(p):
                out.append(p)
    return out


def bind_subset(blocks, work):
    """Bind lines for exactly these modules, plus the monitor files they
    reference. The subset file is written into the run's work dir."""
    full = os.path.join(MON_DIR, "monitors_bind.sv")
    lines, mods = [], set()
    for l in open(full):
        parts = l.split()
        if len(parts) >= 3 and parts[0] == "bind" and parts[1] in blocks:
            lines.append(l)
            mods.add(parts[2])
    if not lines:
        raise SystemExit(f"monitors_bind.sv has no bind lines for {blocks}")
    dest = os.path.join(work, "chain_monitors_bind.sv")
    with open(dest, "w") as f:
        f.write("// GENERATED subset of monitors_bind.sv for a chain run.\n\n"
                + "".join(lines))
    files = [os.path.join(MON_DIR, f"{m.replace('_monitor', '')}_monitor.sv")
             for m in sorted(mods)]
    missing = [f for f in files if not os.path.exists(f)]
    if missing:
        raise SystemExit(f"missing monitor files: {missing}")
    return dest, files


def stage_jobs(path_def, catalog):
    """(name, kind, model_path) per stage, using the same stage machinery the
    structural chain check uses — one source of truth for what each stage
    needs."""
    stages, err = CPC.build_stages(path_def["blocks"], catalog)
    if err:
        return [], err
    jobs = []
    for st in stages:
        kind = CPC.stage_kind(st, catalog)
        st["kind"] = kind
        name = "_".join(st["blocks"])
        artifact = CPC.stage_artifact(st, kind)
        jobs.append({"stage": "+".join(st["blocks"]), "kind": kind,
                     "model": artifact,
                     "scope": name})
    return jobs, None


def judge(trace, jobs, path_id, rep_dir):
    results = []
    for j in jobs:
        if j["kind"] == "autonomous":
            results.append({**j, "verdict": "sva",
                            "note": "time-driven stage; pacing owned by SVA"})
            continue
        if not (j["model"] and os.path.exists(j["model"])):
            results.append({**j, "verdict": "missing_model"})
            continue
        strategy = "invariant" if j["kind"] == "invariant" else "exact"
        rc, out = run_local(
            f"python3 Validation/txn/scoreboard.py --scope {j['scope']} "
            f"--strategy {strategy} --trace {trace} --model {j['model']}")
        first = next((l for l in out.splitlines() if "status=" in l), "")
        verdict = ("pass" if "status=pass" in first
                   else "unknown" if "status=unknown" in first else "fail")
        results.append({**j, "verdict": verdict, "summary": first.strip(),
                        "detail": out.strip().splitlines()[-12:]
                        if verdict == "fail" else []})
    # path-level checker, if one was generated for this path
    pl = os.path.join(PREDICTORS, f"{path_id}_checker.py")
    if os.path.exists(pl):
        rc, out = run_local(
            f"python3 Validation/txn/scoreboard.py --scope {path_id} "
            f"--strategy invariant --trace {trace} --model {pl}")
        first = next((l for l in out.splitlines() if "status=" in l), "")
        verdict = ("pass" if "status=pass" in first
                   else "unknown" if "status=unknown" in first else "fail")
        results.append({"stage": "(path-level)", "kind": "invariant",
                        "model": pl, "scope": path_id, "verdict": verdict,
                        "summary": first.strip(),
                        "detail": out.strip().splitlines()[-12:]
                        if verdict == "fail" else []})
    return results


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", required=True)
    ap.add_argument("--sequence")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--drives", type=int, default=19)
    ap.add_argument("--kinds", default=None,
                    help="entry-stream kinds; defaults to write+read when "
                         "data_path is in the harness (the DRAM stub answers "
                         "reads), writes only otherwise")
    ap.add_argument("--entry-scope", default=None,
                    help="block whose request stream the sequence drives; "
                         "defaults to wb_port when present, else the first "
                         "path block with a drivable stream")
    ap.add_argument("--settle", type=int, default=64,
                    help="cycles after the driver finishes (or the whole "
                         "window for an autonomous path); default = the "
                         "path's settle_cycles / window_cycles")
    ap.add_argument("--stimulus", default=None,
                    choices=["random", "register_walk", "status_poll",
                             "refresh_stress"],
                    help="override the path's stimulus_generator")
    ap.add_argument("--no-coverage", action="store_true")
    ap.add_argument("--prep-only", action="store_true")
    ap.add_argument("--timeout", type=int, default=900)
    args = ap.parse_args()

    with open(CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    with open(PATH_DEFS) as f:
        pdefs = {p["id"]: p for p in json.load(f)["paths"]}
    if args.path not in pdefs:
        print(f"unknown path {args.path!r}; known: {sorted(pdefs)}")
        return 2
    pdef = pdefs[args.path]

    # blocks actually instantiated = path blocks + support closure; needed
    # up front to pick the entry stream and stimulus kinds.
    with open(os.path.join(ROOT, "Validation", "structural",
                           "integration_map.json")) as f:
        imap = json.load(f)
    import chain_harness_gen as CHG
    blocks = CHG.block_closure(pdef["blocks"], imap)

    sys.path.insert(0, os.path.join(ROOT, "Validation", "sequences"))
    import stimulus_select as SS
    with open(os.path.join(ROOT, "Validation", "txn", "generated",
                           "schemas.json")) as f:
        schemas = json.load(f)["interfaces"]

    # Entry, generator and window are decided in one place (stimulus_select)
    # for every runner. An observe path, or an invariant path none of whose
    # blocks can take stimulus (init, calibration), is AUTONOMOUS: it runs
    # from reset with no driver and the whole window is the observation.
    observe = pdef["check_strategy"] == "observe"
    entry = None if observe else SS.entry_block(pdef, blocks, catalog, schemas,
                                                imap, args.entry_scope)
    autonomous = entry is None
    args.settle = SS.window(pdef, autonomous, args.settle)
    if autonomous and args.sequence:
        print("this path has no drivable entry stream; --sequence cannot be "
              "applied (pass --entry-scope to drive a support block)")
        return 2

    kinds = args.kinds
    if kinds is None:
        # Declared per path (a read-return path must drive reads); the
        # older guess-from-blocks rule is only the fallback.
        declared = pdef.get("stimulus_kinds")
        if declared:
            kinds = ",".join(declared)
        else:
            kinds = ("write,read" if "data_path" in blocks and entry == "wb_port"
                     else "write")

    # --- stimulus + harness ------------------------------------------------
    # Everything generated for this run lives in its own directory. Runners
    # used to share seq_driver.sv / chain_harness.sv, so two runs in flight
    # at once overwrote each other's driver mid-upload and the harness
    # elaborated against the wrong module ports.
    work = os.path.join(SEQ_GEN, "runs", args.path)
    os.makedirs(work, exist_ok=True)
    seq_path = args.sequence
    generator = None
    if autonomous:
        rc, out = run_local(
            f"python3 Validation/structural/chain_harness_gen.py "
            f"--path {args.path} --settle {args.settle} --outdir {work}")
        if rc != 0:
            print(f"harness generation failed:\n{out[-600:]}")
            return 1
        print(out.strip())
    else:
        if not seq_path:
            seq_path = os.path.join(SEQ_GEN,
                                    f"{args.path}_seed{args.seed}.json")
            rc, out, generator = SS.generate_sequence(
                pdef, entry, seq_path, seed=args.seed, drives=args.drives,
                override=args.stimulus, kinds=kinds)
            if rc != 0:
                print(f"sequence generation failed:\n{out[-500:]}")
                return 1
            print(f"  stimulus: {generator} on {entry}")
        for cmd, what in [
                (f"python3 Validation/sequences/driver_gen.py "
                 f"--sequence {seq_path} --outdir {work}", "driver codegen"),
                (f"python3 Validation/structural/chain_harness_gen.py "
                 f"--path {args.path} --sequence {seq_path} "
                 f"--settle {args.settle} --outdir {work}",
                 "harness generation")]:
            rc, out = run_local(cmd)
            if rc != 0:
                print(f"{what} failed:\n{out[-600:]}")
                return 1
            print(out.strip())

    bind_path, mon_files = bind_subset(set(blocks), work)
    stub_files = [os.path.join(ROOT, s["source"])
                  for s in imap.get("stubs", [])
                  if s.get("when_block") in blocks]
    # Generated functional coverage and assertions for each instantiated
    # block, when they exist. Without these the run collects code coverage
    # only and the vplan's coverpoints never move.
    fcov_files = generated_checkers(blocks)
    if autonomous:
        driver_files = []
    else:
        driver_files = [os.path.join(work, "seq_driver.sv")]
    rtl = []
    for b in blocks:
        p = rtl_file(b)
        if not p:
            print(f"no RTL for block {b!r}")
            return 1
        rtl.append(p)
    harness = os.path.join(work, "chain_harness.sv")

    if observe:
        # An observe path has no models by design: its blocks run
        # autonomously, so the check is monitors (order/correlation) plus
        # SVA (timing) — see stage_kind/STRATEGY_NEEDS_MODEL. The run
        # records what happened; it never claims 'pass'.
        jobs, err = [], None
    else:
        jobs, err = stage_jobs(pdef, catalog)
    if err:
        if pdef["check_strategy"] == "invariant":
            # An invariant path is judged by its path-level checker; stagewise
            # judgment is a bonus when the blocks happen to form a chain
            # (path_19 ends in bank_tracker, which emits no stream — there is
            # no stage decomposition to demand).
            print(f"  (no stage decomposition: {err} — the path-level "
                  f"checker carries this path)")
            jobs = []
        else:
            print(f"stage derivation failed: {err}")
            return 1

    print(f"\nPath    : {args.path}  [{pdef['check_strategy']}"
          f"{', autonomous' if autonomous else ''}]")
    print(f"Blocks  : {', '.join(blocks)}")
    print(f"Window  : {args.settle} cycles"
          + (" (observation, no driver)" if autonomous else " settle after driver"))
    print(f"Stages  : " + "; ".join(f"{j['stage']}({j['kind']})"
                                    for j in jobs))
    if args.prep_only:
        print("\n  --prep-only: stopping before the cluster run.")
        return 0

    # --- simulate ----------------------------------------------------------
    agent = CadenceSSHAgent(work_subdir=f"runs/{args.path}")
    try:
        agent.connect(password=load_password())
        agent.clean_work_dir()
        uploads = (rtl + stub_files + driver_files
                   + [harness, bind_path] + mon_files + fcov_files)
        agent.upload_files(uploads)
        cov = ""
        if not args.no_coverage:
            with open(CCF) as f:
                agent.write_remote_file("cov_conf.ccf", f.read())
            cov = (f"-coverage A -covoverwrite -covfile ./cov_conf.ccf "
                   f"-covtest {args.path}")
        names = " ".join(os.path.basename(p) for p in uploads)
        cmd = (f"xrun -sv -access +rwc -timescale 1ns/1ps -clean {cov} "
               f"{names} -top chain_harness 2>&1")
        print(f"\nRunning: xrun ... -top chain_harness  "
              f"({len(uploads)} file(s))")
        res = agent.run_sim(cmd, timeout=args.timeout)
        stdout = res.get("stdout", "")
    except Exception as e:
        print(f"\nRUN FAILED: {e}")
        import traceback
        traceback.print_exc()
        return 2
    finally:
        agent.disconnect()

    rep_dir = os.path.join(ROOT, "Validation", "reports", "paths")
    os.makedirs(rep_dir, exist_ok=True)
    log_path = os.path.join(rep_dir, f"{args.path}_sim.log")
    with open(log_path, "w") as f:
        f.write(stdout)
    print(f"  log -> {os.path.relpath(log_path, ROOT)}")

    # *E,ASRTST is a runtime assertion failure — evidence about the design,
    # not a broken build. Everything else with *E/*F stops the run.
    # *E,ASRTST (assertion failed) and *E,EILLVU (illegal coverage bin hit —
    # a spacing coverpoint saw a value below the spec minimum) are runtime
    # evidence about the design, not broken builds. Everything else stops.
    lines = stdout.splitlines()
    asserts = [l for l in lines if "ASRTST" in l or "EILLVU" in l]
    errors = [l for l in lines
              if ("*E," in l or "*F," in l)
              and "ASRTST" not in l and "EILLVU" not in l]
    if errors:
        print("\n  COMPILE/ELABORATION ERRORS — no verdict is possible:")
        for e in errors[:12]:
            print(f"    {e[:160]}")
        return 2
    if asserts:
        import re as _re
        counts = {}
        for l in asserts:
            m = _re.search(r"Assertion \S*\.(\w+) has failed", l)
            if m:
                counts[m.group(1)] = counts.get(m.group(1), 0) + 1
            elif "EILLVU" in l:
                m = _re.search(r"coverpoint \(\S*\.(\w+)\)", l)
                key = "illegal bin: " + (m.group(1) if m else "?")
                counts[key] = counts.get(key, 0) + 1
        print(f"\n  EMBEDDED RTL ASSERTIONS FIRED ({len(asserts)} total) — "
              f"the design's own checks disagree with its behavior:")
        for name, n in sorted(counts.items(), key=lambda kv: -kv[1]):
            print(f"    {name:24} {n}x")
    if "HARNESS_TIMEOUT" in stdout:
        print("\n  HARNESS TIMEOUT — the chain wedged; trace is partial.")

    trace = os.path.join(rep_dir, f"{args.path}_observed.jsonl")
    rc, out = run_local(
        f"python3 Validation/txn/trace_extract.py --log {log_path} "
        f"--out {trace} --summary")
    if rc != 0:
        print(f"trace extraction failed:\n{out[-500:]}")
        return 2
    print(out.strip())

    # --- judge -------------------------------------------------------------
    results = judge(trace, jobs, args.path, rep_dir)
    print("\n" + "=" * 66)
    worst = "pass"
    for r in results:
        v = r["verdict"]
        mark = {"pass": "PASS", "fail": "FAIL", "unknown": "UNKNOWN",
                "sva": "SVA-OWNED", "missing_model": "NO MODEL"}[v]
        print(f"  {r['stage']:28} [{r['kind']:10}]  {mark}")
        if r.get("summary"):
            print(f"      {r['summary'][:120]}")
        for d in r.get("detail", [])[:6]:
            print(f"      {d[:140]}")
        if v == "fail" or (v in ("unknown", "missing_model")
                           and worst != "fail"):
            worst = "fail" if v == "fail" else "incomplete"

    if observe:
        # No model judges an autonomous path; the verdict is what was seen.
        # The design's own assertions and X-valued observations still fail
        # it; otherwise the honest claim is 'observed', never 'pass'.
        import collections
        counts = collections.Counter()
        with open(trace) as f:
            for line in f:
                t = json.loads(line)
                counts[f"{t['iface']}.{t['kind']}"] += 1
                if any(isinstance(v, str) and v.strip("xXzZ") == ""
                       for v in t.get("fields", {}).values()):
                    counts["(x-valued)"] += 1
        for k, n in sorted(counts.items()):
            print(f"  {k:28} {n}")
        if asserts or counts.get("(x-valued)"):
            worst = "fail"
        else:
            worst = "observed"
    print("=" * 66)

    report = {
        "$schema": "validation-path-run/1",
        "path": args.path,
        "strategy": pdef["check_strategy"],
        "verdict": worst,
        "timestamp": datetime.now().isoformat(),
        "blocks": blocks,
        "sequence": (os.path.relpath(seq_path, ROOT) if seq_path
                     else None),
        "stimulus_generator": generator,
        "autonomous": autonomous,
        "window_cycles": args.settle,
        "stages": results,
        "log": os.path.relpath(log_path, ROOT),
        "observed_trace": os.path.relpath(trace, ROOT),
    }
    with open(os.path.join(rep_dir, f"{args.path}_report.json"), "w") as f:
        json.dump(report, f, indent=2)
    print(f"\n  path verdict : {worst.upper()}")
    print(f"  report -> Validation/reports/paths/{args.path}_report.json")
    return 0 if worst in ("pass", "observed") else 1


if __name__ == "__main__":
    sys.exit(main())
