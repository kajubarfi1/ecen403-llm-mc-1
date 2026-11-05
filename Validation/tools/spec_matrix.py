#!/usr/bin/env python3
"""
spec_matrix.py — the spec matrix: every Tier-1 value and every pair, judged
================================================================================
"Does the loop work for any generated spec?" cannot be answered by running
1728 full loops, and five presets only cover the corners. This tool holds a
chosen set of specs and runs each at one of two levels, printing one table:

  level 1  compile the choices with the Frontend's compiler and run our spec
           review (schema, JEDEC, register map, derived identities, intake
           gaps). Seconds per spec, no Olympus.
  level 2  level 1, then the flow's RTL half on that spec (generation, our
           validation, one fix round), reading the run's state and package.
           Minutes per spec on Olympus; run unattended.

`--build` writes Validation/spec/spec_matrix.json: the five presets, a
greedy pairwise covering set over the Tier-1 choices (every value of every
parameter, and every pair of values of two parameters, in at least one
valid spec; pairs no valid spec can hold are listed as infeasible), and the
Tier-2 edges that have bitten before (clock ratios 1/2/8, wider host words,
queue depth at both ends, the other address mapping, BL4, ECC with its
check lane, the largest address space). Every entry is validated by the
compiler's own rules before it is kept.

Usage:
    python3 Validation/tools/spec_matrix.py --build
    python3 Validation/tools/spec_matrix.py                 # level 1 on every entry
    python3 Validation/tools/spec_matrix.py --level 2 [--only NAME ...] [--skip-done]
"""
import argparse
import copy
import datetime
import itertools
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
MATRIX = os.path.join(ROOT, "Validation", "spec", "spec_matrix.json")
REPORTS = os.path.join(ROOT, "Validation", "reports", "spec_matrix")
RUNS = os.path.join(ROOT, "runs", "matrix")
sys.path.insert(0, os.path.join(ROOT, "Frontend2", "scripts", "Microarch"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "spec"))


def _mc():
    import microarch_compiler as MC
    return MC


# ---------------------------------------------------------------- building
TIER1_FIXED = {"ranks": 1}      # the compiler rejects ranks > 1 (single-rank RTL agents)


def valid(MC, choices):
    errs, _warns, norm = MC.validate_choices(dict(choices))
    return (not errs), errs, norm


def pairwise_covering(MC, seed=1):
    """Greedy pairwise set over TIER1_CHOICES (ranks fixed): candidates are
    random valid specs; each pick covers the most still-uncovered pairs."""
    rng = random.Random(seed)
    params = {k: v for k, v in MC.TIER1_CHOICES.items() if k not in TIER1_FIXED}
    keys = sorted(params)
    pairs = set()
    for a, b in itertools.combinations(keys, 2):
        for va in params[a]:
            for vb in params[b]:
                pairs.add((a, va, b, vb))

    def covered_by(ch):
        return {(a, ch[a], b, ch[b]) for a, b in itertools.combinations(keys, 2)}

    def candidate():
        ch = {k: rng.choice(params[k]) for k in keys}
        ch.update(TIER1_FIXED)
        return ch

    chosen, infeasible = [], set()
    uncovered = set(pairs)
    stall = 0
    while uncovered and stall < 40:
        best, best_gain = None, 0
        for _ in range(300):
            c = candidate()
            ok, _e, _n = valid(MC, c)
            if not ok:
                continue
            gain = len(covered_by(c) & uncovered)
            if gain > best_gain:
                best, best_gain = c, gain
        if best is None or best_gain == 0:
            stall += 1
            continue
        stall = 0
        chosen.append(best)
        uncovered -= covered_by(best)
    # what is left is a pair no sampled valid spec holds: test each directly
    for (a, va, b, vb) in sorted(uncovered, key=str):
        found = None
        for _ in range(200):
            c = candidate()
            c[a], c[b] = va, vb
            ok, _e, _n = valid(MC, c)
            if ok:
                found = c
                break
        if found:
            chosen.append(found)
        else:
            infeasible.add((a, va, b, vb))
    return chosen, sorted(infeasible, key=str)


def tier2_edges(MC):
    base = dict(MC.PRESETS["balanced"])
    base.update(TIER1_FIXED)
    edges = {
        "edge_ratio1": {"clock_ratio_ddr_to_controller": 1},
        "edge_ratio2": {"clock_ratio_ddr_to_controller": 2},
        "edge_ratio8": {"clock_ratio_ddr_to_controller": 8},
        "edge_host64": {"host_data_width": 64},
        "edge_host128": {"host_data_width": 128},
        "edge_queue4": {"command_queue_depth": 4, "lookahead_depth": 4},
        "edge_queue32": {"command_queue_depth": 32, "lookahead_depth": 16},
        "edge_bank_row_column": {"address_mapping": "bank-row-column"},
        "edge_bl4": {"burst_length": 4},
        "edge_x16_one_lane": {"device_width": "x16", "byte_lanes": 1},
        "edge_ecc_sideband": {"ecc_mode": 1, "byte_lanes": 3},
        "edge_largest_space": {"density": "8Gb", "byte_lanes": 8, "device_width": "x16"},
        "edge_in_order_close_page": {"scheduler_policy": "in_order", "row_policy": "close_page"},
    }
    out = {}
    for name, ov in edges.items():
        c = dict(base)
        c.update(ov)
        out[name] = c
    return out


def build(seed=1):
    MC = _mc()
    entries = []
    for p in sorted(MC.PRESETS):
        c = dict(MC.PRESETS[p])
        entries.append({"name": f"preset_{p}", "origin": "preset", "choices": c})
    cov, infeasible = pairwise_covering(MC, seed)
    for i, c in enumerate(cov, 1):
        entries.append({"name": f"pair_{i:02d}", "origin": "pairwise", "choices": c})
    for name, c in tier2_edges(MC).items():
        entries.append({"name": name, "origin": "tier2_edge", "choices": c})
    kept, rejected = [], []
    for e in entries:
        ok, errs, norm = valid(MC, e["choices"])
        if ok:
            e["normalized"] = norm
            kept.append(e)
        else:
            rejected.append({"name": e["name"], "errors": errs})
    doc = {"$schema": "validation-spec-matrix/1",
           "$comment": ("Specs the loop is judged on beyond the golden one. Built by spec_matrix.py --build "
                        "(seed in `seed`): the five presets, a greedy pairwise covering set over the Tier-1 "
                        "choices with ranks fixed at 1 (the compiler rejects more), and the Tier-2 edges that "
                        "have bitten before. `infeasible_pairs` are value pairs no valid spec can hold under "
                        "the compiler's rules. Level 1 = compile + spec review; level 2 = the flow's RTL half."),
           "built_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "seed": seed,
           "tier1_parameters": {k: v for k, v in MC.TIER1_CHOICES.items()},
           "infeasible_pairs": [list(p) for p in infeasible],
           "rejected": rejected, "entries": kept}
    with open(MATRIX, "w") as f:
        json.dump(doc, f, indent=2)
    print(f"  {len(kept)} spec(s): {sum(1 for e in kept if e['origin'] == 'preset')} presets, "
          f"{sum(1 for e in kept if e['origin'] == 'pairwise')} pairwise, "
          f"{sum(1 for e in kept if e['origin'] == 'tier2_edge')} Tier-2 edges; "
          f"{len(infeasible)} infeasible pair(s); {len(rejected)} rejected -> {os.path.relpath(MATRIX, ROOT)}")
    for r in rejected:
        print(f"    rejected {r['name']}: {r['errors'][0][:120]}")
    return 0


# ---------------------------------------------------------------- level 1
def level1(entry, out_dir):
    MC = _mc()
    import validate_spec_stage as VS
    os.makedirs(out_dir, exist_ok=True)
    res = MC.compile_spec(dict(entry["choices"]))     # {"spec", "consistency_checks", ...}
    spec = res["spec"]
    sp = os.path.join(out_dir, "microarch_spec.json")
    with open(sp, "w") as f:
        json.dump(spec, f, indent=2)
    rev = VS.review(spec, compile_result=res)
    res = {"revision": spec.get("revision"), "blocking": rev["blocking"], "advisory": rev["advisory"],
           "jedec_fail": [j["id"] for j in rev["jedec"] if j["status"] == "fail"],
           "gaps": [g["id"] for g in rev["gaps"]], "spec_path": os.path.relpath(sp, ROOT)}
    res["status"] = "PASS" if not rev["blocking"] else "FAIL"
    return res


# ---------------------------------------------------------------- level 2
def level2(entry, out_dir, timeout=5400):
    """The flow's RTL half on this spec: one generation, our validation, one
    fix round. Reads the run state and the run-local package."""
    choices_path = os.path.join(out_dir, "choices.json")
    with open(choices_path, "w") as f:
        json.dump(entry["choices"], f, indent=2)
    run_dir = os.path.join(RUNS, entry["name"])
    cmd = [sys.executable, "flow.py", "--choices", choices_path, "--skip-backend",
           "--run-dir", os.path.relpath(run_dir, ROOT), "--max-rtl-rounds", "2"]
    # the matrix judges generation and simulation per spec; the formal
    # replays (20-60 min each) belong to the golden sign-off, not to a sweep
    env = dict(os.environ, VALIDATION_SKIP_FORMAL="1")
    with open(os.path.join(out_dir, "flow.log"), "w") as log:
        try:
            r = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=timeout, env=env)
            rc = r.returncode
        except subprocess.TimeoutExpired:
            rc = -1
    res = {"flow_rc": rc, "run_dir": os.path.relpath(run_dir, ROOT)}
    # A halt caused by the cluster, not the spec (an SSH session refused
    # while other jobs held Olympus, 2026-11-04: four presets "failed lint"
    # on a gate that was never run) is infrastructure: flagged, not judged
    try:
        txt = open(os.path.join(out_dir, "flow.log"), errors="replace").read()
        if "SSH failed" in txt or "Connection reset by peer" in txt or "SSH protocol banner" in txt:
            res["infrastructure"] = "SSH to Olympus failed during the run; result not a judgement of the spec"
    except OSError:
        pass
    st_path = os.path.join(run_dir, "RUN_STATE.json")
    if os.path.exists(st_path):
        st = json.load(open(st_path))
        res["flow_status"] = st.get("status")
        res["halt"] = st.get("halt")
        phases = [s for s in st.get("stages", []) if s.get("stage") == "rtl_generation" and s.get("phase")]
        res["phases_passed"] = sorted({s["phase"] for s in phases if s.get("status") == "PASS"})
        last = {}
        for s in st.get("stages", []):
            last[s["stage"]] = s
        res["stages"] = {k: v.get("status") for k, v in last.items()}
        res["rtl_validation"] = (last.get("rtl_validation") or {}).get("detail")
    hp = os.path.join(run_dir, "validation", "outbox", "current", "HANDOFF.json")
    fp = os.path.join(run_dir, "validation", "outbox", "current", "findings_v2.json")
    if os.path.exists(hp):
        h = json.load(open(hp))
        res["drop"] = h.get("drop_id") or h.get("drop")
        res["design_id"] = h.get("design_id")
        res["validation_status"] = h.get("status")
        res["failed_modules"] = h.get("failed_modules")
    if os.path.exists(fp):
        fd = json.load(open(fp))
        res["findings"] = [{"owner": x.get("owner_module"), "check_id": x.get("check_id"),
                            "status": x.get("status")} for x in fd.get("findings", [])]
    dsp = os.path.join(run_dir, "validation", "outbox", "current", "DROP_STATUS.json")
    if os.path.exists(dsp):
        ds = json.load(open(dsp))
        res["paths_run"] = len(ds.get("paths_run", []))
        res["paths_blocked"] = len(ds.get("paths_blocked", {}) or {})
    return res


# ---------------------------------------------------------------- driver
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true", help="(re)build the matrix file")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--level", type=int, choices=(1, 2), default=1)
    ap.add_argument("--only", nargs="*", default=None, help="entry names to run")
    ap.add_argument("--origin", choices=("preset", "pairwise", "tier2_edge"), default=None)
    ap.add_argument("--skip-done", action="store_true", help="keep entries already in summary.json at this level")
    ap.add_argument("--timeout", type=int, default=5400, help="per spec at level 2, seconds")
    args = ap.parse_args()
    if args.build:
        return build(args.seed)
    if not os.path.exists(MATRIX):
        print("no matrix: run --build first")
        return 2
    doc = json.load(open(MATRIX))
    os.makedirs(REPORTS, exist_ok=True)
    sp = os.path.join(REPORTS, "summary.json")
    summary = json.load(open(sp)) if os.path.exists(sp) else {"$schema": "validation-spec-matrix-summary/1", "results": {}}
    entries = [e for e in doc["entries"]
               if (not args.only or e["name"] in args.only) and (not args.origin or e["origin"] == args.origin)]
    for e in entries:
        prev = summary["results"].get(e["name"], {})
        if args.skip_done and prev.get("level", 0) >= args.level and not (prev.get("level2") or {}).get("infrastructure"):
            continue
        out_dir = os.path.join(REPORTS, e["name"])
        res = {"name": e["name"], "origin": e["origin"], "choices": e["choices"], "level": args.level,
               "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
        res["level1"] = level1(e, out_dir)
        line = f"  {e['name']:26} L1 {res['level1']['status']:4} blocking={len(res['level1']['blocking'])} advisory={len(res['level1']['advisory'])}"
        if args.level == 2 and res["level1"]["status"] == "PASS":
            res["level2"] = level2(e, out_dir, args.timeout)
            l2 = res["level2"]
            line += (f" | L2 {'INFRA ' if l2.get('infrastructure') else ''}flow={l2.get('flow_status')} phases={l2.get('phases_passed')} "
                     f"validation={l2.get('validation_status')} failed={l2.get('failed_modules')}"
                     + (f" halt={str(l2.get('halt'))[:70]}" if l2.get("halt") else ""))
        print(line)
        summary["results"][e["name"]] = res
        with open(sp, "w") as f:
            json.dump(summary, f, indent=2)
    n = len(summary["results"])
    l1p = sum(1 for r in summary["results"].values() if r["level1"]["status"] == "PASS")
    l2 = [r for r in summary["results"].values() if r.get("level2")]
    l2p = sum(1 for r in l2 if r["level2"].get("validation_status") == "PASS")
    print(f"  summary: {n} spec(s); level 1 PASS {l1p}/{n}"
          + (f"; level 2 validation PASS {l2p}/{len(l2)}" if l2 else "")
          + f" -> {os.path.relpath(sp, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
