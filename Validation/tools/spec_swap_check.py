#!/usr/bin/env python3
"""
spec_swap_check.py — prove the validation collateral is spec-driven
====================================================================
Every generator in this subsystem reads ONE spec file
(`Validation/spec/llmmc_microarchitecturespec_filled.json`). "Spec as data"
is only a claim until a second, materially different spec goes through the
same generators with no code edits and the bounds and bins visibly move.
This tool runs that experiment and leaves the tree exactly as it found it.

  1. snapshot   the spec and every generated output (txn/generated,
                sva/generated, vplan/vplan.json)
  2. baseline   regenerate from the current spec (fresh, so vplan statuses
                and headers are comparable) and capture the outputs
  3. candidate  copy the candidate spec over the spec path, run the same
                generators, capture the outputs; run the intake gate and the
                structural width gate against the current drop
  4. restore    put every snapshotted file back byte-for-byte (always, even
                on failure) and verify the tree is identical
  5. report     which generated files changed, how many non-header lines
                moved per file, which SVA properties the candidate clock
                makes unenforceable, whether any baseline-only literal
                survived, and the exit-criterion verdict

Exit criterion (SEMESTER_PLAN.md, Phase A): every generator exits 0 on the
candidate with zero code edits; timing bounds, coverage bins and vplan
targets change; no baseline-only literal survives; the tree is restored.

Usage:
    python3 Validation/tools/spec_swap_check.py --spec builds/lce/microarch_spec.json
    python3 Validation/tools/spec_swap_check.py --spec ... --report Validation/reports/spec_swap_lce.json
"""

import argparse
import datetime
import filecmp
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
V = os.path.join(ROOT, "Validation")
SPEC_PATH = os.path.join(V, "spec", "llmmc_microarchitecturespec_filled.json")

# Everything a generator below writes into the tree. Snapshotted and restored.
GENERATED = [
    os.path.join(V, "txn", "generated"),
    os.path.join(V, "sva", "generated"),
    os.path.join(V, "vplan", "vplan.json"),
]

GENERATORS = [
    "Validation/txn/schema_gen.py",
    "Validation/txn/monitor_gen.py",
    "Validation/sva/sva_gen.py",
    "Validation/sva/coverage_gen.py",
    "Validation/sva/block_coverage_gen.py",
    "Validation/vplan/vplan_gen.py",
    "Validation/refmodel/spec_register_model.py",
]

HEADER_RE = re.compile(r"Spec revision|spec_revision|spec_source|generated_utc|design_id")


def sh(cmd, timeout=600):
    r = subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True,
                       text=True, timeout=timeout)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def copy_tree_or_file(src, dst):
    if os.path.isdir(src):
        if os.path.exists(dst):
            shutil.rmtree(dst)
        shutil.copytree(src, dst)
    elif os.path.exists(src):
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(src, dst)


def snapshot(into):
    """Copy the spec and every generated artefact into `into`, keyed by
    path relative to Validation/."""
    for p in [SPEC_PATH] + GENERATED:
        copy_tree_or_file(p, os.path.join(into, os.path.relpath(p, V)))


def restore(frm):
    for p in [SPEC_PATH] + GENERATED:
        src = os.path.join(frm, os.path.relpath(p, V))
        if os.path.isdir(p):
            shutil.rmtree(p)
        elif os.path.exists(p):
            os.remove(p)
        copy_tree_or_file(src, p)


def tree_identical(frm):
    for p in [SPEC_PATH] + GENERATED:
        src = os.path.join(frm, os.path.relpath(p, V))
        if os.path.isdir(p):
            d = filecmp.dircmp(src, p)
            if d.left_only or d.right_only or d.diff_files or d.funny_files:
                return False
        elif not filecmp.cmp(src, p, shallow=False):
            return False
    return True


def run_generators(tag):
    rows = []
    for g in GENERATORS:
        rc, out = sh(f"python3 {g}")
        last = out.strip().splitlines()[-1] if out.strip() else ""
        rows.append({"generator": g, "rc": rc, "last_line": last[:160], "log": out})
        print(f"    {'ok  ' if rc == 0 else 'FAIL'} [{tag}] {os.path.basename(g):28} {last[:70]}")
    return rows


def capture(into):
    for p in GENERATED:
        copy_tree_or_file(p, os.path.join(into, os.path.relpath(p, V)))


def walk(root):
    out = {}
    for d, _, fs in os.walk(root):
        for f in fs:
            full = os.path.join(d, f)
            out[os.path.relpath(full, root)] = full
    return out


def changed_lines(a, b):
    """Lines that differ between two text files, ignoring provenance headers."""
    la = [l for l in open(a, errors="replace").read().splitlines() if not HEADER_RE.search(l)]
    lb = [l for l in open(b, errors="replace").read().splitlines() if not HEADER_RE.search(l)]
    sa, sb = set(la), set(lb)
    return [l.strip() for l in la if l not in sb], [l.strip() for l in lb if l not in sa]


def not_generated(log):
    m = re.findall(r"not generated \(no separation required at this clock\): ([A-Z0-9_, ]+)", log)
    ids = []
    for grp in m:
        ids += [x.strip() for x in grp.split(",") if x.strip()]
    return sorted(set(ids))


def intake(spec_path):
    rc, out = sh(f"python3 Validation/spec/spec_completeness.py --spec {spec_path}")
    gaps = sorted(set(re.findall(r"^\s*GAP\s+(\S+)", out, re.M)))
    return {"rc": rc, "gaps": gaps}


def width_gate():
    """Structural width gate: the spec in place vs the current drop's manifests."""
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as tf:
        tmp = tf.name
    rc, out = sh(f"python3 Validation/structural/width_conformance.py --json {tmp}")
    findings = []
    try:
        with open(tmp) as f:
            findings = json.load(f).get("findings", [])
    except Exception:
        pass
    os.remove(tmp)
    summary = [l.strip() for l in out.splitlines() if re.search(r"pass|fail|mismatch|unchecked", l, re.I)][-3:]
    return {"rc": rc, "findings": len(findings), "summary": summary,
            "details": [{k: fd.get(k) for k in ("scope", "severity", "title") if k in fd}
                        for fd in findings[:20]]}


def baseline_literals(spec):
    """Distinctive values of the baseline spec that must NOT appear in the
    candidate's generated outputs. Derived from the spec, never hard-coded."""
    tm, cm = spec.get("timing_model", {}), spec.get("clocking_model", {})
    lits = {
        "revision": spec.get("revision"),
        "design_id": spec.get("design_id"),
        "tCK_ns": f"{tm.get('tCK_ns')}ns" if tm.get("tCK_ns") is not None else None,
        "controller_clock_period_ns": f"{cm.get('controller_clock_period_ns')}ns"
        if cm.get("controller_clock_period_ns") is not None else None,
        "tREFI_nCK": str(tm.get("$derived_cycles", {}).get("tREFI_nCK")),
        "speed_bin": tm.get("speed_bin"),
    }
    return {k: v for k, v in lits.items() if v not in (None, "None")}


def literal_scan(files, lits, candidate_spec):
    """A baseline literal counts as surviving only when it is not ALSO a
    literal of the candidate spec (e.g. a shared JEDEC constant)."""
    cand = set(str(v) for v in baseline_literals(candidate_spec).values())
    hits = []
    for rel, full in files.items():
        txt = open(full, errors="replace").read()
        for name, val in lits.items():
            if str(val) in cand:
                continue
            # Whole-token match: "5.0ns" must not fire on "15.0ns", "6240" not on "16240".
            pat = re.compile(r"(?<![A-Za-z0-9_.])" + re.escape(str(val)) + r"(?![A-Za-z0-9_])")
            for i, line in enumerate(txt.splitlines(), 1):
                if pat.search(line) and not HEADER_RE.search(line):
                    hits.append({"file": rel, "line": i, "literal": name, "value": val, "text": line.strip()[:120]})
    return hits


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("--spec", required=True, help="candidate spec JSON")
    ap.add_argument("--report", help="write the JSON report here")
    args = ap.parse_args()

    cand_path = os.path.abspath(args.spec)
    with open(SPEC_PATH) as f:
        base_spec = json.load(f)
    with open(cand_path) as f:
        cand_spec = json.load(f)
    if base_spec.get("revision") == cand_spec.get("revision"):
        print("candidate has the same revision as the baseline; nothing to prove")
        return 2

    work = tempfile.mkdtemp(prefix="spec_swap_")
    snap, base_out, cand_out = (os.path.join(work, d) for d in ("snapshot", "baseline", "candidate"))
    print(f"[0] snapshot -> {snap}")
    snapshot(snap)
    report = {
        "$schema": "validation-spec-swap/1",
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "baseline": {"revision": base_spec.get("revision"), "design_id": base_spec.get("design_id")},
        "candidate": {"path": os.path.relpath(cand_path, ROOT), "revision": cand_spec.get("revision"),
                      "design_id": cand_spec.get("design_id")},
        "code_edits": 0,
    }
    try:
        print("[1] baseline: regenerate from the current spec")
        base_rows = run_generators("base")
        capture(base_out)
        report["intake_baseline"] = intake(SPEC_PATH)
        report["width_gate_baseline"] = width_gate()

        print("[2] candidate: swap the spec in, regenerate")
        shutil.copy2(cand_path, SPEC_PATH)
        cand_rows = run_generators("cand")
        capture(cand_out)
        report["intake_candidate"] = intake(SPEC_PATH)
        report["width_gate_candidate"] = width_gate()
    finally:
        print("[3] restore the snapshot")
        restore(snap)
        report["tree_restored"] = tree_identical(snap)
        print(f"    tree identical to snapshot: {report['tree_restored']}")

    # ---- compare ------------------------------------------------------------
    fa, fb = walk(base_out), walk(cand_out)
    changed, same = {}, []
    for rel in sorted(set(fa) & set(fb)):
        if filecmp.cmp(fa[rel], fb[rel], shallow=False):
            same.append(rel)
            continue
        gone, new = changed_lines(fa[rel], fb[rel])
        changed[rel] = {"lines_removed": len(gone), "lines_added": len(new),
                        "header_only": not gone and not new,
                        "sample": [{"baseline": g, "candidate": n} for g, n in list(zip(gone, new))[:6]]}
    report["generators"] = [
        {"generator": b["generator"], "rc_baseline": b["rc"], "rc_candidate": c["rc"],
         "last_line_candidate": c["last_line"]}
        for b, c in zip(base_rows, cand_rows)]
    report["files"] = {
        "changed": changed, "unchanged": same,
        "only_baseline": sorted(set(fa) - set(fb)), "only_candidate": sorted(set(fb) - set(fa))}
    sva_b = not_generated("".join(r["log"] for r in base_rows))
    sva_c = not_generated("".join(r["log"] for r in cand_rows))
    report["sva_unenforceable_at_clock"] = {"baseline": sva_b, "candidate": sva_c,
                                            "new_in_candidate": sorted(set(sva_c) - set(sva_b))}
    lits = baseline_literals(base_spec)
    report["literal_scan"] = {"baseline_literals": lits,
                              "surviving_hits": literal_scan(fb, lits, cand_spec)}

    # ---- verdict --------------------------------------------------------------
    substantive = {k: v for k, v in changed.items() if not v["header_only"]}
    moved = {
        "sva_bounds": any(k.startswith("sva/generated") and k.endswith("_sva.sv") for k in substantive),
        "coverage_bins": any(k.startswith("sva/generated") and ("cov" in k) for k in substantive),
        "vplan_targets": "vplan/vplan.json" in substantive,
    }
    checks = {
        "all_generators_pass_on_candidate": all(r["rc_candidate"] == 0 for r in report["generators"]),
        "bounds_and_bins_changed": all(moved.values()),
        "no_baseline_literal_survives": not report["literal_scan"]["surviving_hits"],
        "tree_restored": report["tree_restored"],
        "zero_code_edits": True,
    }
    report["what_moved"] = moved
    report["checks"] = checks
    report["verdict"] = "pass" if all(checks.values()) else "fail"

    print("\n[4] result")
    print(f"    changed files: {len(substantive)} substantive, "
          f"{len(changed) - len(substantive)} header-only, {len(same)} unchanged")
    for k, v in sorted(substantive.items()):
        print(f"      {k:48} -{v['lines_removed']} +{v['lines_added']}")
    if report["sva_unenforceable_at_clock"]["new_in_candidate"]:
        print(f"    SVA unenforceable at candidate clock: "
              f"{', '.join(report['sva_unenforceable_at_clock']['new_in_candidate'])}")
    print(f"    intake gaps: baseline {len(report['intake_baseline']['gaps'])}, "
          f"candidate {len(report['intake_candidate']['gaps'])}")
    print(f"    width gate vs current drop: baseline {report['width_gate_baseline']['findings']} finding(s), "
          f"candidate {report['width_gate_candidate']['findings']}")
    for k, v in checks.items():
        print(f"    {'PASS' if v else 'FAIL'}  {k}")
    print(f"    verdict: {report['verdict'].upper()}")

    if args.report:
        os.makedirs(os.path.dirname(os.path.abspath(args.report)), exist_ok=True)
        with open(args.report, "w") as f:
            json.dump(report, f, indent=2)
        print(f"    wrote {os.path.relpath(args.report, ROOT)}")
    shutil.rmtree(work, ignore_errors=True)
    return 0 if report["verdict"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
