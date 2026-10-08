#!/usr/bin/env python3
"""
pipeline_batch.py — Parallel multi-block pipeline runner
DDR3 Memory Controller Backend

Runs multiple bundles through pipeline.py simultaneously using
concurrent.futures.ThreadPoolExecutor. Each block gets its own
subprocess and output is streamed with a block-name prefix so
you can follow all runs in parallel.

Bundle discovery (in priority order):
  1) --bundle_dirs  : explicit list of bundle directories (original behaviour)
  2) --bundles_root : scan a folder and run every subdirectory that contains
                      a manifest JSON  (default: ../bundles/ relative to this script)

Usage:
  # Auto-discover everything in ../bundles/
  python pipeline_batch.py

  # Point at a different bundles folder
  python pipeline_batch.py --bundles_root ../bundles

  # Explicit list (original behaviour still works)
  python pipeline_batch.py --bundle_dirs ../bundles/config_regs ../bundles/init_fsm ../bundles/wb_port

  # With flags
  python pipeline_batch.py --enable_autotuner
  python pipeline_batch.py --optimize_fmax

Exit codes:
  0 -> All blocks PASS
  1 -> One or more blocks FAIL
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, List, Optional


# ─── Blocks to skip (integration/interconnect files, not synthesizable RTL) ───

SKIP_BLOCKS = {}


# ─── Parallelism ──────────────────────────────────────────────────────────────
# Each worker runs its own ORFS container against the same bind-mounted flow
# directory. Under heavy concurrent I/O that mount loses writes: on 2026-09-17 a
# run with one worker per block (11) failed at 3_1_place with
#   mv: cannot stat .../3_1_place_gp_skip_io.tmp.log: No such file or directory
# on 10 of 11 blocks. The flow limped on, the GDS merge never ran, and sign-off
# certified week-old layouts. The same 11 blocks at 2 workers completed cleanly.
#
# The runner and sign-off provenance checks now catch that corruption rather than
# reporting it as success, but the default should not steer into it in the first
# place. Raise this only if you have evidence your machine tolerates more.
# Filesystem mtime granularity, not clock skew: the subprocess runs on this
# machine, so a second of slack is enough to avoid rejecting a real report.
REPORT_MTIME_SLACK_S = 1.0

SAFE_MAX_WORKERS = 2


# ─── ANSI colours (gracefully disabled on terminals that don't support them) ──

COLOURS = {
    "reset":  "\033[0m",
    "bold":   "\033[1m",
    "green":  "\033[92m",
    "red":    "\033[91m",
    "yellow": "\033[93m",
    "cyan":   "\033[96m",
    "blue":   "\033[94m",
    "grey":   "\033[90m",
}

BLOCK_COLOURS = ["\033[96m", "\033[93m", "\033[92m", "\033[94m", "\033[95m"]  # cycle through blocks

def c(text: str, colour: str) -> str:
    try:
        return f"{COLOURS.get(colour, '')}{text}{COLOURS['reset']}"
    except Exception:
        return text


# ─── Bundle auto-discovery ─────────────────────────────────────────────────────

def _has_manifest(directory: Path) -> bool:
    """Return True if the directory contains a manifest JSON file."""
    return (
        (directory / "manifest.json").exists()
        or bool(list(directory.glob("*_manifest.json")))
        or bool(list(directory.glob("*manifest*.json")))
    )


def discover_bundles(bundles_root: Path) -> List[Path]:
    """
    Scan bundles_root for subdirectories that look like valid bundles
    (i.e. contain a manifest JSON). Skips blocks listed in SKIP_BLOCKS.
    Returns a sorted list of bundle Paths.
    """
    if not bundles_root.exists():
        return []

    found = []
    for entry in sorted(bundles_root.iterdir()):
        if not entry.is_dir():
            continue
        if entry.name in SKIP_BLOCKS:
            print(c(f"  [discovery] Skipping non-synthesizable block: {entry.name}", "grey"))
            continue
        if _has_manifest(entry):
            found.append(entry)
        else:
            print(c(f"  [discovery] Skipping {entry.name} — no manifest found", "grey"))

    return found


# ─── Per-block runner ──────────────────────────────────────────────────────────

def run_block(
    bundle_dir: Path,
    out_root: Path,
    env_file: Path,
    enable_autotuner: bool,
    optimize_fmax: bool,
    mode: str,
    optimize_power: bool,
    drop_id: Optional[str],
    spec_revision: Optional[str],
    block_colour: str,
    print_lock: threading.Lock,
) -> Dict[str, Any]:
    """
    Run pipeline.py for a single bundle directory as a subprocess.
    Streams output line-by-line with a coloured block-name prefix.
    Returns a result dict with status, metrics, and timing.
    """
    block_name = bundle_dir.name
    prefix = f"{block_colour}[{block_name}]{COLOURS['reset']} "

    cmd = [
        sys.executable, "pipeline.py",
        "--bundle_dir",  str(bundle_dir),
        "--out_root",    str(out_root),
        "--env_file",    str(env_file),
    ]
    if mode:
        cmd += ["--mode", mode]
    if enable_autotuner:
        cmd.append("--enable_autotuner")
    if optimize_fmax:
        cmd.append("--optimize_fmax")
    if optimize_power:
        cmd.append("--optimize_power")
    # What ties a finding to the RTL it ran on. Without these the emitter writes to
    # outbox/unknown/, which the orchestrator never looks in - a silent dead letter.
    if drop_id:
        cmd += ["--drop_id", drop_id]
    if spec_revision:
        cmd += ["--spec_revision", spec_revision]

    start_time = time.time()

    try:
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )

        lines: List[str] = []
        for line in proc.stdout:
            line = line.rstrip()
            lines.append(line)
            with print_lock:
                print(f"{prefix}{line}")

        proc.wait()
        exit_code = proc.returncode

    except Exception as e:
        elapsed = time.time() - start_time
        return {
            "block_name":   block_name,
            "bundle_dir":   str(bundle_dir),
            "status":       "ERROR",
            "exit_code":    -1,
            "error":        str(e),
            "elapsed_s":    round(elapsed, 1),
            "metrics":      {},
            "validator":    {},
        }

    elapsed = time.time() - start_time

    # Parse final report for summary
    report_path = out_root / f"pipeline_final_report_{block_name}.json"
    metrics: Dict[str, Any] = {}
    validator: Dict[str, Any] = {}
    pipeline_status = "UNKNOWN"

    # A report from an earlier run is not evidence about this one. pipeline.py writes
    # it last, so anything older than this run's start cannot be ours - and a run that
    # died on import writes none at all. Without this test a crash in 0.2s reads as a
    # clean PASS with the previous run's area, power, DRC and LVS attached, which is
    # the most convincing kind of wrong answer this pipeline can give.
    fresh = (report_path.exists()
             and report_path.stat().st_mtime >= start_time - REPORT_MTIME_SLACK_S)

    if not fresh:
        tail = [l for l in lines[-12:] if l.strip()]
        return {
            "block_name":   block_name,
            "bundle_dir":   str(bundle_dir),
            "status":       "ERROR" if exit_code != 0 else "NO_REPORT",
            "exit_code":    exit_code,
            "error":        ("pipeline.py wrote no report for this run"
                             + (f" (exit {exit_code})" if exit_code else "")
                             + (" - last output: " + " | ".join(tail[-3:]) if tail else "")),
            "elapsed_s":    round(elapsed, 1),
            "metrics":      {},
            "validator":    {},
            "output_tail":  tail,
        }

    if report_path.exists():
        try:
            report = json.loads(report_path.read_text())
            pipeline_status = report.get("pipeline_status", "UNKNOWN")
            metrics = {
                "wns_ns":          report.get("sta_wns_ns"),
                "drc_violations":  report.get("drc_violations"),
                "lvs_status":      report.get("lvs_status"),
            }
            validator = {
                "drc":  report.get("drc_violations"),
                "lvs":  report.get("lvs_status"),
                "sta":  report.get("sta_wns_ns"),
                "sta_status": report.get("sta_status"),
            }
            # Optimization outcomes, when the tuners ran. Kept separate from the
            # delivered run's metrics below, which describe a different thing.
            for k in ("fmax_best_closed_mhz", "fmax_best_period_ns", "fmax_best_wns_ns",
                      "power_baseline_mw", "power_best_mw", "power_delivered_mw",
                      "power_delivered_is_best"):
                if report.get(k) is not None:
                    metrics[k] = report[k]
        except Exception:
            pass

    # Also check block-specific reporter summary for richer metrics
    reporter_summary_path = out_root / "reporter" / block_name / "reporter_summary.json"
    if (reporter_summary_path.exists()
            and reporter_summary_path.stat().st_mtime >= start_time - REPORT_MTIME_SLACK_S):
        try:
            rs = json.loads(reporter_summary_path.read_text())
            m = rs.get("metrics", {})
            metrics.update({
                "wns_ns":           m.get("wns_ns"),
                "utilization_pct":  m.get("utilization_pct"),
                "area_um2":         m.get("area_um2"),
                "cell_count":       m.get("cell_count"),
                "fmax_mhz":         m.get("fmax_mhz"),
                "power_mw":         m.get("power_mw"),
            })
        except Exception:
            pass

    # The report is this run's, but it cannot outrank the exit code: pipeline.py can
    # write PASS and then die in teardown. Disagreement goes to the process.
    if exit_code != 0 and pipeline_status == "PASS":
        pipeline_status = "FAIL"

    return {
        "block_name":      block_name,
        "bundle_dir":      str(bundle_dir),
        "status":          pipeline_status,
        "exit_code":       exit_code,
        "elapsed_s":       round(elapsed, 1),
        "metrics":         metrics,
        "validator":       validator,
    }


# ─── Summary table ─────────────────────────────────────────────────────────────

def print_summary(results: List[Dict[str, Any]], total_elapsed: float) -> None:
    print("\n" + "=" * 70)
    print(c("  BATCH PIPELINE SUMMARY", "bold"))
    print(f"  Total wall time: {round(total_elapsed, 1)}s  ({len(results)} blocks in parallel)")
    print("=" * 70)

    all_pass = True
    for r in results:
        status  = r["status"]
        block   = r["block_name"]
        elapsed = r["elapsed_s"]
        m       = r.get("metrics", {})
        v       = r.get("validator", {})

        passed = status == "PASS"
        if not passed:
            all_pass = False

        status_str = c("PASS", "green") if passed else c(status, "red")
        print(f"\n  {c(block, 'bold')}  [{status_str}]  ({elapsed}s)")

        # A block with no metrics produced none; say so rather than printing an
        # empty entry that reads like a block with nothing to report.
        if r.get("error"):
            print(f"    {c('no result', 'red')}    : {r['error']}")
            continue

        if m.get("wns_ns") is not None:
            print(f"    WNS          : {m['wns_ns']} ns")
        if m.get("utilization_pct") is not None:
            print(f"    Utilization  : {m['utilization_pct']} %")
        if m.get("area_um2") is not None:
            print(f"    Area         : {m['area_um2']} um2")
        if m.get("cell_count") is not None:
            print(f"    Cell count   : {m['cell_count']}")
        # Two different quantities. "delivered" is 1/period_min implied by the layout
        # that was actually built; "closed" is the fastest constraint the design met
        # during Fmax optimization. A power-optimized layout reports a lower delivered
        # figure because it was never asked to go fast — that is not a regression.
        has_closed = m.get("fmax_best_closed_mhz") is not None
        if m.get("fmax_mhz") is not None:
            print(f"    {'Fmax (built)' if has_closed else 'Fmax':<13}: {m['fmax_mhz']} MHz")
        if has_closed:
            print(f"    {'Fmax (closed)':<13}: {m['fmax_best_closed_mhz']} MHz  "
                  f"(period={m.get('fmax_best_period_ns')} ns, "
                  f"WNS={m.get('fmax_best_wns_ns')} ns)")
        if m.get("power_mw") is not None:
            print(f"    Power        : {m['power_mw']} mW")
        if m.get("power_best_mw") is not None and not m.get("power_delivered_is_best", True):
            print(c(f"    Power (best) : {m['power_best_mw']} mW at a config that was NOT built "
                    f"(baseline {m.get('power_baseline_mw')} mW)", "yellow"))
        if v.get("drc") is not None:
            drc_str = c(f"PASS  violations={v['drc']}", "green") if v["drc"] == 0 else c(f"FAIL  violations={v['drc']}", "red")
            print(f"    DRC          : {drc_str}")
        if v.get("lvs"):
            lvs_str = c(v["lvs"], "green") if v["lvs"] == "PASS" else c(v["lvs"], "red")
            print(f"    LVS          : {lvs_str}")
        if v.get("sta") is not None:
            sta_str = c(f"PASS  WNS={v['sta']} ns", "green") if (v["sta"] or 0) >= 0 else c(f"FAIL  WNS={v['sta']} ns", "red")
            print(f"    STA sign-off : {sta_str}")
        elif v.get("sta_status") == "N/A":
            print(f"    STA sign-off : {c('N/A  (no timing paths)', 'yellow')}")
        elif v.get("sta_status") == "ERROR":
            print(f"    STA sign-off : {c('NOT VERIFIED  (no timing data)', 'red')}")
        if r.get("error"):
            print(f"    Error        : {c(r['error'], 'red')}")

    print("\n" + "=" * 70)
    overall = c("ALL BLOCKS PASS", "green") if all_pass else c("ONE OR MORE BLOCKS FAILED", "red")
    print(f"  OVERALL STATUS : {overall}")
    print("=" * 70 + "\n")


# ─── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    # Default bundles root is ../bundles/ relative to this script
    script_dir   = Path(__file__).resolve().parent
    default_bundles_root = script_dir.parent / "bundles"

    ap = argparse.ArgumentParser(description="DDR3 Backend Batch Pipeline — runs multiple blocks in parallel")

    # Discovery arguments (mutually exclusive; --bundle_dirs takes priority)
    discovery = ap.add_mutually_exclusive_group()
    discovery.add_argument(
        "--bundle_dirs", nargs="+", type=Path,
        help="Explicit list of bundle directories (overrides auto-discovery)",
    )
    discovery.add_argument(
        "--bundles_root", type=Path, default=default_bundles_root,
        help=f"Folder to scan for bundles (default: {default_bundles_root})",
    )

    ap.add_argument("--out_root",         type=Path, default=Path("./pipeline_out"),
                    help="Output root directory (default: ./pipeline_out)")
    ap.add_argument("--env_file",         type=Path, default=Path(".env"),
                    help="Path to .env file (default: ./.env)")
    ap.add_argument("--enable_autotuner", action="store_true", default=False,
                    help="Enable failure auto-tuner for all blocks")
    ap.add_argument("--optimize_fmax",    action="store_true", default=False,
                    help="Enable Fmax optimization for all blocks")
    ap.add_argument("--optimize_power",   action="store_true", default=False,
                    help="Enable power optimization for all blocks")
    ap.add_argument("--drop_id", default=None,
                    help="The frontend drop's content id, passed to every block so its "
                         "findings can be tied to the RTL they ran on.")
    ap.add_argument("--spec_revision", default=None,
                    help="The spec revision these bundles came from. The orchestrator "
                         "looks the findings outbox up by it; without it findings land "
                         "in outbox/unknown/ where nothing reads them.")
    ap.add_argument("--mode", default="build",
                    choices=["contract", "synth", "build", "full"],
                    help="How far to take each block. contract (seconds, no Docker), "
                         "synth (minutes), build (~1 hour for 11 blocks, default), "
                         "full (hours, adds PPA optimization).")
    ap.add_argument("--max_workers",      type=int, default=None,
                    help=f"Max parallel workers (default: {SAFE_MAX_WORKERS}). Higher values "
                         f"have corrupted runs on this flow — see SAFE_MAX_WORKERS in this file.")
    args = ap.parse_args()

    # ── Resolve bundle list ───────────────────────────────────────────────────
    if args.bundle_dirs:
        # Explicit list provided — use as-is (original behaviour)
        bundle_dirs = args.bundle_dirs
        discovery_mode = "explicit"
    else:
        # Auto-discover from bundles_root
        bundles_root = args.bundles_root
        print(c(f"\n  [discovery] Scanning for bundles in: {bundles_root}", "cyan"))
        bundle_dirs = discover_bundles(bundles_root)
        discovery_mode = f"auto ({bundles_root})"

    if not bundle_dirs:
        print(c("  ERROR: No bundles found. Use --bundle_dirs or --bundles_root to point at your bundles.", "red"))
        return 1

    # Default to the parallelism the flow is known to survive, not to one worker
    # per block. Asking for more is allowed, but it is a deliberate choice and
    # says so out loud.
    max_workers = args.max_workers or min(SAFE_MAX_WORKERS, len(bundle_dirs))
    if args.max_workers and args.max_workers > SAFE_MAX_WORKERS:
        print(c(f"  WARNING: --max_workers={args.max_workers} exceeds the tested safe limit of "
                f"{SAFE_MAX_WORKERS}.", "yellow"))
        print(c(f"           Concurrent ORFS containers have corrupted the bind-mounted flow "
                f"directory at this level,", "yellow"))
        print(c(f"           producing layouts that look complete but are not. Sign-off will "
                f"catch it and halt; expect", "yellow"))
        print(c(f"           failed blocks rather than wrong results.", "yellow"))

    print("=" * 70)
    print(c("  DDR3 Backend Batch Pipeline", "bold"))
    print(f"  Discovery   : {discovery_mode}")
    print(f"  Blocks      : {[b.name for b in bundle_dirs]}")
    print(f"  Workers     : {max_workers}")
    print(f"  out_root    : {args.out_root}")
    print(f"  autotuner   : {args.enable_autotuner}")
    print(f"  mode        : {args.mode}")
    print(f"  opt_fmax    : {args.optimize_fmax}")
    print(f"  opt_power   : {args.optimize_power}")
    print(f"  spec_rev    : {args.spec_revision or '(none - findings go to outbox/unknown)'}")
    if args.drop_id:
        print(f"  drop_id     : {args.drop_id}")
    print("=" * 70 + "\n")

    print_lock = threading.Lock()
    results: List[Dict[str, Any]] = []
    wall_start = time.time()

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(
                run_block,
                bundle_dir=bd,
                out_root=args.out_root,
                env_file=args.env_file,
                enable_autotuner=args.enable_autotuner,
                mode=args.mode,
                optimize_fmax=args.optimize_fmax,
                drop_id=args.drop_id,
                spec_revision=args.spec_revision,
                optimize_power=args.optimize_power,
                block_colour=BLOCK_COLOURS[i % len(BLOCK_COLOURS)],
                print_lock=print_lock,
            ): bd.name
            for i, bd in enumerate(bundle_dirs)
        }

        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            with print_lock:
                status = result["status"]
                colour = "green" if status == "PASS" else "red"
                block_msg = f"[{result['block_name']}] Finished in {result['elapsed_s']}s -> {status}"
                print(f"\n{c(block_msg, colour)}\n")

    total_elapsed = time.time() - wall_start

    # Sort results to match discovered/input order
    order = {bd.name: i for i, bd in enumerate(bundle_dirs)}
    results.sort(key=lambda r: order.get(r["block_name"], 99))

    print_summary(results, total_elapsed)

    return 0 if all(r["status"] == "PASS" for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
