#!/usr/bin/env python3
"""
+======================================================================+
|              FULL PIPELINE RUNNER (Frontend2) -- Phases 1-4          |
|                                                                      |
|  Prompts ONCE for spec path + output dir, then runs Phase 1 -> 2 ->  |
|  3 -> 4 in order. After each phase, pauses and shows where its RTL   |
|  and validation report landed, then lets you continue to the next    |
|  phase or review the report first.                                   |
|                                                                      |
|  Each phase runs as its own subprocess (phaseN_pipeline.py), output  |
|  streamed live -- identical to running it by hand. Subprocess         |
|  isolation is deliberate, not incidental: Phase1/tb_generator.py and |
|  Phase2/tb_generator.py share a module name, so importing both       |
|  phaseN_pipeline modules into one Python process would silently      |
|  reuse whichever tb_generator loaded first (sys.modules caching) --  |
|  running each phase as a separate process sidesteps that entirely.   |
|                                                                      |
|  Requires OLYMPUS_USER / OLYMPUS_KEY already set in the environment  |
|  (see IMPLEMENTATION_PLAN.md infra notes) -- this script doesn't     |
|  relay an interactive SSH password across 4 separate subprocesses.   |
|                                                                      |
|  A failed phase stops the chain there (no auto-continue past a real  |
|  bug) -- same "no retry loop, human review" philosophy as every      |
|  individual phase pipeline.                                          |
+======================================================================+
"""

import json
import os
import subprocess
import sys
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
PYTHON = sys.executable

# (phase_num, subdir, script, rtl_subdir_name)
PHASES = [
    (1, "Phase1", "phase1_pipeline.py", "PHASE1RTL"),
    (2, "Phase2", "phase2_pipeline.py", "PHASE2RTL"),
    (3, "Phase3", "phase3_pipeline.py", "PHASE3RTL"),
    (4, "Phase4", "phase4_pipeline.py", "PHASE4RTL"),
]
VALIDATION_DIR = "VALIDATIONREPORT"


def _check_ssh_env():
    if not os.environ.get("OLYMPUS_USER") or not os.environ.get("OLYMPUS_KEY"):
        print("\n  WARNING: OLYMPUS_USER / OLYMPUS_KEY are not both set in this")
        print("  shell. Each phase's lint/sim gates will SKIP (or a phase may")
        print("  crash waiting on a password prompt this script can't answer)")
        print("  unless both are exported first. See IMPLEMENTATION_PLAN.md.\n")


def _check_scripts_exist():
    missing = []
    for phase_num, subdir, script, _ in PHASES:
        p = Path(HERE) / subdir / script
        if not p.is_file():
            missing.append(str(p))
    if missing:
        print("  ERROR: missing pipeline script(s):")
        for m in missing:
            print(f"    {m}")
        sys.exit(1)


def run_phase(phase_num: int, subdir: str, script: str, spec_path: str, output_dir: str) -> bool:
    script_path = str(Path(HERE) / subdir / script)
    print(f"\n{'#' * 62}")
    print(f"#  RUNNING PHASE {phase_num}")
    print(f"{'#' * 62}\n")
    proc = subprocess.run(
        [PYTHON, script_path],
        input=f"{spec_path}\n{output_dir}\n",
        text=True,
        env=os.environ.copy(),
    )
    return proc.returncode == 0


def show_report(output_dir: str, phase_num: int, passed: bool):
    val_dir = Path(output_dir) / VALIDATION_DIR
    report_name = f"phase{phase_num}_final_report.json" if passed else f"phase{phase_num}_error_report.json"
    report_path = val_dir / report_name
    print(f"\n{'-' * 62}")
    print(f"  Phase {phase_num} report: {report_path}")
    print(f"{'-' * 62}")
    if report_path.exists():
        try:
            print(json.dumps(json.loads(report_path.read_text()), indent=2))
        except Exception as e:
            print(f"  (could not parse report: {e})")
    else:
        print("  (report file not found -- phase may not have reached this stage)")
    print(f"\n  Full validation dir: {val_dir}")
    print()


def prompt_next(phase_num: int, output_dir: str, rtl_dir: Path, passed: bool, is_last: bool) -> str:
    """Returns 'continue', 'finish', or 'quit'."""
    while True:
        print(f"\n{'=' * 62}")
        print(f"  PHASE {phase_num} {'PASSED' if passed else 'FAILED'}")
        print(f"{'=' * 62}")
        print(f"  RTL:        {rtl_dir}")
        print(f"  Validation: {Path(output_dir) / VALIDATION_DIR}")

        if not passed:
            print("\n  This phase failed. Nothing in this pipeline is LLM-driven,")
            print("  so this is a real bug (generator, spec, or testbench) that")
            print("  needs human review -- not something a retry would fix.")
            print("\n  [r] review report   [q] quit")
            choice = input("  > ").strip().lower()
            if choice == "r":
                show_report(output_dir, phase_num, passed)
                continue
            if choice == "q":
                return "quit"
            print("  (unrecognized option)")
            continue

        if is_last:
            print("\n  [r] review report   [f] finish")
            choice = input("  > ").strip().lower()
            if choice == "r":
                show_report(output_dir, phase_num, passed)
                continue
            if choice == "f":
                return "finish"
            print("  (unrecognized option)")
            continue

        print(f"\n  [c] continue to Phase {phase_num + 1}   [r] review report   [q] quit")
        choice = input("  > ").strip().lower()
        if choice == "r":
            show_report(output_dir, phase_num, passed)
            continue
        if choice == "c":
            return "continue"
        if choice == "q":
            return "quit"
        print("  (unrecognized option)")


def main():
    print("+========================================================+")
    print("|   DDR3 Controller -- FULL PIPELINE (Frontend2)          |")
    print("|                                                         |")
    print("|   Phase 1 -> Phase 2 -> Phase 3 -> Phase 4              |")
    print("|   One prompt up front; a checkpoint after each phase.   |")
    print("+========================================================+\n")

    _check_scripts_exist()
    _check_ssh_env()

    spec_path = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec_path):
        print(f"Not found: {spec_path}")
        sys.exit(1)
    spec_path = os.path.abspath(spec_path)

    output_dir = input("Output dir (Enter for ./output): ").strip() or "./output"
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    for i, (phase_num, subdir, script, rtl_subdir) in enumerate(PHASES):
        is_last = (i == len(PHASES) - 1)
        passed = run_phase(phase_num, subdir, script, spec_path, output_dir)
        rtl_dir = Path(output_dir) / rtl_subdir

        action = prompt_next(phase_num, output_dir, rtl_dir, passed, is_last)

        if action == "quit":
            print("\n  Stopped by user.")
            sys.exit(0 if passed else 1)
        if action == "finish":
            print(f"\n{'#' * 62}")
            print("#  FULL PIPELINE COMPLETE -- ALL 4 PHASES PASSED")
            print(f"{'#' * 62}\n")
            for pn, _, _, rtl_subdir2 in PHASES:
                print(f"    Phase {pn} RTL: {Path(output_dir) / rtl_subdir2}")
            print(f"\n    Validation reports: {Path(output_dir) / VALIDATION_DIR}\n")
            sys.exit(0)
        # action == "continue" -> loop to next phase


if __name__ == "__main__":
    main()
