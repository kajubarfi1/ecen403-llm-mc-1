#!/usr/bin/env python3
"""
+======================================================================+
|         FULL PIPELINE RUNNER (Frontend2) -- Spec -> Phases 1-4       |
|                                                                      |
|  Prompts for output dir, then a spec: either an existing spec JSON,  |
|  or synthesize a new one now via Microarch/microarch_cli.py (English |
|  / preset / Tier-1-3 choices), gated by Microarch/                   |
|  dummy_validation_agent.py -- a stub standing in for Jacob's         |
|  Validation subsystem until that hookup exists. Then runs Phase 1 -> |
|  2 -> 3 -> 4 in order same as before. After each phase, pauses and   |
|  shows where its RTL and validation report landed, then lets you     |
|  continue to the next phase or review the report first. On the last  |
|  phase passing, also generates the combined top-level bundle         |
|  (generate_top.py).                                                  |
|                                                                      |
|  A FAILED phase offers [x] run the fix agent, for any phase_num in   |
|  FIX_AGENTS (today: just Phase 1, phase1_validation_agent.py) -- an  |
|  LLM reads that phase's failure report and proposes a human-         |
|  confirmed patch to the generator script (never the emitted RTL      |
|  directly). After it runs, this pipeline re-runs the SAME phase to   |
|  get an authoritative pass/fail, rather than trusting the agent's    |
|  own per-module re-verification as the final word.                  |
|                                                                      |
|  Two optional Frontend Orchestrator checkpoints (Orchestrator/       |
|  orchestrator_agent.py), both prompt-gated and off by default: after |
|  the spec is resolved (spec-stage findings -> Microarch agent, may   |
|  swap in a revised spec) and after the top-level bundle (RTL-stage   |
|  findings -> Phase 1/2 fix agents). They read Validation's outbox.   |
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
from __future__ import annotations

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

# (phase_num, failure_stage) -> fix agent script. Keyed by failure_stage,
# not just phase_num, because the SAME phase can fail for two genuinely
# different reasons that need two DIFFERENT agents -- a real Xcelium sim
# failure (phase1_validation_agent.py, patches the RTL generator) vs. a
# testbench_auditor.py finding (testbench_fix_agent.py, patches the
# testbench generator). Deliberately never one agent for both -- see
# testbench_fix_agent.py's docstring on why that circular-dependency risk
# is worth avoiding by construction. A (phase_num, failure_stage) pair not
# in this map just doesn't offer the [x] option.
FIX_AGENTS = {
    (1, "BEHAVIORAL_SIMULATION"): "Phase1/phase1_validation_agent.py",
    (1, "TESTBENCH_AUDIT"): "Phase1/testbench_fix_agent.py",
    # Phase 2's auditor (Phase2/testbench_auditor.py) is narrower than
    # Phase 1's: it checks the spec-derived localparams, address-slice
    # vectors and ZQCS values, not the TB-owned directed timing constants.
    (2, "BEHAVIORAL_SIMULATION"): "Phase2/phase2_validation_agent.py",
    (2, "TESTBENCH_AUDIT"): "Phase2/testbench_fix_agent.py",
    # Phases 3/4 emit their testbench from the same generator as the RTL, so their
    # agent freezes the testbench methods mechanically (see its docstring).
    (3, "BEHAVIORAL_SIMULATION"): "Phase3/phase3_validation_agent.py",
    (4, "BEHAVIORAL_SIMULATION"): "Phase4/phase4_validation_agent.py",
}


def _check_ssh_env():
    if not os.environ.get("OLYMPUS_USER") or not os.environ.get("OLYMPUS_KEY"):
        print("\n  WARNING: OLYMPUS_USER / OLYMPUS_KEY are not both set in this")
        print("  shell. Each phase's lint/sim gates will SKIP -- and a skipped gate now")
        print("  FAILS the phase (set ALLOW_SKIPPED_GATES=1 to proceed unverified on")
        print("  purpose) -- or a phase may crash waiting on a password prompt this")
        print("  script can't answer. Export both first. See IMPLEMENTATION_PLAN.md.\n")


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


def resolve_spec_path(output_dir: str) -> str:
    """Either an existing spec JSON, or a freshly synthesized one that has
    passed the (stub) validation stage. Returns an absolute path, or exits
    the process if neither path produces one."""
    print("\n  Spec source:")
    print("    [e] existing spec JSON path")
    print("    [s] synthesize a new spec now (microarchitecture generator)")
    choice = input("  > (e/s) [e]: ").strip().lower() or "e"

    if choice == "s":
        spec_path = run_microarch_synthesis(output_dir)
        if not spec_path:
            print("\n  No validated spec produced. Stopping.")
            sys.exit(1)
        return spec_path

    spec_path = input("Spec JSON path: ").strip()
    if not os.path.isfile(spec_path):
        print(f"Not found: {spec_path}")
        sys.exit(1)
    spec_path = os.path.abspath(spec_path)
    if not run_spec_review(spec_path):
        print("\n  Spec failed review. Stopping before Phase 1.")
        sys.exit(1)
    return spec_path


def run_spec_review(spec_path: str) -> bool:
    """The spec-review stage before Phase 1, on every spec however it arrived.
    Validation's validate_spec_stage (schema, JESD79-3, register map, intake
    gate) when it is importable; otherwise the stub dummy_validation_agent,
    said out loud. FAIL blocks. Intake gaps are advisory: listed, never
    silently dropped. Returns True on PASS."""
    print(f"\n{'#' * 62}")
    print("#  SPEC REVIEW")
    print(f"{'#' * 62}\n")
    spec = json.loads(Path(spec_path).read_text())
    try:
        sys.path.insert(0, str(Path(HERE).parents[1] / "Validation" / "spec"))
        from validate_spec_stage import validate_spec
        result = validate_spec(spec, None, spec_path=spec_path)
    except Exception as e:
        print(f"  WARNING: Validation's spec review unavailable ({e}); using the stub.")
        sys.path.insert(0, str(Path(HERE) / "Microarch"))
        import dummy_validation_agent as dva
        result = dva.validate_spec(spec)
    print(f"  validator: {result['validator']}")
    print(f"  status:    {result['status']}")
    review = result.get("review") or {}
    blocking = review.get("blocking", result["findings"] if result["status"] == "FAIL" else [])
    advisory = review.get("advisory", [])
    for f in blocking:
        print(f"    BLOCKING  {f}")
    if advisory:
        print(f"    {len(advisory)} open intake question(s) (advisory; Validation judges under "
              f"pinned conventions until the spec answers them):")
        for f in advisory:
            print(f"      {f}")
    if result["status"] != "PASS":
        print("\n  Revise with:  microarch_cli.py --feedback "
              "Validation/findings/outbox/current/SPEC_REVIEW.json  <request>")
    return result["status"] == "PASS"


def run_microarch_synthesis(output_dir: str) -> str | None:
    """Runs microarch_cli.py (English / preset / choices, interactive),
    then the (stub) dummy_validation_agent.py against whatever it wrote.
    Returns the validated spec's absolute path, or None on abort/failure.

    microarch_cli.py is a REPL, so this inherits stdio rather than piping
    canned answers the way run_phase() does for the (mostly-scripted)
    phase pipelines -- there's no fixed question sequence to script here.
    """
    print(f"\n{'#' * 62}")
    print("#  MICROARCHITECTURE SPEC SYNTHESIS")
    print(f"{'#' * 62}\n")
    default_path = Path(output_dir) / "generated_spec.json"
    print(f"  When asked where to write the spec, press Enter to accept the")
    print(f"  default ({default_path}), or type your own path.\n")

    cli_path = str(Path(HERE) / "Microarch" / "microarch_cli.py")
    env = os.environ.copy()
    env["MICROARCH_DEFAULT_OUT_DIR"] = output_dir
    subprocess.run([PYTHON, cli_path], env=env)

    while True:
        candidate = input(
            f"\n  Path to the spec that was written [{default_path}]: ").strip()
        spec_path = Path(candidate) if candidate else default_path
        if spec_path.is_file():
            break
        print(f"  Not found: {spec_path}")
        again = input("  [r]etry path / [a]bort synthesis: ").strip().lower()
        if again == "a":
            return None

    spec_path = spec_path.resolve()
    spec = json.loads(spec_path.read_text())

    if not run_spec_review(str(spec_path)):
        print("\n  Spec failed review. Stopping before Phase 1.")
        return None

    print(f"\n  Spec validated: {spec_path}")
    return str(spec_path)


def run_orchestrator(stage: str, spec_path: str, output_dir: str) -> str | None:
    """Optional Frontend Orchestrator checkpoint (Orchestrator/
    orchestrator_agent.py). Reads Validation's outbox and routes findings:
    stage "spec" -> Microarch agent, stage "rtl" -> Phase 1/2 fix agents
    (patches still human-confirmed there). Inherits stdio. Returns the path
    of the newest revised spec it wrote (stage "spec" only), else None.
    Skipped by default -- the outbox may be stale relative to this run."""
    print(f"\n  Frontend Orchestrator ({stage} stage): route Validation's findings?")
    print("  Reads Validation/findings/outbox (check its drop is current first).")
    if input("  > run it? (y/N): ").strip().lower() != "y":
        return None
    print(f"\n{'#' * 62}")
    print(f"#  FRONTEND ORCHESTRATOR ({stage.upper()} STAGE)")
    print(f"{'#' * 62}\n")
    subprocess.run(
        [PYTHON, str(Path(HERE) / "Orchestrator" / "orchestrator_agent.py"),
         "--stage", stage, "--spec", spec_path, "--output-dir", output_dir],
        env=os.environ.copy(),
    )
    if stage != "spec":
        return None
    revs = sorted((Path(output_dir) / "ORCHESTRATOR").glob("spec_rev*.json"),
                  key=lambda p: p.stat().st_mtime)
    if not revs:
        return None
    print(f"\n  Orchestrator wrote a revised spec: {revs[-1]}")
    if input("  > use it for Phases 1-4 instead? (y/N): ").strip().lower() == "y":
        return str(revs[-1].resolve())
    return None


def ship_drop(spec_path: str, output_dir: str) -> None:
    """Frontend side of Validation/findings/HANDOFF_CONTRACT.md: ship the
    spec beside the RTL, name the drop by content hash, and warn if any block
    was generated from a different spec revision (Validation would block
    every path through it)."""
    import drop
    drop.ship_spec(spec_path, output_dir)
    chk = drop.spec_consistency(output_dir)
    print(f"\n    Drop id (content hash, matches Validation's): {drop.compute_drop_id(output_dir)}")
    print(f"    Shipped spec: {Path(output_dir) / 'generated_spec.json'}"
          f"  (revision {chk['spec_revision']})")
    stale = drop.top_copy_mismatches(output_dir)
    if stale:
        print(f"    WARNING: TOPRTL copies differ from their phase outputs: {', '.join(sorted(stale))}")
    if chk["foreign"]:
        print("    WARNING: blocks from a different spec revision (Validation will block")
        print("    paths through them -- re-run the phases that produced them):")
        for b, r in sorted(chk["foreign"].items()):
            print(f"      {b}: {r}")
    print()

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


def _read_failure_stage(output_dir: str, phase_num: int) -> str | None:
    report_path = Path(output_dir) / VALIDATION_DIR / f"phase{phase_num}_error_report.json"
    if not report_path.is_file():
        return None
    try:
        return json.loads(report_path.read_text()).get("failure_stage")
    except Exception:
        return None


def prompt_next(phase_num: int, output_dir: str, rtl_dir: Path, passed: bool, is_last: bool) -> str:
    """Returns 'continue', 'finish', 'quit', or 'fix'."""
    while True:
        print(f"\n{'=' * 62}")
        print(f"  PHASE {phase_num} {'PASSED' if passed else 'FAILED'}")
        print(f"{'=' * 62}")
        print(f"  RTL:        {rtl_dir}")
        print(f"  Validation: {Path(output_dir) / VALIDATION_DIR}")

        if not passed:
            failure_stage = _read_failure_stage(output_dir, phase_num)
            has_agent = (phase_num, failure_stage) in FIX_AGENTS
            print("\n  This phase failed. Nothing in this pipeline retries a")
            print("  deterministic generator blindly -- a bare retry reproduces")
            print("  the same bug. What CAN help is a human-confirmed LLM patch")
            print("  agent that reads the failure report and proposes a fix.")
            if failure_stage:
                print(f"  Failure stage: {failure_stage}"
                      f"{'' if has_agent else ' (no fix agent registered for this stage yet)'}")
            opts = "  [r] review report"
            if has_agent:
                opts += "   [x] run the fix agent"
            opts += "   [q] quit"
            print(f"\n{opts}")
            choice = input("  > ").strip().lower()
            if choice == "r":
                show_report(output_dir, phase_num, passed)
                continue
            if choice == "x" and has_agent:
                return "fix"
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


def run_fix_agent(phase_num: int, failure_stage: str, output_dir: str, spec_path: str) -> None:
    """Runs the fix agent registered for this exact (phase_num,
    failure_stage) pair -- see FIX_AGENTS for why that's two-dimensional,
    not just phase_num. Inherits stdio: the agent's own apply/retry/skip
    prompts are answered live by whoever is running this pipeline, same as
    the microarch synthesis REPL. Does not itself judge pass/fail -- the
    caller re-runs the phase afterward, which is the only authoritative
    verdict (an agent's own re-verification is per-module/local, not the
    full phase-level lint+sim gate this pipeline actually gates on)."""
    agent_path = str(Path(HERE) / FIX_AGENTS[(phase_num, failure_stage)])
    print(f"\n{'#' * 62}")
    print(f"#  PHASE {phase_num} FIX AGENT ({failure_stage})")
    print(f"{'#' * 62}\n")
    subprocess.run(
        [PYTHON, agent_path, "--output-dir", output_dir, "--spec", spec_path],
        env=os.environ.copy(),
    )
    print(f"\n  Re-running Phase {phase_num} to get an authoritative verdict...")


def main():
    print("+========================================================+")
    print("|   DDR3 Controller -- FULL PIPELINE (Frontend2)          |")
    print("|                                                         |")
    print("|   Phase 1 -> Phase 2 -> Phase 3 -> Phase 4              |")
    print("|   One prompt up front; a checkpoint after each phase.   |")
    print("+========================================================+\n")

    _check_scripts_exist()
    _check_ssh_env()

    output_dir = input("Output dir (Enter for ./output): ").strip() or "./output"
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    spec_path = resolve_spec_path(output_dir)
    spec_path = run_orchestrator("spec", spec_path, output_dir) or spec_path

    i = 0
    while i < len(PHASES):
        phase_num, subdir, script, rtl_subdir = PHASES[i]
        if i > 0:
            import drop
            mixed = drop.revision_mismatches(
                output_dir, spec_path, [p[3] for p in PHASES[:i]])
            if mixed:
                print(f"\n  STOP: earlier phase(s) in {output_dir} were generated from a different")
                print(f"  spec than the one in use ({Path(spec_path).name}). One generation = one")
                print("  spec; a drop built from two has no single contract.")
                for b, r in sorted(mixed.items()):
                    print(f"    {b}: {r}")
                if input("  [r]e-run from Phase 1 with this spec / [q]uit: ").strip().lower() == "r":
                    i = 0
                    continue
                sys.exit(1)
        is_last = (i == len(PHASES) - 1)
        passed = run_phase(phase_num, subdir, script, spec_path, output_dir)
        rtl_dir = Path(output_dir) / rtl_subdir

        action = prompt_next(phase_num, output_dir, rtl_dir, passed, is_last)

        if action == "fix":
            failure_stage = _read_failure_stage(output_dir, phase_num)
            run_fix_agent(phase_num, failure_stage, output_dir, spec_path)
            continue  # re-run this same phase_num, not the next one

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

            print(f"{'#' * 62}")
            print("#  GENERATING TOP-LEVEL BUNDLE (ddr3_controller)")
            print(f"{'#' * 62}\n")
            top_rc = subprocess.run(
                [PYTHON, str(Path(HERE) / "generate_top.py"),
                 "--output-dir", output_dir, "--spec", spec_path],
                env=os.environ.copy(),
            ).returncode
            if top_rc == 0:
                print(f"\n    Top-level bundle: {Path(output_dir) / 'TOPRTL'}\n")
            else:
                print("\n    Top-level bundle generation FAILED -- see output above.")
                print("    (The 4 phase RTL outputs above are still valid; only the")
                print("    combined top-level bundle failed.)\n")
            ship_drop(spec_path, output_dir)
            if top_rc == 0:
                run_orchestrator("rtl", spec_path, output_dir)
                print("\n    If the orchestrator dispatched fixes, re-run this pipeline")
                print("    to regenerate every phase from the patched generators.\n")
            sys.exit(top_rc)
        # action == "continue" -> advance to the next phase
        i += 1


if __name__ == "__main__":
    main()
