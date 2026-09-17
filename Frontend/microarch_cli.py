#!/usr/bin/env python3
"""
+======================================================================+
|      DDR3 MICROARCHITECTURE GENERATOR -- interactive CLI             |
|                                                                      |
|  English in  ->  microarch_spec.json out.                           |
|                                                                      |
|  This is a STANDALONE explorer. It does NOT run Phase 1-4, lint,     |
|  sim, or backend -- it only produces (and optionally writes) the     |
|  microarchitecture spec so you can see what the agent resolves an    |
|  English request into.                                               |
|                                                                      |
|  Run it:                                                             |
|    python Frontend/microarch_cli.py                 # interactive    |
|    python Frontend/microarch_cli.py "low power ddr3 for a sensor"    |
|    python Frontend/microarch_cli.py --preset balanced               |
|    python Frontend/microarch_cli.py "..." --json    # spec to stdout |
|                                                                      |
|  Needs ANTHROPIC_API_KEY for the English path. Preset / choices-file |
|  paths work with no key.                                            |
+======================================================================+
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import textwrap
from pathlib import Path

# --- make Frontend/Agents importable -------------------------------------
_HERE = Path(__file__).resolve().parent
_AGENTS = _HERE / "Agents"
if str(_AGENTS) not in sys.path:
    sys.path.insert(0, str(_AGENTS))

import microarch_agent as ma      # noqa: E402
import microarch_compiler as mc   # noqa: E402
import microarch_goals as mg      # noqa: E402
import microarch_colors as mcol   # noqa: E402


# ======================================================================
# formatting helpers
# ======================================================================
_W = 68


def _rule(title: str = "") -> str:
    if not title:
        return mcol.header("-" * _W)
    text = f"-- {title} " + "-" * max(0, _W - len(title) - 4)
    return mcol.header(text)


def _print_result(res: dict, proposal: dict | None):
    """res is a microarch_compiler.compile_spec() result dict."""
    r = res["resolved_choices"]
    spec = res["spec"]

    if proposal and proposal.get("rationale"):
        print("\n" + _rule("interpretation"))
        print("  " + proposal["rationale"].strip())

    print("\n" + _rule("resolved configuration"))
    print("  Tier-1")
    for k in mc.TIER1_CHOICES:
        print(f"    {k:24s} {r[k]}")
    print("  Tier-2 / Tier-3")
    for k in list(mc.TIER2_DEFAULTS) + ["target_frequency_mhz",
                                        "area_optimization_goal",
                                        "power_optimization_goal",
                                        "pipeline_latency_cycles"]:
        print(f"    {k:24s} {r[k]}")

    if proposal and proposal.get("assumptions"):
        print("\n" + _rule("assumptions (you did not state these)"))
        for a in proposal["assumptions"]:
            print(mcol.dim(f"    - {a['parameter']} = {a['value']}"))
            print(mcol.dim(f"      {a['reason']}"))

    if res["warnings"]:
        print("\n" + _rule("warnings"))
        for w in res["warnings"]:
            print(mcol.warn(f"    ! {w}"))

    tm = spec["timing_model"]
    dc = tm["$derived_cycles"]
    ge = spec["memory_geometry"]["$derived"]
    cl = spec["clocking_model"]["$derived"]
    print("\n" + _rule("JEDEC-derived (computed, not guessed)"))
    print(f"    speed bin     {tm['speed_bin']}")
    print(f"    tCK           {tm['tCK_ns']} ns"
          f"   ctrl {cl['controller_frequency_MHz']} MHz"
          f" / ddr {cl['ddr_clock_frequency_MHz']} MHz"
          f" / {cl['data_rate_MTps']} MT/s")
    print(f"    CL / CWL      {tm['CL_cycles']} / {tm['CWL_cycles']}")
    print(f"    tRCD tRP tRAS tRC   {dc['tRCD_nCK']} {dc['tRP_nCK']} "
          f"{dc['tRAS_nCK']} {dc['tRC_nCK']}  nCK")
    print(f"    tRFC tFAW tRRD     {dc['tRFC_nCK']} {dc['tFAW_nCK']} "
          f"{dc['tRRD_nCK']}  nCK")
    print(f"    tWR tWTR tRTP tCCD  {dc['tWR_nCK']} {dc['tWTR_nCK']} "
          f"{dc['tRTP_nCK']} {dc['tCCD_nCK']}  nCK")
    print(f"    geometry      {ge['device_density_label']}  "
          f"{spec['memory_geometry']['row_bits']} row / "
          f"{spec['memory_geometry']['column_bits']} col / "
          f"{spec['memory_geometry']['bank_bits']} bank")
    print(f"    channel       {ge['channel_data_width_bits']}-bit"
          f"   {ge['channel_capacity_MB']} MB"
          f"   peak {ge['peak_channel_bandwidth_MBps']} MB/s")

    npass = sum(c["pass"] for c in res["consistency_checks"])
    tot = len(res["consistency_checks"])
    print("\n" + _rule("consistency"))
    mark, paint = ("OK", mcol.ok) if npass == tot else ("FAIL", mcol.err)
    print(paint(f"    [{mark}] {npass}/{tot} checks pass"))
    for c in res["consistency_checks"]:
        if not c["pass"]:
            print(mcol.err(f"      x {c['name']}   ({c['detail']})"))


def _default_out(spec: dict) -> Path:
    return _HERE.parent / "builds" / spec["design_id"] / "microarch_spec.json"


def _write(spec: dict, report_payload: dict, path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(spec, indent=2))
    rp = path.with_name("microarch_report.json")
    rp.write_text(json.dumps(report_payload, indent=2))
    print(mcol.ok(f"\n  wrote {path}"))
    print(mcol.ok(f"        {rp}"))


# ======================================================================
# one-shot
# ======================================================================
def _one_shot(request: str | None, preset: str | None, choices_file: str | None,
              out: str | None, as_json: bool, no_write: bool,
              goal: str | None = None) -> int:
    if preset:
        res = mc.compile_spec(dict(mc.PRESETS[preset]))
        proposal = None
    elif choices_file:
        res = mc.compile_spec(json.loads(Path(choices_file).read_text()))
        proposal = None
    else:
        if goal and not as_json:
            print(_rule(f"goal: {mg.GOALS[goal]['label']}"))
            print(" ", mg.describe_goal(goal).replace("\n", "\n  "))
        try:
            outcome = ma.run_english(request, interactive=False, goal=goal)
        except RuntimeError as e:
            print(f"ERROR: {e}", file=sys.stderr)
            if "ANTHROPIC_API_KEY" in str(e):
                print("  export ANTHROPIC_API_KEY=sk-...   (or use --preset)",
                      file=sys.stderr)
            return 1
        if outcome["status"] == "questions":
            print(mcol.warn("NEEDS CLARIFICATION:"), file=sys.stderr)
            for q in outcome["open_questions"]:
                print(f"  [{q.get('parameter','?')}] {q.get('question','')}",
                      file=sys.stderr)
            print("  re-run interactively (no args) to answer these.",
                  file=sys.stderr)
            return 3
        if outcome["status"] != "ok":
            print(mcol.err("COULD NOT CONVERGE:"), outcome.get("errors"), file=sys.stderr)
            return 3
        res = outcome["compile"]
        proposal = outcome["proposal"]

    if not res["ok"]:
        print(mcol.err("REJECTED:"), file=sys.stderr)
        for e in res["errors"]:
            print(mcol.err(f"  ERROR   {e}"), file=sys.stderr)
        for w in res["warnings"]:
            print(mcol.warn(f"  WARNING {w}"), file=sys.stderr)
        return 2

    if as_json:
        print(json.dumps(res["spec"], indent=2))
        return 0

    _print_result(res, proposal)
    if not no_write:
        path = Path(out) if out else _default_out(res["spec"])
        _write(res["spec"], _report_payload(res, proposal), path)
    return 0


def _report_payload(res: dict, proposal: dict | None) -> dict:
    return {
        "resolved_choices": res["resolved_choices"],
        "assumptions": (proposal or {}).get("assumptions", []),
        "rationale": (proposal or {}).get("rationale", ""),
        "warnings": res["warnings"],
        "consistency_checks": res["consistency_checks"],
        "modifiability": mc.modifiability_report(),
    }


# ======================================================================
# interactive REPL
# ======================================================================
def _print_banner() -> None:
    print()
    print(mcol.header("  DDR3 Microarchitecture Generator") + mcol.dim("  --  English -> spec"))
    print(mcol.dim("  Nothing downstream is wired up; this only produces the spec JSON."))
    print()
    print("  Type a description of the controller you want. Commands:")
    for cmd, desc in [
        ("preset <name>", "compile a named preset (no LLM)"),
        ("presets", "list presets"),
        ("goal", "(re-)ask the primary-goal leading question"),
        ("modifiable", "show which parameters are safe to change"),
        ("quit / exit", ""),
    ]:
        padded = f"{cmd:<18}"
        print(f"    {mcol.label(padded)}{mcol.dim(desc)}")


def _print_customizable() -> None:
    """Tier-1/2/3 knob table: Parameter | Range | Tradeoff, columns sized
    to each tier's own longest entries and the terminal width."""
    width = max(min(shutil.get_terminal_size((100, 24)).columns, 130), 70)
    for tier, params in mg.CUSTOMIZABLE.items():
        print("\n" + _rule(tier))
        name_w = max(len(p[0]) for p in params)
        range_w = max(len(p[2]) for p in params)
        tradeoff_w = max(28, width - name_w - range_w - 6)

        head = f"  {'Parameter':<{name_w}}  {'Range':<{range_w}}  Tradeoff"
        print(mcol.label(head))
        print(mcol.dim("  " + "-" * (name_w + range_w + tradeoff_w + 4)))
        for name, tradeoff, rng in params:
            lines = textwrap.wrap(tradeoff, tradeoff_w) or [""]
            print(f"  {mcol.label(f'{name:<{name_w}}')}  "
                  f"{mcol.accent(f'{rng:<{range_w}}')}  {lines[0]}")
            pad = " " * (name_w + range_w + 6)
            for cont in lines[1:]:
                print(f"{pad}{cont}")

    print()
    print(mcol.dim("  Everything else (tRCD, tRP, CL, CWL, tRFC, ...) is "
                   "never user-set -- it's derived automatically from "
                   "JEDEC tables once you pick speed grade + density."))


def _ask_goal() -> str | None:
    """The leading question, asked on initiation: what's the primary goal?
    Shows the deterministic (no-LLM) recommendation block for whichever
    goal is picked, then returns its key -- or None if skipped. Also offers
    a "what can I customize" info option that loops back to this same
    menu instead of picking a goal."""
    opts = mg.list_goals()
    show_idx = len(opts) + 1
    skip_idx = len(opts) + 2

    while True:
        print("\n" + _rule("before we start"))
        print("  What's the primary goal for this controller?\n")
        for i, (_, label) in enumerate(opts, 1):
            print(f"    {mcol.accent(str(i))}. {label}")
        print(f"    {mcol.accent(str(show_idx))}. What can I customize on this controller?")
        print(f"    {mcol.accent(str(skip_idx))}. Skip -- I'll just describe what I want")

        raw = input("\n  " + mcol.prompt("choice [1]: ")).strip() or "1"
        try:
            idx = int(raw) - 1
        except ValueError:
            idx = 0

        if idx == show_idx - 1:
            _print_customizable()
            continue
        if idx == skip_idx - 1:
            return None
        if not (0 <= idx < len(opts)):
            idx = 0
        key = opts[idx][0]

        print("\n" + _rule(f"recommended for: {mg.GOALS[key]['label']}"))
        print(" ", mg.describe_goal(key).replace("\n", "\n  "))
        return key


def _run_and_handle(request: str, goal: str | None, have_key: bool) -> bool:
    """Returns False if the user wants to end the session after this."""
    if not have_key:
        print("   English input needs ANTHROPIC_API_KEY. "
              "Try:  preset balanced")
        return True
    try:
        outcome = ma.run_english(request, interactive=True, goal=goal)
    except RuntimeError as e:
        print(mcol.err(f"   ERROR: {e}"))
        return True
    if outcome["status"] == "ok":
        return _handle_result(outcome["compile"], outcome["proposal"])
    elif outcome["status"] == "questions":
        print(mcol.warn("   NEEDS CLARIFICATION:"))
        for q in outcome["open_questions"]:
            print(f"     [{q.get('parameter','?')}] {q.get('question','')}")
    else:
        print(mcol.err("   could not converge:"), outcome.get("errors"))
    return True


def _repl() -> int:
    _print_banner()
    have_key = bool(os.environ.get("ANTHROPIC_API_KEY"))
    session_goal = None

    if have_key:
        session_goal = _ask_goal()
        if session_goal:
            extra = input(
                "\n  Anything specific to add, on top of the recommendations "
                "above? (Enter = just use them as-is): ").strip()
            if not _run_and_handle(
                    extra or "Use the recommended defaults for this goal, "
                             "with no further constraints.",
                    session_goal, have_key):
                return 0
    else:
        print(mcol.warn("  (ANTHROPIC_API_KEY not set -- English input "
                        "disabled, presets still work)\n"))

    while True:
        try:
            line = input("\n  " + mcol.prompt("spec> ")).strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return 0
        if not line:
            continue
        low = line.lower()
        if low in ("quit", "exit", "q"):
            return 0
        if low == "presets":
            print("   " + ", ".join(sorted(mc.PRESETS)))
            continue
        if low == "modifiable":
            _show_modifiable()
            continue
        if low == "goal":
            session_goal = _ask_goal()
            continue
        if low.startswith("preset "):
            name = line.split(None, 1)[1].strip()
            if name not in mc.PRESETS:
                print(mcol.err(f"   unknown preset: {name}"))
                continue
            res = mc.compile_spec(dict(mc.PRESETS[name]))
            if not _handle_result(res, None):
                return 0
            continue

        if not _run_and_handle(line, session_goal, have_key):
            return 0


def _handle_result(res: dict, proposal: dict | None) -> bool:
    """Returns False if the user wants to end the session after this."""
    if not res["ok"]:
        print(mcol.err("\n   REJECTED (fix the request and try again):"))
        for e in res["errors"]:
            print(mcol.err(f"     ERROR   {e}"))
        for w in res["warnings"]:
            print(mcol.warn(f"     WARNING {w}"))
        return True
    _print_result(res, proposal)
    default = _default_out(res["spec"])
    ans = input("\n  " + mcol.prompt(f"write spec? [{default}]  (Enter=yes / path / n): ")).strip()
    if ans.lower() in ("n", "no"):
        pass
    else:
        path = Path(ans) if ans else default
        _write(res["spec"], _report_payload(res, proposal), path)
    if input("  " + mcol.prompt("show full JSON? (y/N): ")).strip().lower() == "y":
        print(json.dumps(res["spec"], indent=2))

    cont = input("\n  " + mcol.prompt("Keep the session open to build another "
                                      "config? (Y/n): ")).strip().lower()
    return cont not in ("n", "no")


def _show_modifiable():
    rep = mc.modifiability_report()
    for lvl, items in rep["buckets"].items():
        print("\n" + mcol.header(f"  [{lvl.upper()}]") + f"  {rep['legend'][lvl]}")
        for it in items:
            name = f"{it['parameter']:22s}"
            print(f"    - {mcol.label(name)} {it['effect']}")


# ======================================================================
def main() -> int:
    ap = argparse.ArgumentParser(
        description="English -> DDR3 microarchitecture spec (standalone explorer)")
    ap.add_argument("request", nargs="?",
                    help="one-shot English request; omit for interactive mode")
    ap.add_argument("--preset", choices=sorted(mc.PRESETS))
    ap.add_argument("--from-choices", metavar="FILE")
    ap.add_argument("--out", metavar="PATH", help="where to write microarch_spec.json")
    ap.add_argument("--json", action="store_true",
                    help="print spec JSON to stdout and exit (implies --no-write)")
    ap.add_argument("--no-write", action="store_true",
                    help="don't write files, just show the summary")
    ap.add_argument("--modifiable", action="store_true",
                    help="print the blast-radius classification and exit")
    ap.add_argument("--goal", choices=sorted(mg.GOALS),
                    help="prime the English request with a use-case goal "
                         "(performance/power/cost/balanced) -- one-shot "
                         "equivalent of the interactive leading question")
    args = ap.parse_args()

    if args.modifiable:
        _show_modifiable()
        return 0

    if args.request or args.preset or args.from_choices:
        return _one_shot(args.request, args.preset, args.from_choices,
                         args.out, args.json, args.no_write or args.json,
                         args.goal)
    return _repl()


if __name__ == "__main__":
    sys.exit(main())
