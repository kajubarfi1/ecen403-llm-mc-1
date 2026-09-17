#!/usr/bin/env python3
"""
+======================================================================+
|          ENGLISH -> MICROARCHITECTURE GENERATION AGENT               |
|                                                                      |
|  The one LLM-appropriate piece of the spec-synthesis flow.           |
|                                                                      |
|  Pipeline:                                                           |
|     English (or structured) user request                            |
|        -> [LLM] resolve to a Tier-1/2/3 choice dict                  |
|           (structured tool output, temperature 0.2 -- interpretation |
|            only; the LLM never invents JEDEC timing)                 |
|        -> [deterministic] microarch_compiler.compile_spec()          |
|           * validity matrix  (reject un-buildable Tier-1 combos)     |
|           * JEDEC derive + assemble                                  |
|           * consistency checks                                       |
|        -> on reject: feed the compiler's reasons back to the LLM to  |
|           revise, or surface a clarifying question to the user       |
|        -> on accept: write microarch_spec.json + a report, print the |
|           exact Phase-1 command to run next                          |
|                                                                      |
|  Modes:                                                             |
|     python microarch_agent.py "I need a low-power DDR3 controller    |
|         for a sensor node" --out ./builds/sensor_v1                  |
|     python microarch_agent.py --preset balanced --out ./builds/bal   |
|     python microarch_agent.py --from-choices choices.json --out ...  |
|     python microarch_agent.py --list-modifiable                      |
|                                                                      |
|  --interactive  : ask the user follow-up questions on ambiguity      |
|  --no-llm       : forbid the LLM path (only --preset / --from-choices)|
+======================================================================+
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import textwrap
from pathlib import Path

import microarch_compiler as mc
import microarch_goals as mg
import microarch_colors as mcol


def _load_dotenv() -> None:
    """Minimal, dependency-free .env loader. Looks for Frontend/.env and the
    repo-root .env; only sets keys not already in the environment (a real
    shell export always wins). KEY=VALUE lines, '#' comments, optional quotes."""
    here = Path(__file__).resolve()
    for env_path in (here.parents[1] / ".env", here.parents[2] / ".env"):
        if not env_path.is_file():
            continue
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, _, val = line.partition("=")
            key = key.strip()
            val = val.strip().strip('"').strip("'")
            if key and key not in os.environ:
                os.environ[key] = val


_load_dotenv()

MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-4-5")
TEMPERATURE = 0.2
MAX_ROUNDS = 4          # LLM-only clarify/revise rounds (unattended risk -- kept tight)
MAX_CONFIRM_ROUNDS = 12  # recommendation<->feedback rounds (human-paced, generous)


# ======================================================================
# LLM tool schema -- the structured output the model must return.
# ======================================================================
_ENUM = mc.TIER1_CHOICES
PROPOSE_TOOL = {
    "name": "propose_configuration",
    "description": (
        "Resolve the user's request into a concrete DDR3 controller "
        "configuration. Pick Tier-1 values. Fill Tier-2/3 only when the "
        "user implied a preference or a non-default is clearly better; "
        "otherwise leave them out and the compiler defaults them. Never "
        "output JEDEC timing numbers -- the compiler derives those. If a "
        "Tier-1 choice cannot be reasonably inferred or defaulted, leave "
        "it out and put a question in open_questions with ready=false."
    ),
    "input_schema": {
        "type": "object",
        "properties": {
            # Tier-1
            "speed_grade": {"type": "string", "enum": _ENUM["speed_grade"]},
            "density": {"type": "string", "enum": _ENUM["density"]},
            "device_width": {"type": "string", "enum": _ENUM["device_width"]},
            "ranks": {"type": "integer", "enum": _ENUM["ranks"]},
            "byte_lanes": {"type": "integer", "enum": _ENUM["byte_lanes"]},
            "ecc_mode": {"type": "integer", "enum": _ENUM["ecc_mode"]},
            "scheduler_policy": {"type": "string", "enum": _ENUM["scheduler_policy"]},
            "row_policy": {"type": "string", "enum": _ENUM["row_policy"]},
            # Tier-2 (optional overrides)
            "command_queue_depth": {"type": "integer"},
            "lookahead_depth": {"type": "integer"},
            "address_mapping": {"type": "string",
                                "enum": ["row-bank-column", "bank-row-column"]},
            "burst_length": {"type": "integer", "enum": [4, 8]},
            "host_data_width": {"type": "integer", "enum": [32, 64, 128]},
            "read_buffer_depth": {"type": "integer"},
            "write_buffer_depth": {"type": "integer"},
            "interface_type": {"type": "string",
                               "enum": ["wishbone_classic", "wishbone_pipelined"]},
            "self_refresh_mode": {"type": "string",
                                  "enum": ["disabled", "manual", "auto"]},
            # Tier-3 (optional)
            "target_frequency_mhz": {"type": "integer"},
            "area_optimization_goal": {"type": "string",
                                       "enum": ["area", "balanced", "performance"]},
            "power_optimization_goal": {"type": "string",
                                        "enum": ["low_power", "balanced", "performance"]},
            "pipeline_latency_cycles": {"type": "integer"},
            # meta
            "assumptions": {
                "type": "array",
                "description": "Every value you chose that the user did not "
                               "explicitly state.",
                "items": {
                    "type": "object",
                    "properties": {
                        "parameter": {"type": "string"},
                        "value": {},
                        "reason": {"type": "string"},
                    },
                    "required": ["parameter", "value", "reason"],
                },
            },
            "open_questions": {
                "type": "array",
                "description": "Tier-1 choices you could not infer or safely "
                               "default. Empty if the config is complete.",
                "items": {
                    "type": "object",
                    "properties": {
                        "parameter": {"type": "string"},
                        "question": {"type": "string"},
                        "options": {"type": "array", "items": {"type": "string"}},
                    },
                    "required": ["parameter", "question"],
                },
            },
            "ready": {
                "type": "boolean",
                "description": "true only if every Tier-1 field is set and "
                               "open_questions is empty.",
            },
            "rationale": {"type": "string",
                          "description": "1-3 sentences: how you read the request."},
            "change_discussion": {
                "type": "string",
                "description": "ONLY when you are revising a previously shown "
                               "recommendation because the user gave feedback on "
                               "it (the conversation will contain a message "
                               "saying they reviewed a recommendation and want "
                               "changes): 2-4 sentences discussing the tradeoffs "
                               "of moving away from that previous recommendation "
                               "-- what you gained and gave up by shifting these "
                               "parameters, and whether anything from the "
                               "original goal/request is now less well served. "
                               "Omit entirely on a first proposal (nothing to "
                               "compare against yet).",
            },
        },
        "required": ["assumptions", "open_questions", "ready", "rationale"],
    },
}

SYSTEM_PROMPT = f"""\
You are the DDR3 Microarchitecture Requirements Agent. You turn a user's
plain-English (or partial/structured) request into a concrete, buildable
configuration for a DDR3 memory controller RTL-generation pipeline.

You choose from a FIXED, SMALL option space. You do NOT design timing --
a deterministic compiler derives every JEDEC timing value, geometry
number and CSR reset value from your choices.

TIER-1 (you must resolve all of these, or ask):
  speed_grade      {_ENUM['speed_grade']}
  density          {_ENUM['density']}
  device_width     {_ENUM['device_width']}   (x8 => 1KB page, x16 => 2KB page)
  ranks            {_ENUM['ranks']}   (NOTE: only 1 is supported today)
  byte_lanes       {_ENUM['byte_lanes']}   (prefer 1/2/4/8; +1 lane if ECC on)
  ecc_mode         {_ENUM['ecc_mode']}   (0 = off; >0 needs an extra byte lane)
  scheduler_policy {_ENUM['scheduler_policy']}
  row_policy       {_ENUM['row_policy']}

TIER-2 (leave unset unless the user implies a preference):
  command_queue_depth (power of 2, 4..32), lookahead_depth (0..16),
  address_mapping, burst_length (4/8), host_data_width (32/64/128),
  read_buffer_depth, write_buffer_depth, interface_type, self_refresh_mode

TIER-3 (rarely set): target_frequency_mhz, area_optimization_goal,
  power_optimization_goal, pipeline_latency_cycles

HOW TO MAP INTENT:
  "low power / battery / embedded / cheap / simple" -> low speed grade,
     1 rank, few lanes, ECC off, in_order, close_page, small queue.
  "server / datacenter / reliability / high bandwidth" -> high speed grade,
     more lanes, ECC on, fr_fcfs, open_page, deep queue + lookahead.
     (but if this forces ranks>1, ask the user -- it is unsupported.)
  "sequential / streaming / DMA" -> open_page, row-bank-column mapping.
  "random / scattered / pointer-chasing" -> close_page, fr_fcfs.
  Capacity in MB/GB -> pick density * byte_lanes to cover it.

RULES:
  - Record EVERY value you chose that the user did not state, in assumptions.
  - If a Tier-1 choice is genuinely underdetermined (e.g. no capacity hint
    at all, or the request implies an unsupported feature), leave it unset
    and add an open_questions entry; set ready=false.
  - Prefer defaulting Tier-2/3 (leave unset) over guessing.
  - Never put timing numbers (tRCD, CL, tCK, ...) anywhere.
  - If the request includes a "Primary stated goal:" line, its recommended
    defaults are the authoritative starting point -- use them for anything
    the user did not explicitly override in their own words, and record
    each one you applied in assumptions with reason "from stated goal: X".
    The user's explicit words always win over the goal's defaults.
  - If you are revising a recommendation the user already reviewed and gave
    feedback on, fill change_discussion (see its schema description).
Call propose_configuration exactly once.
"""


# ======================================================================
# LLM plumbing
# ======================================================================
def _anthropic_client():
    try:
        import anthropic
    except ImportError:
        raise RuntimeError("pip install anthropic  (needed for the English path)")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        raise RuntimeError("ANTHROPIC_API_KEY not set")
    return anthropic.Anthropic()


def _resolve(client, messages: list) -> dict:
    """One structured call. Returns the propose_configuration input dict."""
    resp = client.messages.create(
        model=MODEL,
        max_tokens=2048,
        temperature=TEMPERATURE,
        system=SYSTEM_PROMPT,
        tools=[PROPOSE_TOOL],
        tool_choice={"type": "tool", "name": "propose_configuration"},
        messages=messages,
    )
    for block in resp.content:
        if getattr(block, "type", None) == "tool_use" and block.name == "propose_configuration":
            return dict(block.input)
    raise RuntimeError("model did not call propose_configuration")


_CHOICE_KEYS = (list(mc.TIER1_CHOICES)
                + list(mc.TIER2_DEFAULTS)
                + ["target_frequency_mhz", "area_optimization_goal",
                   "power_optimization_goal", "pipeline_latency_cycles"])


def _extract_choices(proposal: dict) -> dict:
    return {k: proposal[k] for k in _CHOICE_KEYS if k in proposal and proposal[k] is not None}


# ======================================================================
# Orchestration
# ======================================================================
def run_english(request: str, interactive: bool = False,
                max_rounds: int = MAX_ROUNDS, goal: str | None = None,
                max_confirm_rounds: int = MAX_CONFIRM_ROUNDS) -> dict:
    """
    goal: optional key into microarch_goals.GOALS (e.g. "performance",
          "power", "cost", "balanced"). When given, its recommended-defaults
          block is prepended to the request as authoritative context (see
          SYSTEM_PROMPT) -- this is the "leading question" step: the CLI
          asks the user's primary goal first, shows them the recommendation,
          then folds it in here before the request is resolved.
    interactive: when True, a candidate configuration that resolves cleanly
          is NOT immediately final -- it's shown to the user as a
          recommendation (_ask_confirmation) who can either confirm it or
          describe changes, which get folded back in as another round. This
          repeats (up to max_confirm_rounds times) until the user confirms;
          only then is the spec actually produced. Also governs whether
          open_questions are asked via input() (existing behavior).

    Returns {status, ...}:
      status = "ok"        -> spec produced (result under 'compile')
      status = "questions" -> needs user input ('open_questions', partial 'choices')
      status = "failed"    -> could not converge ('errors', 'open_questions')
    """
    client = _anthropic_client()
    goal_block = f"{mg.goal_prompt_context(goal)}\n\n" if goal else ""
    messages = [{"role": "user", "content":
                 f"{goal_block}User request:\n{request}\n\n"
                 "Resolve it to a configuration."}]

    total_rounds = max_rounds + (max_confirm_rounds if interactive else 0)
    last = {}
    prev_resolved = None   # previous round's res["resolved_choices"], for the
                            # confirm loop's "what changed" diff -- None until
                            # a first recommendation has actually been shown
    for _ in range(total_rounds):
        proposal = _resolve(client, messages)
        last = proposal
        choices = _extract_choices(proposal)
        oq = proposal.get("open_questions") or []

        # Need the user before we can even try to compile?
        if oq and not proposal.get("ready", False):
            if not interactive:
                return {"status": "questions", "open_questions": oq,
                        "choices": choices, "assumptions": proposal.get("assumptions", []),
                        "rationale": proposal.get("rationale", "")}
            answers = _ask_user(oq)
            messages.append({"role": "assistant",
                             "content": [{"type": "text",
                                          "text": json.dumps(proposal)}]})
            messages.append({"role": "user", "content":
                             "User answered:\n" + json.dumps(answers, indent=2)
                             + "\nRe-resolve with these."})
            continue

        res = mc.compile_spec(choices)
        if res["ok"]:
            if not interactive:
                return {"status": "ok", "compile": res, "proposal": proposal}
            feedback = _ask_confirmation(proposal, res, prev_resolved)
            if feedback is None:
                return {"status": "ok", "compile": res, "proposal": proposal}
            prev_resolved = res["resolved_choices"]
            messages.append({"role": "assistant",
                             "content": [{"type": "text", "text": json.dumps(proposal)}]})
            messages.append({"role": "user", "content":
                             "Reviewed the recommendation above and wants changes "
                             f"before it's finalized:\n{feedback}\n"
                             "Re-resolve incorporating this feedback. Weigh it "
                             "alongside everything already established in this "
                             "conversation (stated goal, prior answers) rather than "
                             "replacing it -- e.g. 'best performance while still "
                             "optimizing power' means push Tier-1/2 choices toward "
                             "performance without abandoning the power-oriented ones "
                             "the feedback doesn't mention. Only drop an earlier "
                             "choice if the feedback explicitly contradicts it."})
            continue

        # Compiler rejected -- give it the reasons and let it revise or ask.
        reasons = "\n".join(f"  - {e}" for e in res["errors"])
        messages.append({"role": "assistant",
                         "content": [{"type": "text", "text": json.dumps(proposal)}]})
        messages.append({"role": "user", "content":
                         f"The deterministic compiler REJECTED that config:\n{reasons}\n"
                         "Revise the choices to satisfy every reason. If a fix needs "
                         "a user decision (e.g. dropping a feature they asked for), "
                         "put it in open_questions and set ready=false instead."})

    # Exhausted rounds.
    res = mc.compile_spec(_extract_choices(last)) if last else {"errors": ["no proposal"]}
    return {"status": "failed", "errors": res.get("errors", []),
            "open_questions": last.get("open_questions", []),
            "choices": _extract_choices(last)}


def _ask_user(open_questions: list) -> dict:
    answers = {}
    print(mcol.warn("\n  I need a few decisions before I can build this:\n"))
    for q in open_questions:
        param = q.get("parameter", "?")
        opts = q.get("options") or []
        prompt = f"  {q.get('question', param)}"
        if opts:
            prompt += mcol.dim(f"\n    options: {', '.join(map(str, opts))}")
        prompt += "\n  " + mcol.prompt(f"{param} = ")
        answers[param] = input(prompt).strip()
    return answers


_CONFIRM_WORDS = {"", "yes", "y", "confirm", "confirmed", "generate", "go",
                   "ok", "okay", "good", "correct", "that's right",
                   "looks good", "sounds good", "do it", "proceed"}


def _ask_confirmation(proposal: dict, res: dict,
                       prev_resolved: dict | None = None) -> str | None:
    """Show a candidate configuration as a recommendation (not yet final)
    and ask the user to confirm it or describe changes. Returns None on
    confirmation, else the user's feedback text to re-resolve with.

    prev_resolved: the previous round's res["resolved_choices"] (None on
    the first recommendation) -- diffed against this round's to show what
    actually moved, with the model's own tradeoff discussion of the move."""
    print("\n" + mcol.header("-" * 68))
    print(mcol.header("  RECOMMENDATION -- review before this is generated"))
    print(mcol.header("-" * 68))
    if proposal.get("rationale"):
        print(f"\n  {proposal['rationale']}")

    changes = None
    if prev_resolved is not None:
        cur = res["resolved_choices"]
        changes = [(k, prev_resolved.get(k), cur[k]) for k in cur
                   if prev_resolved.get(k) != cur[k]]

    _print_report(res, proposal, None, changes=changes,
                  change_discussion=proposal.get("change_discussion"))
    ans = input("\n  " + mcol.prompt("Generate the spec from this, or describe "
                                     "what to change (Enter = confirm): ")).strip()
    return None if ans.lower() in _CONFIRM_WORDS else ans


# ======================================================================
# Reporting
# ======================================================================
def _print_report(res: dict, proposal: dict | None, out_dir: Path | None,
                   changes: list[tuple[str, object, object]] | None = None,
                   change_discussion: str | None = None):
    r = res["resolved_choices"]
    print("\n" + mcol.header("=" * 68))
    print(mcol.header("  RESOLVED CONFIGURATION"))
    print(mcol.header("=" * 68))
    for k in mc.TIER1_CHOICES:
        print(f"    {mcol.label(f'{k:22s}')} {r[k]}")
    print("    " + "-" * 40)
    for k in mc.TIER2_DEFAULTS:
        print(f"    {mcol.label(f'{k:22s}')} {r[k]}")

    if proposal and proposal.get("assumptions"):
        print(mcol.dim("\n  ASSUMPTIONS (values you did not state):"))
        for a in proposal["assumptions"]:
            print(mcol.dim(f"    - {a['parameter']} = {a['value']}  ({a['reason']})"))

    if changes:
        print(mcol.accent("\n  CHANGES FROM THE PREVIOUS RECOMMENDATION:"))
        for param, old, new in changes:
            print(f"    - {mcol.label(param)}: {old} -> {new}")
        if change_discussion:
            print(mcol.accent("\n  TRADEOFFS OF THIS CHANGE:"))
            wrapped = textwrap.fill(change_discussion.strip(), width=64,
                                    initial_indent="    ", subsequent_indent="    ")
            print(wrapped)

    if res["warnings"]:
        print(mcol.warn("\n  WARNINGS:"))
        for w in res["warnings"]:
            print(mcol.warn(f"    ! {w}"))

    npass = sum(c["pass"] for c in res["consistency_checks"])
    tot = len(res["consistency_checks"])
    paint = mcol.ok if npass == tot else mcol.err
    print(paint(f"\n  CONSISTENCY: {npass}/{tot} checks pass"))
    for c in res["consistency_checks"]:
        if not c["pass"]:
            print(mcol.err(f"    x {c['name']}  ({c['detail']})"))

    tm = res["spec"]["timing_model"]
    dc = tm["$derived_cycles"]
    print("\n  DERIVED (JEDEC):")
    print(f"    speed_bin   {tm['speed_bin']}")
    print(f"    tCK         {tm['tCK_ns']} ns   CL {tm['CL_cycles']}  CWL {tm['CWL_cycles']}")
    print(f"    tRCD/tRP/tRAS/tRFC (nCK)  "
          f"{dc['tRCD_nCK']}/{dc['tRP_nCK']}/{dc['tRAS_nCK']}/{dc['tRFC_nCK']}")
    ge = res["spec"]["memory_geometry"]
    print(f"    geometry    {ge['row_bits']} row / {ge['column_bits']} col / "
          f"{ge['bank_bits']} bank   channel {ge['$derived']['channel_data_width_bits']}-bit")
    print(f"    capacity    {ge['$derived']['channel_capacity_MB']} MB   "
          f"peak BW {ge['$derived']['peak_channel_bandwidth_MBps']} MB/s")

    if out_dir:
        print(mcol.ok(f"\n  WROTE  {out_dir / 'microarch_spec.json'}"))
        print(mcol.ok(f"         {out_dir / 'microarch_report.json'}"))
        print(mcol.header("\n  NEXT:") + "  run Phase 1 against it, e.g.")
        print(f"         python Frontend/Agents/phase1_pipeline.py")
        print(f"         (spec path: {out_dir / 'microarch_spec.json'})")


def _write_outputs(out_dir: Path, res: dict, proposal: dict | None):
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "microarch_spec.json").write_text(json.dumps(res["spec"], indent=2))
    report = {
        "resolved_choices": res["resolved_choices"],
        "assumptions": (proposal or {}).get("assumptions", []),
        "rationale": (proposal or {}).get("rationale", ""),
        "warnings": res["warnings"],
        "consistency_checks": res["consistency_checks"],
        "modifiability": mc.modifiability_report(),
    }
    (out_dir / "microarch_report.json").write_text(json.dumps(report, indent=2))


# ======================================================================
# CLI
# ======================================================================
def main() -> int:
    ap = argparse.ArgumentParser(
        description="English -> DDR3 microarchitecture spec")
    ap.add_argument("request", nargs="?",
                    help="natural-language description of the controller you want")
    ap.add_argument("--preset", choices=sorted(mc.PRESETS),
                    help="skip the LLM; compile a named preset")
    ap.add_argument("--from-choices", metavar="FILE",
                    help="skip the LLM; compile a JSON choices file")
    ap.add_argument("--out", metavar="DIR",
                    help="output directory for microarch_spec.json + report")
    ap.add_argument("--interactive", action="store_true",
                    help="ask follow-up questions on ambiguity")
    ap.add_argument("--no-llm", action="store_true",
                    help="forbid the English/LLM path")
    ap.add_argument("--list-modifiable", action="store_true",
                    help="print the blast-radius classification and exit")
    args = ap.parse_args()

    if args.list_modifiable:
        print(json.dumps(mc.modifiability_report(), indent=2))
        return 0

    out_dir = Path(args.out) if args.out else None

    # --- deterministic paths -------------------------------------------
    if args.preset or args.from_choices:
        choices = (dict(mc.PRESETS[args.preset]) if args.preset
                   else json.loads(Path(args.from_choices).read_text()))
        res = mc.compile_spec(choices)
        if not res["ok"]:
            print(mcol.err("REJECTED:"))
            for e in res["errors"]:
                print(mcol.err(f"  ERROR   {e}"))
            for w in res["warnings"]:
                print(mcol.warn(f"  WARNING {w}"))
            return 2
        if out_dir:
            _write_outputs(out_dir, res, None)
        _print_report(res, None, out_dir)
        return 0

    # --- English path ------------------------------------------------
    if not args.request:
        ap.error("give a request string, or use --preset / --from-choices")
    if args.no_llm:
        ap.error("--no-llm set but an English request was given")

    try:
        outcome = run_english(args.request, interactive=args.interactive)
    except RuntimeError as e:
        print(mcol.err(f"ERROR: {e}"))
        return 1

    if outcome["status"] == "ok":
        res = outcome["compile"]
        if out_dir:
            _write_outputs(out_dir, res, outcome["proposal"])
        _print_report(res, outcome["proposal"], out_dir)
        return 0

    if outcome["status"] == "questions":
        print("\n  NEEDS CLARIFICATION -- re-run with --interactive, or "
              "answer these and pass a fuller request:\n")
        for q in outcome["open_questions"]:
            print(f"    [{q.get('parameter','?')}] {q.get('question','')}")
            if q.get("options"):
                print(f"        options: {', '.join(map(str, q['options']))}")
        if outcome.get("choices"):
            print(f"\n  partial config so far: {json.dumps(outcome['choices'])}")
        return 3

    print("\n  COULD NOT CONVERGE after retries.")
    for e in outcome.get("errors", []):
        print(f"    ERROR {e}")
    for q in outcome.get("open_questions", []):
        print(f"    Q  {q.get('question','')}")
    return 3


if __name__ == "__main__":
    sys.exit(main())
