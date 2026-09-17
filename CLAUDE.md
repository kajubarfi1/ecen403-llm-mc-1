# ECEN 404 — LLM MC #1 (DDR3 Memory Controller, Agentic RTL→GDSII Flow)

Continuation of ECEN 403 Final Presentation project "LLM MC #1." Team: Lehana Ramkumar
(Frontend), Dawson Carpenter (Backend), Jacob Zatopek (Validation). TA: Fahrettin Ay.
Sponsor: Stavros Kalafatis.

## Project goal
Fully automate RTL → GDSII for a DDR3 memory controller using an agentic AI pipeline:
user parameters (eventually plain English) → microarchitecture spec → RTL + testbenches
→ validation/lint/sim → backend synthesis → GDSII layout, self-validated at every stage.

## Repo layout
- `Frontend/` — Lehana's subsystem (RTL generation). See `Frontend/Agents/`.
- `backend/` — Dawson's subsystem (RTL → GDSII via OpenROAD). Early-stage (`intake_agent.py`).
- `Validation/` — Jacob's subsystem (reference model, testbench/vector generation, sim,
  failure triage). Separate from Frontend's own per-phase validation agents.
- `Spec/` — the golden microarchitecture contract every agent generates against:
  - `llmmc_microarchitecture.schema.json` — the JSON Schema (top-level sections:
    memory_geometry, clocking_model, timing_model, controller_architecture,
    initialization_sequence, calibration, host_interface, data_path_mapping,
    phy_interface, csr_register_map, latency_model, observability,
    failure_taxonomy, implementation_targets).
  - `llmmc_microarchitecturespec_filled.json` — the current filled instance:
    **DDR3-1600K (CL-CWL-CL 11-11-11), 2Gb density, x8, 2 byte lanes, 1 rank.**
    (Note: some older UI/deck text still says "DDR3-800" — that's stale labeling,
    not the actual spec.)
  - `customizable_parameters_guide.md` — Tier 1 (speed grade, density, ranks, byte
    lanes, ECC, scheduler policy, row policy) / Tier 2 (queue depth, lookahead,
    address mapping, burst length, host bus width, buffer depth, interface type,
    self-refresh mode) / Tier 3 (target frequency, area/power goals, pipeline
    latency) breakdown of what's user-customizable vs. JEDEC-fixed vs. derived.

## Frontend architecture (4-phase LangGraph pipeline)
Each phase: parallel generation agents → validation → lint gate → sim gate (Cadence
Xcelium on TAMU Olympus via SSH) → retry loop (max 4 attempts, failure feedback to
generation agents).

| Phase | Pipeline | Modules |
|---|---|---|
| 1 | `phase1_pipeline.py` | init_fsm, config_regs, wb_port |
| 2 | `phase2_pipeline.py` | addr_decoder, bank_tracker, refresh_ctrl, **calibration** |
| 3 | `phase3_pipeline.py` | cmd_queue, scheduler, cmd_gen |
| 4 | `phase4_pipeline.py` | data_path |

**Important:** calibration is a Phase 2 module (confirmed in code) — an older slide
deck diagram incorrectly grouped it with Phase 4/data_path. Code is ground truth.

Of the 11 module agents, only **4 call an LLM** (init_fsm, config_regs, bank_tracker,
refresh_ctrl — via Anthropic API, model `claude-sonnet-4-5` by default). The other 7
(wb_port, addr_decoder, cmd_queue, cmd_gen, scheduler, calibration, data_path) are
fully deterministic Python/template generators with no model calls. Don't assume all
"generation agents" are LLM-driven — check for an `anthropic` import before assuming.

Known inconsistencies across the 4 LLM agents (candidates for a shared base class):
- Temperature schedules differ (flat 0.3 on retry vs. decaying −0.2/attempt to a
  0.2 floor).
- `max_attempts` means "API-retry count" in two agents and "sanity-check retry count"
  in the other two — same field name, different semantics.
- `_sv_sanity_check` returns a single first-failure string in `config_regs_agent.py`
  but a full list of failures in `bank_tracker_agent.py`/`refresh_ctrl_agent.py`.
- `retry_instructions` key names diverge (`validation_failures` vs. `failed_checks`);
  currently patched by `phase1_validation_agent.py` supplying both keys rather than
  a single canonical schema.
- No prompt caching, no structured/tool-use output (regex code-fence extraction
  instead) — both are open optimization opportunities.

`Frontend/main.py` is currently a stub. `Frontend/userinterface.html` is the actual
working terminal-style UI referenced in the ECEN 403 deck (spec path + output folder
fields only — no per-parameter inputs yet).

## Current 404 goal in progress: microarchitecture spec synthesis agent
Today, "customizing" the design means hand-editing the one filled spec JSON — there is
no code anywhere that takes individual parameters (speed grade, density, ECC mode,
etc.) as input. The 404 goal is to replace golden-spec substitution with genuine
synthesis: an agent that takes user requirements (eventually English) and derives a
new, valid, JEDEC-correct spec — not just edits values in the existing one.

Roadmap (see conversation history for full detail; agreed direction as of this doc):
1. **Codify JEDEC/device timing tables** as a deterministic Python lookup module
   (formalizing the tables already written in prose in `customizable_parameters_guide.md`).
2. **Audit schema coverage** against real DDR3 controller configurators (Xilinx MIG,
   Synopsys uMCTL2, the open-source `UberDDR3` project this repo's
   `sim_diagnostic.py` is named after, LiteDRAM) to confirm/extend what's parametrized.
3. **Build a deterministic spec compiler**: `compile_spec(tier1_choices, overrides)` →
   complete schema-valid spec, generalized beyond the one golden config, with a
   validity matrix rejecting invalid Tier-1 combinations (like MIG's picker does).
4. **Build the intake/requirements agent** (the one LLM-appropriate piece): interprets
   English/structured user input into a resolved Tier-1/2/3 choice dict, asks
   clarifying questions on ambiguity, then hands off to the compiler — modeled on the
   working `examplercadder/agent.py` multi-agent pattern (Claude Agent SDK `query()` +
   `ClaudeAgentOptions`), generalized with real schema/consistency validation.
5. **Validate synthesized specs** before they reach Phase 1–4, extending
   `lint_agent.py`'s cross-check style to the spec level.
6. **Wire into a real CLI** (replacing the `main.py` stub): English in → RTL out,
   one command.
7. **Test against the guide's preset matrix** (low-cost embedded → server-grade) plus
   adversarial/ambiguous inputs.

## Working conventions
- User's email: lehanar57@tamu.edu.
- When asked about Claude Code features/behavior itself (not this project), use the
  `claude-code-guide` agent rather than answering from memory.
