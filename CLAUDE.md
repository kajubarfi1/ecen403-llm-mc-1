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

## Microarchitecture spec synthesis agent — status
**This section used to say "no code anywhere does this" — that's now stale.** Items
1, 3, and 4 of the roadmap below are built, working, and wired into the Frontend2
pipeline (moved from `Frontend/Agents/` to `Frontend2/scripts/Microarch/` on
2026-09-29):

- `Microarch/microarch_jedec.py` — deterministic JEDEC/device timing lookup tables
  (roadmap item 1).
- `Microarch/microarch_compiler.py` — deterministic `compile_spec(choices) -> spec`
  (roadmap item 3): full Tier-1/2/3 validity matrix, preset library, blast-radius
  classification, 27 executable consistency checks. `--selftest` reproduces the golden
  spec exactly. No LLM.
- `Microarch/microarch_agent.py` + `microarch_goals.py` — the English-intake agent
  (roadmap item 4): direct `anthropic` API calls (not the Claude Agent SDK / `query()`
  pattern the roadmap originally described — no `examplercadder/agent.py` exists in
  this repo to model on, so this used a simpler single-tool-call-per-round loop
  instead), reject/revise against the compiler, clarify-question and goal-priming
  flows.
- `Microarch/microarch_cli.py` — standalone interactive REPL/one-shot CLI over the
  above three.
- `Microarch/dummy_validation_agent.py` — **stub**, not roadmap item 5. Sits between
  spec synthesis and Phase 1; today only confirms the spec has every top-level section
  the schema requires. Placeholder for Jacob's Validation subsystem to take over.
- `Frontend2/scripts/full_pipeline.py` now prompts at startup: use an existing spec
  JSON, or synthesize one now (`resolve_spec_path()` → `run_microarch_synthesis()` →
  `dummy_validation_agent.validate_spec()`) before proceeding into Phase 1–4 same as
  before.

Still open (roadmap items 2, 6, 7 — and 5 for real):
2. **Audit schema coverage** against real DDR3 controller configurators (Xilinx MIG,
   Synopsys uMCTL2, the open-source `UberDDR3` project this repo's
   `sim_diagnostic.py` is named after, LiteDRAM) to confirm/extend what's parametrized.
5. **Replace `dummy_validation_agent.py` with Jacob's real Validation subsystem hookup**
   — the stub's `validate_spec(spec, compile_result=None) -> {status, findings, validator}`
   contract is the thing to preserve when this happens.
6. `Frontend2` has no top-level "one command, English in → GDSII out" entry point yet —
   `full_pipeline.py` is closer than `Frontend/main.py` (still a stub) ever got, but it's
   still a sequence of interactive prompts, not a single non-interactive CLI invocation.
7. **Test against the guide's preset matrix** (low-cost embedded → server-grade) plus
   adversarial/ambiguous English inputs.

## Top-level flow (repo root)
`flow.py` is the one-command entry point that chains the subsystems through
their own CLIs: Frontend spec synthesis → Validation spec review → Frontend RTL
generation (phases 1–4 + top) → Validation of the drop → (Frontend
regeneration on findings) → backend RTL→GDSII → (backend→frontend change
requests) → final netlist validation. Runs live in `runs/<run_id>/` with
`RUN_STATE.json`; a halted run resumes with `--resume`. Loops are capped
(`--max-rtl-rounds`, `--max-backend-rounds`). Validation findings go back to the
Frontend through its own phase validation agents
(`Frontend2/scripts/Phase{N}/phase{N}_validation_agent.py`, fed our package
rendered as that phase's error report by
`Validation/findings/to_frontend_error_report.py`); spec-review findings go
back to the microarch agent through the request text. Backend findings
(`backend/findings/outbox`, our envelope) are routed back the same way, and
the final stage runs the backend's per-block netlists through the paths
(`run_path.py --netlist`, sky130 models via `tools/install_sky130_models.py`).
Edges whose counterpart does not exist yet halt and say so: phases without a
validation agent (3, 4) and a top-level-only netlist. `--phases 1` runs a Phase-1-only loop (partial validation, no top-level, no backend); `--revalidate` re-judges a drop changed under a resumed run; `--dry-run` prints the plan. Tests: `tests/test_flow.py`.
The Validation⇄Frontend contract is `Validation/findings/HANDOFF_CONTRACT.md`.

## Working conventions
- User's email: lehanar57@tamu.edu.
- When asked about Claude Code features/behavior itself (not this project), use the
  `claude-code-guide` agent rather than answering from memory.
