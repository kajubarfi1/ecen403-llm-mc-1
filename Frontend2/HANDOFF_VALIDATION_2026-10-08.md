# Handoff to Validation — 2026-10-08

From Frontend (Lehana) to Validation (Jacob). Follows up
`Validation/findings/HANDOFF_FRONTEND_2026-10-01_reply.md`. Your Q1–Q5 are
closed; what is new is listed first.

## 1. A drop to validate: `4b86c7cd3705`

`Frontend2/OutputFolders/` was regenerated from
`Spec/llmmc_microarchitecturespec_filled.json` (golden, rev
`golden_ddr3_1600k_x8_2lane_1rank`) and is now a **single-spec drop**:

- all 11 manifests carry that revision, `generated_spec.json` is the same
  spec, `TOPRTL` copies are byte-identical to the phase outputs;
- drop id `4b86c7cd3705` over all 11 blocks. It equals
  `rtl_drop.drop_id()` on this tree (checked on our side);
- Frontend gates, run on Olympus: Verilator lint PASS and Xcelium sim PASS
  for Phases 1–4 (config_regs 36/36, wb_port 4/4, refresh_ctrl 10/10,
  bank_tracker 31/31, and the Phase 3/4 suites), Phase 2 testbench-audit gate
  PASS, `ddr3_controller` combined lint PASS (0 errors, 10 warnings).

The earlier mixed-spec tree (`c85ae77d1d7c`) is superseded. These are
Frontend gates only; nothing here has been judged by Validation.

## 2. Your Q1: drop id — done

`Frontend2/scripts/drop.py` now hashes the 11 blocks of
`path_definitions.json` (fixed list of 11 as fallback). The orchestrator's
stale-drop check therefore compares like with like.

## 3. Your Q5: both spec decisions taken, as you recommended

- `data_path_mapping.ddr_dm_polarity = "active_high_mask"` in the golden spec
  and the compiler. No RTL change: `data_path` already drives `~sel`.
- `CTRL_STATUS` is now `ref_pending_cnt [8:5]` (4 bits), `self_refresh_active`
  bit 9, `reserved [31:10]`. Golden spec, compiler register template,
  `config_regs_gen` (4-bit `sts_ref_pending_cnt`), `refresh_ctrl_gen`
  (`ref_pending_cnt` output is 4 bits; was `postpone_cnt[2:0]`) and both
  testbench generators follow. Manifest widths are 4, so the integration map
  edge `refresh_ctrl.ref_pending_cnt -> config_regs.sts_ref_pending_cnt` is
  4 → 4. This should make your REF_001 (postpone budget exceeded) reachable.

Specs compiled before this change have the old `CTRL_STATUS` layout; the
generators now assume the new one.

## 4. Your Q4: `--yes` — done, guarded

`phase1_validation_agent.py` and `phase2_validation_agent.py` accept `--yes`.
Off by default. With it:

- patches apply with no prompt; each diff is logged to
  `VALIDATIONREPORT/auto_patches/phase{N}_{module}_attempt{K}.diff`;
- every patch is re-verified (lint + sim of that module); a patch that does
  not verify is **reverted** (generator restored, module regenerated);
- with `--findings`, only modules that have at least one `confirmed` check are
  patched. Modules with only `observed` checks are reported and left alone.
  Say if you would rather `observed` also patch.

Your `flow.py` detects `--yes` in `--help`, so it will now pass it: your
scripted `a` is replaced by these guardrails. Tested with a mocked model only
(bad patch → applied, logged, reverted, generator byte-identical); not yet
against a real model.

## 5. Still open on our side

- (Phase 3/4 fix agents: done, see section 6 below.)
- The spec-gap agent is not yet wired to `completeness_rules.json`
  (`options` / `consequence`), and the remaining intake gaps (taxonomy ids,
  tMRD/tMOD, `block_interfaces`, the CSR semantics) are not yet emitted by the
  compiler.
- `Frontend2/` testbench fix agents have no `--yes`.

## 6. Addendum (same day): Phase 3/4 fix agents, and a bug fix

- `Phase3/phase3_validation_agent.py` (cmd_queue, scheduler, cmd_gen) and
  `Phase4/phase4_validation_agent.py` (data_path) exist, with `--findings` and
  the guarded `--yes`. Your `flow.py` should find them via `--help`, so
  scheduler / cmd_gen / data_path findings no longer have to halt it.
- Their testbench is emitted by the same generator as the RTL, so the agents
  refuse a patch that (1) changes the testbench methods (`generate_tb`;
  `generate_testbench` + `_tb_test_registry`) or (2) changes the emitted
  `_tb.sv` after regenerating. Under `--yes` (2) reverts the patch; interactively
  a human may keep it, since a legitimate parameter fix can show up in
  testbench constants. This means a finding whose real fix is a testbench
  change is not auto-patchable; it needs a person.
- Tested with a mocked model only (RTL-only patch accepted; testbench edit
  rejected; testbench drift reverted); not yet run against a real failure.
- Bug fixed in the Phase 1/2 agents: they regenerated the module into the
  pipeline root while re-verification reads `PHASE{N}RTL/`, so a correct patch
  could never verify (and `--yes` would have reverted it). They now regenerate
  into `PHASE{N}RTL/`. If your flow ran those agents before this, a "did not
  verify" outcome may have been this bug.

## Questions

1. Is `4b86c7cd3705` the drop you will run next? If you need anything else in
   `OutputFolders/` first, say so.
2. `observed`-only modules under `--yes`: leave unpatched (current), or patch?
