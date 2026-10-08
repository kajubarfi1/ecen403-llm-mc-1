# Handoff to Validation — 2026-10-08

From Frontend (Lehana) to Validation (Jacob). Follows up
`Validation/findings/HANDOFF_FRONTEND_2026-10-01_reply.md`, and was extended
twice the same day after your 10/08 reply.

**Current drop: `a7cd3cb93546`. Read section 8 first**: it replies to your
10/08 results, lists what we fixed, and lists four findings we think are stale
on your side. Sections 1 to 7 are the history of how we got here; the drop ids
quoted in them (`c85ae77d1d7c`, `4b86c7cd3705`) are superseded.

## 1. The drop at the start of this thread: `4b86c7cd3705` (superseded by section 8)

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
- `block_interfaces` (INTERFACE_CONTRACTS) is the one intake gap left; see
  section 7. (The rest are closed, and the gap agent now reads
  `completeness_rules.json`; see section 7.)
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

## 7. Addendum 2 (same day): the intake gaps are emitted

The golden spec and `microarch_compiler.py` now state the fields your intake
gate asks for. Your `validate_spec_stage` on the golden spec and on the compiled
presets: PASS, 0 blocking, **1 advisory (INTERFACE_CONTRACTS) instead of 12**.

- `timing_model.tMRD = 5.0` and `tMOD = 15.0` ns (JESD79-3: 4 nCK;
  max(12 nCK, 15 ns)), computed from tCK in the compiler.
- `failure_taxonomy`: `SCHED_001..003` (dropped request, invented command,
  refresh never serviced) and `TIMING_012..014` (tREFI, tMRD, tMOD). The
  compiler appends these to the golden file's taxonomy and never replaces an id;
  the golden spec carries the same entries so the two agree.
- Your pinned conventions are now stated in the spec: `unmapped_read_data =
  zero`, `unmapped_write_behavior = ignored_with_error`,
  `access_violation_error = silent`, `read_byte_enable_semantics = ignored`,
  `status_read_sampling = previous_edge`, `speculative_activate = allowed`.
  **We adopted these as defaults because they are what you judge under; they
  are not a verified description of the RTL and are still an owner decision.**
  They sit in `INTAKE_CONVENTIONS` in the compiler. Because the spec now states
  them, your "pinned convention" and "the spec says" are the same thing; if the
  RTL disagrees with one, that becomes a real finding.
- The RTL is unchanged by this. The drop `4b86c7cd3705` is still current.
- The spec-gap agent (`microarch_gap_agent.py`) now puts the matching
  `completeness_rules.json` entries (options, standard, consequence) in its
  prompt and may not emit a value outside a rule's `options`.
- Still open: `block_interfaces` for the 19 hops. We think it should be
  generated from the manifests' `source` fields rather than hand-written;
  your call whether the spec or `path_definitions.json` owns it.

## 8. Reply to your 10/08 results: a new drop, `a7cd3cb93546`

Same golden spec; 11/11 manifests carry `golden_ddr3_1600k_x8_2lane_1rank`;
`generated_spec.json` is now the CURRENT golden spec (with the intake fields).
Drop id `a7cd3cb93546` equals `rtl_drop.drop_id()` on this tree. Frontend gates
on Olympus: lint + sim PASS in all four phases (Phase 1 unchanged and not
regenerated), `ddr3_controller` combined lint PASS. Your `4b86c7cd3705` results
are about the previous files, not these.

**Fixed on our side (real Frontend defects in your findings)**

1. **Scheduler acted on stale state** (PROTO_001, PROTO_002, TIMING_004, _005,
   _008, _011, and by the same mechanism the `observed` REF_002 / SCHED_004).
   A command takes 2 cycles to reach `bank_tracker` (scheduler register ->
   `cmd_gen` fb register -> tracker state), and the scheduler selected from
   permissions that did not yet reflect it. `scheduler.sv` now tracks the last
   two cycles' commands and holds: any command to a bank blocks a PRE/ACT to
   it; an ACT or PRE to a bank blocks a CAS to it; an ACT blocks every other
   ACT (tRRD/tFAW); a WR blocks RD (tWTR); a REF blocks everything; REF now
   also needs every `bank_act_allowed` (tRP/tRC/tRFC). This is what your repair
   hint described. Cost: after an ACT/PRE/REF the bank is idle for 2 cycles;
   CAS-to-CAS on an open row is not slowed.
2. **`bank_tracker` tWTR** (TIMING_007). `ctr_wtr` was per-bank and gated
   PRECHARGE; tWTR is the write-to-READ turnaround. It is now one device-wide
   counter, loaded at a WR with `tWTR + CWL + BL/2` (the window runs from the
   end of the write data), and gates `bank_rd_allowed` of every bank. It no
   longer gates PRE (tWR does).
3. **Our own testbench had the same misreading.** The Phase 2 `bank_tracker`
   testbench (Section I) asserted "tWTR gates PRE after a WR", so RTL and test
   agreed on the wrong thing. Rewritten to the JESD79-3 behavior (I0-I3).
4. **`wr_data_valid` manifest** (MANIFEST_WRONG_SOURCE). The top already wired
   `req_valid && req_we && enq_ready`; the manifest could only say
   `wb_port.req_valid`. `data_path_manifest.json` now carries `source_expr`
   with the real expression (and `source` stays as the first term), and
   `generate_top.py` builds the glue from `source_expr` instead of a table.
5. `data_path` manifest/result said `phase: 3`; now 4.
6. `SPEC_REVISION_REUSED`: the compiler now suffixes `revision` with a hash of
   the spec content (`compiled_..._<8 hex>`), so a compiled spec can no longer
   share a revision with different content. The hand-maintained golden file
   keeps its fixed revision string; `spec_id` remains the right identity there.

New scheduler tests (T39-T48) cover the hold. Run against the OLD scheduler RTL
they fail 6 checks (repeat ACT, REF right after ACT, RD right after WR), so
they are not vacuous. Scheduler is 48/48 on the new RTL.

**Findings we think are stale on your side (please re-check, not our defects)**

- `MANIFEST_WRONG_SOURCE` on `bank_tracker.cmd_{pre,rd,wr}_bank`:
  `integration_overrides.json` `glue[0]` says cmd_gen has no `fb_pre_bank`,
  `fb_rd_bank`, `fb_wr_bank` and asks us to add them. They exist in
  `cmd_gen.sv` and its manifest (added 09/29, commit d77dc12) and are
  registered with their strobes. That glue entry should be deleted.
- `MANIFEST_WRONG_SOURCE` on `data_path.cmd_aux`: `glue[1]` routes
  `scheduler.cmd_aux`; the top wires `cmd_gen.cmd_out_aux` (cmd_gen's registered
  aux, aligned with `fb_rd_valid`/`fb_wr_valid`), exactly as the manifest says.
  Same: delete the glue.
- `wr_data_valid`: the `expr_glue` is right and now matches `source_expr`; the
  finding should close once your map reads `source_expr`.

**Not fixed / not diagnosed**

- `data_path` write-beat mismatch (`observed`, path_18): not diagnosed. We
  don't know yet whether it is the design or the harness.
- These fixes are verified by unit tests and the mutation check only. Nothing
  here closes the loop between scheduler, cmd_gen and bank_tracker; your next
  run is the first real test of the hold.
- Observation, not changed: `bank_tracker` counters tick in controller cycles
  but are loaded with `*_nCK` values (DDR clocks), so every timing window is
  about 4x longer than the spec requires. Conservative, not a correctness bug,
  but it costs throughput and means the real tWTR/tRCD margins are untested.

## 9. Reply to your evening addenda (`a7cd3cb93546`: 19/19 paths, 0 open findings)

Thank you; both the result and the correction about SCHED_004 are noted. What
we did with your asks:

- **Ask 3 (timestamp in RTL headers): done.** The 8 generators that wrote
  `// Generated: <time>` now write a fixed line pointing at the manifest's
  `generated_utc`; all 11 RTL generators were run twice and are byte-identical
  run to run. This is in the generators only: the drop in `OutputFolders/` is
  still `a7cd3cb93546` and is not regenerated. The manifests still carry
  `generated_utc` and `git_commit`, so `drop_id` still changes on every
  regeneration; your `design_id` is the stable identity.
- **Ask 1 (feed the failure into the next attempt): done in all four phase
  agents.** A re-verify that fails now hands the next attempt the lint/sim
  result, the failing lines, and, when 0 tests ran (the patch did not compile),
  the first simulator errors from the log. A patch that is not valid Python
  also reports why.
- **Ask 2 (manifest `source` forms): done.** The agents' prompt states that
  `source` is `<block>.<port>` or omitted, with `source_expr` for expressions,
  and each agent now rejects and reverts any regenerated manifest whose
  `source` is not `<block>.<port>`, so prose like the one your run produced can
  no longer reach you.
- **Bug found while doing this, in what we pushed last time:** the Phase 3 and
  Phase 4 agents were missing `VALIDATION_SUBDIR` and the Phase 2 agent was
  missing `import re` after an edit. A Phase 3/4 agent would have stopped with
  a NameError before reading a report, and the Phase 2 agent on import.
  `py_compile` does not catch this; fixed, and all four now import and pass a
  static undefined-name check. If your 10/08 afternoon run hit a Phase 3
  failure before attempt 1, this may be why.
- **Your question 2 (`counter_clock`): decided, document it in the spec.**
  `timing_model.counter_clock` now states that the `bank_tracker` timing
  counters and the `refresh_ctrl` tREFI counter are loaded with `*_nCK` values
  but decrement once per controller clock (`window_scale` = 4, taken from
  `clock_ratio_ddr_to_controller`). It is in the golden spec and the compiler
  (identical for the default preset), and `generated_spec.json` in the drop was
  updated. Spec review: PASS, 0 blocking, 0 advisory. The RTL is unchanged, so
  the drop id stays `a7cd3cb93546`; only the spec content (and so `spec_id`)
  changed, under the same `revision` string, so expect `SPEC_REVISION_REUSED`
  for the golden spec to be filed again until we bump its revision (it is
  pinned in `backend/env.template`, so we have not changed it without telling
  Dawson).
- **Correction to what we said earlier ("conservative, not a correctness
  bug"):** that is true of the minimum-spacing timings (tRCD, tRP, ..., tWTR):
  the window is 4x longer than needed, so nothing is violated, but the real
  margin is untested. It is NOT true of **tREFI**, which is a maximum
  interval: `refresh_ctrl` counts 6240 controller cycles = 31.2 us, against the
  7.8 us the spec requires. The spec field records this
  (`effective_tREFI_ns: 31200.0`). Your tREFI check is "undetermined at bound
  201", so it cannot have seen it. We have documented it as asked, but it is a
  real refresh-interval deviation, and we would like to fix at least tREFI in
  `refresh_ctrl` (load the interval in controller cycles); say if you would
  rather we leave it so your checkers judge the design as it is.
- Your age-bound observation on `path_07` is noted; we agree it needs a stated
  policy before it can be a check. Not done.

## Questions

Answered by your 10/08 reply: `observed`-only modules stay unpatched under
`--yes`; `block_interfaces` is owned by `path_definitions.json` plus the
manifests and is retired from the spec rules. Open now:

1. Is `a7cd3cb93546` the drop you will run next? If you need anything else in
   `OutputFolders/` first, say so.
2. Please re-check the four `MANIFEST_WRONG_SOURCE` findings against the stale
   glue in `integration_overrides.json` (section 8). If you agree, delete
   `glue[0]` and `glue[1]`; if you disagree, tell us which port is missing.
3. The first real-model run of the fix agents (`--yes`) is still ahead. The
   scheduler and `bank_tracker` findings are a good first target once your next
   run shows what survives the new hold.
