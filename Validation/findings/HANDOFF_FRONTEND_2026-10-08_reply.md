# Reply to Frontend — 2026-10-08

From Validation (Jacob), answering `Frontend2/HANDOFF_VALIDATION_2026-10-08.md`
(sections 1–7 and the three questions). What changed on our side is marked
**done**; what we need from you is marked **ask**.

## Q1 — Yes: `4b86c7cd3705` ran. Verdict and what it taught us

The drop resolves 11/11 from `PHASE*RTL/`, every manifest carries the golden
revision, and the three `SPEC_MISMATCH` findings of `c85ae77d1d7c` are
**resolved**. Our id of the tree is `4b86c7cd3705`, equal to yours.

Result, all 19 runnable paths simulated on Olympus, judged under the spec the
drop ships (`generated_spec.json`, spec id `59b4edadb45f2bf8`):

| | |
|---|---|
| paths | 8 pass / 11 fail / 0 error |
| findings | 17 open (10 critical, 7 major), 3 resolved |
| failed modules | bank_tracker, cmd_queue, data_path, scheduler |
| config_regs, init_fsm, wb_port, refresh_ctrl, calibration, addr_decoder, cmd_gen | clean |

`Validation/findings/outbox/current/` holds `HANDOFF.json` (`drop_id`
`4b86c7cd3705`, now also `spec_id`), `retry_instructions.json` and
`findings_v2.json`; the archive is `outbox/golden_ddr3_1600k_x8_2lane_1rank/4b86c7cd3705/`.

The 17 are the same scheduler-family defects as before (PROTO_002 ×2310,
TIMING_004 ×2150, TIMING_005, TIMING_011, REF_002, TIMING_007 on bank_tracker,
SCHED_004 on cmd_queue), the data_path write-beat mismatch (now the only
`observed`, see §Q3 of 10-01), and five `MANIFEST_WRONG_SOURCE` findings on
bank_tracker (`cmd_pre_bank`, `cmd_rd_bank`, `cmd_wr_bank`) and data_path
(`cmd_aux`, `wr_data_valid`): the manifest names a `source` port that the
design does not drive directly, and our harness needs declared glue to make
the connection. These are **major / confirmed** now, not advisory; the
manifests are the integration contract, so they should name what the design
actually connects (or declare the glue). The `retry_instructions.json` names
the modules; Phase 3 and 4 fix agents are where they land.

**The `CTRL_STATUS` change is confirmed on the RTL**: `ref_pending_cnt` is
4 bits at [8:5], `self_refresh_active` at bit 9; `path_16_status_refresh`,
which failed on the first judging, passes. The first judging failed because
of two things on *our* side, both fixed and both now guarded:

1. **Validation held a stale copy of the spec under the same revision.**
   Our default spec (`Validation/spec/llmmc_microarchitecturespec_filled.json`)
   was the 09-24 golden file: `ref_pending_cnt [7:5]`, no DM polarity, no
   tMRD/tMOD. Same `revision` string, different content, so the revision
   check passed. `validate_drop.py` now computes a **spec id** (sha256 of the
   canonical JSON, `Validation/spec/spec_identity.py`), judges against the
   spec the drop ships when it carries a known revision with different
   content, and records the id beside every `spec_revision` it writes
   (`HANDOFF.json.spec_id`, `findings_v2.json.spec_id`, model provenance).
   **done.**
2. **One agent-generated model was built for the 3-bit field.** The
   config_regs predictor (accepted 10-01) masked `ref_pending & 0x7`, so a
   count of 8 read as 0 and 20 CTRL_STATUS reads mismatched. Its gate did
   not drive status levels across their full width; it does now (every RO
   field that mirrors a hardware level is driven with its top bit and all
   ones), the model was regenerated and accepted, and `validate_drop.py`
   now **re-grades every accepted model under the drop's spec** before
   judging and regenerates the ones the gate rejects. **done.**

**ask — one finding for the spec/compiler, filed as `SPEC_REVISION_REUSED`
(major):** `golden_ddr3_1600k_x8_2lane_1rank` has now named three different
specs (our 09-24 copy, the one the drop ships, and `Spec/…filled.json` after
addendum 2: ids `e7da1af6b67b7e06`, `59b4edadb45f2bf8`, `2fb3bbdd55dd72be`).
Make `revision` change whenever the content does — a content hash suffix from
the compiler is the simplest — or add a `spec_id` field the compiler fills.
Until then the finding stands on every run (`Validation/spec/revision_ids.json`
remembers which ids a revision has named).

Related: the drop's `generated_spec.json` is the golden spec **before**
addendum 2 (no `unmapped_read_data`, `speculative_activate`, SCHED_001–003,
TIMING_012–014). That is fine for this drop — we judge against what the RTL
was generated from — but the next drop should ship the spec it was actually
compiled from, which will then carry the intake fields.

Also noted by the backend: `backend/bundles/data_path/data_path_manifest.json`
says `phase: 3` while the block lives in `PHASE4RTL`. We do not read `phase`
(we resolve by directory), but it is wrong in the manifest.

## Q2 — `observed`-only modules under `--yes`: leave them unpatched

Keep the current behaviour. `confidence: observed` means one model and the
design disagree and no second model, repair or assertion has taken a side;
on this drop that is exactly the data_path write-beat finding (the primary
predicts two beats the design never produced) and cmd_queue `SCHED_004` /
scheduler `REF_002` (two occurrences each). A patch that makes the RTL
match an unconfirmed prediction can silence a real check or encode a model's
mistake into the design; a human should look at those. Everything
`confirmed` is where the automated loop earns its keep, and 14 of the 17
are confirmed.

If a module has only `observed` checks, the agent reporting and leaving it
is the right outcome; our `flow.py` treats "agent fixed nothing" as a halt
for a human, which is what we want there. We will raise the confidence on
our side where we can (second opinions, repairs), not lower the bar on yours.

## Q3 — `block_interfaces`: `path_definitions.json` + the manifests own it

Stop asking the spec for it. The 19 hop contracts are what the manifests'
`source` fields already declare and what our integration map is generated
from; a hand-written or derived copy in the spec would be a second source of
truth that can only drift. `INTERFACE_CONTRACTS` is **retired** in
`Validation/spec/completeness_rules.json` (`disposition: retired`, kept as a
record); `validate_spec_stage` now reports 0 advisory on the golden spec and
on the compiled presets. **done.** Your gap agent reads the same rules file,
so it will stop proposing it without a change on your side.

## Sections 2–7, acknowledged

- §2 drop id: agreed on both sides (`4b86c7cd3705`). Our stamp now carries the
  whole-drop id plus `blocks_used` for partial runs, so per-path reports and the
  outbox name the same drop.
- §3: DM polarity `active_high_mask` is now stated in the spec, so our
  bus-bridge gate grades the per-beat mask against it (inverted byte-enable
  slice) and the catalog note that said "polarity deliberately unchecked" is
  gone. **REF_001 reachability**: partly. Under our M06 mutant (an
  acknowledge increments `postpone_cnt`) the status level
  `sts_ref_pending_cnt` now climbs to 11 with `max_postpone = 8`, which the
  3-bit field could never show — so yes, the state is reachable and visible
  on CTRL_STATUS. Our `path_05` checker still did not raise REF_001, and the
  reason is ours: the `refresh_req` monitor samples `pending` on the rising
  edge of `ref_required` only (it stays high, so every request reads
  `pending = 1`). A change-qualified view of the refresh levels is the next
  thing we add; M06 is still killed (REF_002 and TIMING_011 grow), just not
  by the id the catalogue names. One design note for you: in the clean RTL
  `postpone_cnt` saturates at `cfg_max_postpone` (`if (postpone_cnt <
  cfg_max_postpone)`), so "count exceeded max" can never occur by
  construction; the design's own signal for REF_001 is `ref_starve_flag`
  (count **≥** max), which the taxonomy text should say.
- §4 `--yes`: our `flow.py` passes it when `--help` advertises it; the
  auto-patch log and revert-on-no-verify are what we hoped for. The first
  real-model run through it is the next thing we do together.
- §6 Phase 3/4 agents: found by `--help`, so scheduler / data_path findings
  route instead of halting. The testbench-freeze refusal is right; a finding
  whose fix is a testbench change will come back to a person, and our
  `retry_instructions.json` marks `requires_human_review` for those.
- §7 intake fields: our spec review on the golden spec is PASS, 0 blocking,
  0 advisory.

## Status after this drop (our side)

- Paths 8/11; findings 17 open, all on two independent models or a repair
  except the three `observed` above.
- Model agreement: every checker scope agrees with its second opinion on
  every trace; config_regs and data_path second opinions regenerated under
  the stated conventions (status-level width, baseline emission, DM polarity).
- Seeded faults: 23/23 killed, 0 masked, 0 survived on this drop (M07's
  reset value now comes from the spec instead of a literal; M06 see §3).
- Tests: 25 files under `Validation/tests/` plus `tests/test_flow.py`.

## Addendum (same day, evening): the first real-model run of the loop

`flow.py --spec Spec/…filled.json --skip-backend --max-rtl-rounds 2`, run
`runs/2026-10-08-full-loop/`. Spec review PASS, phases 1–4 and the top
generated in 90 s, validation round 1 on the fresh drop `3596e1ec698e`
(same RTL as `4b86c7cd3705` except the `// Generated:` timestamp in seven
headers, which is why the id differs; see ask 3), then your agents under
`--yes`:

- **Phase 2 agent: FIXED bank_tracker** (claude-sonnet-5, attempt 1, lint
  PASS, sim PASS on re-verify). Root cause it found: tWTR is device-wide but
  the generator loaded it per bank and gated only PRECHARGE with it, so a READ
  after a WRITE was allowed immediately. It added a global `ctr_wtr_g`
  loaded on any WRITE and gated `bank_rd_allowed` with it. The diff is in
  `VALIDATIONREPORT/auto_patches/phase2_bank_tracker_attempt1.diff` and is
  applied to `Frontend2/scripts/Phase2/bank_tracker_gen.py` in Jacob's
  working tree (not committed; your call).
- **Phase 2 agent also rewrote three manifest `source` fields to prose**
  ("glue: derived bank-tracking logic (…)") to answer the
  `MANIFEST_WRONG_SOURCE` findings. Our map generator refused that drop
  (`source` must be `<block>.<port>`), so round 2 could not judge it. Our
  finding text was at fault: it said "stop claiming a direct connection"
  without saying what is accepted. It now carries a `fix` with the two
  accepted forms (see §MANIFEST below).
- **Phase 3 agent: scheduler unresolved.** Attempt 1 produced a patch with a
  Python syntax error; attempt 2 a plausible "feedback-lag hold" patch
  (per-bank hold counters so the scheduler does not trust bank_tracker's
  permissions for the cycles after its own command) whose re-sim reported
  `0 passed, 0 failed` and was reverted. That shape means the patched RTL did
  not compile; the attempt-3 prompt only sees "sim FAIL". **ask 1:** feed the
  compile log's first error into the next attempt, otherwise the model
  cannot tell a wrong fix from a typo.
- **Attempt 3, and every agent on round 2, failed on the API account: "Your
  credit balance is too low"** (the key in Jacob's setup.env). The run halted
  for a human exactly as designed; it resumes with `--resume` once the
  account is funded.
- Five of 19 paths in round 1 did not simulate: Olympus reset the SSH
  connection with your gates and our four parallel paths open at once. Our
  runner now retries connects with backoff, and a path that did not run is
  carried as untested instead of keeping its previous report.

**ask 2 (MANIFEST):** a manifest `source` is `<block>.<port>` of a port that
exists in the drop, or absent when the design has no direct driver. For
`bank_tracker.cmd_{pre,rd,wr}_bank` the real fix is in cmd_gen: emit
`fb_pre_bank` / `fb_rd_bank` / `fb_wr_bank` beside the pulses, and keep the
manifest as it is. The alternative is `"source": "scheduler.cmd_bank"` with a
note that it is registered one cycle, which is what our harness does today.

**ask 3:** drop the `// Generated: <timestamp>` line from the RTL headers
(the manifest's `generated_utc` already records it). With it, two generations
of identical RTL get different drop ids, every regeneration looks like a new
drop, and the findings history keys on ids that never repeat.

**Orchestrator change from this run:** the flow now halts only when *no*
phase agent changed a generator; one phase fixing something is enough to
regenerate and validate again, with the other phases' findings still open in
the next package. A validate_drop that stops before judging (as the refused
manifest did) is now a halt with the generator's reason, never read as a
verdict.

## Addendum 2 (same day, night): drop `a7cd3cb93546` validated; your section 8 answered

Run on your new tree (all 19 runnable paths simulated on Olympus, judged under
the spec it ships, id `2fb3bbdd55dd72be`, the current golden spec):

| | `4b86c7cd3705` | `a7cd3cb93546` |
|---|---|---|
| paths | 8 pass / 11 fail | **19 pass / 0 fail** |
| findings open | 17 | **0** |
| formal, command path (JasperGold, 20 min) | 4 proven / 8 counterexamples | **12 proven at infinite bound / 0 counterexamples**; tREFI undetermined at bound 201 as before |
| findings resolved by this drop | | 15: PROTO_002, TIMING_004, TIMING_005, TIMING_007, TIMING_011, REF_002, SCHED_004, the data_path write-beat mismatch, all five MANIFEST_WRONG_SOURCE, and the three repair-proven composites |
| model agreement | every scope | every scope, every trace |

The scheduler hold and the device-wide tWTR do what you say: every
scheduler-family check that fired on the old drop is silent on this one, on
two independent checkers per scope. `path_18_full_write` (the data_path
write-beat finding) passes too, so that one was the stale scheduler state
seen through data_path, not a data_path defect.

**Your four "stale on your side": agreed, all four were ours.** cmd_gen has
carried `fb_pre_bank` / `fb_rd_bank` / `fb_wr_bank` and `cmd_out_aux` since
09/29; our `integration_overrides.json` glue predated them and superseded
correct manifests. Both glue entries are deleted (recorded under `retired`
with the reason). `source_expr` is read by the map generator now: a manifest
that declares it is the driver, no edge is derived from the first term, and
our old `expr_glue` for `wr_data_valid` is reported redundant. **done.** The
`MANIFEST_WRONG_SOURCE` finding also carries a `fix` now that states the
accepted forms, which is what sent your agent down the prose path this
afternoon.

**What is still open on this drop, and whose it is**

- `SCHED_004` on `path_07` / `path_20` (cmd_queue+scheduler, `observed`):
  **ours, not yours.** Two writes to one bank and column with different rows;
  you served the younger first and each WR landed on its own row. Our
  checker paired a CAS with the oldest request by (bank, col) and called
  both wrong-row. The rule now states the pairing (the request whose row the
  CAS carries, else the oldest to that bank/col; a younger request may go
  first) with a legal variant that rejects the old checker; both checkers
  were regenerated under it, and `path_07` and `path_20` pass. **Closed,
  ours.**
- `PROTO_001`, `TIMING_008` (scheduler, formal): **closed by formal.**
  JasperGold on this drop's command path proves every generated timing and
  protocol assertion except tREFI (undetermined at bound 201, the long
  interval; unchanged), including the two that had counterexamples on
  `5661e03`.
- One observation, not a taxonomy violation: on `path_07` a write enqueued at
  149 µs to bank 6 waited until 1.9 ms while four younger requests to the
  same bank were served (cols 0x298, 0x118 and the row-0x64b2 write). Under
  FR-FCFS that is legal, but there is no age bound in the policy today;
  SCHED_001 would only fire if it never issued. If you want an age cap we
  will add the check once the spec states one.
- Seeded faults: 22 of 23 substitutions still match your new RTL; M12
  (row-conflict precharge) is re-seeded to the new condition. The suite reruns
  on the merged tree.
- Your note on `*_nCK` loads into controller-cycle counters (every window
  about 4× long): agreed it is conservative, and it is why TIMING_* margins
  are untested rather than violated. Worth a spec field (`counter_clock`)
  so the checkers can judge the real margin; your call when.

**Fixed on our side from this drop:** repair-proven findings (R01–R03) were
re-filed on a drop that no longer has the defect, because the repair matrix
from an earlier drop counted as evidence. A repair now files only when this
drop still raises the check or still carries the edited source text.

**Housekeeping:** the `bank_tracker_gen.py` patch our run applied this
afternoon is superseded by your commit 6e2d7ad and is discarded on our side.

**Questions**

1. `a7cd3cb93546` is the drop in our outbox now (`HANDOFF.json`, status
   PASS, 0 open findings). The next loop run (`flow.py`) starts from it once
   the API account is funded, and with 19/19 paths passing it goes straight
   to the backend stage. Still to run on it on our side: the seeded-fault
   suite (after the merge) and the checker-known-good suite.
2. Would you add `counter_clock` (or state in the spec that bank_tracker
   counts in controller cycles with nCK loads) so the timing checks can be
   exact rather than conservative?
