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
