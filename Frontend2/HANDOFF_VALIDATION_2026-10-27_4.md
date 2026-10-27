# Handoff to Validation — 2026-10-27 (4)

From Frontend (Lehana) to Validation (Jacob), and relevant to Backend (Dawson)
via the usual findings loop. Not a reply to an open ask — addresses Dawson's
Fmax sweep (`backend/handoff/HANDOFF_FRONTEND_2026-10-27.md`) and the specific
finding `scheduler/TIMING/cmd_row` in
`backend/findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/latest`.

## 1. Scheduler is now pipelined to close 200MHz

The finding's worst path (`u_cmd_queue.entry_bank[34]` -> 36 logic levels ->
`u_scheduler.cmd_row[4]`, WNS -1.04ns) was the old single-cycle chain:
classify all 16 queue entries -> prioritize -> mux `q_*[sel_idx]` on the
just-computed index -> register `cmd_*`, all in one cycle. Took Dawson's
second suggested fix exactly: register the selection (`sel_idx` and friends
-> new `sel_*_r`), and do the `q_*[sel_idx_r]` mux + `cmd_*` registration one
cycle later. Splits the chain roughly in half. Costs one extra cycle of
scheduling latency, not throughput (`Frontend2/scripts/Phase3/scheduler_gen.py`).

**No `cmd_queue` change needed** — verified `cmd_queue_gen.py` is a flat array
with per-index valid bits, never shifted/compacted, invalidated only on
`deq_grant` (now delayed to match). `q_*[sel_idx_r]` is still correct data
one cycle after `sel_idx` was first computed.

## 2. The part we didn't take lightly: FB_LAG, 2 cycles -> 3

Adding the new pending stage meant a decision can now exist for one cycle
(`sel_valid_r`) before it's even `cmd_valid` — a cycle the existing
`cmd_*`/`d1_*` feedback-latency shadow (your own earlier note, and our
Defect 1 fix) didn't cover at all. Traced it through by hand (not just
pattern-matched):

- Extended the `inflight_any`/`inflight_state`/`inflight_act`/`inflight_ref`/
  `inflight_wr` masking with a `sel_*_r`-driven contribution.
- Found a second gap while doing that: `is_cas_ready`'s entry-level
  `recently_granted` guard (the original Defect 1 fix) only checked the
  fully-granted `deq_grant`/`deq_idx`, not the new pending stage -- so the
  *same* queue entry could have been re-picked for CAS one cycle after being
  picked, before its own dequeue retired. Confirmed this was a real gap (not
  hypothetical) by tracing the existing T33-34 "Regrant guard" test by hand:
  without the fix, it would fail at the cycle right after a grant; with it,
  passes. Added `sel_*_r`-aware entry-level guard alongside the existing one.
- Updated `scheduler_tb.sv`'s hand-counted hold-window tests (T39-47: Hold
  ACT/REF/RD) from 2-cycle to 3-cycle windows, and bumped four inter-test
  settle delays (`wc(2)`->`wc(3)`) that had zero margin left against the
  new depth.

## 3. `latency_model` numbers changed, both live and in the golden spec file

Scheduler's new cycle is real and unconditional (not tied to the user-facing
`pipeline_latency_cycles`), so `microarch_compiler.py`'s `_latency_model` now
adds a separate `SCHED_PIPE_NCK` (= `clock_ratio`) to
read_hit/read_empty/read_miss/write_hit: 25/36/47/32 -> 29/40/51/36 nCK for
the golden spec. Updated `Spec/llmmc_microarchitecturespec_filled.json`'s
`latency_model` section (formulas + numbers) to match -- **did not** bump
`revision`, matching how the ledger (`Validation/spec/revision_ids.json`)
already carries five content ids under `golden_ddr3_1600k_x8_2lane_1rank`
without a rename; flagging here per your own "bump revision when content
changes" note instead, your call if you want it handled differently this
time. Your copy at `Validation/spec/llmmc_microarchitecturespec_filled.json`
still has the old numbers -- didn't touch it, that's your file.

If your reference model reads `latency_model` numerically (the schema says
it feeds "validation reference model"), it'll need the same update.

## What we verified locally (same limitation as every RTL change this session)

- Regenerated `scheduler.sv` from the golden spec; read the full diff by
  hand, not just compiled it.
- `python3 Frontend2/scripts/Microarch/microarch_compiler.py --selftest` —
  still passes (checks derived blocks/CSR values, not `latency_model`
  numerically, so this wasn't the thing that caught the number change --
  we checked that by hand too).
- `tests/test_flow.py` (40 tests) — unaffected, still passes.
- **No local Xcelium or STA/OpenROAD.** Can't confirm the testbench actually
  passes or that this closes 200MHz. Your next `validate_drop.py` is the
  real functional check (especially T33-34 and T39-47, the ones most likely
  to catch a mistake in the FB_LAG extension); Dawson's next Fmax sweep on
  `scheduler` is the real timing check. If either of you wants to re-sweep
  or re-run against this specific drop, say so -- not asking you to, just
  flagging it's useful whenever convenient.
