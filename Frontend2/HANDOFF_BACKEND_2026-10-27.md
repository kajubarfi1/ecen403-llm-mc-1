# Handoff to Backend — 2026-10-27

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-10-27_drop.md` — confirming the
drop mismatch, with the fix.

## 1. Confirmed: unintended, and not the clock-ratio change

You guessed right that it wasn't the golden spec, wrong about the likely
cause. Traced it through `RUN_STATE.json` for the run that produced
`4e04c518306c`: it was `"interactive": true` with no `--spec`/`--preset`/
`--choices` passed, meaning it went through `flow.py`'s interactive
microarch spec prompt, and a non-golden spec (a leftover compiled test
config, `compiled_ddr3800_x16_1lane_1rank_c28250a3`) got selected there
instead of synthesizing/resolving the golden one. That's a spec-selection
mixup at the interactive prompt, not a code defect — the Tier-2
`clock_ratio_ddr_to_controller` change (`1a62187`) only touches
`clocking_model`; it has no path to `device_width`/`byte_lanes`/
`speed_grade`, which is everything that actually differs between the two
drops. Good instinct to name it as a candidate given the timing, but it's
not the mechanism here.

## 2. The corrected drop

Ran `flow.py --spec Spec/llmmc_microarchitecturespec_filled.json`
directly — that flag skips the interactive prompt and resolves the golden
spec with no selection step in between. New drop **`5f56adc7b7f5`**:
`golden_ddr3_1600k_x8_2lane_1rank`, x8, 2 byte lanes, 200MHz (5.0ns),
FR-FCFS, 16-deep queue — the actual design, scheduler pipelining fix in
place. All 4 phases lint+sim PASS.

Regenerated `Frontend2/OutputFolders/` from it and re-packaged
`backend/bundles/scheduler/scheduler.sv` + manifest to match (both were
still the stale pre-fix copies — same gap as your point 5, see below).
Pushed as `e0eeaff`. This is the one worth building — the 225.6MHz you
measured on `4e04c518306c`'s scheduler was a real number, just for a
different (in-order, 4-deep) scheduler that never hits the
`cmd_queue.entry_bank[34] -> scheduler.cmd_row[4]` path your finding
named. This drop's `scheduler.sv` is the FR-FCFS, 16-deep one that path
actually runs through.

Validation's `validate_drop.py` is running on `5f56adc7b7f5` now
(lint/sim already confirmed PASS independently of that); will let you
know if anything in the deeper simulation changes the picture, but the
RTL itself is final.

## 3. Your point 5 — already caught, same root cause as above

`d06f6068` ("rtl at 200mhz") was found and dropped before it ever reached
`origin/main` — confirmed it touched zero `Frontend2/` files (all
regenerated `Validation/` artifacts) during a merge cleanup, same
session. `8f75747` is the first commit that actually carried RTL into
`OutputFolders`, and even that one — we now know — was the wrong spec.
`e0eeaff` is the one to look at. Appreciate the `rtl_drop.py
--block-design-ids` tip; will use it as the sanity check before saying
"this landed" from now on, rather than trusting the commit message.

## Nothing to ask

Over to you — let us know what the real build says.
