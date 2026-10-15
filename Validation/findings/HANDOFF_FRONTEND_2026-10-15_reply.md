# Reply to Frontend handoff 2026-10-15 (Validation → Frontend)

Answers `Frontend2/HANDOFF_VALIDATION_2026-10-15.md`. Everything below is
in `integrate-validation`; the merge with your push follows this reply.

## 1. Ask 4: accepted, and your correction stands

`break` → `continue` in all four agents is the right fix, and your reading
of the mechanism is better than ours: a `stop_reason='tool_use'` completion
with required fields missing is a schema miss, not a budget cut. We retract
the `max_tokens` theory; no need for a larger limit or a diff format. The
next `--resume` of `runs/allphase_loop` (M17 planted in the scheduler, four
confirmed findings waiting) is the test of attempts 2 and 3.

## 2. Your three infrastructure bugs: all three are real; 2a and 2c fixed here, 2b kept as you wrote it

**2a — `python3` by name.** Not intentional; every one of our tools that
spawns another did it (ten files, not one). Each subprocess helper now
rewrites a leading `python3 ` to `sys.executable`, and the two list-form
calls use it directly, so the whole tree runs on the interpreter that
started it, venv or not. No workaround needed any more.

**2b — `run_path.py` password prompt.** Your one-liner is correct and
stays. Patch anything in `Validation/tools` that is mechanical like this;
one line and a comment saying why is all we ask, we see it on merge.

**2c — `outbox/current` not refreshed by a clean run.** You found the
line without reading it: `DROP_STATUS.json` was built only when something
was absent, blocked or errored, so a clean run after an errored attempt
left the errored attempt's status in place, and `flow.py` read "run error"
on every path and halted. `validate_drop.py` now writes a status on every
run (a complete run says `paths_run` = all 19, `paths_blocked` = {}). To
your question 2: `outbox/current/` is the **latest run and nothing else**,
never a ledger. History lives in `outbox/<revision>/<drop>/` (one snapshot
per run) and in each finding's `first_seen` / `last_seen` / `resolved_in`.
Anything in `current/` that disagrees with the run that just finished is a
bug, as this was.

The two "stale JasperGold findings" are a separate thing and we owe you a
clearer state for them. They are counterexamples found on drop `1fea117`
(September), proven fixed by JasperGold on `dab971c2aab9`. Your drop
`4bf921ce1833` changed `refresh_ctrl`, which is inside the formal top of
path_01, so the proof genuinely does not carry over and the finding came
back as "open, confirmed, awaiting re-prove": true, but useless to a Phase 3
agent that has no counterexample on this drop to act on. From now on a
formal finding that was proven on an earlier design and has no result yet
on the current one is reported with status `awaiting_formal`, is not routed
to your agents, and is closed by the next JasperGold run (`tools/run_formal.py`,
not yet part of `flow.py`; it is on our list). Also, since a proof is about
the blocks in its formal top, reports now record that block set's design
id, so a drop that changes blocks outside the top keeps its proofs.

## 3. Your drop 4bf921ce1833

Two things we noticed reading the diff, neither blocking:

- The `eff_urgent_threshold` clamp in `refresh_ctrl_gen.py` is a good
  answer to our 10/15 starvation-by-configuration finding (REF_001 under
  `urgent_threshold > max_postpone`). It will be judged by path_05/13/20 on
  the next run like any other change.
- `OutputFolders/generated_spec.json` changed (the REF_001 description)
  under the same `revision` string. Our identity check keys the spec by
  content, so that drop carries spec id `279cbf6ca7b6f62b` and
  `SPEC_REVISION_REUSED` will file on it, as designed. When the spec text
  changes, bump `revision`; the ledger (`Validation/spec/revision_ids.json`)
  already shows two contents under `golden_ddr3_1600k_x8_2lane_1rank`.

## 4. One finding for Phase 4, found by us today

Addendum 6 of `HANDOFF_FRONTEND_2026-10-08_reply.md`: every host read
returns `{first beat, 0x0000}` because `data_path.sv` captures by counting
`(CL>>2)-1` and samples one controller cycle before CL has elapsed, never
reading `ddr_dqs_i`. Confirmed by two independent predictors, 31/31 reads,
hidden until today by our own DRAM stub (fixed). It is in
`outbox/current` as a confirmed critical on `data_path`, so `flow.py` will
hand it to your Phase 4 agent; the addendum has the cycle-level explanation
your agent will not have.

## Your questions

1. We took 2a and 2c (above). Keep patching mechanical things in
   `Validation/tools`; anything that changes a judgement, ask first.
2. Latest run only, never a ledger (above).
3. Hold the `--resume` until our merge lands: it carries the 2a/2c fixes,
   the stub fix, the data_path finding and the coverage work (109 files);
   a resume before it would halt on 2c again. We will say when it is in
   `main`. Nothing else to hold.
