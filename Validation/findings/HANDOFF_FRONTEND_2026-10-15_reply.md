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

## Addendum (2026-10-21): we ran the resume; Phase 3 is passed off, Phase 4 is not yet

We resumed `runs/allphase_loop` ourselves on 10-20 (everything was in
`main`). Four rounds, unattended.

**Phase 3: closed.** Round 3 validation: FAIL on the planted scheduler
fault (REF_001, SCHED_003, both twin-confirmed) and, new since the stub
fix, the data_path read-capture defect. Your Phase 3 agent, attempt 1:
root cause "both refresh-selection branches gated by `if (1'b0)`", which
is exactly the planted line, regenerated, and round 4 has every scheduler
finding resolved. Your `break`→`continue` fix is confirmed in the same
run (below). That is the Phase 3 loop end to end: validation finds it,
routes it, your agent names it, the fix lands, validation confirms.

**Phase 4: your agent reached it, the retry fix worked, the patch did
not.** Attempts 1 and 2 were the schema miss again (`missing required
field(s): explanation`, `stop_reason='tool_use'`), and this time the loop
carried on to attempt 3, which applied a patch: it rewrote the read-word
assembly (`rd_word_assembled` as a per-beat slice write) on the theory
that the beats were swapped. Re-validation: identical wrong value
(`0x7f670000` for `0x9dac7f67`), 31/31 reads, round cap reached, halted.
The patch is in `Frontend2/scripts/Phase4/data_path_gen.py` in Jacob's
working tree and will not be kept. The real cause is in addendum 6 of
the 10-08 reply: capture starts one controller cycle before the DRAM
drives beat 0 (`rd_lat_ctr <= (cfg_CL_nCK >> 2) - 1`), and `ddr_dqs_i`
is never read; the assembly was never wrong.

Two asks from that:

**ask 6: give the agent the block's inputs.** It could not have seen
the timing from expected vs actual and a FIFO anchor. Every mismatch
check now carries a `context` field: the transactions on the block's
other interfaces just before the first wrong value, then the wrong value
(`retry_instructions.json`, `failed_checks[].context`). For this finding
it reads: `dp_cmd.read`, then `ddr_rd_beat data=0x7f67`, then
`ddr_rd_beat data=0x9dac` in the same cycle as the response
`data=0x7f670000`. Beat 0 in the high half, nothing in the low half,
beat 1 never seen: the capture is a cycle early. Please put `context`
into the line your prompt builds from each check (beside `anchors` and
`fix`); it is a list of short strings.

**ask 7: the schema miss is not rare.** Two of three Phase 4 attempts
and one of one Phase 3 attempt on 10-15 lost a required field. The retry
now rescues it, at the cost of an attempt each time. If the tool schema
has a field the model keeps dropping, consider making it optional with a
default, or asking for it in a second, smaller call.

Also in that run: Olympus dropped off the network overnight during
round 4's formal step, which turned a 20-minute step into seven hours of
reconnect timeouts before the round could finish. The verdict was
already in (simulation had completed), and formal now waits for a round
that passes simulation, so a failing loop round no longer pays for
proofs it will not keep.

## Addendum 2 (2026-10-22): your push, and two more Phase 4 runs

Thank you for ask 6: all four agents now carry `context`. We ran the
loop twice on your pushed generators (`runs/phase4_loop`,
`runs/phase4_loop_2`), fresh from the golden spec each time.

**What still fails, and why it is now yours.** The data_path read is
unchanged by your hand edit to `data_path_gen.py` (slot-per-beat plus a
delayed push) and by both patches your agent applied: the response is
`0x7f670000` for `0x9dac7f67` every time, 31 of 31 reads. All three
changes rework the word assembly; none moves the capture window, which
starts one controller cycle before the DRAM drives beat 0 and never
reads `ddr_dqs_i` (addendum 6 of the 10-08 reply, restored after your
"blah" commit accidentally deleted addenda 5 and 6 from that file). In
the second run your agent's three attempts all lost required tool-call
fields (`explanation`; then all four; then
`corrected_generator_source`) and the module went unresolved with no
patch at all. **ask 8:** apply the capture fix by hand from addendum 6
(count ceil(CL / CLK_RATIO) from the registered command, or capture on
`ddr_dqs_i`), and treat the schema miss as a blocker: three of three
attempts is not a rare event.

**One thing on our side.** The context events were in the prompt and
the agent still reasoned about word order, so each mismatch now also
carries `value_provenance`: which input landed in which slice of the
wrong value, and which should have. For this finding it reads

```
data: observed [31:16]=ddr_rd_beat#1.data (t-10000), [15:0]=0
data: expected [31:16]=ddr_rd_beat#2.data (t-5000), [15:0]=ddr_rd_beat#1.data (t-10000)
```

beat 1 where beat 2 belongs, nothing where beat 1 belongs: the capture
is one beat early. It is a list of strings under
`failed_checks[].context.value_provenance`; please add it to the prompt
line beside the events.

**Our false positive, fixed.** The first run also raised REF_001 on the
scheduler from a new starvation assertion we had bound to refresh_ctrl;
on paths whose harness has no scheduler nothing can acknowledge a
refresh, so it fired by construction. Your Phase 3 agent said "not this
module" and was right. REF_001 is now a bounded obligation at the
scheduler (an urgent refresh acknowledged within tRAS + tRP + tRFC in
the enforced windows plus a cycle per bank, under the spec's
urgent-preempt policy), silent on the clean drop and firing on the
seeded scheduler-ignores-refresh fault; the second run had only the
data_path finding.
