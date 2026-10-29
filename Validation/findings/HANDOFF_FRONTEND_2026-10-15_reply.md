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

## Addendum 3 (2026-10-22, evening): your "Phase 4 validation changes" push

Three things in it, two of them good news.

**Three specs that are not the golden one.** Your `--phases 1,2` runs on
the compiled DDR3-800, -1066 and -1600 x8 one-lane specs: spec review
PASS on each, 8 of 8 runnable paths PASS on each, packages under their
own revision directories. That is the first evidence the validation
holds on specs it was not built against, a different byte-lane count
included. Keep doing that; the next step up is a two-rank or ECC preset
through the same loop.

**tRFC for 4Gb, 260 → 300 ns.** The spec review's JEDEC table flagged
it (J-TIM-009) and your note explains the vendor-bin origin exactly. A
generator-side error caught by the review stage is the stage doing its
job.

**`--formal` in flow.py.** Fine as an opt-in, and we kept it. One
overlap to know about: since 10-20 `validate_drop.py` step 4b already
re-proves every path with formal history when a round passes simulation
and no report applies to the design, so on a passing round your stage
would have run JasperGold a second time on the same design. It now
reuses the report validate_drop produced when one applies (same drop,
design, or blocks) and only runs its own job otherwise.

**One request.** Your commit carried `Validation/txn/generated`,
`Validation/sva/generated`, `Validation/formal/chain_formal.sv` and the
predictor provenance files from your last run, generated for the
one-lane DDR3-1600 spec against manifests under your run directory. They
are regenerated on every run, so nothing broke at runtime, but the
committed tree then described a drop that is not in the repo and our
unit tests tripped on manifests that do not exist here (made
self-healing now). Before committing, please leave those paths out
(`git checkout -- Validation/txn/generated Validation/sva/generated
Validation/structural/integration_map.json Validation/formal` is
enough); the outbox packages under your spec revisions are welcome.

**data_path:** unchanged in this push, so ask 8 stands.

## Addendum 4 (2026-10-22, night): your "phase4changes" push, run once

Your hand fix landed and the loop ran on it (`runs/phase4_loop_3`,
drop `36dcdfaf136e`). Two results.

**The capture moved one cycle too far.** With
`rd_lat_ctr <= (cfg_CL_nCK + CLK_RATIO - 1) / CLK_RATIO` the read now
returns `0x00009dac` for `0x9dac7f67`: beat 2 in the low half, nothing in
the high half. Before it was `0x7f670000`, beat 1 in the high half,
nothing in the low half. One cycle early became one cycle late, because
the RD_IDLE → RD_WAIT transition already spends the cycle in which the
registered command is seen. The count is one less:

```
rd_lat_ctr <= (cfg_CL_nCK + CLK_RATIO - 1) / CLK_RATIO - 1'b1;
```

which at CL = 11, ratio 4 waits 2 and captures beats 0 and 1 on the two
cycles the DRAM drives them. Capturing on `ddr_dqs_i` would not have
this off-by-one at all. The package said it in one line
(`value_provenance`: "observed [31:16]=0, [15:0]=ddr_rd_beat#2";
"expected [31:16]=ddr_rd_beat#2, [15:0]=ddr_rd_beat#1").

**Your agent still cannot act on it.** With the schema reordered, two of
three attempts still dropped `explanation` (`stop_reason='tool_use'`),
and the third died on a network read timeout during an outage on our
side; the three attempts took four hours end to end and applied nothing.
So the schema miss is not the field order. Two of three attempts, on a
one-line fix with the evidence spelled out, is the blocker for Phase 4
now; the validation side has nothing left to add to the package.
Suggestions, in the order we would try them: drop `explanation` and
`shift_left_recommendations` from the required set (they are prose the
loop never reads), or ask for `root_cause` + `confidence` in one call and
the corrected source in a second.

## Addendum 5 (2026-10-27): your self-audit of the contract

Good catch, and the right kind: a gap found by reading the contract
against the code before it bit. The CRLF normalisation in
`compute_drop_id` is exactly the backend's 10-08 incident waiting to
repeat on the first Windows checkout, and the way you verified it, the
same id from both implementations on the same tree, is the check the
contract asks for. Nothing to add; we will stop printing "matches
Validation's" as a claim and let the two ids being equal be the proof.

Still open from addendum 4: the `- 1` on the read latency count, and the
tool-call schema miss. The run after those is the one that should pass.

## Addendum 6 (2026-10-27): it passed

`runs/phase4_loop_4`, fresh from the golden spec on your "Phase 4: fix
read-latency off-by-one" push: spec review PASS, all four phases
generated, **19 of 19 paths PASS in round 1**, no findings, drop
`5c30eb9e7184`. Both read paths that had failed every round since 10-15
pass; read-after-write returns the word that was written. Validation
then re-proved the design (a passing round triggers it): command path 13
proven at infinite bound, REF_001 bounded, tREFI bounded under the
assumed configuration with no undetermined property left; coverage
unchanged at 28 covered and 11 unreachable by spec. The flow completed
with the backend skipped.

That is the first all-phase pass on a defect that was not planted: found
by validation on 10-15, explained in addendum 6, fixed by you from that
explanation. Your relaxed agent schema went untested this round because
there was nothing left for the agent to fix, which is the right way for
it to go untested.

**One ask, so the repo carries the passing drop.** The checked-in
`Frontend2/OutputFolders` still holds the old `data_path.sv`, so the
repo's own drop (`efece348d04e`) still fails the two read paths and the
outbox for it still says so. The passing drop exists only under
`runs/phase4_loop_4/drop`. Please regenerate `OutputFolders` from the
current generators and commit it (the drop id should come out as
`5c30eb9e7184` if the LLM-generated blocks reproduce; a different id is
fine, we judge content). Then the next thing to run is a full flow with
the backend on, where Dawson's scheduler timing finding becomes the
first backend-to-frontend change request the loop carries.

## Addendum 7 (2026-10-27, evening): a non-golden spec through all four phases, and a testbench finding

`runs/preset_lowcost`: `flow.py --preset low-cost-embedded`, the first
spec other than the golden one through Phases 1–4 (DDR3-800 at tCK 2.5
ns, ONE byte lane, CL 6, a 4-deep command queue; revision
`compiled_ddr3800_x8_1lane_1rank_08cc0fbc`). Spec review PASS, Phases
1–3 PASS, then **your Phase 4 pipeline failed its own sim gate** on
data_path:

```
[FAIL] 15: C3: rd_rsp_data=0x12121234     (expected 0xCAFE1234)
```

We then ran our validation on that drop as it stood (the data_path RTL
is there; only your gate refused it): **19 of 19 paths PASS**, 0
findings, read-after-write returns the written word on four 8-bit beats,
second opinions agree, code coverage 84.8 %. Your generator is right and
your testbench is wrong. `data_path_tb.sv` line 88:

```
assign ddr_dq_i = (dut.rd_burst_ctr == 2'd0) ? ... : ...;
```

The testbench drives the read beats by peeking at the DUT's internal
burst counter with a two-way choice, so with WORD_BEATS = 4 beats 1, 2
and 3 all get the same byte: `0x12121234` is beat 0 = 0x34 and 0x12 three
times. **ask 9:** generate the read-beat stimulus from the testbench's
own count, one value per beat for WORD_BEATS beats, and not from
`dut.rd_burst_ctr`; a testbench that reads the design's internal state
to decide what to drive cannot catch a wrong count in that state. The
same white-box pattern is worth a scan in the other phases' testbench
generators.

On our side from this run: `flow.py` now hands a phase's own gate
failure to that phase's agent (it reads your error report natively) and
regenerates, instead of halting for a person; and the vplan is
regenerated from the judged spec on every validation (it was still the
golden one's text on this spec). Three specs have now been through
Phases 1–2 and one through all four; a two-rank or ECC preset is the
next one worth sending.

## Addendum 8 (2026-10-27, night): a Phase 1 finding — tMOD in the init sequence

Regenerating the verification plan from the spec (it had been the
golden plan's text since 10-08) surfaced six taxonomy items nothing
measured, among them tMRD and tMOD, which are in the spec's
`timing_model` since the October revisions but had no assertion because
they were not when the init rules were written. Both are now asserted on
the init FSM's own command stream (`init_fsm_sva.sv`: TIMING_013,
TIMING_014), and TIMING_014 fires once on the golden drop:

```
MRS (MR2)  t
MRS (MR3)  t + 1 cycle
MRS (MR1)  t + 2
MRS (MR0)  t + 3
ZQCL       t + 4          <- 1 controller cycle = 4 nCK after MR0; tMOD = 12 nCK (15 ns)
```

`init_fsm.sv` goes `S_MR0 -> S_ZQCL` on the next cycle with no wait
(lines 75 and 95). JESD79-3 requires tMOD, max(12 nCK, 15 ns), between
an MRS and any non-MRS command; the MRS-to-MRS spacing (tMRD, 4 nCK)
is met because one controller cycle is 4 nCK. It will arrive in the
next package as `init_fsm/TIMING_014`, owner init_fsm, Phase 1: a
tMOD wait state (3 controller cycles at this clock, derived from
`timing_model.tMOD` and the clock period, not a literal) between the
last MRS and ZQCL. It is the second defect validation has found on the
real design, and the first in an LLM-generated block; the first was
the data_path read capture.

## Addendum 9 (2026-10-28): two more real defects, found by driving the port the way the spec describes it

We went after code coverage today and the stimulus that closed it found
two defects in the checked-in drop (efece348d04e), one in Phase 1 and
one in Phase 4. Both are in the current package
(`Validation/findings/outbox/current/`, 9 findings, FAIL on data_path,
init_fsm, wb_port) and will route to your Phase 1 and Phase 4 agents on
the next flow run as `wb_port/CONSERVE/HOST_BEAT_TO_REQUEST`,
`wb_port/HANDSHAKE/wb`, `data_path/CONSERVE/READ_CMD_TO_RESPONSE`,
`data_path/CONSERVE/WRITE_CMD_TO_BEATS` and
`data_path/CONSERVE/WRITE_REQUEST_TO_DATA`. Code coverage on the drop is
85.4 % (was 77.3 %), over the 85 % target for the first time.

### What changed on our side

Every sequence we had ever driven on the host port used classic single
cycles: present one beat, wait for its ack, present the next. The
spec's `host_interface` says `wishbone_pipelined`, linear bursts up to
8 beats, a 16-deep read buffer, and your `wb_port.sv` header says
"Wishbone B4 pipelined slave", so the burst tracker, `cti`/`bte` and
the tag FIFO had never run. Two generators now drive what the spec
declares: `wb_burst` (linear bursts, `cti` INCREMENTING then END,
reads and writes, and a pile of pipelined reads deeper than the read
buffer) on path_02, and `saturate` (240 back-to-back mixed beats, the
next presented the cycle after the previous is accepted, acks trailing)
on path_07. The refresh paths (05, 20) and path_18 pick up the
pipelined driver too.

Our `wb_rsp` monitor was wrong under this traffic: it qualified a read
response on `wb_ack_o && !wb_we_i` and read `wb_adr_i` at ack time,
which on a pipelined bus are a later beat's. It now qualifies on your
`rsp_valid` input and attaches the accepted read addresses in order.
That was a monitor bug, not a design one, and it is fixed; nothing
below depends on it.

### Finding 1 — wb_port loses accepted beats when the queue fills (Phase 1, critical)

`wb_stall_o` is combinational from `req_ready` (the queue's
`enq_ready`), and the accepted beat is registered into `req_*` and
presented to the queue one cycle later, with no holding register and
no check that the queue still has room. When the request already in
flight fills the queue on that same edge (count 15 → 16), the beat just
accepted is presented to a full queue and dropped: `enq_valid &&
!enq_ready` in `cmd_queue.sv` is ignored. For a write the host has
already received `wr_ack_r`, so the write is acknowledged and lost; for
a read, nothing ever comes back and the host waits forever.

Evidence (all from this drop, Olympus, today):

| path | beats accepted | requests taken by the queue | lost | host saw |
|---|---|---|---|---|
| path_07 (saturate) | 243 | 218 | 25 (18 writes, 7 reads) | 12 beats never acknowledged |
| path_05 / path_20 (refresh_stress, now pipelined) | 600 | 350 | 250 | — |
| path_18 (write_read) | 24 | 20 | 4 | 4 beats never acknowledged |

Every lost beat sits at a cycle where the queue reached 16 on the edge
that accepted it (`cq_enq` / `cq_deq` counted from the trace). Under
sustained traffic the port loses about one beat per freed slot, which
is why path_05 and path_20 lose 250 of 600. This violates vplan
VP_FLOW_001 ("no accepted request may be lost while back-pressure is
asserted") and `controller_architecture.command_queue_depth`. Fix on
the generator (`wb_port_gen.py`): either stall when the queue is one
short of full while a request is in flight (`!req_ready || (req_valid
&& <queue_count == DEPTH-1>)` needs the count, which the port does not
see), or the cleaner one: hold `req_valid` until `req_ready` (a
one-entry skid) and assert `wb_stall_o` while the holding register is
occupied. The `req` monitor's qualifier is `req_valid && req_ready`, so
a request the queue did not take is, correctly, not a request.

While reading the port for this we noticed `wb_ack_o = wr_ack_r |
rd_ack`: a write acknowledge (one cycle after the beat) and a read
response arriving in that same cycle merge into one ack, and the host
loses one completion. We did not see it happen in today's runs; it is
now a port property, HOST_001, that formal will prove or refute on the
next formal run and that fires in simulation if it ever occurs. Not a
finding yet; flagged so the same fix can take it into account (hold
one of the two).

### Finding 2 — data_path ignores a RD or WR command while its FSM is busy (Phase 4, critical)

`rd_state` and `wr_state` are one-deep. A RD command (`cmd_rd_valid`)
is only latched in `RD_IDLE`; a WR command only in `WR_IDLE`. With
CL = 11 nCK the read FSM is busy for 4 controller cycles per read
(wait 2, capture 2); the write FSM likewise. The spec allows CAS to CAS
at tCCD = 4 nCK = one controller cycle, and your scheduler and cmd_gen
issue at that rate, so the second and third of three back-to-back
reads are simply never captured: no response, no entry in the response
FIFO, the port's tag FIFO goes out of step (`p_tag`, your WB-009,
fires on every later response) and the host never gets an ack. For
writes, a WR command issued while `wr_state != WR_IDLE` pops nothing
from the write buffer and drives nothing on DQ, so the DRAM receives a
WRITE with no data, and the un-popped words accumulate until `wr_full`
refuses new ones (`p_wr_no_overflow`, your DP-001, fires).

| path | RD cmds | read responses | lost | WR cmds | DQ words driven | WR without data | write words refused at full buffer |
|---|---|---|---|---|---|---|---|
| path_02 (wb_burst) | 46 | 33 | 13 | 31 | 12 | 19 | 6 |
| path_07 (saturate) | 63 | 55 | 8 | 155 | 112 | 43 | 40 |

The 13 lost reads on path_02 are exactly the RD commands issued within
4 cycles of the previous one. Who fixes it is your call: pipeline the
capture (a shift of pending `(aux, CL countdown)` entries, one per RD,
is the usual shape), or make the data path tell cmd_gen it is busy and
have the scheduler hold CAS until it is not. The second needs a port
the manifests do not have; the first stays inside data_path. The
finding is filed on data_path because that is where the command is
dropped.

Note this is why path_02 had passed before today: a read the data path
drops predicts nothing downstream (our port predictor answers a read
only when the data path does), so every stage checker matched what
appeared. We added a `(conservation)` stage from catalog rules (every
transaction a block is handed must have produced the one it owes by
the end of the run, attributed to the block that must deliver) and a
`(host handshake)` stage from the driver's own count of beats never
acknowledged. Those are what carry these two findings; the exact
stages corroborate them on path_07 and path_18 (`req` missing).

### Still open from before

The data_path read-capture defect (addendum 2) and the init_fsm tMOD
defect (addendum 8) are still in the checked-in drop; both are fixed
in your generators, so a regenerated `OutputFolders` clears them. Ask 9
(your testbench's white-box read beats) stands.

**Update, same day, on your pushed drop 99f72da45a32** (data_path read
fix, pipelined scheduler): path_03 passes, so the read-capture defect
(addendum 2) is confirmed closed on the checked-in drop. The two
findings above stand unchanged (the port's lost beats, the data path's
dropped commands), tMOD (addendum 8) is still in `init_fsm.sv`, and
code coverage on this drop is 86.8 %. The scheduler's two old formal
findings (PROTO_001, TIMING_008, proven closed on the previous design)
went back to `awaiting_formal` because the scheduler changed. The
re-proof on the pipelined scheduler (JasperGold, 20 min, everything
free) has run: TIMING_008 is proven again and that finding is closed.
PROTO_001 and PROTO_002 came back undetermined at depth 49 where the
old scheduler proved them in 14 min; the pipelined design has more
state, so they need a longer run and PROTO_001 stays `awaiting_formal`
until then (nothing says it is broken; nothing yet says it holds).

The same run settled HOST_001, the ack collision flagged under Finding 1
above: **counterexample at 24 cycles, no abstraction, no assumptions.**
A write beat accepted in one cycle and a read response arriving in the
next give one `wb_ack_o` pulse for two completions
(`assign wb_ack_o = wr_ack_r | rd_ack`, wb_port.sv:158). It is now the
third wb_port finding in the package, `wb_port/HOST_001`, critical,
confirmed, routed to the Phase 1 agent with the other two; the fix is
the same holding stage. One honest note on method: the run under the
assumed refresh configuration showed no collision to 8245 cycles, but
that configuration never answers a read, so its bound is vacuous, and a
counterexample found with everything free is a witness in the real
design. We tightened our own sign-off rule on that today (a bounded
proof counts only if its trigger was witnessed) so it cannot happen
silently again.

**Simulation witness (10-29).** It is no longer only a formal trace:
`path_23_host_ack_collision` (new, `ack_collision.py`) reads one open
row and lands a write beat d+1 cycles later for every d in the spec's
latency window. On your drop the collision lands at d = 40: the write
is acknowledged in the same cycle the read data returns, `a_HOST_001`
fires once, every request and response is conserved, and the host
counts one beat never acknowledged -- the pulse the two shared. The
path runs on every drop from now on, so the fix has its test.

**Loop run 10-29 (`runs/oct29_loop`), halted inside your Phase 3.** We
ran the flow on the current spec to carry the three modules' findings
to your agents. It never reached our validation: Phase 3 regenerated
the scheduler from your current `scheduler_gen.py` (the sel_idx_r
change) and your own simulation gate failed it, T36 "RefBlock: REF once
banks idle" and T37 "RefBlock: ref_ack", both seeing `cmd=4` (WR) where
the testbench expects REF after the forced precharge. The flow handed
the gate report to your Phase 3 agent (that route works); it diagnosed,
at low confidence, that the testbench's `ref_ok` expectation does not
account for the in-flight PRE that the pipelined scheduler now tracks,
proposed deriving the expected offset from the spec's derived cycles
rather than a literal, and exited without a fix, so the run halted.
Two things worth knowing: the drop you pushed carries a scheduler from
the same generator commit, so either the gate was not re-run before the
push or the testbench is sensitive to something that differs between
runs; and the regenerated `scheduler.sv` is byte-identical to the one you
pushed (so are cmd_queue, cmd_gen, wb_port and refresh_ctrl; only
init_fsm differs, by the tMOD wait your agent added in our tree). So
T36/T37 fail on the scheduler that is in the repo, and the question is
whether that scheduler is wrong or the testbench is. Our answer is the
testbench: on your pushed drop every scheduler and refresh check we
hold the pipelined scheduler to passes (REF_001, REF_002, SCHED_001-003
on paths 04, 05, 06, 19, 20; REF_002 and TIMING_008 proven by formal;
REF_001 bounded-proven), and the only failures on those paths are the
port's lost beats. A forced PRE followed by REF on the next eligible
cycle is what we see; the testbench expects REF on a fixed cycle the
pipeline no longer meets. Suggest the testbench derive that offset from
the spec's derived cycles, as your agent proposed, and that the Phase 3
gate be re-run before a drop is pushed. Our validation of the
regenerated Phase 1-3 drop itself: 8 of 8 runnable paths pass, and
TIMING_014 (tMOD) is resolved on it, which confirms your agent's init
fix regenerates cleanly.

## Addendum 10 (2026-10-29, afternoon): your three fixes, judged

Replies to `Frontend2/HANDOFF_VALIDATION_2026-10-29.md` (data_path) and
`_2.md` (wb_port). Short version: tMOD is closed, the port fix works, the
data_path fix stops the drops but breaks every read's data, and the drop
as pushed does not compile, so only eight paths ran on it.

### 1. The drop as pushed (5994bb667dba) does not compile

`scheduler.sv` from 5ec2dc7 (fix (b) reverted) uses `sel_bank_eff_r` at
lines 178 and 179 and declares it as a `wire` at line 372. Xcelium
rejects a net used before its declaration (`*E,UNDIDN ... undeclared
identifier`, IEEE 1800 §6.10: implicit nets are only created in port
connections and continuous-assignment LHS). The comment at line 133 says
it is "declared further down"; the generator's line 418 is where. Move
the declaration above its first use (or keep (b)'s registered copy). The
drop was regenerated with `--no-lint`, which is why your gate did not
see it; Yosys may accept the forward reference, Xcelium does not.

Every path that instantiates the scheduler, 12 of 20, has no verdict on
this drop; the package carries their findings as untested, not resolved,
and holds one new critical finding, `scheduler/COMPILE_ERROR`, anchored
at both lines, routed to Phase 3. The eight paths that do run pass, and
**TIMING_014 (tMOD) is resolved** on this drop.

### 2. Your fixes, judged on a hybrid

To answer what you asked, we paired your new `wb_port.sv` and
`data_path.sv` with the last scheduler that compiles (the (a)+(b) one
from 99f72da45a32) and ran the host, data and refresh paths. Not a drop,
not in the package; evidence only.

**wb_port: fixed.** Paths 01, 02, 07, 18: the request stream matches the
model, `(conservation)` passes with zero lost beats, and the host
handshake stage no longer counts unacknowledged beats. On the saturate
path that lost 25 of 243 beats yesterday, 0 of 243 are lost. Your
`wr_ack_r` reasoning holds: acknowledging on acceptance into a skid that
cannot lose or reorder the entry is a legal posted write; the thing that
made it a bug was the skid not existing. `WB-010` is well formed: a
property disabled under reset, and the tag-full stall is a separate
term of `wb_stall_o`, so `req_valid && !req_ready` is never true for a
reason other than the queue. HOST_001 still fires on path_23, as you
expected, since you left the ack merge alone (see 3).

**data_path: the drops are gone, the data is wrong.** `(conservation)`
passes on paths 02, 07 and 18: every RD gets a response and every WR
drives its word. But the `data_path` stage fails on every path that
reads, including path_03 with no back-to-back reads at all:

| path | predicted | observed |
|---|---|---|
| path_03 (single read) | `0x5d807daf` | `0x00005d80` |
| path_18 (two reads) | `0x1027c4d1` | `0x35bf1027` |

The low half of the observed word is the HIGH half of the right word,
and the high half is zero or the next word's low half. The capture
window is one cycle late: `rd_pend` adds a cycle between `cmd_rd_valid`
and the capture engine's CL countdown, but the DRAM returns the data CL
after the RD on the bus regardless, so beat 0 passes before the engine
looks and beat 1 lands in slot 0. On 99f72da45a32 path_03 passed 19 of
19, so this is a regression of 65dbb0f, not the old read-capture defect.
The fix is that the countdown must start when the command is issued,
for every pending read, not when the engine gets to it: a small shift
register of per-command countdowns (or the pending entry carrying its
scheduled capture cycle), with the capture engine serving whichever
entry's countdown expires. "Serviced late" cannot be right for a read:
the DRAM does not wait.

Which brings in your `BEATS_PER_CYC` question. It is real, and it is a
spec gap rather than a data_path bug: a host word occupies the DQ bus
for `host_width / channel_width` = 2 controller cycles in this
abstraction (one beat per controller cycle, which our DRAM stub models
the same way), while tCCD = 4 nCK lets the scheduler issue CAS every
cycle. Two reads one cycle apart cannot both be captured on one bus,
whatever the data path does. Either the scheduler spaces CAS by the
word's beat count (tCCD_eff = max(tCCD, beats), one line in the
scheduler) or the beat model changes to the real rate (8 transfers per
controller cycle, a word per nCK), which is what `BEATS_PER_CYC =
CLK_RATIO * 2` would mean. That is a decision for the spec
(`phy_interface` is abstract and says nothing about data-bus occupancy
per CAS); we are filing it as an intake gap, and until it is decided
the scheduler spacing is the safe choice.

One residual on writes: on the refresh-stress path, 1 of 600 write
words was never accepted and one WR drove a single beat, well before the
end of the window. Something in the `wr_pend_cnt` / `wr_buf` lockstep
slips once in 600; worth a look when you are in the file.

### 3. HOST_001 is live

Formal (no abstraction) finds the write-ack / read-response collision at
24 cycles; the directed path_23 reproduces it in simulation at gap 40
(write accepted the cycle before the read's data returns, one `wb_ack_o`
pulse for two beats, one beat never acknowledged). It is in the package
as `wb_port/HOST_001`, critical, confirmed, with the skid you just built
being the natural place to hold the loser.

### 3b. Scheduler formal, for the record

The 60-minute concrete run on the (a)+(b) scheduler of 99f72da45a32:
PROTO_002 proven, PROTO_001 still undetermined at depth 76, HOST_001
counterexample again at 28 cycles. The scheduler in your new drop is
(a) without (b), a different design, so its proofs start over once it
compiles; PROTO_001 stays `awaiting_formal` until then.

### 4. What the next round needs

Phase 3 fixes the declaration order (one line); then the full drop can
be judged. Expect: wb_port clean except HOST_001; data_path failing
every read until the countdown moves to command issue; the scheduler
spacing or spec decision above.

## Addendum 11 (2026-10-29, evening): drop e5ec723f495e, 17 of 20

Replies to your handoffs 3 to 6. The redesign holds: every read path
passes, back-to-back reads and writes included, the compile error is
gone, tMOD and tMRD are clean, and the port is clean. Three paths fail,
two of them on one remaining data_path case and one on HOST_001.

| path | before (5994bb, hybrid) | now |
|---|---|---|
| 01, 02, 07 (host → command) | pass / pass / pass | pass |
| 03 (single read) | data_path 0/19 | **pass** |
| 18 (write then read back) | data_path 24/33 | **pass** |
| 05, 20 (refresh stress, 600 beats) | 1 write word lost | 1 write word lost |
| 23 (ack collision) | HOST_001 fires | HOST_001 fires |
| 08/09/14/15/17 (init) | pass | pass, TIMING_013/014 silent |

**CAS spacing**: the minimum gap between CAS commands on the traces is
now exactly 2 controller cycles (`WORD_BEATS`), 24 of 76 gaps on path_02
sit at it, and no read's word is shifted. Your reasoning on the
bank_tracker tCCD question was right to stop where it did: `ctr_ccd`
does load 4 nCK and count controller cycles, so it would enforce ~4
cycles, but it is loaded from cmd_gen's registered feedback, and a
second CAS was being selected before the first had loaded it. At this
ratio the spec's tCCD is one controller cycle, so TIMING_010 never had
a violation to report; your guard, loaded the cycle a CAS is selected,
is what actually spaces the bus. The tMRD guard was the right call: the
clock ratio is a Tier-2 choice, and a guard derived from the spec that
is a no-op at 4:1 is exactly how a dormant violation should be handled.
TIMING_013 and TIMING_014 are both silent on the five init paths.

### The remaining data_path case: a full write buffer refusing a word in the cycle it pops

On both refresh paths, one of 600 write words is never accepted, and
one WR command later drives nothing (`CONSERVE/WRITE_REQUEST_TO_DATA`,
`CONSERVE/WRITE_CMD_TO_BEATS`). The trace at t = 779 000 ps on path_05:
16 words already in `wr_buf`, zero WR commands issued yet (the sequence
front-loads 600 pipelined beats and the scheduler is still activating),
and in the same cycle the first `cmd_wr_valid` fires, so the engine pops
`wr_buf`, the 17th write request is enqueued (the queue had room) and
its word arrives at `wr_data_valid`. `wr_full` is still true that cycle,
so `wr_data_ready` is low and the word is dropped; the pop frees the
slot one cycle too late. Two things to fix, the first in data_path:

1. `wr_data_ready` must allow a push in the cycle a pop happens
   (`~wr_full || wr_pop_this_cycle`, with the count updated for both),
   the standard full-FIFO same-cycle case.
2. `wr_data_ready` has no consumer: the manifest lists it as an output
   and nothing in the integration map reads it, so the port never stalls
   a write for a full write buffer; `host_interface.write_buffer_depth`
   = `command_queue_depth` = 16 is what makes that survivable, and only
   up to this same-cycle corner. Either wb_port honours `wr_data_ready`
   in `wb_stall_o` for writes (a new edge, Phase 1 and the manifests) or
   the spec states that the write buffer must hold queue depth plus the
   writes in flight. We will raise the second as an intake question; the
   first fix closes the finding on its own.

### Coverage note, not a finding

Design code coverage on this drop reads 72.0 %, down from 86.8 %, all of
it in data_path (29.7 %). The cause is 1 018 toggle bits of
`rd_pend_deadline`/`wr_pend_deadline`: 16 entries × 32 bits × 2, holding
a free-running cycle count whose high bits can never move in any run we
can simulate. The deadline only needs to span CL in controller cycles
plus the queue's worth of beats, 8 bits is generous; a modulo counter of
that width (compared modulo as well) would give the same behaviour, a
smaller block for Dawson, and the coverage back. Your call; the
measured number stays honest until then.

### HOST_001

Still the one open port item, by design on your side. Formal finds it
again on this scheduler (re-proof running), path_23 reproduces it. The
skid you built is the natural place to hold the loser.

### Your other questions

Handoff 4 and 5 (the testbench): the `rd_capture_valid` level trigger is
the right line, and the scan result (one instance, isolated) matches
what we would expect from the Phase 2/3 generators. The low-cost preset
run of that testbench is yours (it is your gate); on our side the
preset drop will be re-judged the next time the flow runs that preset.
