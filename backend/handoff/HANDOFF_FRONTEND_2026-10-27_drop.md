# Handoff to Frontend — 2026-10-27 (drop `4e04c518306c`)

From Backend (Dawson) to Frontend (Lehana), urgent for tomorrow's update. We
built the new drop and the scheduler closes 200 MHz - but it is not the same
design we were trying to fix, so we cannot report it as the fix working. Please
confirm which of these is intended before anyone presents a number.

## 1. The drop targets a different part

Every block's manifest changed part configuration, not just the clock:

| | drop `efece348d04e` | drop `4e04c518306c` |
|---|---|---|
| `spec_revision` | `golden_ddr3_1600k_x8_2lane_1rank` | `compiled_ddr3800_x16_1lane_1rank_c28250a3` |
| `clock_period_ns` | 5.0 (200 MHz) | **10.0 (100 MHz)** |

All eleven blocks moved to 10.0 ns. Parameters moved with them:

| block | parameter changes |
|---|---|
| **scheduler** | `DEPTH 16->4`, `IDX_BITS 4->2`, **`POLICY fr_fcfs->in_order`**, `ROW_POLICY open_page->close_page`, `ROW_BITS 15->14` |
| **cmd_queue** | `DEPTH 16->4`, `ENTRY_W 33->32`, `IDX_BITS 4->2`, `ROW_BITS 15->14` |
| wb_port | `QUEUE_DEPTH 16->4`, `ADDR_WIDTH 29->28`, `ROW_BITS 15->14` |
| data_path | `CL 11->6`, `CWL 8->5` |
| init_fsm | `WAIT_CKE 100000->50000`, `WAIT_RESET 40000->20000`, `WAIT_TXPR 34->17`, ... |
| refresh_ctrl | `tREFI_nCK 6240->3120`, `tRFC_nCK 128->64`, `REFI_CTR_W 13->12` |
| addr_decoder, bank_tracker, cmd_gen | `ROW_BITS 15->14` and width knock-ons |

The golden spec file itself is untouched, so this looks like the regeneration
being pointed at a compiled spec rather than the golden one - possibly a
side-effect of the Tier-2 clock-ratio change (`1a62187`). But we cannot tell from
here whether it was intended.

## 2. What we measured, and why it does not settle the timing question

Built `scheduler` from `4e04c518306c` twice.

**As the manifest specifies (10.0 ns):** PASS, WNS +4.122 ns, 1,970 cells. That
reads like success but only says the block closes 100 MHz, which was never in
doubt. We caught it because the reported Fmax of 170.14 MHz is arithmetically
impossible at 5 ns - it only works at 10.

**Forced to 5.0 ns:** PASS, **WNS +0.566 ns, Fmax 225.6 MHz**, 2,004 cells,
DRC 0 violations, LVS match.

So the block in this drop does close 200 MHz with margin. The problem is the
comparison:

| | old scheduler | new scheduler |
|---|---|---|
| queue depth | 16 | 4 |
| policy | FR-FCFS | in-order |
| cells at 5 ns | 9,183 | 2,004 |
| Fmax | 159 MHz | 225 MHz |

An in-order scheduler with a 4-deep queue has no out-of-order selection: no
16-way priority chain, no bank-state lookup feeding a row comparison, none of
the structure the critical path ran through. The path our finding named -
`u_cmd_queue.entry_bank[34] -> u_scheduler.cmd_row[4]` - does not exist in this
design.

**A simpler scheduler closing timing does not show that the pipelined FR-FCFS
scheduler closes timing.** We are not willing to present it as that, and we would
not want you to either - it is the kind of claim that does not survive one sharp
question.

## 3. What we need

**Confirm the intent.** Is `4e04c518306c` meant to be the project's design -
x16 single-lane at 100 MHz, in-order, 4-deep - or did the regeneration pick up a
compiled test spec instead of the golden one?

If unintended: regenerate from `golden_ddr3_1600k_x8_2lane_1rank` with the
scheduler pipelining fix in place, and we will rebuild and give you the real
answer. That is one block and about 25 minutes on our side, so if it lands
tonight we can still have it for tomorrow.

If intended: the whole team needs to know, because the 200 MHz target, the
FR-FCFS policy and the 16-deep queues are in everyone's reports and slides, and
Validation's path checkers are written against the old configuration.

## 4. The part of the loop that did work

Worth saying plainly, because it is the real result: your handoff cites our Fmax
sweep and the finding `scheduler/TIMING/cmd_row` by name, and §1 of it is the
pipelining change. The spec absorbed the latency cost explicitly -
`SCHED_PIPE_NCK` added to `latency_model`, read-hit 25 -> 29 nCK - rather than
the cost being hidden. That is backend measuring a miss, emitting a routable
finding, frontend acting on it, and the spec recording the trade. The loop ran.

Only the verification step is blocked, and only because the drop we were handed
is a different design.

## 5. One smaller thing

Three commits today were named as though they carried RTL - `rtl at 200mhz`,
`frontend updates`, and the `scheduler_gen.py` change - and none touched
`Frontend2/OutputFolders/PHASE*RTL/`. We spent a while confirming that before
`8f75747` actually landed it.

A quick self-check after any regeneration, which is also what Validation's
staleness tooling keys on:

```
python Validation/structural/rtl_drop.py --block-design-ids
```

If the block you regenerated shows the same id as before, the RTL did not move
regardless of what was committed.
