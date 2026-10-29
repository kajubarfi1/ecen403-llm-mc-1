# Handoff to Validation — 2026-10-29

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 9 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md` — finding 2
only (`data_path` drops a RD/WR command issued while its FSM is busy).
Finding 1 (`wb_port` lost beats), addendum 8 (tMOD), and ask 9
(`data_path_tb.sv`'s white-box read beats) are not touched here; picking
them up next.

## What changed

`Frontend2/scripts/Phase4/data_path_gen.py` — both `rd_state`/`wr_state`
were one-deep: a new RD/WR command was only accepted from `RD_IDLE`/
`WR_IDLE`, so a command issued while the engine was mid-wait or
mid-capture/drive was silently dropped. At CL=11, the read engine is busy
4 controller cycles per read (wait 2, capture 2); at tCCD = 4 nCK = 1
controller cycle the scheduler and cmd_gen can legally issue every cycle,
so any back-to-back pair inside that window vanished — exactly your
finding 2 numbers.

Fix: decoupled "accept" from "capture/drive."

- **Reads**: `cmd_rd_valid` now always pushes into a new `rd_pend` queue
  (depth `RD_FIFO_DEPTH`, same sizing as the response FIFO). The capture
  engine drains `rd_pend` one entry at a time from `RD_IDLE`, instead of
  requiring `cmd_rd_valid` to coincide with `RD_IDLE`. A queued read is
  serviced late, never dropped.
- **Writes**: added `wr_pend_cnt`, incremented on every `cmd_wr_valid`
  (independent of `wr_state`) and decremented each time the drive engine
  dequeues one. `wr_buf` (already FIFO-ordered by wb_port's acceptance)
  and `wr_pend_cnt` (incremented in issue order) stay in lockstep, so
  `WR_IDLE`'s trigger is `wr_pend_cnt != 0` instead of `cmd_wr_valid`.

Deliberately did **not** try to let two captures run concurrently —
`ddr_dq_i` is a single DQ_WIDTH-wide bus, one value per cycle, so two
reads' capture windows can't overlap regardless of how the FSM is
written. The queue keeps the bus side strictly serialized (same behavior
as today, one capture at a time) and only changes the accept side, which
is the part your finding showed losing data, not the bus model.

**One thing I didn't change and want your read on:** whether 4 nCK is
really tCCD's full floor here given the real channel width. `WORD_BEATS`
(2, the cycles the capture/drive FSM is sized on) happens to equal
`BURST_CTRL_CYCLES` (also 2) for this spec, but the two are computed
differently (`DATA_WIDTH/DQ_WIDTH` vs. `BURST_LEN/BEATS_PER_CYC`) and the
comments in the generator say `BURST_CTRL_CYCLES` is kept for
documentation only, not used to size anything. If `BEATS_PER_CYC` should
be `CLK_RATIO * 2` (DDR = double data rate, so 4 DDR *clock* cycles per
controller cycle is 8 *transfers*, not 4) rather than `CLK_RATIO` alone,
the real physical burst occupies half as many controller cycles as
modeled, which would separately matter for how tight back-to-back CAS
can legally be. I'm flagging this rather than touching it — it's a
clock-ratio/timing-model question that would touch the scheduler's own
tCCD enforcement too, not a data_path-only fix, and I'd rather get your
and Dawson's read on whether it's real before changing it.

Two new checks, added for the same reason `p_wr_no_overflow` exists:
`DP-013` (rd_pend never overflows — i.e. a RD command is never actually
dropped) and `DP-014` (wr_pend_cnt never wraps, same idea for writes).
Header docs and the manifest's assertion list updated DP-001..012 to
DP-001..014.

## What I checked, and what I didn't

Regenerated from both the standalone golden spec and
`Frontend2/OutputFolders/generated_spec.json`; diffed the two runs to
confirm the only delta vs. the pre-fix RTL is this change (98 lines, all
in the two FSM blocks and the new SVA). `py_compile`,
`tests/test_flow.py` (43, pass), and `microarch_compiler.py --selftest`
(27/27, pass) — none of these exercise data_path's actual timing
behavior, just regression safety elsewhere.

**Not verified**: no local Xcelium, so I haven't simulated the fix myself
— I'm relying on your next `validate_drop.py` run for that, same as every
other RTL change this session. In particular I'd like your check on two
things I reasoned through by hand rather than measured: that `rd_pend`
and the response FIFO staying in the same order as issue order holds
under your `wb_burst`/`saturate` traffic, and that a write queued behind
a busy engine doesn't let a later write's data get associated with an
earlier command's `wr_pend_cnt` slot (both `wr_buf` and the counter are
pure FIFOs in issue order, so I don't see how they'd skew relative to
each other, but a second pair of eyes beats an argument here).

Also regenerated `TOPRTL` (`generate_top.py --no-lint`, no Olympus here)
rather than hand-copying `data_path.sv` into it, which picked up
Dawson's provenance nit from today's backend handoff for free — the
manifest's `generated_utc` now matches what's actually in the directory.
`drop.py`'s `top_copy_mismatches` is empty and the new drop id is
`71ef73482973`.

## Questions

None blocking. Let me know what the next `validate_drop.py` run says on
this drop, and whether the `BEATS_PER_CYC`/tCCD question above is worth
a closer look or a non-issue for reasons I'm not seeing.
