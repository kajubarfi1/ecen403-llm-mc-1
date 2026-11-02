# Handoff to Backend — 2026-11-02

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-11-02.md` -- both the
deadline-width narrowing and the registered due flag, plus the two
reversals.

## 1. Narrowed the deadlines -- saturating countdown, both sides

Took your proposed shape exactly: each `rd_pend`/`wr_pend` entry now
stores a 4-bit saturating countdown (the remaining wait, loaded at
issue, decrementing to 0 and stopping) instead of a 32-bit absolute
timestamp compared against a free-running counter. "Due" is a
zero-test. No modular comparison anywhere, because there's nothing to
wrap -- the free-running counters (`rd_cycle_ctr`, `wr_cycle_ctr`) are
gone, not just narrowed. That's 16 entries x 4 bits x 2 sides = 128
flops where there were 1,024.

Every queued entry decrements every cycle regardless of queue
position -- not just the head -- since real time passes for an entry
whether or not it's at the front; I called this out because it's the
one part of the shape that isn't obvious from "store the wait instead
of the deadline" alone.

Verified the due-cycle timing is bit-for-bit identical to the old
(correct) absolute-deadline design before writing any RTL: a Python
model checked against 5 CL/ratio combinations spanning the full valid
range (including both extremes, CL=14/ratio=1 and CL=5/ratio=8) landed
on the exact same due cycle every time, and 5,000 cycles of random
push/pop traffic lost or double-counted nothing.

## 2. Registered the due flag -- on the WR_IDLE path, not the chain path

`wr_head_due_r` is a registered "the current head of `wr_pend` has a
zero countdown," computed one cycle ahead so `wr_data_ready` reads a
flop instead of indexing `wr_pend_wait` by `wr_pend_rptr` and
comparing it combinationally. This covers the path you measured
(`wr_pend_rptr[0] -> data_path_wr_data_ready`) and the general
WR_IDLE dequeue, which I'd expect to be the common case.

**What it does not cover**: the WR_DRIVE chaining path (back-to-back
writes chaining straight into the next one without detouring through
WR_IDLE) still reads `wr_pend_wait[rptr] <= 1` combinationally --
narrowed to 4 bits like everywhere else, but not registered. Tracking
"will the head be due by next cycle" through a pop that can also
change which entry *is* the head turned out to need real care to get
right (I verified `wr_head_due_r` itself against a Python model for
exactly this reason -- 2,000 cycles, zero mismatches against a fresh
combinational check every cycle, including through pops). Doing the
same for a *wider* ("due or about to be") predicate on the rarer
chaining path felt like it was trading a meaningful verification
effort for a smaller win than the WR_IDLE path gave, so I stopped
there. If your next measurement shows the chain path is still a
problem, flag it and I'll go back in -- I have the verification
harness already.

## 3. Keeping the CAS spacing guard, holding bank_tracker

Noted both -- no code changes, nothing for you to re-measure on either
front from our side.

## What I checked

`py_compile`, 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` all pass. Declaration ordering hand-checked and then
verified programmatically (every new signal's first appearance in the
generated RTL, comments excluded, is its own declaration). Regenerated
the actual in-use testbench and confirmed it's byte-identical --
`dut.rd_capture_valid` means the same thing regardless of what drives
the state transition into it, so nothing there needed to change.

New drop `ee9962151d05`, `top_copy_mismatches` clean.

**Not verified**: no local synthesis or STA, so the flop count and
timing improvement are my own structural accounting, not a
measurement -- that's the thing I most want from your side on this
one.

## Questions

None blocking. Let us know what the chip measures, and whether the
WR_DRIVE chain path is worth registering too once you've seen a real
number.
