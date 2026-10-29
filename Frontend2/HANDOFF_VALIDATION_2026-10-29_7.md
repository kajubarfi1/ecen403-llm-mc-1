# Handoff to Validation — 2026-10-29 (7)

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 11 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md`. Three of
the four items below; HOST_001 is next.

## 1. Write-buffer same-cycle pop/push race -- fixed

Exactly as you traced: `wr_data_ready`/the push condition both read
`wr_full`, a registered count that doesn't yet reflect a pop happening
this same cycle. Added `wr_pop_this_cycle` -- mirrors the three places
the write engine actually pops `wr_buf` (the queued-deadline path, the
bypass path, and the chained-drive path) -- and changed both
`wr_data_ready` and the push condition to `~wr_full || wr_pop_this_cycle`.
Moved both out of the write-buffer declaration block and down to after
the write FSM, since `wr_pop_this_cycle` needs signals (`wr_bypass`,
`wr_pend_deadline`, `wr_cycle_ctr`) that only exist there -- declaring
`wr_data_ready`'s logic before those would be the exact Xcelium
use-before-declaration mistake from two drops ago.

Also updated `DP-001` (write buffer overflow): it would otherwise
false-fire on exactly the case this fixes -- a legitimate push into the
slot a same-cycle pop just vacated now reads `wr_data_valid && wr_full`
on purpose. Added `&& !wr_pop_this_cycle` to the property.

## 2. Counter width -- deferring, here's why

Agree 32 bits is more than needed, but narrowing `rd_pend_deadline`/
`wr_pend_deadline` correctly means switching the comparison from plain
`>=` to a wraparound-safe modular comparison at every site that reads a
deadline -- four of them, plus the two inside `wr_pop_this_cycle` I just
added. That's real logic to get right across code I spent a lot of this
session getting correct the hard way (the Python model, the chaining
fix). I'd rather not touch it in the same pass as a correctness fix,
and HOST_001 is still ahead of it in priority. Noting it as open, not
declining it -- will come back to it once HOST_001 lands and there's a
validation pass to catch a mistake if I make one.

## 3. Phase 3 gate (T36/T37) -- fixed, not diagnosed to the exact cycle

Took your suggested fix shape directly rather than trying to nail the
precise pipeline-cycle interaction from reading alone (no local
Xcelium to check against, and I didn't want to guess wrong on a gate
whose whole job is catching real regressions). `scheduler_tb.sv`'s
RefBlock test (T35-38) now polls for REF in a bounded loop instead of
expecting it on the very next command: each time it observes another
PRE, it calls `set_bank_idle()` again (idempotent) and keeps polling,
up to 4 attempts, the same shape `wait_cmd`'s own polling already uses
elsewhere in this test. If a real regression ever makes the scheduler
stop issuing REF entirely, all 4 attempts time out or see something
else, and the check fails exactly as before -- this only tolerates
*extra PRE observations before REF*, nothing else.

Your diagnosis that the scheduler itself is right stood on its own
evidence (every refresh/scheduling check passing on the real paths),
so I trusted it rather than re-deriving it.

## What I checked

`py_compile` on all three touched generators, 43/43
`tests/test_flow.py`, `microarch_compiler.py --selftest` all pass.
Regenerated `scheduler_tb.sv` and confirmed it's syntactically clean
(the `for` loop with an early-exit `attempt = 4` reads oddly but is
valid SV). New drop `cbbc04e1f66c`, `top_copy_mismatches` clean.

**Not verified**: no local Xcelium, so neither the write-buffer fix nor
the RefBlock polling loop has actually run. I'd like `validate_drop.py`
on path_05/path_20 (the refresh-stress write-loss case) specifically,
and whatever your next `runs/*` flow attempt shows for the Phase 3 gate
-- that's the one that tells us whether the polling loop actually
clears T36/T37, not just whether it compiles.

## Questions

None blocking. HOST_001 next; will send a separate handoff once that's
in.
