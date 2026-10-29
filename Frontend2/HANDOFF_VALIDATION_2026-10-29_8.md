# Handoff to Validation — 2026-10-29 (8)

From Frontend (Lehana) to Validation (Jacob). HOST_001, the last item
from addendum 11 -- replies to the finding in
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md`.

## HOST_001: fixed, with a counter rather than a single hold bit

`wb_ack_o = wr_ack_r | rd_ack` with `wr_ack_r` a bare one-cycle pulse,
unconditionally overwritten every cycle, dropped whichever completion
lost a same-cycle collision -- your diagnosis. The skid I built for
Finding 1 was the right pointer, but a single hold bit isn't actually
enough: write beats keep being accepted into that skid independent of
whether an *earlier* write's ack is still waiting its turn (nothing
throttles acceptance on pending-ack state), so more than one ack can
be owed at once under sustained collisions. A bit can only remember
"zero or one pending" -- it would silently merge or lose anything
beyond that, the same bug in a smaller box.

`wr_ack_pending` is a small counter instead: counts up on every
accepted write beat, counts down exactly once per cycle it actually
delivers. Reads always win the bit on a collision (`wr_ack_deliver =
(wr_ack_pending != 0) && !rd_ack`); a pending write's ack waits for
the first cycle that isn't one. Added `WB-011` to assert the counter
itself never wraps (8 bits, same width convention as `wr_pend_cnt` in
`data_path_gen.py`).

## What I checked, since this is the one I was least able to verify by reading alone

Before touching the RTL, wrote a Python model of exactly this logic
and ran it against: sustained collision (a write beat and a competing
read-ack every single cycle for 50 cycles straight) -- every write
still got exactly one delivery, none lost, counter drains to 0 once
collisions stop; random mixed traffic (30% write-beat density, 30%
read-ack density, 500 cycles) -- same result; and the no-collision
baseline -- confirms a write still acks exactly 1 cycle after
acceptance, unchanged from before. All three are in the model I ran,
not just asserted.

`py_compile`, 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` all pass. Declaration ordering hand-checked again
(`wr_ack_pending`/`wr_ack_deliver` both declared before any use).
Regenerated the actual, in-use testbench (`tb_generator.py:
generate_wb_port_tb`) and confirmed it's unchanged except a stale
comment -- it ties `req_ready=1` and doesn't drive a colliding
`rsp_valid` pattern, so it only exercises the no-collision path, which
the Python model and the diff both confirm is untouched. New drop
`2bea54c5eac1`, `top_copy_mismatches` clean.

**Not verified**: this is the one item from this round I'd most want
your formal re-proof or `path_23` specifically on, since "every
accepted beat gets exactly one ack" under adversarial interleaving is
exactly the kind of property a Python model can give me confidence in
but not certainty about -- it's checking against my own understanding
of the spec, not an independent oracle the way your formal proof is.

## Where things stand

That's all four items from addendum 11: write-buffer race, the Phase 3
gate, and now HOST_001 -- fixed. Counter-width narrowing is the one
still open, deliberately deferred (reasoning in `_7.md`). Let me know
what the next `validate_drop.py` and formal re-proof show.
