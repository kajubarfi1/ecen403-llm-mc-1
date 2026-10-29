# Handoff to Backend — 2026-10-29

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-10-29.md` ("loop break,
measured") — here's "(a) without (b)" to measure.

## What's in this drop

Reverted fix (b) only, kept fix (a). `Frontend2/scripts/Phase3/
scheduler_gen.py`, drop `5994bb667dba`:

- **(a) stays**: `sel_onehot_r`, the registered one-hot decode, still
  drives `recently_granted` (`sel_onehot_r[i]`, not an equality
  comparison against `sel_idx_r`). You confirmed this one closed the
  loop completely — untouched.
- **(b) reverted**: `sel_bank_eff_r` is a `wire` again —
  `sel_from_queue_r ? q_bank[sel_idx_r] : sel_bank_r`, read by the
  registered `sel_idx_r` each cycle, exactly the form your handoff
  quoted as the original line 128. No longer registered directly from
  an un-registered `sel_bank_eff`.

So this is deliberately your two-options framing from the loop-break
handoff, option (a) alone: the residual mux-through-`sel_idx_r` loop is
back, the one-hot isn't. Structurally identical to what scheduler.sv
looked like before (b) was ever applied, modulo (a) staying in.

## What I checked, and what I didn't

Diffed the regenerated file against the (a)+(b) version — 48 lines
changed, all in the `sel_bank_eff_r` declaration/registration and its
explanatory comments; the rest of the module (including everything (a)
touches) is untouched. `py_compile`, 43/43 `tests/test_flow.py`,
`microarch_compiler.py --selftest` all pass. Regenerated `TOPRTL`,
`top_copy_mismatches` clean.

**Not verified**: timing, obviously — that's what you're measuring.
Also haven't re-run Jacob's `validate_drop.py` on this exact drop yet;
functionally it should be identical to the (a)+(b) drop he already
passed 19/19 on (same mux expression, same cycle, just not captured in
an extra flop in between), but I'm not asserting that without his sim
confirming it — sending you this now rather than holding it for that,
same as last time.

## Question

None blocking — send the measurement when you have it, and if the
residual loop turns out to be the better of the two, nothing further
needed from us on this specific path; if (b) turns out cheaper after
all, say so and we'll put it back.
