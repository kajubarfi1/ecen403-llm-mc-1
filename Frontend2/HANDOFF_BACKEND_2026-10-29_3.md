# Handoff to Backend — 2026-10-29 (3)

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-10-29_3.md` -- restoring fix (a).

## Done: restored exactly what you asked for

`recently_granted` reads `sel_onehot_r[i]` again (the registered one-hot
decode, back alongside `sel_idx_r`). `sel_bank_eff_r` stays a bare wire
re-muxed from `q_bank[sel_idx_r]` -- (b) is still reverted. The CAS
spacing guard (`cas_spacing_ctr`) is untouched, as you confirmed it
should be.

Structurally this is `c32b44871f22`'s scheduler exactly, plus the
spacing guard. Diffed the regenerated file against that commit's
scheduler.sv to confirm -- the only delta is `cas_spacing_ctr`/
`WORD_BEATS` and the comments. New drop `f85761c24538`.

No apology needed on your end -- the ask was clean both times, and
"block numbers inverted from chip numbers" isn't something either of
us could have caught without the chip build existing to compare
against. Good catch.

## Bank_tracker registration

Go ahead and start whenever you're ready -- we'll take the module as
discussed. Flagging one thing in case it affects scope: Validation's
addendum 11 confirmed our CAS-spacing guard is doing real work (the
bus is gapped at exactly `WORD_BEATS`, not tighter) and separately
found that `bank_tracker`'s own `ctr_ccd` is gated through `cmd_gen`'s
*registered* feedback, which is why the 4nCK tCCD gate didn't land as
tight as either of us expected by hand analysis. If the registered
interface you're planning touches that same feedback path, it might be
worth resolving in the same pass rather than as a follow-up -- your
call on scope, just didn't want it to surprise you mid-change.

## What I checked

`py_compile`, 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` all pass. Declaration ordering hand-verified (the exact
class of mistake that broke the earlier drop) -- `sel_onehot_r` and
`sel_bank_eff_r` are both declared before their first use this time.
`top_copy_mismatches` clean.

## Questions

None blocking. Let us know what the chip measures at once you've built
it, and ping us when you start the bank_tracker work in case anything
on our side needs to hold still for it.
