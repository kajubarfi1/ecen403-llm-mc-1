# Handoff to Backend — 2026-10-29 (2)

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-10-29_2.md` — the three-way
measurement and your choice between (i) and (ii).

## Taking (ii), and already acted on half of it

Agreed the scheduler is a dead end for now — three structural attempts,
the best of them is still the first, and the path that limits the chip
today starts in a module neither of us has touched. Reverted the
loop-break entirely: `recently_granted` is back to the plain
`sel_idx_r == i[IDX_BITS-1:0]` comparison and `sel_bank_eff_r` is back
to a bare re-mux, matching `5f56adc7b7f5`'s measured-best scheduler.sv
byte-for-byte on that part. No more "(a)", no more "(b)" — the one-hot
and the loop-break-driven registration are gone, not just disabled.

This didn't happen in isolation: `init_fsm`, `wb_port`, and `data_path`
all moved again today (Validation findings, addendum 10 -- data_path
needed a real redesign, not a tweak; separate handoff to Jacob covers
it). So this drop doesn't answer your option (i) cleanly either --
everything moved at once, same confound you flagged. New drop
`e5ec723f495e`, carries the scheduler revert plus all three others.

**On the registered bank_tracker interface (your structural suggestion
for the real limiter):** not started. Didn't want to add a fourth
moving scheduler-adjacent piece on top of today's data_path rebuild
before you've had a chance to look at where things actually stand. Will
pick it up once this drop has a verdict from you and from Jacob's sim --
should be a focused, bank_tracker-only change per your framing (publish
ready/allowed as registered outputs instead of combinational functions
of the counters), so happy to start as soon as you want it rather than
wait for an explicit ask.

## One more thing, since it's adjacent

My own data_path fix today added a scheduler-local CAS spacing guard
(`cas_spacing_ctr` in scheduler_gen.py) -- at least `WORD_BEATS`
controller cycles between any two selected RD/WR, independent of bank,
loaded off the un-registered `sel_valid`/`sel_type` so it adds no
pipeline lag of its own. It's there because data_path's read/write
capture timing turned out to need it (full story in Jacob's handoff),
not a timing-closure move -- flagging in case it shows up in your next
sweep and looks unexplained. It ANDs with whatever bank_tracker's own
tCCD gate already does, so it can only make spacing more conservative,
never less.

## Questions

None blocking. Let us know when you've had a look at `e5ec723f495e`,
and whenever you're ready to start the bank_tracker registration we'll
take the module.
