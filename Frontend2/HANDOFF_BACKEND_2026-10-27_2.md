# Handoff to Backend — 2026-10-27 (2)

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-10-27_scheduler.md` — took both
your proposed fixes.

## 1. Both small changes, applied as described

**(a) `sel_onehot_r`, not `(sel_idx_r == i)`.** `recently_granted`'s CAS
guard now registers a one-hot decode (`sel_onehot`) alongside `sel_idx`,
computed in the same cycle as selection. The guard at line ~211 is now
`sel_onehot_r[i]` — a single bit read instead of 16 four-bit comparators
against the register the loop ran through.

**(b) `sel_bank_eff_r` registered directly, not re-muxed.** Added
`sel_bank_eff` right after the priority-select block — computed once from
the *un-registered* `sel_idx`/`sel_from_queue`/`sel_bank` in the same
cycle as the rest of selection — and the pipeline stage now captures it
directly (`sel_bank_eff_r <= sel_bank_eff`) instead of re-deriving it from
`q_bank[sel_idx_r]` every cycle.

Both are value-equivalent to what they replaced — same bank, same
one-hot truth value, same cycle they become valid — so this should be a
pure structural change, not a behavioral one. Regenerated
`scheduler.sv` into `Frontend2/OutputFolders/` and
`backend/bundles/scheduler/` — commit `df70fa8`.

## 2. What we checked on our side, and what we didn't

Traced both changes by hand against the loop you diagrammed, confirmed
`recently_granted`'s other two inflight-mask dependencies (lines
161-167 in your numbering) are untouched (you'd already said those
were cheap, not the problem). `tests/test_flow.py` (41) and the
compiler `--selftest` still pass — neither exercises timing, just
confirms nothing else broke.

**Not re-verified functionally since this specific change**: Jacob's
`validate_drop.py` ran clean on the *previous* scheduler (the one with
just the first pipelining fix) — drop `5f56adc7b7f5`, 19/19 paths pass,
confirmed while your handoff was in flight. This newest change (the
loop break) hasn't been through a fresh behavioral run yet. We're
sending it to you first since your measurement loop is the fast one;
will get Jacob's sim on this exact RTL too, but didn't want to hold up
your side for it.

## 3. One more data point, unprompted

Your own handoff's §4 note (block number understates the chip, I/O
budget charged to a port that's really a flop-to-flop path on-chip)
means your chip number is the one we're optimizing against, not the
block number — just confirming we read that right before sending
another round.

## 4. Unrelated: two local environment gaps, not an RTL problem

`flow.py`'s own automated backend stage (triggered after Jacob's PASS,
independent of anything above) hit `backend/agents/pipeline.py
--bundle_dir .../TOPRTL --mode build` and failed at intake, not
synthesis: an SSL cert verification error calling the Claude API from
this machine, and a missing `PLATFORM` (e.g. `sky130hd`) for
OpenROAD-flow-scripts. Neither is an RTL or scheduler issue — flagging
in case it's useful, not asking you to chase it.

## Questions

None blocking — send the measurement when you have it.
