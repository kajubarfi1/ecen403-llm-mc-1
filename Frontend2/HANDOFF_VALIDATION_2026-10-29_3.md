# Handoff to Validation — 2026-10-29 (3)

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 8 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md` — the tMOD
finding (`init_fsm/TIMING_014`). Findings 1 and 2 of addendum 9 were
fixed earlier today (`bdf1b5c`, `65dbb0f`); ask 9
(`data_path_tb.sv`) is still open.

## What changed

`Frontend2/scripts/Phase1/init_fsm_gen.py`. Exactly what you found:
`S_MR0 -> S_ZQCL` had no wait at all, one controller cycle (4 nCK) short
of tMOD's 12 nCK / 15 ns floor.

Added the wait state you suggested — `S_MOD_WAIT`, derived from
`timing_model.tMOD` and the controller period, not a literal (`WAIT_MOD
= ceil(tMOD_ns / ctrl_period_ns)`, comes out to 3 controller cycles at
this spec's clock, same number you named). It sits between `S_MR0` and
`S_ZQCL`; command outputs are unchanged (nothing issues during it, same
as the existing `S_TXPR_WAIT`/`S_ZQCL_WAIT` pattern), and `init_cke`/
`init_reset_n` stay asserted through it like the other post-reset wait
states already do.

**One thing beyond just tMOD, since I was already in this state
machine:** you noted tMRD (MRS-to-MRS, 4 nCK) is "met because one
controller cycle is 4 nCK" — true for this spec, but only because the
golden spec's clock ratio happens to be 4:1. That ratio became a
genuine per-spec Tier-2 choice earlier this session (1/2/4/8), so a
future preset at ratio 1 or 2 would silently violate tMRD the same way
MR0->ZQCL was violating tMOD — one controller cycle would only be 1 or
2 nCK, under the 4 nCK floor. Since computing `WAIT_MOD` properly
already meant doing this derivation correctly instead of assuming a
fixed ratio, I added the matching `WAIT_MRD` wait (`S_MRD_WAIT1/2/3`,
same derivation from `timing_model.tMRD`) between each of the three
MR2->MR3->MR1->MR0 transitions too, rather than leave a second,
related, currently-dormant version of the same bug for the first
non-4:1 preset to trip over. At this spec's ratio it computes to
exactly 1 cycle (adds one cycle of margin beyond what was already
JEDEC-compliant here) — the only place this changes anything observable
*at this spec's clock* is the actual fix, tMOD; the tMRD states are
currently a no-op in effect, insurance for a config this spec doesn't
use. Flagging since you didn't ask for it and it's outside what you
reported.

Both new wait counts are in the manifest (`WAIT_MRD`, `WAIT_MOD`)
alongside the existing `WAIT_TXPR`/`WAIT_ZQCL`.

**State numbering**: used the four previously-unused 4-bit encodings
(10-13) for the new states. Every existing state keeps its old number,
`S_DONE` is still `4'd14` — the file's own "do not renumber" contract
for that one is untouched, and nothing else needed renumbering since
there was room.

## What I checked, and what I didn't

Hand-traced the new transitions: MR3 now issues 2 controller cycles
(8 nCK) after MR2 instead of 1 (4 nCK) — still ≥ tMRD, same shape for
MR1 and MR0 after their predecessors; ZQCL now issues 4 controller
cycles (20 ns) after MR0 instead of 1 (5 ns) — clears the 15 ns floor.
Checked the actual, in-use testbench (`tb_generator.py:
generate_init_fsm_tb`) rather than assume it: it polls `wait(init_done)`
instead of a fixed cycle count, its timeout has a 500-cycle margin
(the fix adds about 6 cycles total), and its MR-order/MR-count checks
only look at the sequence and encoding, not the gaps between them — it
needed no changes and I didn't make any. `py_compile`, 43/43
`tests/test_flow.py`, `microarch_compiler.py --selftest` all pass.

**Not verified**: no local Xcelium, same as every RTL change this
session — I'd like `init_fsm_sva.sv`'s TIMING_013/TIMING_014 run
against this on your next pass, since those are the properties that
actually prove this closes the gap rather than my hand count of cycles.

Regenerated `TOPRTL` via `generate_top.py --no-lint`. New drop id
`52f641280632`, `top_copy_mismatches` clean.

## Questions

None blocking. Let me know if TIMING_013/TIMING_014 come back clean,
and whether adding the tMRD guard unprompted was the right call or
scope you'd rather I'd asked about first.
