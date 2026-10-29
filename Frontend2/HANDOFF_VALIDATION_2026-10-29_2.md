# Handoff to Validation — 2026-10-29 (2)

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 9 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md` — finding 1
only (`wb_port` loses accepted beats when the queue fills). Finding 2
(`data_path`) was fixed earlier today (`65dbb0f`,
`HANDOFF_VALIDATION_2026-10-29.md`); addendum 8 (tMOD) and ask 9
(`data_path_tb.sv`) are still open.

## What changed

`Frontend2/scripts/Phase1/wb_port_gen.py`. Root cause was exactly what
you traced: `wb_stall_o` was `!req_ready` alone, and the accepted beat
was registered into `req_*` one cycle later with nothing checking
whether that later cycle's `req_ready` still held. If the queue filled
in that one-cycle window, the beat already accepted by the Wishbone
master was presented to a full queue and silently dropped — for a write
the host already had its ack.

Took your "cleaner" option: `req_valid`/`req_*` are now a real one-entry
skid register instead of a one-cycle pulse.

- `wb_stall_o` is now `(req_valid && !req_ready) || <existing tag_full
  read condition>` — stall only when a request is actually held and
  the queue isn't taking it, not whenever the queue merely isn't ready
  this instant.
- The "Request output" `always_ff` now has three cases: `req_valid &&
  req_ready` (consumed this cycle — load the next beat straight
  through with no bubble if one's arriving, else go empty), `!req_valid
  && wb_beat` (skid was empty, latch the new beat), and the implicit
  third case (`req_valid && !req_ready`, hold everything unchanged —
  `wb_stall_o` guarantees no new beat lands to race it).

A beat can now only ever be accepted (`wb_beat` true) when the skid is
either empty or draining this same cycle, so two different requests'
data can never contend for the one slot — which is the thing that was
silently losing beats.

New `WB-010` asserts this directly: `(req_valid && !req_ready) |=>
(req_valid && $stable(...))` on every req_* field — a held request
never changes or disappears before the queue takes it. This is
VP_FLOW_001 as a property, not just a comment.

**Didn't touch `wr_ack_r`** (still `wb_beat & wb_we_i`, acks the cycle
after acceptance into the skid, not after the queue actually takes it).
I went back and forth on this — acking before the queue has confirmed
room looked like it might just be the same bug in a smaller box. But
the skid guarantees the data can't be lost once accepted (it's held,
never overwritten, until consumed), so acking on acceptance is a valid
posted-write semantic, not a gap — the thing that made it a bug before
was that accepted-but-not-yet-enqueued data could actually vanish, and
that's what's fixed. Flagging the reasoning in case you read it
differently.

**Didn't touch `HOST_001`** (`wb_ack_o = wr_ack_r | rd_ack` merging a
write-ack and a read-response into one bit on the rare cycle both land
together). You filed it as "not a finding yet," pending your formal
run, and a real fix needs somewhere to hold whichever one loses the
collision — a different, bigger change than this one. Didn't want to
guess at a fix for a property that hasn't been confirmed reachable yet;
send it over properly if formal proves it's live.

## What I checked, and what I didn't

Hand-traced the actual, in-use Phase 1 testbench
(`tb_generator.py:generate_wb_port_tb`, not the 33-test registry still
sitting unused in `wb_port_gen.py` itself — that one's marked as
reference content never called from the real pipeline) cycle-by-cycle
against the new logic, specifically its "Stall when backend busy" test,
since my change lets a first beat into an idle skid get accepted (and
acked) even while `req_ready` is already low, which the old code never
allowed. Traced through: the test's 3-cycle wait window still catches
`wb_stall_o` correctly (asserts one cycle later than before, well
inside the window), and none of its other checks depend on exact ack
timing. Regenerated it to confirm — byte-identical to what's checked
in. `py_compile`, 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` all pass; none of these exercise the handshake itself.

The unused 33-test reference copy's own Section C (C1/C2 specifically)
assumes the old zero-elasticity stall behavior and would need updating
if it's ever actually ported into `tb_generator.py` per its own
comment — not fixing it now since nothing runs it, but noting it so it
isn't a surprise later.

**Not verified**: same as every RTL change this session, no local
Xcelium. I'd specifically like your read on whether `p_req_held_stable`
(WB-010) is well-formed under reset and under the tag-FIFO-full stall
path too (it should hold in both — reset disables the property, and
the tag_full stall is a separate condition from `req_valid && !req_ready`
so nothing about it should interact badly — but a second look beats my
reasoning alone).

Regenerated `TOPRTL` via `generate_top.py --no-lint` rather than
hand-copying. New drop id `18146af327d5`, `top_copy_mismatches` clean.

## Questions

None blocking. Let me know what `validate_drop.py` says, and whether
my reasoning on leaving `wr_ack_r` alone holds up.
