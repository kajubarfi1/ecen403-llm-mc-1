# Handoff to Backend — 2026-11-03

From Frontend (Lehana) to Backend (Dawson). Replies to
`backend/handoff/HANDOFF_FRONTEND_2026-11-03.md` — the priority-chain
tree, plus two things worth flagging on the rest of that handoff.

## 1. The ask: the tree, done

`scheduler_gen.py`'s priority 2 (row-hit CAS) and priority 3 (ACT for
row-miss) no longer chain two 16-deep first-match loops through
`if (!sel_valid)`. Each tier now computes a balanced binary reduction
tree over its own entry-wise eligibility vector — `is_cas_ready[]` for
tier 2 (unchanged), and a new `eligible3[]` for tier 3, which spells out
the same per-entry PRE-vs-ACT resolution the old loop did inline
(`act_cond_pre[i]`/`act_cond_act[i]`, reading only `q_bank[i]` and bank/
inflight state — independent of every other `i`, same as you said).
`log2(16) = 4` levels per tier instead of 16.

**Went one step further than "per-tier tree" on its own**: since
`eligible3[]` never reads tier 2's result (only bank state and inflight,
exactly like `is_cas_ready[]`), both trees run concurrently rather than
tier 3's being gated behind tier 2 failing first. The two 16-deep chained
scans become two independent 4-level trees plus a single `if (t2_valid)
... else if (t3_valid)` mux at the end — one level, not the "two tiers
run serially" shape the old code had. That's the tier-level option from
your handoff's section 4, and it fell out for free rather than needing
its own pass — `eligible3[]`'s reads were already independent of tier
2, nothing had to be restructured to get it.

Semantics preserved exactly as you described needing: same entry wins,
same tier order (tier 1 urgent-refresh/forced-PRE still beats tier 2/3,
tier 4 normal-refresh still only fires if neither tier found anything —
that outer 4-tier cascade is untouched, it was never the 16-deep part),
same first-come-lowest-index rule within a tier. `sel_onehot`/
`sel_onehot_r` (fix (a)) are untouched — the tree still produces a
binary `sel_idx`, decoded into `sel_onehot[sel_idx] = 1'b1` exactly like
the old loop did, so fix (a)'s registered one-hot read in
`recently_granted` needs nothing from this change. (Note: with both
tiers resolving concurrently, `eligible3[]`'s own per-entry reads are
independent of tier 2's result, so running them in parallel changes
nothing about which tier wins when both have a candidate — tier 2 still
wins, exactly as the old nested-loop gating enforced.)

**Out of scope, on purpose**: the bank-level loops in priority 1 (urgent
forced-PRE) and priority 4 (normal forced-PRE) are still a serial ripple
over `NUM_BANKS` (8, not 16 — `log2(8)=3` serial levels at most). Your
report's 19 failing endpoints all start at `entry_bank`, none at a bank
index, and those two loops are gated behind `ref_urgent`/`ref_required`
failing to go straight to REF, so they're not the thing you measured.
Left them as the existing ripple rather than touching something you
didn't ask about.

## 2. What I verified, since this is exactly the risk you named

"The off-by-one that would pick a different entry under a tie" — wrote
a Python model of both the old nested-loop logic and the new tree for
both tiers and ran them against: 200,000 random eligibility vectors (15%
density for tier 2, 30% for tier 3, independently randomized `we`/
`cond_pre`/`cond_act` per trial) — zero mismatches on `(valid, idx,
type)`, comparing only when `valid` is true (idx/type are don't-care
otherwise in both designs, same as the real RTL only writing
`sel_onehot[idx]` inside the `if`); every single-bit-set pattern (just
entry 0 eligible, just entry 1, ... just entry 15); the all-zero and
all-eligible cases. All in the model I ran, not just reasoned through.

Declaration order checked programmatically the same way as every prior
round this session — every new signal (`eligible3`, `act_cond_pre`,
`act_cond_act`, the 24 per-level tree arrays) has its first appearance
in the generated RTL at its own declaration, comments excluded.

`py_compile`, 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` all pass. Regenerated `scheduler_tb.sv` and confirmed it's
byte-identical — this change doesn't touch the module's interface,
latency, or FB_LAG masking (still 3 stages: pending `sel_*_r`, 1-cycle
`cmd_*`, 2-cycle `d1_*`), only how `sel_valid`/`sel_idx`/`sel_type` get
computed within the same cycle, so there's nothing for the testbench to
exercise differently. New drop `56ca186bf893`, `top_copy_mismatches`
clean.

**Not verified**: no local Xcelium or STA, so I can't confirm the tree
actually simulates correctly end-to-end or what it measures — same
limitation as every round this session. The Python model gives me
confidence the arbitration logic is equivalent, not that the generated
SystemVerilog elaborates to the same thing on your tools; that's the
usual gap your build closes.

## 3. Two things from your handoff I'm not touching, and why

**`sel_bank_eff_r`/fix (a)/(b)**: no change — you said chip-level (a)
alone is still the best measured scheduler and (b) should stay reverted.
Nothing in this round revisits that.

**`cas_spacing_ctr`**: you confirmed it's a destination, not a cause,
and said keep it. No change. It still loads off the un-registered
`sel_valid`/`sel_type` (not `sel_*_r`), same as before — the tree
rewrite doesn't change when those are available, so no update needed
there either.

## Questions

None blocking. Send it and tell us where the limiter lands — your
handoff was explicit that you won't predict it, and after two rounds of
the limiter moving somewhere neither of us expected, neither will I.
