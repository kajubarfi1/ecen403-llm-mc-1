# Handoff to Frontend -- 2026-11-04: the tree worked, and the last 0.12 ns is ours

From Backend (Dawson) to Frontend (Lehana). The measurement on
`56ca186bf893`, as asked.

**The tree worked, and it is the best chip this project has produced on every
axis at once. We have no RTL ask for you this round.** The remaining gap looks
like a backend floorplan problem, not a frontend one, and we want to try our
side before sending you back into `scheduler.sv`.

## 1. The numbers

| metric | `ee9962151d05` (ripple) | **`56ca186bf893`** (tree) |
|---|---|---|
| WNS | -0.292127 | **-0.121629** |
| TNS | -2.648 | **-0.238** (-91%) |
| failing endpoints | 19 | **6** |
| Fmax (estimated) | 188.96! | **195.25!** |
| **cells** | 25,564 | **24,945** (-619) |
| core area um2 | 783,595 | 782,375 |
| power mW | 97.53 | 101.4 |
| DRC | 0 | **0** (396 s) |
| LVS | match | **match** (14,595 nets / 391 pins, 403/403 pins in layout) |

**0.122 ns from 200 MHz**, down from 0.353 at the previous best chip. The `!`
still applies -- 195.25 is 1000/(5 + 0.122), not a frequency any build has run
at.

**It is faster *and* smaller.** Two chained 16-deep first-match loops cost more
logic than two 4-level trees, so you took 619 cells out while taking 0.17 ns
off. Every previous timing fix on this project traded area for speed; this is
the first that improved both. It showed up at elaboration too -- 4,594 generic
cells against the ripple's 5,425 -- and survived synthesis.

## 2. The chain is actually gone, not merely shorter

This is the part that confirms the mechanism rather than just the outcome.

Under the ripple, all 19 failing paths started at the **deepest** queue entries
-- `entry_bank[46]`, `[34]`, `[29]` -- because entry 15 could not resolve until
all fifteen ahead of it had. The new limiter starts at **`entry_bank[7]`**,
which is entry 2.

A merely-shallower chain would still show the deep entries dominating. They do
not appear at all. Depth is now equalised across entries and what is left is an
ordinary path.

Supporting evidence from the flow itself: `repair_timing` at the global-route
stage took **20 seconds**, against 307 seconds on the broken 32-bit build. The
optimiser has almost nothing left to fix.

Remaining 6, all in `u_scheduler`: `sel_idx_r[0]` at -0.12, then
`sel_onehot_r[4]` -0.05, `[15]` -0.03, `[3]` -0.02, `[12]` and `[5]` -0.01.
Five of the six are inside the noise.

## 3. Your call to de-chain the tiers was right, and we checked it

You went past the ask and made tiers 2 and 3 resolve concurrently rather than
gating tier 3 behind tier 2 failing. We had said not to start there. You were
right that it fell out for free, and we verified the argument rather than taking
it:

`eligible3[i]` reads `is_act_needed[i]`, `q_bank[i]`, `bank_is_active`,
`bank_pre_allowed`, `bank_act_allowed` and the `inflight_*` flops.
`is_act_needed` is driven back in the earlier eligibility block from `q_valid[i]`
and bank state. **None of those are written anywhere in the tier-select
`always_comb`** -- tier 2 only writes `sel_valid`, `sel_idx`, `sel_onehot` and
`sel_type`. So the parallel form and the gated form select identically, and
`if (t2_valid) ... else if (t3_valid)` keeps tier 2 winning ties.

We also checked the two things a tree rewrite usually breaks:

- **Index selection** is a correct lowest-index-wins reduction at every level
  (`v_L1[0] ? idx_L1[0] : idx_L1[1]` prefers the left subtree whenever it has
  any candidate).
- **Type travels alongside index with the same select** at every level, so the
  PRE-vs-ACT decision follows the winning entry rather than being recomputed.
  That is the off-by-one shape we were most worried about and it is wired
  correctly.

`sel_onehot[t2_idx] = 1'b1` is unchanged, so fix (a)'s registered one-hot read
needs nothing, exactly as you said.

Leaving the priority-1 and priority-4 bank loops as serial ripples was also the
right scope call -- they are over `NUM_BANKS` (8), and none of our 19 reported
endpoints started at a bank index.

## 4. The last 0.12 ns looks like ours, not yours

We pulled the full path report before writing you an ask, and the ask
dissolved. From `entry_bank[7]/Q` at 1.42 ns to `sel_idx_r[0]/D` at 5.97 ns is
4.55 ns of logic and wire. Its composition:

| | |
|---|---|
| real logic gates | **14** |
| buffers | **6**, totalling **1.14 ns** |
| buffering as a share of the path | **25%** |
| launch clock insertion | 1.01 ns |
| capture clock insertion | 0.93 ns (net penalty only 0.08 ns) |

Two things follow. The clock is nearly matched here -- 0.08 ns of net penalty,
not the ~0.98 ns unmatched insertion that made `data_path_wr_data_ready` so
hard. And 14 logic levels for a cross-module path that still has to resolve a
16-way priority and mux is **reasonable**. We do not think there is another
0.12 ns of logic depth to find in it.

What is not reasonable is **a quarter of the path being buffers**. Six buffers
in a twenty-cell path means the path is crossing distance -- `cmd_queue` and
`scheduler` are sitting far apart on the die.

And that is our setting, not your RTL. The packager hardcodes
`CORE_UTILIZATION = 20`, and the build came in at **24.99%** -- the die is
roughly four times the area the logic needs, so the placer has no reason to pull
those two modules together.

We have direct evidence in this design that the lever works: between the 32-bit
build and DLW8 the die shrank 966,150 -> 801,884 um2 and the scheduler's
`sel_idx_r` loop improved **0.79 ns on byte-identical RTL**. Same mechanism,
opposite direction.

So: **we are going to sweep core utilisation before asking you for anything.**

Honest about the risk: higher utilisation means more congestion, and congestion
can cost more than the shorter wires save. There is a sweet spot and 20 may not
be miles from it. We are not promising this closes 200 MHz -- we are saying it
is the next thing to try, it is ours to try, and it would be wrong to send you
back into `scheduler.sv` for 0.12 ns before we have.

If the sweep stalls, we will come back with a measured ask rather than a
guess.

## 5. What we actually need now is Validation, not timing

Worth saying plainly, because it is a change in what the critical path *is*.

Nothing has simulated this RTL. Your 200,000-trial Python model shows the
arbitration is equivalent; our build shows it synthesises, routes, and is
physically correct (DRC 0, LVS match on 14,595 real nets). **Neither of those
shows the generated SystemVerilog behaves correctly end to end.** You flagged
exactly this gap -- "I can't confirm the tree actually simulates correctly" --
and you were right to.

At 6 failing endpoints and -0.12 ns, the larger risk to sign-off is now a
functional regression in the selection logic, not the clock period. The tree
touches how every command gets chosen. We would rather Jacob exercise it than
spend another round shaving picoseconds.

## 6. Two caveats for the record

**Power gave back the countdown drop's win.** 97.53 -> 101.4 mW, about 4%.
Expected, and the right trade: the tree evaluates all 16 eligibility terms
unconditionally where the ripple short-circuited on the first match, so more
logic toggles per cycle. But it means this project's best timing number and
best power number are now different builds, and we should stop quoting them as
if one chip held both. Power optimisation is still a terminal stage, after
timing closes.

**Everything we report is single-corner.** The platform ships one liberty file,
`sky130_fd_sc_hd__tt_025C_1v80.lib` -- *typical* process, 25 C, 1.80 V. We do
not run slow or fast corners, voltage or temperature sweeps. So -0.12 ns is a
typical-corner result, not a silicon-ready one; a slow-corner number would be
meaningfully worse. Nothing to do on your side, but we should all say "at the
typical corner" rather than let 195 MHz travel on its own.

## Summary

| | status |
|---|---|
| Priority chain -> tree | **done, measured, worked** -- faster and 619 cells smaller |
| Tier de-chaining | **right call**, verified semantically equivalent |
| Remaining -0.12 ns | **ours** -- floorplan utilisation sweep, no RTL ask |
| `bank_tracker` registration | still parked |
| CAS spacing guard | keep |
| Functional simulation of the tree | **the real open item**, Validation |

Nothing blocking on us, and nothing we need from you this round. Thank you for
the verification work -- checking `(valid, idx, type)` rather than just the
index is what let us review this by inspection instead of asking for another
pass.
