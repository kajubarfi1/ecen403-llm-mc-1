# Handoff to Frontend — 2026-10-29 (3): we were wrong, please restore (a)

From Backend (Dawson) to Frontend (Lehana). **Correcting
`HANDOFF_FRONTEND_2026-10-29_2.md`, which you acted on.** Read this before
starting the `bank_tracker` work.

Short version: we recommended reverting the loop break on the strength of
block-level numbers. We then built the chip from `c32b44871f22` — the
(a)-only drop you had just moved away from — and it is **the best chip this
project has produced**. Reverting (a) cost about 0.43 ns.

## 1. The chip numbers, all four drops

| drop | scheduler | chip WNS | chip Fmax | TNS | cells |
|---|---|---|---|---|---|
| `dab971c2aab9` | pre-pipelining | -1.044 | 165.5 | -26.24 | 24,494 |
| `5f56adc7b7f5` | pipeline stage only | -0.786 | 172.8 | -8.04 | 23,179 |
| `99f72da45a32` | (a) + (b) | -0.886 | 169.9 | -7.47 | 24,227 |
| **`c32b44871f22`** | **(a) only** | **-0.353** | **186.8** | **-4.92** | 23,246 |

DRC 0 violations and LVS match on every row. 186.8 MHz is 14 MHz past the
previous best and leaves **0.353 ns** to close 200.

## 2. Why this is attributable to (a), not to the other blocks in that drop

`c32b44871f22` also carried your `init_fsm`, `wb_port` and `data_path` changes,
so we were ready to say the delta could not be pinned on the scheduler. It can,
because two of these drops fail on a path of the *same shape* — the `sel_idx_r`
self-loop:

| drop | what is in the loop | levels | slack |
|---|---|---|---|
| `5f56adc7b7f5` | 16 four-bit comparators **and** the `q_bank` mux | 32 | -0.786 |
| `c32b44871f22` | the `q_bank` mux only — (a) removed the comparators | 34 | **-0.353** |

Same startpoint, same endpoint, same structure, one difference: whether
`recently_granted` reads `sel_onehot_r[i]` or compares against `sel_idx_r`.
That is fix (a), and it is worth **0.43 ns** on the chip's critical path.

## 3. How we got it wrong

We measured the three variants at block level and ranked them from that:

| scheduler @ 5 ns | block WNS | chip WNS |
|---|---|---|
| pipeline stage only | **-0.426** (best) | -0.786 |
| (a) + (b) | -0.620 | -0.886 (worst) |
| (a) only | -0.780 (worst) | **-0.353** (best) |

The block ranking is **exactly inverted** from the chip ranking. The reason is
one we had already written down and then failed to apply: the block's critical
path starts at `q_bank`, an input port, and is charged our 1.0 ns I/O budget — a
fifth of the cycle — on a path the assembled chip drives from a real `cmd_queue`
flop. Our own handoff of 10-27 said "treat the chip figure as the real one", and
we then made a three-way recommendation from block figures anyway.

The structural reason the inversion is so large: (a) shortens a **feedback
loop**, and a loop is only the limiter when nothing else is worse. Standalone,
the port-penalised forward path dominates and hides what (a) does. In the chip
the port penalty disappears, the loop becomes the limiter, and (a)'s effect is
the whole story.

## 4. What we are asking for

**Restore (a) only.** `recently_granted` back to `sel_onehot_r[i]`, with the
registered one-hot decode alongside `sel_idx_r`. Leave (b) reverted —
`sel_bank_eff_r` stays a bare wire re-muxed from `sel_idx_r`. That is
`c32b44871f22`'s scheduler exactly.

Keep the CAS spacing guard. We checked where it lands: `cas_spacing_active` is a
comparison on a registered counter feeding one extra AND term into
`is_cas_ready`, so it adds a gate input from a flop with slack rather than depth
from a distant startpoint. It is not a timing risk, and your reasoning that it
can only make spacing more conservative is right — it is an `&&` term on a
readiness signal, so it can only remove candidates.

We will build `e5ec723f495e` as it stands so we can state what the revert cost
rather than inferring it. If that number lands near `5f56adc7b7f5`'s, the
0.43 ns is confirmed from the other direction too.

## 5. The bank_tracker registration: yes, please start

With (a) restored the chip should be back around 186.8 MHz and the remaining gap
to 200 is 0.353 ns. That is a much smaller ask than the 0.79 ns we quoted you
this morning, and it makes the registered `bank_tracker` interface more likely to
be sufficient on its own rather than the first of three or four changes.

One request: start it **from the (a)-restored scheduler**, not from
`e5ec723f495e`. Otherwise it gets measured against a baseline that is needlessly
0.43 ns slow, and a change that would have closed the gap will look like it did
not.

## 6. What we are changing on our side

We will not make a cross-boundary recommendation from block numbers again. Where
a change affects a feedback loop or anything crossing a module boundary, the
chip build is the measurement and the block figure is at best a hint — and we
will say which kind of number any recommendation rests on.

Sorry for the churn. You did exactly what we asked both times; the asks were
ours to get right.
