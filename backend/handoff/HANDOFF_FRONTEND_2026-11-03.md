# Handoff to Frontend -- 2026-11-03: countdown measured, best chip yet, one thing left

From Backend (Dawson) to Frontend (Lehana). The measurement you asked for on
`ee9962151d05` -- "no local synthesis or STA, so the flop count and timing
improvement are my own structural accounting, not a measurement -- that's the
thing I most want from your side."

Here it is, and your accounting was right.

**Both changes worked. This is the best chip the project has produced, and
`data_path` is now completely clean.** One structural item remains, in a
different module.

## 1. The numbers

Built `ee9962151d05` from `Frontend2/OutputFolders/TOPRTL`. 31 minutes end to
end -- the smaller design routes much faster than the bloated one did.

| metric | `2bea54c5eac1` (32-bit) | DLW8 (our 8-bit probe) | **`ee9962151d05`** |
|---|---|---|---|
| WNS | -1.4169 | -0.80481 | **-0.292127** |
| TNS | -348.629 | -4.248 | **-2.648** |
| Fmax (estimated) | 155.84! | 172.27! | **188.96!** |
| cells | 29,741 | 25,423 | 25,564 |
| core area um2 | 966,150 | 801,884 | **783,595** |
| power mW | 108.0 | 110.3 | **97.53** |
| DRC | 0 | 0 | **0** |
| LVS | match | match | **match** (15,207 nets / 391 pins) |

Against the previous best chip (`c32b44871f22`, -0.353 / 186.8 MHz) this is
better on WNS and on estimated Fmax. We are **0.292 ns** from closing 200 MHz.

The `!` still applies: 188.96 is 1000/(5 + 0.292), a frequency no build has run
at. Nothing has closed 200 MHz yet.

**The power number is the quiet win.** 97.53 mW is about 10% below every chip
we have built, and it is the first real power improvement of the project.
Deleting ~959 flops that were toggling every cycle did that -- the two
free-running 32-bit counters especially, since those switched unconditionally
whether or not any transfer was in flight. You removed them rather than
narrowing them, which we had not asked for and which is where a good part of
this came from.

## 2. data_path is clean -- zero failing endpoints

`data_path_wr_data_ready` appears **zero times** in the finish report. Across
the three builds, `u_data_path`'s failing endpoint count went **844 -> 111 ->
0**. There is nothing left in that module.

**Your open question, answered: the WR_DRIVE chaining path does not need
registering.** You left `wr_pend_wait[rptr] <= 1` combinational there, flagged
it as the thing you would go back for, and kept the verification harness ready.
You do not need it. Narrowing that read from 32 bits to 4 was enough on its own
-- the 32-bit mux and the 32-bit magnitude compare were nearly all of those 30
logic levels, so once they shrank, the path stopped mattering even unregistered.
Your judgment to stop there was correct, and the effort you declined would have
bought nothing.

**And a concern of ours did not materialise.** Before building, we flagged that
`wr_head_due_r`'s update now traverses two serial array muxes --
`wr_pend_wait[wr_pend_rptr]` feeds `wr_pop_this_cycle`, which feeds
`wr_pend_head_idx_next`, which indexes `wr_pend_wait` a second time. We thought
it might become the new limiter. It does not appear in the violators at all.
The reason we gave for why it probably would not is what happened: you moved
that computation off the output port's 4.0 ns budget onto the full ~4.9 ns
register-to-register budget. The logic got *longer* and has more room than
before. That is the right trade and we would not change it.

## 3. What is left: all 19 failures are one path, in the scheduler

TNS -2.648 over 19 failing endpoints. Every one is in `u_scheduler`, from -0.29
down to -0.01. And every one **starts at `u_cmd_queue.entry_bank[*]`** -- 15 of
the 19 from bit 46 alone, the rest from 34 and 29, all high-numbered bits of the
flattened `[16] x 3` array, i.e. the deepest queue entries.

| endpoint | slack |
|---|---|
| `sel_type_r[0]` | **-0.29** |
| `sel_idx_r[3]` | -0.24 |
| `sel_idx_r[0]` | -0.23 |
| `sel_idx_r[2]`, `sel_type_r[2]` | -0.21 |
| `sel_onehot_r[4]` | -0.20 |
| `sel_idx_r[1]` | -0.19 |
| `sel_bank_r[0..2]` | -0.18 .. -0.17 |
| `sel_onehot_r[1]`, `[9]` | -0.16, -0.15 |
| `sel_is_ref_r` | -0.08 |
| `cas_spacing_ctr[1]` | -0.07 |
| `sel_onehot_r[2]`, `[3]`, `[13]`, `[14]`, `sel_from_queue_r` | -0.03 .. 0.00 |

This is **one structural cause, not 19 problems**: a single slow source fanning
out into the scheduler's whole selection register set.

It is the 16-deep serial priority chain, which we first wrote up on 2026-09-29
and which has never been the limiter until now because the scheduler loop and
then `data_path` were always worse. It is the only thing left.

The mechanism, concretely. The selection scans are written as sequential
first-match loops:

```systemverilog
if (!sel_valid) begin
    for (int i = 0; i < DEPTH; i++) begin
        if (cond[i] && !sel_valid) begin
            sel_valid = 1'b1;
            sel_idx   = i[IDX_BITS-1:0];
            ...
        end
    end
end
```

Iteration `i`'s condition reads `!sel_valid`, which depends on every earlier
iteration, so synthesis unrolls it into a 16-level serial chain. Priority 2
(row-hit CAS, line 306) and Priority 3 (ACT for row-miss, line 316) each contain
one, and they are chained to each other by `if (!sel_valid)` at line 315. Two
chained 16-deep scans is **32 serial decision levels** -- and STA reports the
worst path at exactly `levels=32`. That is why entry 15's bank bits are the
startpoint: that entry's eligibility cannot resolve until all fifteen ahead of
it have.

## 4. The ask: make the priority reduction a tree

The per-entry work is **already independent**. Each iteration computes
`b = q_bank[i]` and then reads `bank_is_active[b]`, `bank_pre_allowed[b]`,
`inflight_any[b]` -- none of which depend on any other `i`. Only the
"first one wins" arbitration is serial.

So: compute an `eligible[DEPTH]` bit vector for each priority tier in parallel
(all 16 at once, which the current code already effectively does for the bank
lookups), then resolve lowest-set-index with a balanced reduction tree instead
of a ripple. That takes the arbitration from 16 levels to log2(16) = 4, per
tier.

This should be semantics-preserving: same entry selected, same tier order,
same first-come-lowest-index rule, no protocol change, no extra cycle. It is a
rewrite of *how* the winner is found, not of *which* entry wins -- which is
the property worth getting your verification harness onto, since it is exactly
the kind of change where an off-by-one in the tree would pick a different
entry under a tie.

**Scope note:** this is a `scheduler.sv` change. `cmd_queue` is only the
startpoint because `entry_bank` is what the chain consumes -- nothing is wrong
in `cmd_queue` and it should not need touching. We mention it only because the
STA report names it, and we did not want you chasing it.

A tier-level option if the tree is not enough on its own: Priority 2 and
Priority 3 are chained, so their 32 levels are serial. If each tier's winner
were computed independently and the tier choice resolved at the end, the two
scans would run concurrently and the depth would be one tier's, not two. That
is a larger change and we would not start there -- the tree alone may well be
sufficient for 0.292 ns.

## 5. CAS spacing guard: still not the problem

`cas_spacing_ctr[1]` does now appear in the violator list, at -0.07. For the
avoidance of doubt: it is a **destination**, fed from `entry_bank[46]` like the
other eighteen. It is downstream of the same slow source, not a cause of
anything, and -0.07 is the second-smallest violation on the chip.

We have defended this guard twice from static reasoning. This is the first
build where its own counter shows up in a report, and it still is not the
issue. Keep it.

## 6. Caveat on the remaining 0.292 ns

We are not going to tell you the tree closes 200 MHz. Removing the worst
endpoint leaves `sel_idx_r[3]` at -0.24, but all 19 of these paths share one
startpoint, so fixing the chain should lift the whole cluster at once rather
than peeling them off one at a time -- which is a better position than 19
independent problems would be.

What we will not predict is where the limiter lands afterward. Twice now the
limiter has moved somewhere neither of us was looking, and this design has
shown 0.79 ns of slack movement on byte-identical RTL from die-size change
alone. The chip build is the measurement. Send it and we will run it.

## Summary

| | status |
|---|---|
| Saturating countdown | **done, measured, worked** -- 99.2% of TNS gone across the two steps |
| Registered due flag | **done, measured, worked** -- output port gone from violators |
| WR_DRIVE chain path | **not needed** -- leave it combinational |
| CAS spacing guard | keep |
| `bank_tracker` registration | still parked |
| Priority chain -> tree | **the one remaining ask** |

Nothing is blocking on us. `data_path` is closed out as far as timing goes --
thank you for the verification work on it, the Python model against both CL
extremes is what let us build this without a correctness re-litigation first.
