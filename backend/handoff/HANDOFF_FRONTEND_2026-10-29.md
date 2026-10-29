# Handoff to Frontend — 2026-10-29 (loop break, measured)

From Backend (Dawson) to Frontend (Lehana), on drop `99f72da45a32`
(spec `d2f58e28c0d78d24`, the same spec content as `5f56adc7b7f5`, so this is a
like-for-like measurement of the loop break alone). Replies to
`Frontend2/HANDOFF_BACKEND_2026-10-27_2.md`. Nothing in `Frontend2/` was
changed by us.

Short version: **fix (a) worked completely. Fix (b) cost more than it bought.**
We would like to keep the first and drop the second, but there is a reason that
needs measuring rather than assuming — §4.

## 1. Results

Scheduler block, built at the manifest's 5.0 ns, DRC 0 violations and LVS match:

| scheduler | WNS @ 5 ns | Fmax | cells |
|---|---|---|---|
| original fr_fcfs | -0.915 | 169.1 MHz | 7,454 |
| + feedback-latency hold | -1.283 | 159.2 | 9,183 |
| + pipeline stage (`5f56adc7b7f5`) | **-0.426** | **184.3** | 7,771 |
| + loop break (`99f72da45a32`) | -0.620 | 177.9 | 8,641 |

Full chip, DRC 0 violations and LVS match throughout:

| ddr3_controller | WNS | Fmax | TNS | cells |
|---|---|---|---|---|
| `dab971c2aab9` | -1.044 | 165.5 MHz | -26.24 | 24,494 |
| `5f56adc7b7f5` | **-0.786** | **172.8** | -8.04 | 23,179 |
| `99f72da45a32` | -0.886 | 169.9 | **-7.47** | 24,227 |

TNS is the one number that still improved. Both drops have a single violating
endpoint, so the design is not broadly slow in either.

## 2. Fix (a) did exactly what it was meant to

`sel_idx_r` **does not appear anywhere in the chip timing report** — we grepped
it, zero hits. The 32-level self-loop that gated the chip is not shortened, it
is gone. Registering the one-hot decode instead of comparing against the index
removed the structure entirely, and it is free: nothing downstream got longer
because of it.

## 3. Fix (b) moved the mux out of the loop and into the forward cone

`sel_bank_eff = sel_from_queue ? q_bank[sel_idx] : sel_bank` is computed from
the **un-registered** `sel_idx`, which is what takes it out of the feedback
loop — correct, and what we asked for. But `sel_idx` is the output of the whole
priority-selection chain, so the 16-way mux is now in series with all of it.
It left the loop and joined the longest forward path.

Block, same startpoint both times:

| drop | worst path | levels | arrival | slack |
|---|---|---|---|---|
| `5f56adc7b7f5` | `q_bank[22]` -> `sel_type_r[0]` | 30 | 5.70 ns | -0.43 |
| `99f72da45a32` | `q_bank[45]` -> `sel_bank_eff_r[1]` | 32 | 5.96 ns | -0.62 |

Chip, where the loop used to be the limiter:

```
u_bank_tracker.ctr_rtp[33]  ->  u_scheduler.sel_type_r[2]
38 logic levels, arrival 6.78 ns, required 5.89, slack -0.886
```

That path was always there, behind the loop. It has not merely been uncovered,
though: in the previous build it must have been better than -0.786 or it would
have been the worst path then, so **(b) cost it at least 0.10 ns**. We cannot
give the exact before-figure — that build's timing report was overwritten — so
0.10 ns is a floor, not the measurement.

## 4. What we would like next, and why it is not simply "revert (b)"

Send us **(a) without (b)** and we will measure it.

We are not asking for a plain revert because (b) is not obviously redundant.
Without it, line 128 reads `q_bank[sel_idx_r]` again, feeding the inflight mask,
which feeds `is_cas_ready`, which feeds the selection that produces the next
`sel_idx_r` — so a loop through the mux comes back. The question is whether that
residual loop is shorter than the forward-cone cost (b) imposes. Our numbers
cannot answer it; only the variant can.

If it turns out the residual loop is the worse of the two, (b) stays and the
next move is on the `bank_tracker -> scheduler` path instead.

One block build plus one chip build is about 50 minutes on our side, so send it
whenever it is ready and we will turn it around the same day.

## 5. Two things we checked rather than took on trust

**The one-hot is genuinely one-hot.** Every `sel_onehot[i] = 1'b1` sits inside a
`!sel_valid` guard in the branch that sets `sel_valid`, so at most one bit can
set. Worth saying because if any of those guards had been missing,
`recently_granted` would have masked extra entries and this would have been a
functional bug wearing a timing fix's clothes.

**One corner where "value-equivalent" is an argument, not a measurement.** The
old code sampled `q_bank[sel_idx_r]` in the cycle *after* selection; the new
code samples `q_bank[sel_idx]` *during* selection and registers it. Those differ
only if that entry's bank changes across the pipeline boundary, which it should
not, since the entry is the pending pick. Jacob's sim on this exact RTL would
settle it; we only have timing.

## 6. A provenance nit on the top

`TOPRTL/manifest.json` still reads `generated_utc 2026-10-27T20:38:01`, but the
`scheduler.sv` it lists was rewritten at `02:08:55` the next day. The file
content is what synthesis reads, so the build was correct and we verified
`TOPRTL/scheduler.sv` byte-identical to `PHASE3RTL/scheduler.sv` before running.
But the top manifest under-reports its own drop, and anything keying on that
timestamp would conclude the top predates the fix.

## 7. Your flow.py backend stage: there was a third blocker, and it was ours

Your §4 flagged the SSL cert failure and the missing `PLATFORM`. Both are real.
Behind them sat one of ours, which you would have hit next:

our packager named the ORFS design **directory** after the bundle directory
(`TOPRTL`) while `DESIGN_NAME` in `config.mk` came from the **module**
(`ddr3_controller`). ORFS files results under `DESIGN_NAME`; our runner looked
for them under the directory name. For every block those are the same string
(`bundles/scheduler` holds module `scheduler`), so it never surfaced in a year
of block builds. The top is the one place they differ — and the failure mode is
nasty: the chip synthesises, routes and merges correctly, then reports
`final GDS not found` after about 25 minutes.

Fixed today. The two names are now resolved separately and `config.mk` is
written from the same resolved value, so they cannot drift again. We also made a
run that produces zero artifacts fail at the runner rather than pass the
emptiness downstream, which is how that build managed to look like `exit 0`.

So when your two environment problems are sorted, the backend stage should run
through. With Jacob's `flow.py` change routing timing failures to you, the
backend -> frontend edge is now live end to end.
