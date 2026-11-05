# Handoff to Frontend -- 2026-11-05: 200 MHz closed. The floorplan sweep did it.

From Backend (Dawson) to Frontend (Lehana). This closes the promise at the end
of `HANDOFF_FRONTEND_2026-11-04.md` -- "we are going to sweep core utilisation
before asking you for anything... if the sweep stalls, we will come back with a
measured ask rather than a guess."

It did not stall.

**The 200 MHz spec target is MET. `PIPELINE STATUS: PASS`, DRC 0 violations,
LVS netlists match on 14,398 real nets. No RTL change -- your drop
`56ca186bf893` is byte-identical across all four builds below.** This is the
first full sign-off PASS the project has produced.

Two things to read before celebrating too hard. Section 6: the margin is 22
picoseconds at one corner. Section 7: validation pushed twice while this was
being written -- the tree **simulates clean and two scheduler formal findings
are now closed**, but the newest run reports FAIL on `config_regs` and we think
that is a spec-label mismatch rather than a defect. Jacob needs to settle it.

## 1. The sweep

Four full-chip builds, one floorplan setting changed between them, RTL
`cmp`-verified identical each time.

| point | achieved util | WNS | TNS | area um2 | cells | power mW | DRC | LVS | STA |
|---|---|---|---|---|---|---|---|---|---|
| util 20 (11-04) | 24.99% | -0.121629 | -0.238 | 782,375 | 24,945 | 101.365 | 0 | match | **FAIL** |
| util 30 | 36.50% | **+0.0197744** | **0** | 520,893 | 21,340 | 99.372 | 0 | match | **PASS** |
| **util 35** | **42.09%** | **+0.0219957** | **0** | **445,715** | **20,183** | **99.4557** | **0** | **match** | **PASS** |
| util 40 | 47.55% | -0.0177485 | -0.025 | 389,674 | 19,293 | 98.2976 | 0 | match | FAIL |

**The curve has a peak and we found it.** 30 and 35 both close; 40 goes back
negative. The top is nearly flat -- 30 and 35 are 2.2 ps apart, which is noise,
not a difference.

**We recommend util 35 as the sign-off configuration.** Not because it is
faster -- on timing it ties 30 -- but because it is **14.4% smaller at equal
timing and equal power** (445,715 vs 520,893 um2). Its clock skew is also
slightly better, 0.12 ns against 0.16 ns.

Against the util-20 build you last saw: **43% less die area and 19% fewer cells,
on identical RTL.** Most of that is fill cells rather than logic -- a smaller
die needs less filler -- but the cell count drop is real logic the optimiser no
longer has to insert.

## 2. Why this worked, and the evidence that it is the mechanism we claimed

The 11-04 handoff argued the remaining 0.12 ns was **distance, not logic depth**:
1.14 ns of that 4.55 ns path was six buffers against only 14 real logic gates,
with the clock near-matched at 0.08 ns of net penalty. The claim was that
`cmd_queue` and `scheduler` were sitting far apart on a die roughly 4x the area
the logic needed, and that pulling them together was a backend lever, not an
RTL one.

The confirmation is not the WNS number. It is **where the limiter went.**

| point | worst path | slack |
|---|---|---|
| util 20 | `u_cmd_queue.entry_bank[7]` -> `u_scheduler.sel_idx_r[0]` | -0.1216 |
| util 30 | `u_cmd_queue.entry_bank[4]` -> `u_scheduler.sel_onehot_r[6]` | +0.0198 |
| **util 35** | `u_scheduler.sel_idx_r[1]` -> `u_scheduler.sel_onehot_r[12]` | **+0.0220** |
| util 40 | `u_scheduler.sel_idx_r[1]` -> `u_scheduler.sel_type_r[0]` | -0.0177 |

At util 20 and 30 the limiter is the **cross-module** `cmd_queue` -> `scheduler`
crossing. At util 35 and 40 it is **entirely inside `u_scheduler`** -- a local
register-to-register path.

The cross-module crossing is no longer the critical path at all. That is what
"the modules were too far apart" predicts if it is true, and it is not what a
generic "more optimisation effort" explanation would predict. The startpoint
also marched down the queue as the die shrank -- `entry_bank[7]` (entry 2) to
`entry_bank[4]` (entry 1) -- consistent with the tree having already equalised
depth across entries, as we reported on 11-04.

Precedent held too. We cited the 966,150 -> 801,884 um2 shrink buying 0.79 ns on
byte-identical RTL. This is the same mechanism, deliberately: 782,375 ->
445,715 um2 bought 0.144 ns.

## 3. What this means for your side: nothing, and that is the point

**No RTL ask.** Not "none this round" as a holding position -- the chip meets
spec on the RTL you already shipped. The tree drop `56ca186bf893` is the
sign-off RTL.

The two items you have parked stay parked and are now parked for a better
reason than before:

- **`bank_tracker` registration** -- still not the limiter, and now there is no
  limiter to beat. Every `bank_tracker` endpoint passes.
- **CAS spacing guard** -- keep. Nothing in four builds implicates it.
- **WR_DRIVE chain path** -- stays combinational. `data_path` has zero failing
  endpoints and did not appear in any violator list across the sweep.

If frequency ever becomes the ask again, the honest next target is the one the
table above names: **`sel_idx_r` -> `sel_onehot_r` / `sel_type_r` inside the
scheduler, which STA measures at 28 logic levels.** That is the one-hot decode
and type mux downstream of the registered index. We are *not* asking for it. We
are writing it down so that if someone asks "where would the next nanosecond
come from," the answer is already measured rather than guessed.

## 4. A prediction of ours that was wrong

We expected util 40 might fail to **route** -- that congestion at 47.55%
occupancy would break physical closure. It did not. **DRC 0 violations, LVS
match on 14,221 nets, 403/403 pins in layout.** It built cleanly and lost on
*timing*: congestion cost delay on the scheduler's internal path rather than
making the design unbuildable.

Worth recording because it changes what the failure mode at high utilisation
actually is. There is no routability cliff anywhere in 20-40% for this design;
there is a gradual delay cost that crosses zero slack somewhere between 35 and
40. If we ever sweep again, the thing to watch is slack, not DRC.

## 5. What the Fmax figures do and do not mean

The flow reports `core_clk period_min = 4.98, fmax = 200.88` for util 35. Our
marking convention applies to us:

- **200.00 MHz is demonstrated.** A build ran at a 5.0 ns constraint, closed
  timing, and signed off DRC and LVS. That is a frequency this chip has
  actually met.
- **200.88 MHz is estimated** (`*`). It is OpenSTA's `report_clock_min_period`
  extrapolating from this build's slack. No build has run at a 4.98 ns
  constraint, and the optimiser behaves differently when you ask it for a
  tighter period, so 200.88 is not a result.

The difference is 0.88 MHz and nobody should care about it. We are being
pedantic because we have asked you to read our `!` and `*` marks all project and
should not drop the habit the one time the number is good.

## 6. The caveat that matters: 22 picoseconds, one corner

This is the part to carry into any slide or report, and it is a deliberate
decision not to chase it further.

**The margin is 0.022 ns on a 5.0 ns period -- 0.44%.** util 30's is 0.0198 ns.
Both are hairline. TNS is exactly 0, so nothing fails, but nothing has room
either.

**And every number in this document is single-corner.** The platform ships
exactly one liberty file, `sky130_fd_sc_hd__tt_025C_1v80.lib` -- *typical*
process, 25 C, 1.80 V. There is no slow corner, no fast corner, no voltage or
temperature sweep available to us. A slow-corner build would be meaningfully
worse than typical, and 22 ps of typical-corner margin would not survive it.

So the correct claim is: **"the design closes 200 MHz at the typical corner with
DRC and LVS clean."** Not "the design runs at 200 MHz." We should all say it the
long way.

This is also why we are **not** running an Fmax sweep to find the ceiling. We
could probably push the constraint to 4.8 or 4.9 ns and close something -- this
project has shown the optimiser works *to* the constraint rather than to a fixed
intrinsic delay (the scheduler block hit 9.11 ns under a 10 ns constraint and
5.95 ns under a 5 ns one, so leftover slack at 5.0 does not bound what closes
at 4.8). But buying a frequency we have 20 ps of margin on, at one corner, is
not worth the builds. **Margin at spec is the open exposure, not speed above
spec.** If we spend compute on timing again it should go toward margin at 200
MHz, not toward 210.

## 7. Validation moved twice while we were writing this

Two pushes landed during this write-up -- `b83b87c` at 00:32 and `f7d2d02` at
17:14. They point in opposite directions and the second one needs a decision
from Jacob before anyone quotes a validation status. Here is the state as we
read it.

### The simulation gap is closed, and the scheduler is clean in both runs

**The tree simulates.** In the 00:32 run all 23 paths PASS. Better than that,
the drop comparison against `2bea54c5eac1` -- which predates *both* the
saturating countdown and the tree -- shows **22 of 23 paths produced
byte-identical observed transaction streams** (`kind: "same"`). The only one
that moved is `path_21_wb_port_standalone`, from the HOST_001 work, and it still
passes.

Two substantial RTL rewrites, and **no observable behavioural change on any
scheduler path**: `path_04_scheduler_bank_loop`,
`path_05_scheduler_refresh_loop`, `path_06_scheduler_dequeue`,
`path_19_row_conflict` and `path_20_refresh_preempt` all come back `same` /
`pass`. Your 200,000-trial Python model predicted the tree was
arbitration-equivalent; the simulator agrees on real stimulus through the full
chain. All five still pass in the 17:14 run too.

Your model, four chip builds, and Jacob's paths now agree. The item we have
been carrying since 11-03 is closed.

### Two critical findings got closed by formal

`SIGNOFF.md` records a 60-minute concrete JasperGold run on this design:
**12 properties proven at infinite bound, and `PROTO_001` and `TIMING_008` are
closed.** Those are the two scheduler findings -- READ-after-PRE without an
intervening ACT, and PRE-after-WRITE violating tWR. Both are gone from the
ledger.

`HOST_001` remains open at `awaiting_formal`, now with no counterexample against
the corrected 968-cycle bound (the old 254-cycle counterexample was against the
old bound). `PROTO_002` is undetermined at 67. Neither is a scheduler item.

### The 17:14 run reports FAIL, and we think the label is wrong

`findings/outbox/current/HANDOFF.json` now reads `"status": "FAIL"`,
`"failed_modules": ["config_regs"]`, with 4 of 23 paths failing --
`path_10_csr_to_timing`, `path_11_csr_to_refresh`,
`path_12_csr_timing_to_scheduling`, `path_13_csr_refresh_to_scheduling` -- and
7 new `minor` config_regs mismatches, all `first_seen: 56ca186bf893`.

**We do not think this is a defect in the drop, and the arithmetic is clean
enough to be worth your five minutes.**

The headline mismatch:

```
expected  cfg_refresh.update ... trefi=0x1860 ...     (6240)
actual    cfg_refresh.update ... trefi=0x1450 ...     (5200)
```

6240 / 5200 = **1.2 exactly**. And both values decode:

| | clock | tREFI 7.8 us | x window_scale 4 |
|---|---|---|---|
| DDR3-1600 (1600/8 = 200 MHz, 5.0 ns) | 5.0 ns | 1560 | **6240 = 0x1860** = `expected` |
| DDR3-1333 (1333/8 = 166.67 MHz, 6.0 ns) | 6.0 ns | 1300 | **5200 = 0x1450** = `actual` |

Both sides land exactly on a speed bin. This is not a counter that is slightly
off; it is **two different speed grades being compared to each other.**

The corroboration is in the same push. `txn/generated/schemas.json` was
regenerated and now declares:

```
spec_source   : ddr3_mc_1333_x8_2lane_1rank
spec_revision : compiled_ddr31333_x8_2lane_1rank_1ebcc694
manifest      : runs/matrix/preset_balanced/drop/PHASE1RTL/config_regs_manifest.json
```

while `HANDOFF.json` and `DROP_STATUS.json` from the same commit still claim
`golden_ddr3_1600k_x8_2lane_1rank` and `spec_id 00d082c3f72d1b34`.
`revision_ids.json` gives the 1333 spec a different id, `d4550ccb88541f32`.

So the most likely reading: **the 17:14 run is a spec-matrix run on the new
DDR3-1333 `preset_balanced` spec** (`spec/spec_matrix.json` and
`tools/spec_matrix.py` are both new in this push, built 02:09 today), and its
results were written into `current/` and archived under the *golden 1600*
directory carrying the golden label. The config_regs mismatch would then be
stimulus from one spec checked against expectations from the other -- a harness
bookkeeping inconsistency, not an RTL bug.

**That is a hypothesis, not a conclusion, and it is Jacob's to settle** -- he
can check which spec the harness elaborated in one command and we cannot. We
are flagging it because the alternative reading is that drop `56ca186bf893`
genuinely regressed config_regs between 00:32 and 17:14 on byte-identical RTL,
which is not possible, so something in the labelling has to give.

Two things we are confident of either way:

1. **No scheduler, cmd_queue or data_path path fails in either run.** All four
   failures are CSR-timing-programming paths. Whatever this is, it is not the
   tree and not the countdown.
2. **It does not touch the backend result.** The chip was built from `TOPRTL` at
   `56ca186bf893`, the netlist is what it is, and DRC/LVS/STA are measurements
   on that netlist. A spec-label question upstream does not move 22 ps of slack.

### One thing the spec matrix does imply for us

If the matrix becomes part of the bar -- and a greedy pairwise cover over speed
grade, density, width, ranks, lanes and ECC mode is a lot of specs -- then note
that **the backend has only ever built the golden DDR3-1600 spec.** Every number
in this document is that one spec at one corner. A DDR3-1333 drop would want a
6.0 ns constraint rather than 5.0, which we would expect to close with far more
margin than 22 ps, but we have not built it and will not claim it.

That is worth deciding deliberately rather than discovering at the end, and it
is squarely the full-pipeline integration question rather than a frontend one.

## 8. Two housekeeping notes

**Power is unchanged and is now the next optimisation target.** 99.46 mW at
util 35, against 101.37 at util 20 -- a 1.9% improvement that came free with the
smaller die, not from any power work. Power optimisation has been deferred
project-long behind timing closure. Timing is now closed, so for the first time
it is actually available. Nothing for you to do; noting that the ordering
constraint we have cited all project no longer applies.

**How to reproduce.** The sweep driver is
`experiments/sweep_utilization.sh` in the backend tree (not in this repo). It
re-stages fresh from `Frontend2/OutputFolders/TOPRTL` and `cmp`-verifies every
`.sv` against the drop before each build, so a stale bundle cannot silently
produce a number. The only injected difference is
`manifest.orfs_config.CORE_UTILIZATION`. Points must run sequentially -- every
bundle shares the module name `ddr3_controller` and ORFS keys its results path
on `DESIGN_NAME`, so two concurrent builds would overwrite each other.

## Summary

| | status |
|---|---|
| **200 MHz spec target** | **MET** -- `56ca186bf893` at CORE_UTILIZATION 35 |
| DRC | **PASS**, 0 violations (280 s) |
| LVS | **PASS**, 14,398 nets / 391 pins, 403/403 pins in layout, 0 wrong pairings |
| STA | **PASS**, WNS +0.0220 ns, TNS 0 |
| Sign-off configuration | **util 35** -- ties util 30 on timing, 14% smaller |
| RTL ask | **none** -- the shipped tree drop meets spec unmodified |
| Remaining margin | **22 ps, typical corner only** -- the real exposure |
| Fmax sweep above 200 MHz | **declined** -- margin matters more than headroom |
| Next RTL target *if ever needed* | `sel_idx_r` -> `sel_onehot_r`/`sel_type_r`, 28 levels |
| Functional simulation of the tree | **PASS** -- 23/23 at 00:32, 22 byte-identical to the pre-tree drop |
| Scheduler formal findings | **`PROTO_001` and `TIMING_008` CLOSED** by the 60-min concrete run |
| Open critical findings | **1** -- `formal/wb_port/HOST_001`, `awaiting_formal`, not a scheduler item |
| 17:14 run reporting FAIL on config_regs | **likely a spec-label mismatch** (1600 vs 1333) -- Jacob's to settle, section 7 |

The tree is what closed this. Two chained 16-deep ripples would not have gotten
to 0.12 ns no matter what we did to the floorplan, and the floorplan lever only
worked because you had already taken the logic depth out. Thank you for going
past the ask on the tier de-chaining -- that one was yours, not ours.
