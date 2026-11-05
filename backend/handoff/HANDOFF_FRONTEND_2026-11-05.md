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
picoseconds at one corner. Section 7: Jacob's validation run landed while we
were building this and the tree **simulates clean, 23/23 paths** -- but three
critical formal findings are still open in the ledger.

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

## 7. Validation landed while we were building this. The tree simulates.

Jacob pushed `b83b87c` -- a complete validation run on `56ca186bf893` -- a few
hours before this was written. It answers the question the last two handoffs
have been carrying as the open item, and it answers it well.

**All 23 paths PASS.** 20 runnable paths simulated, 3 derived paths taking their
verdict from their host run, 0 blocked, no module failed. `HANDOFF.json` reports
`"status": "PASS"`, `"failed_modules": []`, and `DROP_STATUS.json` records
"complete run: every runnable path simulated on this drop."

**The stronger result is in the drop comparison.** Against `2bea54c5eac1` --
which predates *both* the saturating countdown and the tree -- **22 of the 23
paths produced byte-identical observed transaction streams** (`kind: "same"`).
The only path that changed at all is `path_21_wb_port_standalone`, from the
HOST_001 work, and it still passes.

That means two substantial RTL rewrites in a row produced **no observable
behavioural difference on any scheduler path** -- `path_04_scheduler_bank_loop`,
`path_05_scheduler_refresh_loop`, `path_06_scheduler_dequeue`,
`path_19_row_conflict` and `path_20_refresh_preempt` all come back `same` /
`pass`. Your 200,000-trial Python model predicted the tree was
arbitration-equivalent. The simulator now agrees with it on real stimulus
through the full chain. That is about as direct a confirmation as this project
can produce.

So: your Python model, the four chip builds, and Jacob's 23 paths now agree. The
gap we have been flagging since 11-03 is closed.

### What is still open, and why it is not yours

Three findings remain in the ledger, all `severity: critical`:

| id | module | status | first seen |
|---|---|---|---|
| `formal/scheduler/PROTO_001` | scheduler | `awaiting_formal` | drop `1fea117` |
| `formal/scheduler/TIMING_008` | scheduler | `awaiting_formal` | drop `1fea117` |
| `formal/wb_port/HOST_001` | wb_port | `awaiting_formal` | drop `99f72da45a32` |

Four things about these, because two of them name `scheduler` and that will
look alarming next to a tree rewrite:

1. **None are tree-introduced.** All three have `first_seen` on drops that
   predate `56ca186bf893`, and `confidence: unverified` with
   `status: awaiting_formal` -- they are carried forward from earlier JasperGold
   runs and are awaiting re-prove on this drop, not newly found on it.
2. **All three are formal-only.** `detectors: ["formal:jaspergold"]`, and each
   one's mechanism says explicitly it was never reached in simulation. They are
   counterexamples under a free protocol-legal host, in interleavings no path
   stimulus produces.
3. **The two scheduler ones are anchored to `PHASE3RTL/scheduler.sv` and
   `PHASE2RTL/bank_tracker.sv`**, not to the `TOPRTL` tree we built. Worth
   someone confirming which tree the formal harness actually elaborated before
   anyone acts on them.
4. **They are bank-state and timing-protocol issues, not arbitration issues.**
   PROTO_001 is a READ one cycle after a PRE to the same bank with no ACT
   between; TIMING_008 is a PRE one cycle after a WRITE to the same bank
   (tWR). Both are about whether `bank_tracker` gating lets a command through,
   which is a different question from which entry the tree selects.

Note also that Jacob's own `SIGNOFF.md` §2 defines Drop PASS as every path
passing **and** no critical finding open. His tooling issued PASS with these
three sitting at `awaiting_formal`, which is a defensible reading -- unverified
is not confirmed -- but it is a judgement call, not an arithmetic one, and
somebody should say out loud which reading the final report uses. We are not
the right people to decide that; we are flagging that it needs deciding.

**Nothing here is a backend ask or, as far as we can tell, a frontend ask
either.** It is a formal re-prove on the current drop.

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
| Functional simulation of the tree | **PASS** -- 23/23 paths, 22 byte-identical to the pre-tree drop |
| Open critical findings | **3**, all formal-only and `awaiting_formal`, none tree-introduced |

The tree is what closed this. Two chained 16-deep ripples would not have gotten
to 0.12 ns no matter what we did to the floorplan, and the floorplan lever only
worked because you had already taken the logic depth out. Thank you for going
past the ask on the tier de-chaining -- that one was yours, not ours.
