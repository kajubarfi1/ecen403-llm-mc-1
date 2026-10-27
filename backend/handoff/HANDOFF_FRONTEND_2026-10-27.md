# Handoff to Frontend — 2026-10-27

From Backend (Dawson) to Frontend (Lehana), on drop `efece348d04e`
(design `766dc69c37e9`). We swept every block to find the fastest clock each one
actually closes at, so the frequency target you are adding to the spec has a
per-block number to aim at rather than one global figure. Nothing in
`Frontend2/` was changed by us.

Verified before writing: all eleven blocks' RTL is byte-identical to what these
builds were cut from, compared against the preserved synthesis input in the ORFS
design directory. Your 10-27 Phase 4 change touched `data_path_gen.py`, not the
committed RTL, so nothing below is stale.

Also noted: `drop.py` now normalises CRLF before hashing (`5366a48`). That closes
the issue we raised on 10-08 - the id is the same on every checkout now, ours
included.

## 1. What each block can actually do

Measured, not extrapolated: each figure is a clock period a build really closed
at, with DRC 0 violations and LVS matching. **All eleven passed DRC and LVS at
every period tried**, including the tightened ones.

| block | Fmax | vs 200 MHz | limited by |
|---|---|---|---|
| cmd_gen | 546.8 MHz | 2.73x | |
| calibration | 490.7 | 2.45x | |
| config_regs | 411.7 | 2.06x | |
| init_fsm | 361.7 | 1.81x | |
| wb_port | 330.9 | 1.65x | |
| cmd_queue | 302.8 | 1.51x | |
| **bank_tracker** | **232.1** | **1.16x** | RTL depth |
| **data_path** | **231.7** | **1.16x** | RTL depth |
| refresh_ctrl | 204.8 | 1.02x | constraint artifact, see §3 |
| **scheduler** | **misses 200** | - | RTL depth |
| addr_decoder | n/a | - | purely combinational, no timing paths |

Every figure is a **floor**. The search stops after three iterations and all nine
were still improving when it stopped, so each block is at least this fast.

## 2. Where a frequency target would and would not help

The useful signal is not the Fmax but how much the logic improved when the tools
were squeezed. Each block was rebuilt three times at successively tighter
constraints; a block whose delay falls a lot had slack the tools were not
bothering to take, and one whose delay barely moves is limited by how deep the
RTL is.

| block | logic delay, first build -> last | read |
|---|---|---|
| config_regs | 3.561 -> 2.262 ns (**-36.5%**) | tools had plenty of room |
| cmd_gen | 2.640 -> 1.743 (**-34.0%**) | |
| wb_port | 4.017 -> 2.766 (-31.1%) | |
| calibration | 2.399 -> 1.919 (-20.0%) | |
| init_fsm | 3.154 -> 2.598 (-17.6%) | |
| cmd_queue | 3.601 -> 3.163 (-12.2%) | |
| **data_path** | 4.463 -> 4.096 (**-8.2%**) | near its structural limit |
| **bank_tracker** | 4.511 -> 4.142 (**-8.2%**) | near its structural limit |
| refresh_ctrl | 4.859 -> 4.751 (-2.2%) | limited by the I/O budget, see §3 |

The full per-iteration record is in `backend/outputs/FMAX_SWEEP.json`.

So: **`scheduler`, `bank_tracker` and `data_path` are the three blocks where a
frequency target would change anything.** On those, synthesis has run out of
ideas and only different RTL - fewer levels per cycle, a pipeline stage, a
narrower comparison - moves the number.

On the other six, please do not pipeline for frequency. `cmd_gen` already runs at
2.7x the target; adding a stage there spends a cycle of latency on every
transaction and buys nothing. A target of "meet 200 MHz" is correctly satisfied
by those blocks as they stand.

That matters for a memory controller specifically. Latency is part of the
product, and the `scheduler` fix we have already proposed costs a cycle and
changes the `cmd_queue` handshake. Pipelining is not free anywhere it is applied.

## 3. Two numbers not to read at face value

**`refresh_ctrl` at 204.8 MHz is not a real limit.** Its critical path runs
input port to output port (`cfg_urgent_threshold[2]` -> `ref_urgent`) and gets
charged our 1.0 ns I/O budget - a fifth of the whole cycle - which is an SDC
convention for a block built alone, not a property of the logic. In the chip,
that input comes from a `config_regs` flop and the output drives `scheduler`,
with real and smaller delays. Do not treat it as a tight block; the full-chip
run's critical path was nowhere near it.

By contrast `bank_tracker`, `data_path`, `cmd_queue` and `wb_port` all have
flop-to-flop critical paths, so their numbers are genuine.

**A block's standalone number can be lower than the chip's.** `scheduler` reads
159 MHz alone but 165.5 in the assembled chip, for the same reason - alone it is
charged the I/O budget on a path the chip drives from a real register. Block
figures are conservative for anything crossing a boundary.

## 4. The chip, and what gates it

The full controller builds: **DRC 0 violations, LVS PASS, 24,494 cells,
756,622 um2 die**. It misses timing at **165.5 MHz** against the 200 MHz target,
and the critical path is

```
u_cmd_queue.entry_bank[34] -> u_scheduler.cmd_row[4]     slack -1.044 ns
```

The top-level integration cost is small - about 2% - so the chip runs at roughly
the speed of its slowest block. `scheduler` is the only thing between you and
200 MHz today.

If `scheduler` is fixed, the ceiling moves to where `bank_tracker` and
`data_path` sit, around 230 MHz, and those two become the next constraint. That
is the order worth working in.

The open change request for `scheduler` is in
`backend/findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/`, owned by
`scheduler` with `cmd_queue` named as a co-candidate because the path crosses
that boundary - registering `cmd_queue`'s output would help as much as
pipelining `scheduler`'s input.

## 5. The spec plumbing already works

Worth knowing before you build anything: `clocking_model.controller_clock_period_ns`
already reaches us. All eleven manifests carry `clock_period_ns: 5.0`, our
packager reads it (`manifest["clock_period_ns"]`, with our own default only as a
fallback that never fires), and our timing findings quote the resolved period and
cite `clocking_model.controller_clock_period_ns` as the spec reference.

So if a user asks for 250 MHz and that becomes 4.0 ns in the spec, it flows into
the manifests and we constrain to it with no change on our side, and a block that
misses it produces a finding stating the right requirement. The only missing
piece is the one you are building: generators that *design to* the number rather
than record it.

## 6. How to read the figures, and what we would do differently

Each block got a baseline build plus up to three rebuilds at tighter periods,
with a margin of 2% of the current period. The reported Fmax is the fastest
period a build actually met - we also record what the leftover slack implies, but
that is an extrapolation about a build nobody ran and should not be quoted.

The reason that distinction matters: logic delay changes with the constraint.
`cmd_gen` at a 5 ns target built 2.640 ns of logic; squeezed, it built 1.743 ns.
Estimating Fmax from slack at a loose constraint does not mis-measure the
circuit, it measures a different and slower circuit.

If you want a block re-swept after a change, it is one command and a few minutes
per block, so ask rather than guessing from the table above once the RTL moves.
