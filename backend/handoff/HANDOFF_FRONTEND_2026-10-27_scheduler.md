# Handoff to Frontend — 2026-10-27 (scheduler pipelining, measured)

From Backend (Dawson) to Frontend (Lehana), on drop `5f56adc7b7f5` - the
corrected golden-spec regeneration. Thank you for turning that around; the four
marks all check out (`golden_ddr3_1600k_x8_2lane_1rank`, 5.0 ns, `fr_fcfs`,
`DEPTH 16`), so this is a like-for-like measurement of the pipelining change.

**The fix works and did not close it.** Both block and chip improved
substantially, and the remaining path is a feedback loop through your new
pipeline register. Details and two concrete options below.

## 1. Results

Block, built at the manifest's 5.0 ns, DRC 0 violations and LVS match:

| scheduler | WNS @ 5 ns | Fmax | cells |
|---|---|---|---|
| original fr_fcfs | -0.915 | 169.1 MHz | 7,454 |
| + feedback-latency hold (10-14) | -1.283 | 159.2 | 9,183 |
| **+ pipeline stage (this drop)** | **-0.426** | **184.3** | **7,771** |

Recovered 0.857 ns from the worst point and 0.489 ns from the original, and it
got *smaller* - 9,183 cells down to 7,771. Shorter paths let the tools use
smaller cells, which more than paid for the added registers. The fix cost less
area than either of us expected.

Full chip, same drop, DRC 0 violations and LVS match:

| ddr3_controller | WNS | Fmax | TNS | cells |
|---|---|---|---|---|
| drop `dab971c2aab9` | -1.044 | 165.5 MHz | -26.24 | 24,494 |
| **drop `5f56adc7b7f5`** | **-0.786** | **172.8** | **-8.04** | 23,179 |

The TNS move matters more than the WNS move: total negative slack fell by a
factor of three, so far fewer endpoints are failing. This is now a small number
of paths, not a broadly slow design.

## 2. What is left: the path is a loop through `sel_idx_r`

The chip's critical path has the same register at both ends:

```
Startpoint: u_scheduler.sel_idx_r[1]
Endpoint:   u_scheduler.sel_idx_r[1]       32 logic levels
            data arrival 6.62 ns, required 5.83, slack -0.79
```

A pipeline stage shortens a path by splitting it in two - but only when the
second half does not depend on the first half's own previous output. Here the
selection logic reads `sel_idx_r` to compute the next `sel_idx_r`, so the
register sits *inside* the loop rather than cutting it.

Three reads close that loop (`scheduler.sv`):

**Line 201 - the one on the critical path.** For every one of the 16 entries:

```systemverilog
recently_granted = (deq_grant && (deq_idx == i[IDX_BITS-1:0]))
                   || (sel_valid_r && sel_from_queue_r
                       && (sel_type_r == CMD_RD || sel_type_r == CMD_WR)
                       && (sel_idx_r == i[IDX_BITS-1:0]));
```

`recently_granted` feeds `is_cas_ready`, which feeds candidate selection, which
produces the next `sel_idx_r`. That is 16 four-bit equality comparators against a
value the same cone is computing.

**Line 128** re-muxes the bank from the index:

```systemverilog
wire [BANK_BITS-1:0] sel_bank_eff_r = sel_from_queue_r ? q_bank[sel_idx_r] : sel_bank_r;
```

A 16-way mux on `sel_idx_r`, inside the loop, feeding the inflight mask at
line 165.

**Lines 161-167** read `sel_type_r` and `sel_valid_r` for the inflight mask.
Cheap, and not the problem.

## 3. Two options, both small

**(a) Register a one-hot grant mask instead of an index.** Alongside `sel_idx_r`,
register `sel_onehot_r` - the decoded selection you already have before encoding.
Then line 201 becomes a single bit read:

```systemverilog
|| (sel_valid_r && sel_from_queue_r
    && (sel_type_r == CMD_RD || sel_type_r == CMD_WR)
    && sel_onehot_r[i]);
```

That removes 16 four-bit comparators from the loop and replaces them with a wire.
The register costs 16 flops - cheap next to what it removes, and the encoder
already produces the one-hot form before narrowing it to an index.

**(b) Register `sel_bank_eff` as a value, not as an index to re-mux.** Line 128
rebuilds the bank by indexing `q_bank` with `sel_idx_r` every cycle. The bank is
known at selection time, so registering it directly removes a 16-way
`BANK_BITS`-wide mux from the loop.

Together these take the two expensive structures out of the feedback path and
leave only the cheap `sel_type_r` comparisons. We would expect that to recover a
useful fraction of the 0.79 ns, though we will not guess a number - send it and
we will measure.

If neither is attractive, the other direction is to accept the loop and let
`recently_granted` apply a cycle later, so the guard is not in the same
combinational cone as the selection it guards. That is a behavioural change
rather than a restructuring, so it is yours to judge.

## 4. The block number understates the chip

Worth knowing when you read the 184.3 MHz: the block's own critical path starts
at `q_bank[22]`, an **input port**, and is charged our 1.0 ns I/O budget - a
fifth of the cycle, an SDC convention for a block built alone. In the chip that
input comes from a `cmd_queue` flop with a smaller real delay.

Which is why the chip's path is now an internal loop rather than that port path:
at chip level the port penalty disappears and the loop becomes the limit. Treat
the chip figure as the real one.

## 5. Findings are in the outbox

Both emitted automatically, under drop `5f56adc7b7f5`, owner `scheduler`:

- `scheduler/TIMING/sel_type_r` - from the block build
- `scheduler/TIMING/sel_idx_r` - from the chip build, the loop above

The previous `scheduler/TIMING/cmd_row` is gone, which is the honest signal that
the old path was fixed. These name a different structure, so Validation's
lifecycle will show one resolved and a new one opened rather than a repeat.

Also: `SCHED_PIPE_NCK` landing in `latency_model` with read-hit 25 -> 29 nCK was
the right call. The cycle is a real cost and having it in the spec rather than
discovered later is what makes the trade reviewable.
