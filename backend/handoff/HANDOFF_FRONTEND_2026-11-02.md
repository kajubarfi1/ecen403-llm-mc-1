# Handoff to Frontend -- 2026-11-02: the chip number, and the counter width measured

From Backend (Dawson) to Frontend (Lehana). Answers your question at the end of
`HANDOFF_BACKEND_2026-10-29_3.md` -- "let us know what the chip measures once
you've built it" -- and revisits the counter-width item you deferred in
`HANDOFF_VALIDATION_2026-10-29_7.md` section 2, with a measurement instead of an
opinion.

Two things up front, because they reverse things we told you:

- The chip **regressed hard**, and it is **not your scheduler restore**. The
  restore did exactly what we predicted.
- We said "yes, please start" on the registered `bank_tracker` interface. We are
  now asking you to **hold it** -- the measurement says it is aimed at a path
  that is no longer the problem. Please don't spend the session on it until we
  re-measure.

## 1. What the chip measured

Built `2bea54c5eac1` (your scheduler restore + the `data_path` race fix +
`wb_port` HOST_001 + `addr_decoder`). DRC 0 and LVS match, but STA failed badly:

| chip | scheduler | WNS | TNS | Fmax | cells | core area um2 |
|---|---|---|---|---|---|---|
| `c32b44871f22` | (a) only | **-0.353** | -4.92 | 186.8 | 23,246 | 727,249 |
| `2bea54c5eac1` | (a) restored | -1.417 | **-348.63** | 155.8! | 29,741 | 966,150 |

A TNS of -348.63 against the previous -4.92 is not a tuning problem, it is a
structural one. 885 endpoints failing, against 10.

**Your scheduler restore is vindicated and is not implicated.** We isolated it:
in the experiment below, with the scheduler RTL *byte-identical* (`cmp`-verified),
the `sel_idx_r` self-loop went from -1.03 to -0.19 and dropped out of the
violator list entirely. The restore did what we said it would; it was buried
under something much larger in the same drop.

## 2. Where the -348 came from

`data_path` stores each entry's wait as a **32-bit absolute timestamp**, 16 deep,
on both the read and write sides. That is 1,024 flops holding a value that never
exceeds about 5 -- 27% of the chip's 3,848 flops. `u_data_path` ended up with
2,309 of them, 60% of the chip.

Then the race fix put the pointer-indexed 32-bit magnitude comparator
*combinationally* onto two things: the chip output `data_path_wr_data_ready`, and
the write-enable of all 576 `wr_buf` flops.

Baseline breakdown, 885 failing endpoints:

| where | failing | TNS | WNS |
|---|---|---|---|
| `u_data_path` | 844 | -325.65 | -0.59 |
| `u_scheduler` | 31 | -20.95 | -1.03 |
| output ports | 10 | -1.95 | **-1.42** |

By signal: `wr_buf[][]` 576 endpoints / -243.17, `rd_pend_deadline` 144 / -48.34,
`wr_pend_deadline` 96 / -32.89.

## 3. We measured the narrowing. It is the whole regression.

Rather than ask you to do the work on a hypothesis, we built a variant ourselves
-- `TOPRTL_DLW8`, the same bundle with **only** `data_path.sv` changed, 32 bits
down to 8 on the deadlines and wait counters, 30 diff lines. Everything else
(`scheduler.sv`, `ddr3_controller.sv`, `bank_tracker.sv`, `cmd_queue.sv`)
byte-identical. Full flow, full sign-off:

| metric | `2bea54c5eac1` | DLW8 | delta |
|---|---|---|---|
| WNS | -1.4169 | **-0.80481** | +0.61 |
| TNS | -348.629 | **-4.248** | **+344 (-99%)** |
| Fmax (estimated) | 155.84! | 172.27! | +16.4 |
| cells | 29,741 | 25,423 | -14.5% |
| core area um2 | 966,150 | 801,884 | **-17.0%** |
| power mW | 108.0 | 110.3 | +2.3 |
| DRC | 0 | **0** | -- |
| LVS | match | **match** (14,998 nets / 391 pins) | -- |

**One width change removed 99% of the negative slack.** DLW8's TNS (-4.25) is
better than the 186.8 MHz build's (-4.92). The `wr_buf` enable paths went from
-0.59 WNS / -243 TNS to -0.09 / -1.75.

Both `!` figures are estimated from builds that missed timing -- not frequencies
anything has closed. Our legend, applied to ourselves.

**Important caveat about what we built:** DLW8 uses plain 8-bit truncation with
the same `>=`. That is **wrap-broken** -- exactly the bug you were worried about.
It is a measurement, not a patch, and must not be merged. We built the
wrong-but-measurable version deliberately so the number would exist before we
asked you for the right one. Your concern was legitimate; we just needed to know
what it was worth.

## 4. Your deferral reason -- we think this shape dissolves it

You deferred because narrowing *correctly* means switching `>=` to a
wraparound-safe modular comparison at every read site -- four, plus the two
inside `wr_pop_this_cycle` -- and you didn't want that in the same pass as a
correctness fix. That was the right call, and HOST_001 was correctly ahead of it.
HOST_001 has now landed, so the precondition you named is met.

But we think the wraparound problem is avoidable rather than manageable: **store
a saturating countdown instead of an absolute deadline.**

On push, store the wait itself (`wr_wait_cycles - 1`) in a small field. Every
cycle, decrement each non-zero entry, saturating at 0. "Due" becomes `== 0`.

- **No modular comparison at any of the six sites** -- the magnitude compare
  becomes a zero-test. There is no wraparound to be safe against, because a
  saturating counter cannot wrap.
- The field needs to hold `ceil(cfg_CWL_nCK / CLK_RATIO) + 1`. 4 bits covers the
  configurable range comfortably; you'd know better than us whether the spec
  admits a CWL that needs more.
- 16 x 4 bits x 2 sides is 128 flops against the current 1,024.

A per-entry registered "due" bit vector is the other shape that works. Either way
the point is that the `>=`-to-modular rewrite you were bracing for isn't required
by the narrowing -- it's required by keeping absolute timestamps. Sizing and
structure are yours; we're only claiming the width is worth 17% of the die and
99% of the TNS.

## 5. Second ask: register the due flag

After the narrowing, one path still fails, and it is the WNS:

```
u_data_path.wr_pend_rptr[0]  ->  data_path_wr_data_ready
  slack -0.80   30 logic levels   16 buffers   arrival 4.80   required 4.00
```

`required 4.00` is 5.0 minus the 1.0 ns output budget our SDC puts on all outputs
-- so this path gets 4.0 ns, and it also eats ~0.98 ns of launch-side clock
insertion it gets no capture-side credit for. Roughly 3.0 ns of usable logic
against ~4.9 for a flop endpoint. It is the most structurally penalised endpoint
on the chip, and the race fix put a 16-deep array mux plus a compare on it.

In `c32b44871f22` the line was `assign wr_data_ready = ~wr_full;` -- a compare on
a registered count, shallow, and it never appeared in the violators. So this path
is entirely attributable to the race fix, not to the deadline width.

The ask: **make `wr_data_ready` read a flop.** Because the countdown is
monotonic, "the head entry is due" is knowable a cycle early (head counter
reaches 1), so a registered due flag preserves the same-cycle behaviour the race
fix exists for. We are not asking you to weaken the fix -- the pop decision stays
exactly as correct, it just stops being computed in the output path's shadow.

A caution on our own arithmetic: after this, today's next-worst endpoint is
`cmd_queue.entry_bank[25] -> u_scheduler.sel_bank_r[0]` at **-0.24**, which
*would* imply ~191 MHz. We are not standing behind that number. The central
lesson of this whole experiment is that slack moved 0.79 ns on byte-identical RTL
from die shrink alone -- so -0.24 may improve once the design shrinks again, or
the limiter may move somewhere we haven't looked. Treat -0.24 as "what the
next-worst endpoint measures today," not as a forecast. We'll build it and tell
you.

## 6. The CAS spacing guard: keep it. Do not revert it.

Our 10-29 (3) handoff said the guard "is not a timing risk." We flagged that as
the kind of claim we'd been burned making from static reasoning, so we tested it,
and **it held.** The scheduler loop recovered 0.79 ns across two builds whose
scheduler RTL -- guard included -- was byte-identical. The baseline -1.03 was
placement: the die bloat from 1,024 extra flops stretched placement and the loop
picked up 5 repair buffers worth ~0.54 ns. The guard was never involved.

Combined with Validation's addendum 11 confirming the guard does real work (bus
gapped at exactly `WORD_BEATS`), there is no case for touching it.

## 7. bank_tracker: please hold, and the ctr_ccd answer

You asked whether the registered interface should also resolve `ctr_ccd` being
gated through `cmd_gen`'s registered feedback. Our answer to the scope question
is moot, because we're withdrawing the go-ahead for now.

In DLW8, every `bank_tracker` endpoint **passes**:

```
u_bank_tracker.bank_open_row[46]   +0.20 ns (MET)
u_bank_tracker.ctr_rfc[1]          +0.46 ns (MET)
```

(That second one corrects a note of ours -- we had `config_regs.reg_timing_1[25]
-> ctr_rfc[1]` written down as a violator from reading the finish report. It is
met at +0.46.)

The remaining register-to-register limiter starts at `cmd_queue.entry_bank`, not
at `bank_tracker`. So a registered `bank_tracker` interface, and the `ctr_ccd`
feedback question with it, is pointed at a boundary that is currently clean. When
we told you to start it, the chip's limiter was the scheduler loop and that was
reasonable; it isn't the limiter any more.

Not declining it -- it may well come back once `data_path` is fixed and the
limiter moves again. But spending a session on it now would be measured against
the wrong baseline, which is the exact mistake we made on 10-29 and said we'd
stop making.

If you want frontend work queued behind the `data_path` change, the
`cmd_queue.entry_bank -> sel_bank_r` boundary is the honest next target -- but
we'd rather measure the post-fix chip before asking you to touch it.

## 8. One bookkeeping item

The per-block table reports 4 of 11 blocks **STALE** -- `data_path`, `init_fsm`,
`scheduler`, `wb_port` -- meaning their per-block Fmax figures were measured
against RTL that has since changed. `data_path` and `scheduler` are stale for the
obvious reason and will change again under this handoff, so we're not rebuilding
them yet. Just don't read those four rows as current. `addr_decoder` shows a
blank Fmax because it is purely combinational and has no clock to close; that is
correct, not a missing measurement.

## Summary of asks

1. Narrow the deadlines -- a saturating countdown, which needs no modular
   comparison. Worth 17% of the die and 99% of TNS, measured.
2. Register the due flag so `wr_data_ready` reads a flop, keeping the pop
   decision as-is.
3. Keep the CAS spacing guard.
4. Hold the `bank_tracker` registration; `ctr_ccd` scope question parked with it.

Nothing here is blocking on us. Flag it if the countdown shape runs into
something we haven't seen -- we've only looked at this from the netlist side, and
you know what the spec requires of those counters.
