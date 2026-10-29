# Handoff to Validation — 2026-10-29 (4)

From Frontend (Lehana) to Validation (Jacob). Replies to ask 9 of
addendum 7, `Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md`
— the `data_path_tb.sv` white-box read-beat bug. This was the last open
item from the 10-28/10-29 findings; findings 1/2 (addendum 9) and the
tMOD finding (addendum 8) were fixed earlier today.

## What changed

`Frontend2/scripts/Phase4/tb_generator.py`. Confirmed your diagnosis
exactly: `ddr_dq_i` was driven by `(dut.rd_burst_ctr == 2'd0) ?
test_rd_word[DQ_WIDTH-1:0] : test_rd_word[DATA_WIDTH-1:DQ_WIDTH]` — a
hardcoded 2-way choice. Correct by coincidence on the golden spec
(WORD_BEATS==2 exactly), wrong for anything else: at WORD_BEATS==4
(your low-cost-embedded preset), beats 1, 2 and 3 all got the same
slice.

Two changes, not one, since just generalizing the ternary to an N-way
mux would still leave the thing you actually objected to: the testbench
reading `dut.rd_burst_ctr` -- the design's own count -- to decide what
to drive.

- **Generalized**: the 2-way ternary is now a `for` loop over
  `WORD_BEATS`, the same shape `data_path_gen.py`'s own write-path RTL
  already uses to assemble `ddr_dq_o` from `wr_burst_ctr` -- reused the
  pattern rather than inventing a new one.
- **Not from `dut.rd_burst_ctr` any more**: added `tb_rd_beat`, a
  counter the testbench maintains itself -- reset to 0 and incremented
  purely off `dut.rd_capture_valid`, a one-bit *state* signal
  (`rd_state == RD_CAPTURE`), not the *count*. In a correct design the
  two stay in lockstep cycle-for-cycle (traced by hand: both are 0 on
  the first capture cycle, both increment together after), so this
  changes nothing when the RTL is right. But they're computed from
  different DUT signals, so a `rd_burst_ctr` arithmetic bug -- skips a
  value, wraps wrong, miscounts -- wouldn't be silently mirrored into
  the stimulus the way reading the count directly would; it'd desync
  `tb_rd_beat` from whatever the DUT actually captured, and the
  assembled word would come out wrong. That's the actual gap your ask
  is about: a testbench that reads design state to decide what to drive
  can't catch a wrong count in that state, and now this one isn't
  reading the count, only a coarser "window open" level.

I didn't try to get to a fully black-box (zero hierarchical reference)
version -- there's no port-level signal that says "capture window just
opened" (`rd_rsp_valid` only fires after the whole word is assembled,
one+ cycles later), and hand-computing that edge from CL/CWL timing
instead is the exact fragility the file's own comment already warns
about (a real bug last time: off by one cycle, read data was never
actually captured). `rd_capture_valid` is a state-level signal, a
different kind of thing from the count `rd_burst_ctr` itself -- if
that's not the line you'd draw, say so and I'll take another look.

## What I checked, and what I didn't

Regenerated against both the golden spec (WORD_BEATS=2) and a
byte_lanes=1 variant (WORD_BEATS=4, matching your low-cost-embedded
preset) to confirm the loop actually covers all 4 beats now, not just
2. `py_compile`, 43/43 `tests/test_flow.py`,
`microarch_compiler.py --selftest` all pass. `compute_drop_id` is
unchanged (`5994bb667dba`) -- testbenches aren't part of drop identity,
so no `TOPRTL` regen needed for this one.

**Not verified**: no local Xcelium, same as everything else this
session -- I'd like this run against your `--preset low-cost-embedded`
path specifically, since that's the one that actually exposed the
original bug.

## Questions

None blocking. One open item from your note: "the same white-box
pattern is worth a scan in the other phases' testbench generators" --
haven't done that scan yet. Want it as its own pass, or should I fold
it into whatever's next?
