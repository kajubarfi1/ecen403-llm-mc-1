# Handoff to Validation — 2026-10-29 (6)

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 10 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md` -- the
`data_path` regression (every read corrupted, not just dropped ones)
and the `BEATS_PER_CYC`/scheduler-spacing question. The scheduler
compile error (§1 of your addendum) was already fixed (`522cec2`) and
Dawson independently confirmed it's logically byte-identical to the
rejected file, so that one's closed.

## 1. data_path: redesigned the read side, and found the write side had the same bug

Your root cause was exactly right: `rd_pend` added a cycle between
`cmd_rd_valid` and the capture engine's CL countdown, but the DRAM
drives data CL cycles after the RD was issued, full stop -- not CL
cycles after our engine notices it. The fix isn't a tweak to the old
design; I rebuilt the read-capture engine around two ideas, and
checked both with a cycle-accurate Python model before trusting the
RTL (no local Xcelium, so this was the best verification available
without you):

- **Bypass**: when the engine is idle and nothing's queued, a fresh
  `cmd_rd_valid` is handled the same cycle, same as the design before
  `rd_pend` ever existed. Zero added latency -- this is the common case,
  and it's where the regression actually lived (your path_03 example
  had no contention at all).
- **Per-entry deadline**: a command that genuinely arrives while the
  engine is busy gets queued with its OWN deadline -- `rd_cycle_ctr`
  (free-running) sampled AT THE CYCLE IT WAS ISSUED, not recomputed
  later. The engine captures once that deadline arrives, no separate
  wait state.
- **Chaining**: the part my first draft got wrong. Checking the deadline
  only in `RD_IDLE` still cost a cycle on the way out of `RD_CAPTURE`
  for back-to-back reads -- the engine would sit in `RD_IDLE` for one
  cycle before noticing the next deadline had already passed, during
  which the DRAM (which doesn't wait) had moved on. `RD_CAPTURE`'s own
  exit now checks whether the next queued read's deadline arrives this
  cycle or the next, and chains straight into its capture instead of
  detouring through `RD_IDLE`.

Simulated three cases in Python before generating RTL: an isolated read
(capture starts at issue+wait_cycles, matches the pre-`rd_pend` design
exactly), three back-to-back reads at the scheduler's new spacing
(zero-gap, zero-overlap, each read's own data correctly separated), and
the CL<=ratio fast path (ratio=8 case, capture starts 1 cycle after
issue, unaffected since it's pure bypass). All three came out exactly
where they should.

**The write side had the identical bug, unreported because nothing had
exercised it yet.** `wr_pend_cnt` is a bare counter, not a flag -- same
one-cycle registration delay as `rd_pend`'s array, same wrong-not-just-
late consequence once I worked through it (CWL is anchored to the WR
command's issue cycle exactly the way CL is for reads). Gave it the
same three-part treatment: bypass, per-entry deadline
(`wr_pend_deadline`, a new queue separate from `wr_buf` since write
*data* and write *commands* are different event streams), and chaining
on `WR_DRIVE`'s exit. Also simulated in Python (isolated + back-to-back)
before generating RTL; both came out correct.

## 2. BEATS_PER_CYC / scheduler spacing: took the safe choice, self-contained

Added a CAS-spacing guard directly in `scheduler_gen.py` --
`cas_spacing_ctr`, global (not per-bank), loaded to `WORD_BEATS-1`
whenever a CAS is selected, gating `is_cas_ready` until it expires. Two
things worth knowing:

- **Independent of `bank_tracker`'s own `tCCD` gate, deliberately.** I
  tried to hand-verify `ctr_ccd`'s actual enforced spacing against the
  golden spec's `tCCD_nCK=4` and kept getting a result (~5 controller
  cycles) that didn't match your description of commands issuing at
  "the scheduler's own tCCD rate" -- I never resolved that discrepancy
  (it's gated through `cmd_gen.fb_rd_valid`/`fb_wr_valid`, a feedback
  path I didn't want to guess about without a real sim). Rather than
  risk shipping a fix built on a wrong understanding of that path, I
  made this guard self-contained: loaded off the un-registered
  `sel_valid`/`sel_type` the same cycle a CAS is selected, no
  dependency on `cmd_gen`'s timing at all. It ANDs into `is_cas_ready`
  alongside `bank_rd_allowed`/`bank_wr_allowed`, so the effective
  spacing is `max(whatever tCCD enforces, WORD_BEATS)` regardless of
  how that discrepancy resolves.
- **Didn't touch the `BEATS_PER_CYC` question itself** (whether it
  should be `CLK_RATIO * 2` to model DDR's real transfer rate) -- still
  yours and Dawson's call, same as your addendum said. This is the
  "safe pending a decision" spacing you recommended, nothing more.

## What I checked, and what I didn't

`py_compile`, 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` all pass. Regenerated `data_path_tb.sv` and confirmed it's
byte-identical to what's checked in -- `dut.rd_capture_valid` means the
same thing regardless of what drives the transition into it, so my ask-9
fix from earlier today needed no changes. Hand-verified declaration
ordering throughout (the exact class of mistake that broke the
scheduler drop) -- every new signal is declared before its first use.

**Not verified**: no local Xcelium, so the Python model is the only
check beyond hand-reading the generated RTL. I'd specifically like
`validate_drop.py` on path_03 (isolated read), path_02/path_07 (your
back-to-back traffic), and whatever exercises back-to-back writes --
the write side has no existing coverage I'm aware of for this exact
failure shape, so a clean pass there would be new information, not a
confirmation of something already checked.

## 3. Scheduler: the loop-break is gone

Separately -- Dawson's measurement (his handoff to us) found both
loop-break variants measure worse at chip level than the plain
pipeline stage with neither. Reverted `recently_granted` and
`sel_bank_eff_r` to that measured-best form; kept today's spacing guard
(orthogonal, not part of that experiment). New drop `e5ec723f495e`.

## Questions

None blocking. Let me know what `validate_drop.py` says, and whether
my reasoning on leaving the `bank_tracker`/`cmd_gen` tCCD timing
question unresolved (rather than guessing) was the right call.
