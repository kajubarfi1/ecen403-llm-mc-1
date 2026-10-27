# Handoff to Validation — 2026-10-27 (3)

From Frontend (Lehana) to Validation (Jacob). Not a reply to an open ask —
a new feature, plus a defect found while building it.

## 1. The DDR:controller clock ratio is now a per-spec choice, not a constant

`clock_ratio_ddr_to_controller` used to be a fixed global (`jd.
CLOCK_RATIO_DDR_TO_CTRL = 4`, and `"const": 4` in the schema), so only
DDR3-1600 ever landed on a clean 200MHz controller clock. It's now a Tier-2
choice (`microarch_compiler.TIER2_DEFAULTS`, default still 4 — every
existing preset and the golden spec are byte-for-byte unchanged,
`--selftest` confirms) accepting `{1, 2, 4, 8}` (the DDR3 controller
gearbox rates actually implemented: full/half/quarter/eighth-rate).
Controller frequency = `data_rate_MTps / 2 / ratio`. Concretely:
DDR3-800 + ratio=2 now gives exactly 200MHz; DDR3-1600 + ratio=2 gives
400MHz. Schema, compiler validity matrix/consistency checks, the blast-
radius table (`regen_local` — only `data_path_gen`/`refresh_ctrl_gen`
regenerate, port names stable), and the English-intake agent's tool schema
all know about it now. `target_frequency_mhz` is unchanged (still an
independent backend synthesis-floor hint, not a derivation input).

## 2. Found while generalizing it: the write-path latency counter had your read-path bug too

`data_path_gen.py`'s write-side CWL latency counter was still
`wr_lat_ctr <= (cfg_CWL_nCK >> 2) - 1'b1;` -- a hardcoded `>> 2`
(divide-by-4), the same shape as the read path's `(cfg_CL_nCK >> 2) - 1`
before your addendum-4/5 fixes, and for the same reason: it can't be right
for any ratio but 4, and almost certainly has the identical off-by-one
(floor instead of ceiling, no final adjustment). Fixed to the same
formula the read side now uses:

```
wr_lat_ctr <= (cfg_CWL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] - 1'b1;
```

We didn't have a failing write-path finding to confirm the off-by-one
against (nothing in outbox has flagged a write-path timing defect) — found
it by inspection while making the counter ratio-generic, not from one of
your runs. Worth a specific look on your next pass since we have no
independent confirmation it was wrong in practice, only that it was
structurally the same bug shape as the one that was.

## What we verified locally

- `python3 Frontend2/scripts/Microarch/microarch_compiler.py --selftest`
  still reproduces the golden spec exactly.
- Compiled DDR3-800/ratio=2 (200.0MHz), DDR3-1600/ratio=2 (400.0MHz),
  ratio=1 (800.0MHz), ratio=8 (100.0MHz): all `errors: []`, consistency
  checks pass.
- Regenerated `data_path.sv` and `refresh_ctrl.sv` against all four;
  `validate()` returns `[]`, `generate_rtl()` raises nothing, and both
  `rd_lat_ctr`/`wr_lat_ctr` lines use the parametric `CLK_RATIO` formula
  with no stale `>> 2`.
- Rejecting ratio=3 gives a clear compiler error rather than a silent
  generator failure.
- `tests/test_flow.py` (40 tests) still passes.
- No verilator/Xcelium locally (Olympus-only, per our own convention) —
  your next `validate_drop.py` run on a spec that actually uses a
  non-default ratio is the real check, same caveat as our last two fixes.

## Nothing to ask

Flagging both for visibility; no blocking question on either.
