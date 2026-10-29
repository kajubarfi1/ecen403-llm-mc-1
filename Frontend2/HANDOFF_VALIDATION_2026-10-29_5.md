# Handoff to Validation — 2026-10-29 (5)

From Frontend (Lehana) to Validation (Jacob). Closes the open question
at the end of `HANDOFF_VALIDATION_2026-10-29_4.md` -- whether the
`data_path_tb.sv` white-box pattern shows up elsewhere.

## Scan result: no, it's isolated

Grepped every `dut.` hierarchical reference across all four real,
in-use testbench generators (`Frontend2/scripts/Phase{1,2,3,4}/
tb_generator.py` -- not the unused reference copies still sitting in
some `*_gen.py` files, which are a separate, already-flagged thing).

- **Phase 2, Phase 3**: zero `dut.` references. Nothing to scan.
- **Phase 4**: the only two hits are this week's own fix (the comment
  explaining the old bug, and the new `dut.rd_capture_valid` level
  trigger) -- already addressed.
- **Phase 1**: four hits, all `dut.MR0_VAL`/`MR1_VAL`/`MR2_VAL`/
  `MR3_VAL` inside `check()` calls. Different pattern, not the same
  bug class: these compare the DUT's own *constant* parameter against
  an expected value computed independently from the spec
  (`_encode_mr0()` etc., per the file's own comment -- "computed
  independently of the RTL ... not extracted from it"). That's a
  cross-check that the RTL's encoding agrees with the spec, not
  stimulus generation keyed off dynamic internal state. A bug in how
  `init_fsm_gen.py` computes `MR0_VAL` would still be caught (the
  independently-computed `mr0_hex` wouldn't match); a bug in dynamic
  internal state has nothing analogous here to go wrong the way
  `rd_burst_ctr` did.

So `data_path_tb.sv` was the one instance, not a systemic habit --
nothing else to fix from this ask.
