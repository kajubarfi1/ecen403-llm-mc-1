# Handoff to Validation — 2026-10-29 (9)

From Frontend (Lehana) to Validation (Jacob). Not a reply to anything
of yours -- found this running a local sweep (deterministic,
`compile_spec()` + all 11 generators' RTL generation, no Olympus) over
the full 1,728-combination Tier-1 space, part of scoping out the
"test multiple specs" work. Doesn't touch the golden spec at all.

## addr_decoder: a real 1-bit formula mismatch, ecc_mode > 0 only

384 of the 1,728 combinations failed `addr_decoder`'s own
`validate()` with "Address bits overflow: N > N-1", always off by
exactly 1, always with `ecc_mode > 0`. Traced it: `addr_decoder_gen.py`
computed its burst-byte-offset from `memory_geometry.byte_lanes` (every
physical lane, ECC included), while `microarch_compiler.py` derives
`host_interface.address_width_bits` from `channel_capacity_bytes`,
which correctly excludes the ECC lane
(`memory_geometry.$derived.data_byte_lanes`). Two independently-written
formulas for the same quantity, agreeing everywhere ECC is off (where
the two lane counts are equal) and disagreeing by exactly one bit
everywhere it's on. Fixed `addr_decoder_gen.py` to use
`data_byte_lanes` instead of `byte_lanes`.

No change for the golden spec (`ecc_mode: 0`, so the two lane counts
were already equal there) -- confirmed via `validate()` before and
after, zero diff. 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` pass.

## The sweep, if useful

896/1,728 valid before this fix, 1,280/1,728 after (the other 448 are
two already-understood non-bugs: host/channel width not dividing
evenly, and address space over wb_port's 32-bit field for very large
density x lane combos -- neither is a formula disagreement, just real
configuration limits). Zero crashes anywhere in the full space, before
or after. Happy to send the full report if it's useful for picking a
Tier-3 sample once you're ready for that.
