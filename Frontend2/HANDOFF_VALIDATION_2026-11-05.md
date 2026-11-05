# Handoff to Validation — 2026-11-05

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 14 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md` ("What we
need from you now (2026-11-05)"), items 1–4, plus the three completeness
decisions from `Validation/spec/completeness_rules.json`.

## 1. The five compiler/schema defects — all fixed or rejected with the real reason

1. **`unpack_32_to_64`**: `validate_choices` now rejects `channel_data_width
   > host_data_width` outright (`data_path_gen.py` has no unpack path,
   confirmed by reading it — `WORD_BEATS` only ever divides host width by
   channel width). `pack_mode` is unconditionally `pack_*` now; the
   `unpack_*` branch is unreachable and gone.
2. **33-bit addresses**: `validate_choices` now rejects
   `address_width_bits > 32` directly, with the real reason (the 32-bit
   CSR/host address field), instead of letting it reach `_csr_map` (where
   it was producing an inverted `31:33` reserved-bit range) or
   `wb_port_gen.py`'s later check.
3. **`row_bits: 17` on 8Gb x8**: root-caused to `page_size_bytes_per_device`
   being density-independent for x8 (always 1KB) — correct through 4Gb,
   one bit short at 8Gb. DDR3's address bus is a fixed 16 pins across
   every density (that's a hardware fact, not a convention), so page size
   is what has to grow; x16 already always used 2KB and that happened to
   still fit through 8Gb, which is why only x8 showed the overflow. 8Gb
   x8 now also gets 2KB, landing at `row_bits=16`, column_bits=11 — both
   inside the schema's existing caps.
4. **8Gb's tRFC vs. the 8-bit field**: real bug, not just a missing
   check — `_pack_le_bytes` was silently truncating 280 → 24 rather than
   erroring. Rejected at `validate_choices` with the real reason. Did
   **not** widen the field: `TIMING_1.tRFC_nCK` shares one 32-bit word
   with `tRRD`/`tWTR`/`tFAW`, and widening it means restructuring that
   whole word plus every consumer (`config_regs_gen.py`,
   `bank_tracker_gen.py`, `refresh_ctrl_gen.py`, and two testbench
   generators) — flagging it as a real follow-up rather than bundling a
   register-map change in with four other fixes.
5. **MR0 `on_the_fly`**: spelling fix to `on_the_fly_4_8`.

1200 of 16,384 raw Tier-1 combinations are valid post-fix (down from the
1,728 my earlier sweep found, since items 1/2/4 above correctly shrink
what's accepted to what's actually supported — not a regression, the
intended effect). 43/43 `tests/test_flow.py`, `microarch_compiler.py
--selftest` pass; no change to the golden spec's own derived values.

## 2. SSH retry + honest skipped-gate reporting — done

`simulator.py`'s `XceliumSimulator.connect()` now retries a refused
connection 6 times with backoff, same shape as your own
`CadenceSSHAgent.connect()`. Separately, every phase pipeline's
`lint_failure()` now reports `failure_stage: LINT_NOT_RUN` (not `LINT`)
when the gate's own status was `SKIPPED`, and `flow.py`'s top-level
assembly step reads `top_lint_report.json` before claiming "its lint
failed" — if the report says `SKIPPED`, the halt reason says the gate
wasn't run and why. The presets that failed on this during your netlist
jobs should get an honest reason the next time this happens, even where
retrying doesn't fully save the run.

## 3. Three completeness-rules decisions, answered

- **`PHY_DATA_BUS_OCCUPANCY` → `host_word_beats`**: now an explicit
  `phy_interface.data_bus_cycles_per_cas` field, formalizing what
  `scheduler_gen.py`'s `cas_spacing_ctr` already independently derives
  and enforces as `WORD_BEATS`.
- **`HOST_WRITE_BUFFER_BACKPRESSURE` → `port_stalls_on_full`**: real RTL,
  not just a spec field — `wb_port` now takes `data_path`'s previously-
  unconsumed `wr_data_ready` as an input and stalls a write beat on it,
  same shape as the existing `tag_full` read-side stall. New assertion
  WB-012 checks the stall actually fires. New drop `e6e1ab286a8f`,
  `top_copy_mismatches` clean. Not simulated (no local Xcelium) — this is
  the one I'd most want `path_23` or an equivalent on, since "the write
  that filled the buffer is held, not dropped" is exactly the kind of
  property a read of the RTL gives me confidence in but not certainty
  about.
- **`HOST_ACK_ORDERING` → `in_request_order`**: decided and recorded
  (`host_interface.ack_ordering`), **but not yet enforced in RTL, and I
  want to flag why before building it.** Tracing where `rd_pend` gets
  pushed (`data_path_gen.py`: `rd_pend_push = cmd_rd_valid && ...`) — it's
  at DRAM command issue time, not host-acceptance time. Since the
  scheduler's FR-FCFS row-hit priority can issue a later-queued read's
  CAS before an earlier-queued read's (exactly the reordering it exists
  to do), **two reads can already complete out of their host-acceptance
  order today, independent of any write.** `wb_port`'s own tag mechanism
  (`tag_mem`/`rsp_aux` matching) reads as built to tolerate exactly this
  — but the existing assertion on it (`rsp_aux == tag_mem[tag_rd]`)
  reads as assuming the opposite, that reads return in submission order.
  I haven't resolved which of those is actually true in practice, and a
  fence that only holds writes behind outstanding reads (the direct read
  of your rule, and what HOST_001's precedent would extend naturally)
  would be a real but **partial** answer to "in_request_order" if reads
  can also reorder among themselves — worse to ship something that looks
  like it closes the rule than to say plainly that it doesn't yet. Can
  you tell me whether `path_23` (or whichever path exercises concurrent
  outstanding reads) has ever actually seen two reads complete out of
  order, or whether something I haven't traced prevents it? That answer
  decides whether the write-fence queue I have designed is sufficient or
  whether this needs a general completion reorder buffer.

## 4. Tier-1 sweep choices, full set

`Spec/tier1_sweep_choices.json` — every currently-valid Tier-1
combination (1,200, post the five fixes above), same `{"name", "origin",
"choices"}` shape as your own `spec_matrix.json` entries, `origin:
"tier1_sweep"`. Should drop straight into `--only`/merge the way you
described.

## Where things stand

Nothing here touches the scheduler tree or anything Backend measured —
their 2026-11-04 handoff has no RTL ask this round and asked specifically
for functional simulation of the tree before more timing work, so I'd
treat that as the priority read on this batch too, ahead of the WB-012
backpressure path and definitely ahead of starting the ack-ordering
redesign.
