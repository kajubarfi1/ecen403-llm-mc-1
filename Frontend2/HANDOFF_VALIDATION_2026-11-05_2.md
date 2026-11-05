# Handoff to Validation — 2026-11-05 (2)

From Frontend (Lehana) to Validation (Jacob). Replies to addendum 17's
`wb_port/HOSTMEM/wb_rsp` and `wb_port/HOST_002`, and addendum 18's
`data_path/CONSERVE/WRITE_CMD_TO_BEATS`/`WRITE_REQUEST_TO_DATA` —
`HANDOFF_FRONTEND_2026-10-15_reply.md`.

## All four: fixed, same root cause, same design on both sides

You were right that it's one mechanism: the FR-FCFS scheduler legitimately
issues commands out of host-acceptance order (row-hit priority, for reads
**and** writes), and both `wb_port`'s read-ack path and `data_path`'s
write-buffer assumed acceptance order and command-issue order stay in
lockstep. Both no longer do.

**The automated fix-loop's draft on `wb_port` was wrong, and I want to be
explicit about why rather than just discard it.** It added a kind-order
FIFO (`ord_mem`) — correct, closes `HOST_002` — plus a plain FIFO for read
*data*, which still assumes response arrival order matches acceptance
order. I traced your col-488/col-496 counterexample through it: 496's data
still gets bypassed straight through as 488's answer. Same bug, moved down
one level. That draft isn't in the tree; both fixes below are designed
fresh.

**The fix, same shape on both sides**: both modules already carry a
per-accepted-beat unique tag end to end (`wb_port.aux_ctr` → `req_aux` →
`cmd_queue.enq_aux` → scheduler's `q_aux` → `cmd_aux`). Instead of a FIFO
or a full associative search, address a small array **directly by the
tag's own low bits** — collision-free since the tag space already matches
the outstanding-request window.

- **`wb_port`**: `rd_data_buf`/`rd_data_valid`, written by each response's
  own `rsp_aux` regardless of arrival order; delivery uses the existing
  `tag_mem[tag_rd]` (the oldest outstanding read's own tag) as the index,
  gated by a new `ord_mem` kind-order FIFO so a write can't ack ahead of
  an earlier read. `tag_rd` now advances on delivery, not arrival.
- **`data_path`**: new `wr_data_aux` input from `wb_port.req_aux`
  (manifest-wired, no `generate_top.py` change needed), `wr_pend_aux[]`
  mirroring the read side's existing `rd_pend_aux[]`, and `wr_buf`
  converted to tag-indexed (`wr_buf_valid[]` added). `wr_wptr`/`wr_rptr`
  stay pure occupancy counters — every existing backpressure invariant
  (`wr_data_ready`, WB-012, DP-001) is unchanged.

**A prerequisite I found that wasn't on anyone's radar**: `wb_port`'s
`aux_ctr` was one counter shared by reads and writes. Up to 16 of each can
be outstanding independently — 32 total — while the shared counter only
has 16 distinct values. Nothing used `aux` as a storage address before, so
it never bit; this fix does address by it, so it had to be split into
`rd_aux_ctr`/`wr_aux_ctr` first, or the new tag-indexed buffers would trade
one corruption bug for a rarer one. `validate()` in both generators now
checks `AUX_WIDTH` is wide enough for both buffer depths.

## What I checked

Python model before trusting the RTL (same discipline as every prior
round): the shared counter demonstrably aliases under realistic
read/write outstanding mixes (529 collisions / 2000 trials with a
"reads drain slow, writes drain fast" traffic shape), the split counters
don't (0 / 5000); read delivery matches acceptance order under fully
randomized out-of-order arrival, including your exact counterexample;
`HOST_002` kind ordering holds under randomized read/write interleavings;
write tag-matching delivers each command its own data under randomized
command-vs-push reordering. Declaration order checked programmatically on
the generated RTL. 60/60 `tests/test_flow.py`, `microarch_compiler.py
--selftest` pass. New drop `a18722d6c863`, `top_copy_mismatches` clean.

Added two new checks: `WB-009` is replaced (the old "responses arrive in
acceptance order" version fired 66 times in your run, which is exactly
the signal that it needed replacing, not patching); `DP-015` checks a WR
command is never issued before its own data has arrived in `wr_buf`.

**New RTL-level test**: `wb_port`'s testbench gets an explicit
out-of-order-delivery test — 2 reads accepted back to back, DRAM
responses delivered in reverse — the literal shape of the bug, not just
the Python model's abstraction of it.

## What I have not verified

No local Xcelium, so none of this has actually simulated — same gap as
every round this session. That includes the new RTL-level test itself: I
reasoned through its exact cycle timing by hand against the Python
model's semantics, but it's never run. This is the one I'd most want a
real `path_18`/`path_23` re-run on before trusting it fully.

## Not touched, on purpose

`wb_port/HANDSHAKE/wb` (1 of 17 beats never acked, anchored on the
Finding-1 skid-register lines) — this fix only changes which counter
supplies `req_aux` and how responses are stored/delivered *downstream* of
acceptance; it doesn't touch the skid register or `wb_stall_o` at all. A
beat that's never acked is a drop at or before acceptance, upstream of
everything here, and possibly interacts with WB-012's stall term in a way
that needs its own investigation — folding it into this change risked
masking its root cause.

## Questions

None blocking. If `path_18`/`path_23`/the 3-lane ECC refresh paths clear,
that's the four critical findings closed; `HANDSHAKE/wb` is still open
and I'd want your read on whether it's a skid-register race before I
start on it.
