# Handoff to Validation — 2026-11-06 (2)

From Frontend (Lehana) to Validation (Jacob). This is the real root cause
behind the `HOSTMEM`/`MISMATCH wb_rsp[data]` findings from round 2 of
`runs/20261106-095850-interactive` — and it isn't an RTL bug.

## The finding: `wb_rsp_monitor.sv` was firing on the wrong signal

I spent a long time trying to find a data-corruption bug in `wb_port`
before I actually proved there wasn't one. The decisive step was
instrumenting the real chain_harness directly (`run_path.py --probe`,
no guessing) and dumping `wb_ack_o` alongside everything internal
(`rd_head_idx`, `rd_pending`, `rsp_valid`, `ord_head_rd`) around the exact
cycles of two of round 2's "mismatched" `wb_rsp.read_data` events on
`path_02_read_cmd`. Result: **`wb_ack_o` was `0` for the entire window
around both events.** `wb_port` never actually delivered anything to the
host at those cycles — it was correctly still waiting on `rd_data_valid`
for the real head tag.

So where did the trace events come from? `wb_rsp_monitor.sv` (from
`interface_catalog.json`) was firing its "transaction complete" `$display`
on **`rsp_valid`** — `data_path`'s "a response for *some* outstanding tag
just arrived" signal, not `wb_port`'s host-visible completion. Your
2026-10-28 note on that qualifier is correct about *why* `wb_ack_o &&
!wb_we_i` doesn't work (wb_we_i at ack time reflects whatever beat the
master is currently presenting, not the one completing) — but `rsp_valid`
was only a safe substitute as long as it was synchronous with delivery,
which stopped being true the moment `wb_port` started buffering
genuinely-reordered responses (HOSTMEM/HOST_002 fix, 2026-11-05). Every
`rsp_valid` pulse — even for a tag that's just being buffered, nowhere
near delivery — got credited to whatever address the monitor's own FIFO
thought was oldest, logging `wb_dat_o` (frozen, since no real ack
happened) as if it were that read's answer. That's exactly the "exact
duplicate value for two different reads" and "exact zero" patterns across
the two rounds — not corrupted data, a monitor false-positive.

## Fix

`wb_port` now exposes `rd_ack` as a new output port — its own internal,
`ord_mem`-order-correct "a read is being delivered this cycle" signal
(previously a bare wire). It doesn't have the live-`wb_we_i` problem your
original note flagged, since it comes from the FIFO-order kind tracker,
not the bus. `wb_rsp`'s `qualifier` is now `rd_ack`; `pending.push` (the
address capture) didn't need to change.

Also regenerated `schemas.json` and all 27 monitors/the bind file —
`schemas.json` as checked in pointed every manifest at
`runs/matrix/preset_server-grade/drop/...`, which no longer exists on
disk; `Validation/spec/rtl_drop.json` declares `Frontend2/OutputFolders`
as the one canonical root, so I regenerated against that. Several
monitors' port widths were stale against the current golden-spec
manifests independent of anything I touched (`wb_adr_i` 31→29 bits,
`sched_row` 16→15, `ddr_dq_o` 32→16, `deq_idx` 5→4 bits) — correcting,
confirmed by re-running `path_02_read_cmd` and watching
`addr_decoder`/`cmd_queue+scheduler`/`cmd_gen`/conservation all go back to
PASS once the full monitor set (not just `wb_rsp`) was regenerated
together (my first attempt, scoped to `--iface wb_rsp` alone, clobbered
`monitors_bind.sv` down to one bind statement — caught and fixed before
committing).

## What's still open — not an RTL bug, flagging for your side

`path_02_read_cmd` still fails: `HOST_002` fires 24x, and a handful of
`wb_rsp[data]` mismatches remain. I did **not** chase these further,
because I'm confident they're the same class of staleness, just two
levels further in:

- **`HOST_002`'s own SVA** (`wb_port_order_sva.sv`) asserts `rsp_valid`
  must coincide with *every* read ack. That's only true for the
  bypass (non-reordered) delivery path — a genuinely-buffered delivery
  acks on a cycle where the response arrived earlier and `rsp_valid` is
  correctly `0` that cycle. Same stale assumption the monitor had, just
  written into the checker instead.
- The remaining `wb_rsp[data]` mismatches are very likely the
  **predictor** comparing against the same stale assumption (or a stale
  schema snapshot) — I confirmed directly via probing that `rd_pending`/
  `rsp_take`/`rd_data_buf` all behave exactly as designed, so I don't
  think there's a second real data bug underneath this.

I stopped here on purpose rather than hand-patch SVA or predictors
myself: `validate_drop.py`'s own step 4 (stale-model detection +
`predictor_agent.py` regeneration) is built exactly for this, and
standalone `run_path.py` skips it — which is what let the monitor go
stale against the architecture change in the first place. A full
`validate_drop.py` pass (or `predictor_agent.py --scope wb_port`) is
probably the right next step on your side, and HOST_002's property likely
needs rewriting to something like "the delivered data matches the head
tag's own response" rather than "rsp_valid coincides with the ack".

## What I checked

Direct Xcelium probing of the real chain_harness (not a model, not
reasoning from the generator source) for the specific failure; confirmed
the fix compiles and generates cleanly; re-ran `path_02_read_cmd`
end-to-end post-fix and confirmed every *other* scope (not touched by
this bug) is back to PASS. New drop `2a18a7929dce`, `top_copy_mismatches`
clean, 60/60 `test_flow`, 27/27 compiler selftest.

## Questions

Should I go ahead and run `predictor_agent.py --scope wb_port` (or the
full `validate_drop.py`) myself to clear the remaining staleness, or do
you want to look at HOST_002's property first? I don't have strong
context on how expensive/disruptive a predictor regen is on your side, so
deferring to you rather than guessing.
