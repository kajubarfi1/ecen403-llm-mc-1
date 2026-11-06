# Handoff to Validation — 2026-11-06

From Frontend (Lehana) to Validation (Jacob). Correction to
`HANDOFF_VALIDATION_2026-11-05_2.md` — round 1 of the automated fix-loop's
own real Olympus simulation (finally reachable once I was on VPN) caught a
genuine timing bug in that round's `wb_port` fix. This replaces it.

## What your sim caught

`runs/20261106-095850-interactive/validation/round_1/retry_instructions.json`
against the committed reorder fix (`e7c5034`): `wb_port` failed —
`DATA_001` (X/Z on `wb_rsp.read_data`), two address/data `MISMATCH`
findings, `HOST_001_progress` fired 24x, `HOST_002` fired 45x. `data_path`
passed on attempt 1.

I read `wb_port_order_sva.sv`'s actual `HOST_002` definition to get the
exact invariant it's checking: a read's ack must coincide with `rsp_valid`
**the same cycle**. That's what exposed the bug — my `rd_data_valid` array
only reflects a new value the clock edge *after* `rsp_valid` fires, and
`rd_ack` gated purely on reading it. That adds one cycle of latency to
**every** read, not just a reordered one — the exact case `HOST_002` is
built to catch. `DATA_001`'s X/Z follows from the same design:
`rd_data_buf` had no reset (reasoned "never observable" since it's only
read while acking) — wrong, because `wb_dat_o` reads it continuously, so an
unwritten slot's X was visible even while idle.

## Fix

A same-cycle bypass: `rsp_is_head = rsp_valid && rsp_aux == rd_head_idx`.
When the incoming response is for the current head, `rd_ack`/`wb_dat_o`
fire off it directly instead of waiting a cycle for `rd_data_buf` —
restoring the original zero-added-latency timing for the common case,
while a genuinely-reordered response still buffers by tag exactly as
before. Gave `rd_data_buf` a real reset.

Separately, your automated fix-loop had already found and fixed a real
multi-driver violation on `data_path`'s `wr_buf_valid` (three FSM consume
sites each cleared it directly, racing the push block's own driver) — that
fix was sitting in the generator but hadn't been copied to the canonical
RTL locations; done now, same commit.

## What I checked

My Python model (`reorder_verify.py`) was too abstract to have caught this
— it modeled delivery as a discrete step, not same-cycle-combinational vs.
next-cycle-registered RTL timing. Rewrote it to separate those explicitly.
Confirmed a faithful replica of the pre-fix design reproduces the exact
one-cycle-late-ack under this precise model (proving the model *would*
have caught it, if I'd had this version last round); confirmed the bypass
design doesn't, and holds data correctness + acceptance-order delivery
over 5000 randomized trials mixing same-cycle and buffered delivery.
`py_compile` clean, 60/60 `tests/test_flow.py`, `microarch_compiler.py
--selftest` 27/27. New drop `c54434d369b0`, `top_copy_mismatches` clean.

## What I have not verified

Still no local Xcelium — this is reasoned from your SVA source and a
hand-rewritten Python model, not an actual re-run. This is the one I'd
most want `path_18`/`path_23` re-run against before trusting it fully; the
live round-1 run that found this bug was working against the old RTL, so
its remaining attempts are moot — a fresh run or resume against this
commit is what would actually confirm it.

## Not touched, on purpose

Same as last time: `wb_port/HANDSHAKE/wb` is still open.

## Questions

None blocking. If a fresh `wb_port` re-verification clears `DATA_001`/
`HOST_002`/the `MISMATCH` findings, that's this round closed.
