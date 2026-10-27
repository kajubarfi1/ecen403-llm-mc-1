# Handoff to Validation — 2026-10-27 (2)

From Frontend (Lehana) to Validation (Jacob). Replies to Addendum 5 of
`Validation/findings/HANDOFF_FRONTEND_2026-10-15_reply.md` — the two items
still open from addendum 4.

## 1. Read-latency off-by-one: fixed as you specified

`Frontend2/scripts/Phase4/data_path_gen.py`: `rd_lat_ctr` now gets
`ceil(CL / CLK_RATIO) - 1` instead of the bare ceiling —

```
rd_lat_ctr <= (cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] - 1'b1;
```

matching your addendum 5 line exactly (the `- 1` accounts for the cycle
RD_IDLE → RD_WAIT already spends registering the command). Regenerated
`data_path.sv` from the golden spec locally to confirm the generator emits
it correctly (`(cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] -
1'b1`, CL=11/ratio=4 waits 2 cycles as you said); didn't have verilator
locally to lint it (per our own notes, that only runs on Olympus/through
`testbench_auditor.py`'s path) — your next run on it is the real check.
Did not touch the checked-in `Frontend2/OutputFolders/PHASE4RTL/data_path.sv`
or any `runs/*/drop/` copy — all of them predate even your addendum-4 fix
(still have the old `(cfg_CL_nCK >> 2) - 1'b1`), so they're stale build
artifacts from earlier sessions, not something to hand-patch; the generator
is the source of truth and the next real pipeline run regenerates them.

## 2. Schema miss: took your first suggestion

`Frontend2/scripts/Phase4/phase4_validation_agent.py`: `explanation` and
`shift_left_recommendations` are out of `_REQUIRED_PROPOSAL_KEYS` (still in
the tool schema as requestable fields, just not fatal if the model drops
one under pressure). Made the two call sites that used to index them
directly (`proposal['explanation']`, `proposal["shift_left_recommendations"]`)
defensive (`.get(...)`, printed/recorded only when present) so dropping
them from required doesn't trade a `RuntimeError` for a `KeyError`
somewhere else. Three of three attempts losing a required field on a
one-line fix was the actual blocker per your addendum 4/5 — this should
turn that into first-attempt applies going forward.

Only touched Phase 4 — the same required-field list (and the same
asymmetry CLAUDE.md already flags) exists verbatim in `phase{1,2,3}_
validation_agent.py`, but you've only seen this failure mode hit Phase 4
repeatedly and Phase 3 once; didn't want to change three files' behavior
on the strength of one data point. Say if you want the same relief
applied there too once there's more signal.

Both changes are generator/agent-source only; nothing regenerated or
committed under `Frontend2/OutputFolders` or `runs/`. `tests/test_flow.py`
(40 tests) still passes.

## Nothing to ask

Your next loop run on this is the test for both.
