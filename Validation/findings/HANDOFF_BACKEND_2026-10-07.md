# Handoff to Backend — 2026-10-07

From Validation (Jacob) to Backend (Dawson), on `backend/findings/emit_findings.py`
and the five fields it marks PENDING, plus what the top-level flow now does
with backend output. Nothing in `backend/` was changed by us.

## 1. Your findings are consumed as they are

`flow.py` (repo root) reads `backend/findings/outbox/<spec_revision>/latest`
after a backend run that fails on the RTL, turns `findings_v2.json` into a
retry package with the same adapter validation uses
(`Validation/findings/retry_adapter.py`), hands it to the Frontend's phase
validation agents, and validates the regenerated drop before running the
backend again. Tested against your committed `3b542a6` outbox: the scheduler
timing finding routes to `scheduler` with `expected: slack >= 0 ns at a
5.0 ns period`, `actual: WNS -0.910 ns …`.

## 2. The five PENDING fields — answers

| # | field | answer |
|---|---|---|
| 1 | `kind: "timing_defect"` | Accepted. Our vocabulary is `rtl_defect` / `manifest_defect` / `spec_gap`; `timing_defect` joins it. The adapter does not key on `kind`. |
| 2 | `severity: "critical"` for a missed hard target | Accepted. Same scale as ours (`critical` / `major` / `minor`). |
| 3 | anchor: file only | Accepted as the floor. If OpenSTA's worst path names a start/end point, add `"signal": "<reg or port name>"` to the anchor; the Frontend's agents show anchors to the model, and a signal name is what lets them find the logic. Line numbers are not expected from a timing report. |
| 4 | `suggested_fix` | Accepted. The adapter maps it to the package's `fix` field (the same slot our repair-proven hypotheses use), so the Frontend sees one field whoever wrote it. Keep it a sentence a generator author can act on ("split the 4-deep compare on cmd_row into two stages"), not a tool directive. |
| 5 | `drop: {git_head, spec_revision}` | One change: name the drop by content, not git. Since 2026-10-01 a drop's id is the SHA-256 (first 12 hex) over every block's `<block>.sv` + `<block>_manifest.json`, blocks sorted, 11 blocks (`Validation/structural/rtl_drop.py: drop_id()`; recipe in `Validation/findings/HANDOFF_CONTRACT.md` §2). Git HEAD is informational — on one machine with drops generated in place there is none. Write `drop: {"drop_id": <hash>, "spec_revision": …, "git_head": <optional>}` and name the outbox folder by `drop_id`. The flow keys the backend's output to the drop it ran on through that id. |

Also: `confidence: "observed"` is right for STA (a tool's measurement, not a
model); `repro.command` is fine as a string — our records use `repro.cmd`,
the adapter accepts either.

## 3. Your netlists run through our paths now

The final stage of the flow is ours: every backend netlist (`6_final.v`)
is simulated in place of its block's RTL on every validation path that
instantiates the block (`run_path.py --netlist <block>=<6_final.v>`), with
the sky130_fd_sc_hd functional models installed on Olympus
(`Validation/tools/install_sky130_models.py`; the models are mirrored from
the open PDK under `Validation/refdesigns/sky130/`, Apache-2.0). First
results on the netlists committed under `backend/outputs/` (synthesized from
the August RTL):

- `wb_port/6_final.v` on `path_21_wb_port_standalone`: **PASS 19/19** — the
  gate-level port does exactly what the spec predicts.
- `init_fsm/6_final.v` on `path_14_status_init`: exposed two defects in
  *our* checkers rather than the netlist (an assertion counter that read
  gate-level flops a cycle early, and a path verdict that ignored fired
  assertions), both fixed; result in the plan.

What this needs from the backend side: **per-block netlists**, i.e.
`pipeline_batch.py` on `backend/bundles/<block>` so the run directory has
`runner/<block>/6_final.v` per block. A top-level netlist (`ddr3_controller`)
has no block path to run on yet. `flow.py` looks for
`<run>/backend/runner/<block>/6_final.v` and says so when only a top-level
one exists.

## 4. `--mode`

`contract` / `synth` / `build` / `full` is the right shape for an orchestrator.
`flow.py` runs `build` by default today; a `--backend-mode` option mapping to
yours is a one-line addition when you want it driven.
