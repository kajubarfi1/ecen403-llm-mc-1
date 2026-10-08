# Reply to Backend — 2026-10-08

From Validation (Jacob), answering `backend/handoff/HANDOFF_VALIDATION_2026-10-08.md`
(branch `backend-anchors-2026-10-08`). Numbered as your sections.

## 1. Anchors — received, rendered

Your envelope renders through `retry_adapter.adapt` → `to_frontend_error_report`
with `file`, `signal`, `bit` and `role` intact:
`scheduler.sv  cmd_aux[3] (endpoint)` / `q_bank[33] (startpoint)`. The
signal-keyed id (`TIMING/cmd_aux`) is right; one "old resolved, new opened"
on the first drop is expected and harmless. Agreed on `phase`: we never read
it either (we resolve by `PHASE*RTL/` directory and never choose `TOPRTL/`);
it is wrong in `data_path_manifest.json` and is noted to the Frontend.

## 2. `flow.py` — done

`stage_backend` now runs
`pipeline.py --bundle_dir <drop>/TOPRTL --out_root <run>/backend --drop_id <id>
--spec_revision <rev> --mode <mode>`. The id is the one `validate_drop.py`
stamped on the drop (`RUN_STATE.json.drop_id`, content hash over the 11
blocks); `--spec_revision` is the revision of the spec the run was
synthesized from. `tests/test_flow.py` pins all three.

## 3. Renderer — done

`_lines()` now omits the `:line` when there is none, prints
`signal[bit] (role)`, accepts `repro.command` / `repro.cmd` / a string, and
drops the dangling "on". `retry_adapter.adapt` sets `pipeline` from the
document's `producer` (yours says `backend`), so a reader of the package
alone attributes a timing defect to you, not us.
`Validation/tests/test_to_frontend_error_report.py` has a backend-anchor
case.

## 4. Outbox lookup — the ddr3800 concern is moot; one addition for you

The drop we validate today (`4b86c7cd3705`) is single-spec, revision
`golden_ddr3_1600k_x8_2lane_1rank`; `compiled_ddr3800_x8_1lane_1rank` was a
spec our flow synthesized in a dry test, not a change of part. Your
200 MHz / 1600 numbers stand.

What did bite us today: that revision string has named **three different
spec contents** (the Frontend changed the golden file in place). We now
identify a spec by content as well — `spec_id` = sha256 of the canonical
JSON, first 16 hex digits (`Validation/spec/spec_identity.py`) — and write it
beside `spec_revision` in `HANDOFF.json`, `findings_v2.json` and model
provenance. The `--spec_revision` you take from `flow.py` is unchanged; if
you want to be safe against the same thing, write `spec_id` into your
findings document too (`flow.py` can pass `--spec_id` the day you accept
it; say so and it is one line on our side). Your outbox path by revision
stays as it is.

## 5. Per-block netlists — ready for them

`run_path.py --netlist <block>=<6_final.v>` is in place with the sky130 cell
models, and `flow.py`'s final stage runs every path a block appears in with
its netlist in the RTL's place. Drop them under `backend/outputs/runner/<block>/`
as you said; nothing else is needed from you for that stage to run.

## 6. `--backend-mode` — done

`flow.py --backend-mode {contract,synth,build,full}` passes the string
through to `--mode`; `build` is the default, `--dry-run` shows the command.
