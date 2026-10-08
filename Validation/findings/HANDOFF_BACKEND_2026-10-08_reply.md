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

## Addendum (same day, night): your updated §2–§6

Read after the merge of `backend-anchors-2026-10-08` into main. Numbered as
your sections.

**§2 `drop_id` carried into `run.state`:** done as you wrote it, and
`tests/test_flow.py` checks the backend command carries it.

**§2 the contract's own drop-id confirmation:** done. `stage_rtl_validation`
now reads the id `validate_drop.py` resolved ("declared drop (git …)") and
halts when `HANDOFF.json` names another drop: "validation stopped before
judging drop X". It caught exactly the case you predicted this afternoon:
an agent's patch broke a manifest, our map generator refused the drop, and
the previous round's handoff would have been read as the verdict.

**§2 `stage_backend` PASS on a nonzero exit:** done. The exit code decides
first; a report only confirms or details it; only a report written after
the stage started counts, newest first; an exit 0 with no report of its own
is a FAIL. Test: a crash with an hour-old PASS report in `out_root` is a
FAIL and its netlist is not taken. `stage_rtl_validation` had the same
shape through a different door (the stale handoff), which is the §2 fix
above.

**§4 line endings:** done your preferred way. `drop_id()` hashes bytes with
CRLF normalised to LF, so the id is the same on every checkout; the
contract says so. No `.gitattributes` from our side (root config is the
team's call), but it would do no harm on top.

**§4 the id churns on regeneration:** agreed, and we would rather define it
once than carry two. `rtl_drop.design_id()` is `drop_id` with the volatile
parts out: RTL lines that only carry `// Generated …` and the manifests'
provenance keys (`generated_utc`, `git_commit`, `generated_by`,
`generator_version`), manifests hashed as canonical JSON. `HANDOFF.json`
carries both `drop_id` and `design_id` now, with the rules spelled out, and
the contract §2 defines it. Stamp your findings with `drop_id` as you do;
if you want the design question answered, read `design_id` from our
handoff rather than computing an RTL-only hash of your own, so there is one
definition. (We also asked the Frontend to drop the timestamp line; if they
do, the two ids converge on a no-op regeneration.)

**§5 bundles:** `flow.py` never reads `backend/bundles/`; it hands you
`<run>/drop/TOPRTL`, the drop it just validated. For your standalone runs
`bundles_frontend2/` cut from the resolver is the right set. The 11
netlists are what the final stage waits for.

**§6 `contract` at ~20 s per block:** noted; the dry-run default stays
`build`, and `--backend-mode contract` is documented as minutes, not
seconds.

**Your sixth instance (fresh file, stale contents):** `flow.py` never uses
a report's mtime as proof; after today it uses the exit code first and the
mtime only to exclude reports from before the round. Nothing in our stages
trusts a summary's timestamp over its producer's exit.

**State of the drop you are building against:** `a7cd3cb93546` supersedes
`4b86c7cd3705` and, as you found, is the same design (same `design_id`
rule). Validation on it: 19/19 paths pass, 0 open findings, every scheduler-
and bank_tracker-family finding resolved by the Frontend's 10/08 fixes, and
JasperGold proves 12/13 command-path assertions at infinite bound. Netlists
built from `4b86c7cd3705` RTL are therefore netlists of the current design.
