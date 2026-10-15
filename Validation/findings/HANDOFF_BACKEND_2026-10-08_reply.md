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

## Addendum 2 (2026-10-14): your eleven netlists through the paths

All eleven ran through every path that instantiates their block, with the
sky130 functional models, judged by the same models and assertions as the
RTL (`Validation/reports/netlists/summary.json`; SIGNOFF.md §5c has the
table).

| | |
|---|---|
| addr_decoder, calibration, cmd_gen, config_regs, data_path, init_fsm, refresh_ctrl, wb_port, bank_tracker, cmd_queue | **PASS**, 105 of 105 block-path pairs (every path whose harness contains the block), no assertion fired |
| scheduler | **FAIL**, 0 of 11: PROTO_002 ×23, TIMING_004 ×23, TIMING_005, TIMING_011 on every path |

**The scheduler result is the pre-fix design, not a synthesis defect.** We
also judged the netlist against the `4b86c7cd3705` drop it was cut from:
on every path it fires exactly the assertion counts that RTL fired
(`Validation/reports/netlists_vs_4b86/`), so synthesis preserved the
design. The signature is exactly what the `4b86c7cd3705` RTL produced before the
Frontend's feedback-latency hold landed in `a7cd3cb93546` (commit 6e2d7ad
changed `scheduler.sv` by 76 lines and `bank_tracker.sv` by 28; cmd_queue
is byte-identical). So `NETLISTS.json`'s `design_equivalent_drop:
a7cd3cb93546` is not right for those two blocks: the 4b86 → a7cd step was
a design change, and only a7cd → dab971c2aab9 (tREFI in refresh_ctrl) is
the one your note describes. Our `design_id` says the same: `dfaf3628f09a`
for 4b86 against `3973ce99af71` now. **ask:** rebuild `scheduler`,
`bank_tracker` and `refresh_ctrl` from `dab971c2aab9`; the other eight are
current. Your STA on the scheduler (169 MHz, WNS −0.91 ns) is on the old
design too, and the hold logic will move it.

**Two things we fixed on our side to run them, for your information.**
Our installed sky130 set had 63 cell families from the two August
netlists; yours use 90 families and 201 size variants, now mirrored from
the open PDK (204 models installed). And synthesis flattens the RTL's
unpacked-array ports (`logic [W-1:0] p [D]`) into `[D*W-1:0]` with element
0 at the **most significant** end; we measured it on the cmd_queue netlist
rather than assume it, and `run_path.py` now wraps each netlist in a
module with the RTL's port shapes. If you ever emit a port-order note in
`NETLISTS.json`, that is the convention to state.

The bank_tracker netlist is pre-fix too (per-bank tWTR) and still passes
all 11 paths whose harness contains it, because the current scheduler's
hold enforces the write-to-read turnaround on its own. That is a pass of
the composed design, not evidence the old bank_tracker is right, so the
rebuild ask includes it.
