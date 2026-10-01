# LVS + DRC for ORFS sky130hd — working configuration

The ORFS-shipped `platforms/sky130hd/lvs/sky130hd.lylvs` has never produced a
valid result here. This directory holds the configuration that does, and the
evidence that it passes good layouts and fails deliberately broken ones.
DRC scripts and evidence are in `../drc/`.

## Result (batch run 2026-09-10, flow image openroad/orfs:latest = 26Q1)

All 11 blocks, produced end to end by `pipeline_batch.py` with the new validator
(sign-off results written 12:24 to 13:03):

| block | LVS | nets / pins compared | black-boxed inst. | audit: pins / feedthroughs | DRC |
|---|---|---|---|---|---|
| addr_decoder | match | 31 / 31 | 0 | 60/60, 25/25 | 0 |
| bank_tracker | match | 4184 / 287 | 4 | 287/287 | 0 |
| calibration | match | 103 / 8 | 0 | 9/9 | 0 |
| cmd_gen | match | 283 / 102 | 0 | 106/106 | 0 |
| cmd_queue | match | 1996 / 595 | 2 | 595/595 | 0 |
| config_regs | match | 1225 / 333 | 0 | 333/333 | 0 |
| data_path | match | 2508 / 173 | 0 | 173/173 | 0 |
| init_fsm | match | 199 / 28 | 1 | 36/36 | 0 |
| refresh_ctrl | match | 222 / 46 | 0 | 46/46 | 0 |
| scheduler | match | 5030 / 753 | 4 | 754/754 | 0 |
| wb_port | match | 537 / 189 | 0 | 221/221, 32/32 | 0 |

Evidence: `evidence_2026-09-10_batch.log`, generated from each block result file.

**Why these numbers differ from the first table made earlier the same day.** That table
was measured by hand on the April 25 layouts. The batch rebuilt every block from unchanged
RTL, and 8 of 11 netlists changed: same flip-flops, different gate mapping (config_regs
went from 1,883 to 1,225 compared nets). During the April runs the repair, tuner and
optimizer steps had written extra settings into config.mk (5 to 13 lines per block; for
example, on 2026-03-31 the Fmax optimizer tightened config_regs from a 10 ns to a 1.912 ns
clock). The packager rewrites config.mk from scratch on every run, so the batch used clean
defaults. Both layout sets passed. The layouts above are current and reproducible from the
code alone; the hand-run evidence for the April layouts is in `evidence_2026-09-10.log`
and `evidence_2026-09-10_cmd_gen_init_fsm.log`. The negative controls below were run on
the April layouts with the same deck and scripts.

cmd_gen and init_fsm were first re-run on 2026-09-10 after the `_normalize_rtl` fix; their
old GDS (built from RTL missing ddr_addr/init_addr) is kept as
`flow/{results,logs,reports}/sky130hd/<block>_stale_0421`.

## Negative controls (every one must FAIL — all do)

| check | mutation | blocks | outcome |
|---|---|---|---|
| LVS | swap a flip-flop's CLK and D | config_regs, cmd_queue, cmd_gen, init_fsm | mismatch |
| LVS | delete one cell | config_regs, cmd_queue, cmd_gen, init_fsm | mismatch |
| LVS | swap inputs on a black-boxed cell | scheduler, cmd_queue | mismatch |
| audit | pair each feedthrough with the wrong partner | addr_decoder, wb_port | 0 accepted |
| DRC | inject 3 illegal met1 shapes into a GDS copy | config_regs | 6 violations (m1.1, m1.2, m1.6) |

## Deck changes (sky130hd_fixed.lylvs vs vendor)

1. `report()` -> `report_lvs()` — vendor deck never wrote an LVS database.
2. `connect(METnPIN, METnTXT)` + `connect(METn, METnPIN)` (n=1..5, LI) — pin labels sit
   on pin-purpose shapes the vendor deck never bound; 268/333 pins were lost.
3. `connect_global(PTAP, "VNB")` — p-taps contact the substrate; without it the
   substrate never joins VSS and every cell's bulk mismatches.
4. `netlist.simplify` -> `make_top_level_pins` + `combine_devices` (no purge) — purge
   deletes pin-only nets (feedthroughs, unused ports) and device-less circuits.
5. `blank_circuit` for a2111oi_2, a211oi_4, o211ai_4, a21oi_2 — SkyWater's GDS for these
   cells has more transistors than its own CDL (split series branches), so they are
   compared by pin connectivity only (11 instances in the 2026-09-10 batch). All other cells: transistor level.

## Reference-netlist prep (prep_reference.py)

OpenROAD's `write_cdl` and KLayout's SPICE reader lose information the layout keeps:
- tap cells removed (no devices); antenna diodes removed (deck has no diode extraction;
  72 instances in the 2026-09-10 batch: bank_tracker 5, cmd_queue 1, config_regs 1, data_path 1, scheduler 64)
- `conb_1` ties: CDL `short` means the nets are joined — instance removed, nets joined
- `assign` feedthroughs dropped by write_cdl — nets joined (pin names preserved)
- library `.SUBCKT`s included only if instantiated, copied verbatim from the vendor CDL

## Known blind spot and how it is covered

KLayout's comparison does not check nets that touch only pins (verified: cutting a
feedthrough still "matches"). `audit_pins.rb` covers it: every schematic pin must exist
as a layout label, and both ends of every pin-to-pin `assign` must share one layout net.

## Limitations to state in any writeup

- 11 cell instances verified at pin level only (vendor GDS/CDL disagree for 4 cells).
- 72 antenna diodes excluded from LVS.
- Block timing in the table above is optimistic: those runs used a constraint.sdc with only
  the clock, so only register-to-register paths were timed. Since 2026-09-10 the packager
  writes ORFS-style input and output delays (20% of the period on every port), so the next
  batch run times port paths too. Checked on cmd_gen: the old file left 87 endpoints and 39
  inputs unconstrained, the new one leaves none.
- addr_decoder has no flip-flops and no clock, so there is nothing to time. Since 2026-09-10
  the pipeline reports its STA as N/A (no timing paths) instead of a PASS.
- DRC/LVS decks are the ORFS-bundled KLayout decks (with the fixes above), not a
  foundry-certified sign-off deck.

## Pipeline integration (2026-09-10)

`agents/pipeline.py` validator_node runs these checks through `signoff/signoff_runner.py`
inside the ORFS container, in the order DRC, then LVS plus pin audit, then STA.

- A check that cannot run (Docker off, deck missing, CDL cannot be generated, results
  stale) returns ERROR and halts the pipeline. Previously such cases reported PASS.
- Outputs per design: `<out_root>/validator/<design>/signoff/` holds signoff_result.json,
  drc.lyrdb, lvs.lvsdb, reference.cdl, extracted.cir and one log per step.
- Pre-change code: `agents/pipeline.py.bak_2026-09-10` (later steps: `*.bak_2026-09-10_*`).
- STA that cannot determine slack halts as NOT VERIFIED (it used to warn and pass), and a
  missing slack value is no longer read as 0 ns. A block with nothing to time reports N/A.
- The Fmax tuner rewrites the period in both SDC styles and warns if it finds none.

Tested 2026-09-10: validator_node gives PASS on cmd_gen, and NOT VERIFIED (halt) with
USE_DOCKER=0 and with a missing design config. The runner matches the manual numbers
on config_regs and addr_decoder, and its self-test (`--mutate swap`) fails LVS as required.

Run the runner alone (from the ORFS flow directory, inside the container):

    python3 /signoff/signoff_runner.py --design <block> --platform sky130hd --out <dir> [--mutate swap|delete]

## Upstream

Deck items 1–3 would break LVS for any ORFS sky130hd design; worth reporting to ORFS.

## Full-chip sign-off (2026-09-16)

The integration scaffold `ddr3_controller` (11 blocks flattened, generated by
`integration/generate_top.py`) went through the same pipeline as a leaf block and
signed off clean:

    DRC   PASS  0 violations                     315 s KLayout
    LVS   PASS  match, 13528 nets / 556 pins      59 s
    audit PASS  601/601 pins in layout, 32/32 pin-to-pin feedthroughs
    STA   PASS  WNS +1.70 ns, TNS 0, hold +0.44 ns

Layout: die 801,338 um2 (0.90 x 0.90 mm), 23,587 std cells, 23.9% utilization,
0 routing violations, 50.7 mW, Fmax 120.5 MHz. GDS 25,491,450 bytes.

Reference netlist prep on the full chip: 10,174 taps, 51 diodes, 13 tie cells,
32 feedthroughs, 7 pin aliases, 144 library cells, no missing definitions.

Black-boxed in LVS are layout-only cells with no schematic counterpart: VIA arrays,
`__fill_*`, `__tapvpwrvgnd_1`, `__diode_2` and `__conb_1`. These carry no device-level
connectivity to compare, so flattening them is correct, not a skipped check.

This is an integration scaffold, not a functionally complete controller: it wires the
50 connections the frontend declared and promotes the remaining 111 signals to chip
pins. It is structurally a real chip; `calibration` and `data_path` still drive nothing
internally until the frontend backfills the `source` fields.

## Stale-artifact failure and the two provenance checks (2026-09-17)

A full 11-block batch run exposed a bug in the backend, not in the decks.

**What happened.** ORFS make died at `3_1_place_gp_skip_io` with
`mv: cannot stat .../3_1_place_gp_skip_io.tmp.log` — a filesystem race on the Docker
bind mount under 11 parallel containers. The flow still rewrote `6_final.odb`,
`6_final.def` and `6_final.v`, but the GDS merge never ran, so `6_final.gds` stayed at
its 2026-09-10 version. The runner then hit this:

    [runner] GDS exists despite exit_code=2 - treating as success.

Existence was being read as proof of completion. DRC and LVS went on to certify
week-old geometry for 10 of 11 blocks, reporting 8 PASS. Only `addr_decoder`, which
finished early enough to avoid the race, exited 0 and produced a current layout.
The same staleness explains why WNS was unchanged from the previous batch: the final
timing report is generated from `6_final.sdc`, also left at its pre-I/O-delay version.

Three blocks (`bank_tracker`, `data_path`, `scheduler`) failed instead of passing,
because CDL generation tried to rebuild the missing upstream steps and exceeded the
900 s sign-off timeout. The halt gate refused to certify what it could not rebuild —
working as designed.

**Fix 1, runner provenance** (`agents/pipeline.py`, backup `.bak_2026-09-17_runner`).
A non-zero make exit is still allowed to be overridden by a finished GDS, because ORFS
does exit non-zero on late cosmetic failures. But the GDS must be one *this run* wrote.
`_gds_is_from_this_run` applies two independent tests: the GDS must not predate the
moment make launched (host clock), and must not be older than `6_final.def` (same-run
consistency, immune to host/container clock skew). A legitimate override is recorded in
`runner_result["gds_exit_override"]` so it is never indistinguishable from a clean run.

**Fix 2, sign-off provenance** (`signoff/signoff_runner.py`, backup `.bak_2026-09-17`).
`assert_gds_is_current` runs before any check. ORFS writes the final artifacts in a fixed
order with the merged GDS last (`6_final.odb -> .def -> .v -> .gds`), so in a complete run
the GDS is the newest of the four. If any of the others is newer, the merge did not run
and sign-off halts. This is independent of the runner, so a stale layout cannot be
certified regardless of what invoked the flow.

The two checks cover different faults: the runner catches a layout left over from an
earlier run; the sign-off check catches a layout inconsistent with the netlist beside it.
A block whose whole artifact set is old but self-consistent is correctly still signable.

**Verified** on the real files: the three blocks rebuilt at low parallelism are accepted,
`cmd_gen`, `config_regs` and `wb_port` (stale GDS, fresh netlist) are halted, and the
DEF-consistency test still catches all three with the clock test disabled.

**Operational note.** Run the batch at reduced parallelism. `--max_workers 2` completed
the GDS merge cleanly on all three large blocks; the default of one worker per block
(11 here) triggered the race.

## Result (batch run 2026-09-17) — current code, all layouts rebuilt

The first batch in which every block was built and verified by the same run, with the
runner and sign-off provenance checks both active. All 11 pass.

| block | LVS | nets / pins | black-boxed | audit: pins / feedthroughs | DRC | STA |
|---|---|---|---|---|---|---|
| addr_decoder | match | 31 / 31 | 0 | 60/60, 25/25 | 0 | N/A n/a (no timing paths) |
| bank_tracker | match | 4192 / 287 | 4 | 287/287 | 0 | PASS 3.683 ns |
| calibration | match | 104 / 8 | 0 | 9/9 | 0 | PASS 6.508 ns |
| cmd_gen | match | 282 / 102 | 0 | 106/106 | 0 | PASS 6.363 ns |
| cmd_queue | match | 1995 / 595 | 2 | 595/595 | 0 | PASS 5.424 ns |
| config_regs | match | 1229 / 333 | 0 | 333/333 | 0 | PASS 5.211 ns |
| data_path | match | 2493 / 173 | 0 | 173/173 | 0 | PASS 3.442 ns |
| init_fsm | match | 198 / 28 | 1 | 36/36 | 0 | PASS 5.799 ns |
| refresh_ctrl | match | 222 / 46 | 0 | 46/46 | 0 | PASS 4.252 ns |
| scheduler | match | 5094 / 753 | 4 | 754/754 | 0 | PASS 0.886 ns |
| wb_port | match | 537 / 189 | 0 | 221/221, 32/32 | 0 | PASS 4.136 ns |

Evidence: `evidence_2026-09-17_batch.log`. Machine-readable results for every block are
committed under `signoff/results/<block>.json` — these are the files the table is
generated from, not a transcription of them.

Timing in this table is the first to include port paths (the packager now writes input
and output delays at 20% of the period). Earlier runs timed only register-to-register
paths, so WNS and Fmax in the 2026-09-10 table above were optimistic: scheduler, for
example, reported 1072 MHz then and 110 MHz here. The DRC, LVS and audit columns are
unaffected by that change.

## Two vacuous-result fixes (2026-09-24)

**Bundle validator could pass a set with no connections.** Every cross-bundle check was
per-port: it asked whether a declared `source` resolved, never whether any were declared.
A set whose manifests carried no `source` at all therefore reported a clean PASS while
describing blocks that drive nothing and are driven by nothing, each port silently
promoted to a chip pin. Measured on three disconnected Phase 1 bundles: PASS, 0 internal
nets, 81 top-level pins.

`schema/validate_bundles.py` now adds SET-030 (ERROR: more than one block and not one
declared connection) and SET-031 (WARNING: some blocks have no connection in either
direction), and the console report leads with connectivity coverage. Verified: the
disconnected set now FAILs, the 11-block sets still report PASS_WITH_WARNINGS, and
SET-031 correctly stays quiet for a block whose outputs are consumed even though none of
its inputs carry a source. Backup `schema/validate_bundles.py.bak_2026-09-24`.

**Batch default steered into the known parallelism failure.** `--max_workers` defaulted to
one worker per block, which is the configuration that corrupted the 2026-09-17 run. The
safe limit was documented but not enforced. `agents/pipeline_batch.py` now defaults to
`SAFE_MAX_WORKERS = 2` and warns when a higher value is requested explicitly. Backup
`agents/pipeline_batch.py.bak_2026-09-24`.

## Tuner fixes: optimization that could not tell it had made things worse (2026-09-24)

A single-block run of `cmd_gen` with `--enable_autotuner --optimize_fmax --optimize_power`
(946 s, 8 ORFS runs) exposed four defects. All four are the same pattern as the rest of
this file: a stage reporting success without checking it produced something better.

**Power optimization shipped a regression.** Baseline 0.6385 mW; iteration 1 improved to
0.5997 mW; iterations 2 and 3 made it worse (0.6807, then 0.7530). The tuner kept the last
iteration, so the delivered layout was 18% worse on power and 39% larger than doing no
optimization at all — 15,090 um2 and 542 cells against 10,840 and 391 — and the pipeline
reported PASS. Worse, iteration 3 was told power had risen, concluded its settings "weren't
fully applied", and applied more of them, spreading the design further and adding the wire
capacitance that was driving power up.

`_best_power_observation` now selects the lowest-power observation that still closes
timing, the baseline is a legitimate winner, and a regression stops optimization and
reverts config.mk to the best configuration instead of asking for another proposal.

**Both tuners discarded their final result.** Each records the metrics it was given, then
proposes the next change, so the run following the last proposal had no row. The Fmax
phase closed at 2.561 ns with +0.661 ns of slack and reported 2.972 ns — the previous
iteration. Recording the final observation raises the reported result from 336.47 MHz to
390.47 MHz on the same run. `_with_final_observation` and `_with_final_fmax_observation`
close this; both are idempotent, and the Fmax one is captured at the tradeoff transition
because the clock is reset to the original period for the power phase.

**The summaries were never written in tradeoff mode.** Both writers were guarded by
`and not in_tradeoff`, so a run using both optimizers wrote only the tradeoff report.
`fmax_summary.json` and `power_summary.json` on disk were from 2026-04-14 and 2026-04-21 —
five months stale and indistinguishable from current results. Now always written.

**The tradeoff report mixed iterations.** It took `power_mw` and `wns_ns` from the best
iteration and `area_um2` and `utilization_pct` from the final run, then reasoned about the
difference: the 2026-09-24 report explained a 39% area increase as "high-Vt cells with
larger footprints", which was an artifact of the mixed rows. Every field now comes from one
observation, and the report carries `delivered_is_best`, `delivered_power_mw` and
`baseline_power_mw` so a reader can see whether the layout on disk is the one described.

Verified by replaying the real 2026-09-24 numbers: best selection picks 0.5997 mW (-6% vs
baseline) where the old code shipped 0.7530 mW (+18%); the Fmax summary reports 390.47 MHz
instead of 336.47; the regression guard fires at iteration 2, before iteration 3 ever runs.
Edge cases covered: nothing beats the baseline, a lower-power run that breaks timing, no
usable rows, and repeated calls to both append helpers. Backup
`agents/pipeline.py.bak_2026-09-24_tuners`.

**Still open.** The layout on disk is the last run, not the best. The guard reverts
config.mk and the report flags `delivered_is_best: false`, but making the artifact match
the claim needs one confirming re-run at the best configuration.

## Black-box list is now detected, not enumerated (2026-09-24)

Running `scheduler` at the spec's 5 ns target failed LVS:

    LVS HARD FAIL - netlists do not match; top circuit status Skipped;
    cells not matching: SKY130_FD_SC_HD__A21BOI_2, SKY130_FD_SC_HD__O211A_4

Neither cell was a design defect. Both show the same SkyWater GDS/CDL device-count
disagreement as the four cells the deck already black-boxed:

    a21boi_2   layout=10  cdl=8    delta +2
    o211a_4    layout=14  cdl=10   delta +4
    nand2_1    layout=4   cdl=4    agree   (control)

The tighter timing constraint made synthesis reach for two gates no earlier run had
used. Because the list lived in the deck as a literal, it only ever contained cells
that had already broken a run - so every new synthesis choice could produce a failure
that is indistinguishable from a real mismatch, and the top-level comparison is
skipped, meaning the design itself goes unverified.

`signoff/lvs/detect_blackbox.py` finds the condition instead: it compares device
counts per library cell between `extracted.cir` and `reference.cdl` and reports any
that disagree. A cell is only added when it has devices in both files, so a zero count
(already black-boxed, or absent) is never mistaken for evidence. The list lives in
`blackbox_cells.txt`, the evidence in `blackbox_cells.json`, and the deck reads the
list rather than hardcoding it.

`signoff_runner.py` runs the detector on an LVS mismatch and retries once if it finds
anything, recording what it added under `lvs.blackbox_auto_added`. One retry only - a
second failure is not a library problem.

Two things this cost, both worth knowing. Black-boxing means pin-level comparison only,
so the documented total goes from 11 instances to 13. And the deck is an XML wrapper
around the Ruby: `&` must be written `&amp;`, and Ruby in the ORFS container defaults
to US-ASCII, so `blackbox_cells.txt` is kept ASCII-only and the deck reads it with an
explicit UTF-8 encoding. Both of those were caught by syntax-checking the extracted
script inside the container rather than trusting it to work.

Verified: the detector finds exactly the two real disagreements and nothing else across
the whole library, is idempotent, the deck's XML parses, its Ruby passes `ruby -c` in
the container, and Ruby reads the list back as 6 cells. Backups
`sky130hd_fixed.lylvs.bak_2026-09-24`.

**Not yet proven end to end**: no LVS run has been done since the change. Re-running
`scheduler` at 5 ns is the real test, and it will also answer whether that netlist
actually matches - the earlier failure skipped the top-level comparison, so it explained
the failure without clearing the design.

## Reporter could report a previous run's metrics (2026-09-29)

A Docker outage mid-batch failed five blocks with `docker exit 125`. The pipeline
halted them correctly, but the reporter still returned timing for four of them -
`data_path` 3.442 ns, `refresh_ctrl` 4.252, `wb_port` 4.136, `scheduler` -0.952 -
read from ORFS reports dated 2026-09-17 and 2026-09-24, at a different clock period.
The numbers were plausible enough to nearly reach a status-update slide.

`_parse_metrics` reads whatever reports are in the ORFS tree and cannot tell a fresh
one from a leftover. `reporter_node` now withholds all design metrics when the runner
did not pass, keeping them under `metrics.withheld_values` so a failure is still
debuggable while nothing downstream can mistake them for the current run.

This is the third place the same fault appeared: the runner accepted a stale GDS
(fixed 2026-09-17), sign-off could certify a layout older than its netlist (fixed
2026-09-17), and now the reporter. The common shape is a stage reading an artifact
without establishing that the artifact belongs to the run being reported.

Verified by replay: the four contaminated cases return None with the old values
preserved under `withheld_values`, a passing run is untouched, and a failed run with
no reports on disk does not crash. Backup `agents/pipeline.py.bak_2026-09-29`.

## Run modes for orchestration (2026-10-01)

The backend now declares four tiers so an orchestrator can choose depth by name and
know roughly what it costs. A full optimization run takes hours, far too slow to sit
inside an automated loop; a contract check takes seconds. Naming the tiers is what
lets a loop use a cheap one and keep optimization as a terminal stage.

    contract  23 s    manifest and RTL satisfy the interface. No Docker, no layout.
    synth     42 s    the RTL synthesizes. ORFS target `synth`. No sign-off.
    build     ~1 hr   reaches a clean signed-off layout (11 blocks).
    full      hours   build plus PPA optimization. Terminal stage, runs once.

`--mode` on both pipeline.py and pipeline_batch.py; `full` implies the three tuner
flags so a caller names one thing rather than three. Every run records `mode` and
`checks_applicable` in the final report: a PASS from `contract` and a PASS from
`build` mean very different things and a consumer must be able to tell them apart
without inferring it.

A tier that produces no layout returns PASS without running DRC/LVS/STA. That is not
a skipped check - the tier never claimed them - and `checks_applicable` says so.

**Fourth instance of the stale-artifact fault, found while testing this.** A synth run
reported `gds`, `def`, `spef`, `timing_rpt` and four more as artifacts, all written two
days earlier, because the files existed in the ORFS tree and nothing established when.
An orchestrator reading `artifacts.gds` from a synth run would have been handed a
two-day-old layout. `_collect_artifacts` now filters on the run's start time and names
what it excluded. Verified: synth reports 4 artifacts and names 8 exclusions, while a
build run still collects all 29 with none wrongly dropped.

Gate tiers also skip the Claude narrative report, which is latency on output an
orchestrator does not read; that took contract from 38 s to 23 s. The remaining 23 s is
intake's own LLM summary and could come out too.

Verified end to end on real bundles: contract on the frontend's top-level module
(bundles_top), synth and build on addr_decoder. Backups agents/*.bak_2026-10-01.

## Timing findings emitted upstream (2026-10-01)

The backend used to terminate: it produced a verdict ("STA FAIL, WNS -0.915 ns") and
stopped. That tells the backend owner the block is slow and tells the frontend nothing
they can change. For the three-subsystem pipeline the backend has to participate, so a
timing failure now emits a routable record naming the owning module, the failing path
and the deficit.

`findings/emit_findings.py` parses an ORFS 6_finish.rpt for failing paths, endpoints,
slack, logic depth and the arrival-vs-required split, and writes a record in
Validation's `validation-findings/2` envelope to a drop-stamped outbox mirroring their
layout. validator_node calls it when STA fails, best effort: a failure to emit never
changes the pipeline verdict, which is established by the checks themselves.

The record carries TNS alongside WNS and says what the ratio means. On scheduler, WNS
-0.91 ns against TNS -29.32 ns is "many endpoints failing, not a single outlier" -
the difference between nudging one path and restructuring the block, which the reader
should not have to work out.

Three things the testing caught:

- `report_checks` prints the worst path twice (once for -path_delay max, again under
  its path group), so the same path arrived twice and would have overstated how many
  endpoints fail. Deduped on startpoint, endpoint and slack.
- The finding id was built from the endpoint `cmd_row[5]$_DFFE_PN0P_`. That suffix is
  a synthesis-generated instance name that changes when the block is re-synthesised,
  so the finding would not have matched itself across drops and lifecycle tracking
  would have broken silently. The id keys on the RTL signal; the full instance stays
  in the evidence.
- The drop stamp came back null because ddr3_backend sits beside the team repo rather
  than inside it. BACKEND_GIT_REPO covers that, and the emitter warns when no head is
  resolved, because a finding that cannot be tied to a code state has lost most of its
  value.

Lifecycle is verified: re-emitting a finding preserves `first_seen`, and a run where
timing closes marks the previous finding resolved with `resolved_in`. The outbox is a
ledger, not a snapshot, so a consumer can tell a fixed defect from one never re-tested.

**Five fields are backend decisions pending agreement with Validation**, each marked
PENDING in the source and all additive, so a consumer that ignores them still works:
the `kind` value (`timing_defect`, extending their hardcoded `rtl_defect`), the
severity mapping (ERROR/WARNING/INFO against their rules-driven `major` default), an
anchor without a line number (synthesis does not preserve one), a `suggested_fix`
field the schema has no home for, and the outbox location.

A sixth is worth raising: the anchor names the bundle path the backend read, not the
upstream source. `Frontend2/OutputFolders/PHASE3RTL/scheduler.sv` would be far more
useful to the team that has to fix it, but the backend is never told it - that needs a
manifest field the frontend fills in.
