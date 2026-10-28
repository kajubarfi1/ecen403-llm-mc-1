# Validation signoff criteria — v1 (2026-09-24)

What "validated" means for an RTL drop of the DDR3 controller, written once so
the cockpit, the plan and the findings ledger all cite the same bar. Numbers
here are measured by `tools/validate_drop.py`; nothing in this document is a
judgement call at signoff time except the waiver decisions, which have a
named approver.

## 1. Drop acceptance (before any verdict is issued)

A drop is accepted for validation only when:

| # | Criterion | Measured by |
|---|---|---|
| A1 | Every block in the interface catalogue resolves to exactly one RTL file and one manifest in the declared drop root (`spec/rtl_drop.json`); no substitution from other trees | `structural/rtl_drop.py` |
| A2 | The drop carries a stamp: git commit, spec `revision`, generation timestamp (contract C1; until the Frontend writes it, our resolver stamp is the record) | `rtl_drop.py stamp` |
| A3 | Manifest `source` fields, the integration map and the harness wiring agree: every named port exists, widths and directions match | `structural/integration_map_gen.py --check`, `chain_harness_gen.py --check` |
| A4 | Spec intake gate has no **new** gaps relative to the previous drop (existing gaps are filed as spec findings and do not block) | `spec/spec_completeness.py` |
| A5 | All generated collateral regenerates from the drop with zero code edits (schemas, monitors, SVA, coverage, vplan, register model) | `validate_drop.py` step 3 |

A drop failing A1 or A3 is returned to the Frontend without simulation.

## 2. Verdict per path and per block

| Level | Criterion |
|---|---|
| Path PASS | every stage checker passes, no assertion failure, no illegal coverage bin, no harness timeout, no X on a checked field, every request conserved (`(conservation)` stage: each catalog `conservation` rule's `from` count produced its `to` count by the end of the run) and every accepted host beat acknowledged (`(host handshake)` stage from the driver's count; expected to fail only on a standalone path with responses tied off) |
| Path FAIL | otherwise; the failing stage and first failing check are recorded, and a finding is emitted (or re-attached to an open one) |
| Block PASS | every path that instantiates the block passes, **and** every formal property owned by the block is proven or bounded-proven to the agreed depth |
| Block PASS-with-waivers | as above, except failures that are covered by an approved waiver (§5) |
| Drop PASS | all 20 paths PASS or PASS-with-waivers, and no critical finding is open |

The 20 paths in `spec/path_definitions.json` are all mandatory. The 17 runnable
ones must simulate; the 3 derived single-hop paths take their verdict from
their host run. No path may be excluded from a drop verdict.

## 3. Coverage targets

Code coverage is measured by IMC on the design modules only (testbench,
monitors, stubs and generated covergroups are excluded by `coverage/cov_conf.ccf`),
merged over exactly the drop's own runs (`measure_coverage.py --since <run start>`,
never over runs of other drops).

| Block | Target | Rationale |
|---|---|---|
| scheduler, cmd_queue, bank_tracker | ≥ 85 % | arbitration and timing state machines; every uncovered branch is a scheduling decision never exercised |
| cmd_gen, addr_decoder, refresh_ctrl, config_regs, calibration, init_fsm | ≥ 90 % | narrow, mostly combinational or single-FSM blocks |
| wb_port, data_path | ≥ 85 % | data movers; the remainder must be in the exclusion list |
| design total | ≥ 85 % | |

Functional coverage: **100 % of reachable bins** in the spec-derived covergroups
(`sva/generated/*_fcov.sv`, `cmd_gen_coverage.sv`). A bin is "unreachable" only
when listed in §4 with a reason; "not hit" is not "unreachable".

Current measurement (drop dab971c2aab9, 2026-10-15, directed + random
stimulus): design 77.2 %; scheduler 79.8 %, cmd_queue 66.0 %, bank_tracker
80.8 %, wb_port 59.9 %, data_path 77.1 %; vplan 34/45 items fully covered
and the other 11 `unreachable_by_spec` (the exact-minimum timing bins under
`timing_model.counter_clock.window_scale = 4`, §4), 0 partial, 0 not
measured (the plan is regenerated from the judged spec on every run since
2026-10-27; the six taxonomy items that regeneration surfaced, tREFI /
tMRD / tMOD and SCHED_001–003 exercised, have coverpoints now, and the
tMOD rule found a Phase 1 defect on the golden drop). Code coverage reached
the target on 2026-10-28: 85.4 % on drop efece348d04e (cmd_queue 85.8,
scheduler 90.3, wb_port 84.3, data_path 78.2, bank_tracker 80.8) once the
host port was driven as the spec describes it (pipelined bursts, `wb_burst`
and `saturate`); that stimulus also found two defects (reply addendum 9).
Functional: 33/45 covered, 11 unreachable by spec, 1 partial
(`cg_refresh.cp_ref_002_exercised`, covered on 10-27, lost while the port
drops half the pipelined traffic; it returns with the wb_port fix).

## 4. Exclusion rules

An uncovered item may be excluded from the target only for one of these
reasons, recorded in `coverage/exclusions.json` with the item, the reason code
and the approver. An entry with `status: proposed` and `approved_by: null` is
a proposal: `coverage/apply_exclusions.py` reports the adjusted percentage it
would give but the raw number stands until a named approver sets
`status: approved`. Three proposals are on file (2026-10-28): the constant
column bits [2:0] of the queue and scheduler entry storage (E-SPEC, the
burst-aligned address mapping fixes them) and the reset defaults (E-RESET).

| Code | Reason | Example |
|---|---|---|
| E-RESET | reachable only during reset or before initialisation completes, and covered by the init paths' assertions instead | default branch of a state machine |
| E-SPEC | the spec forbids the input that would reach it | ECC error handling with `ecc_mode = 0` |
| E-SPEC (automatic) | a timing-boundary bin the spec's own `timing_model.counter_clock.window_scale` places inside the design's enforced window: the exact-minimum spacing cannot occur while the design is declared to hold every command `window_scale` times longer than the JEDEC value. `coverage_rollup.py` reports these as `unreachable_by_spec`, citing the declaration; no entry in `exclusions.json` and no approver, because the spec is the approver, and they return to `partial` when the declaration goes | `cg_timing.cp_trcd_spacing.at_minimum` (3 cycles) on a design that issues ACT→CAS at 14 (2026-10-15) |
| E-DEAD | provably unreachable (formal `unreachable` on the corresponding cover, or a constant-propagation argument cited in the entry) | a case arm under a fixed parameter |
| E-TOOL | tool artefact (IMC counts an item that is not design logic) | |

Not allowed: "hard to hit", "would need a longer run", "not in this phase".

## 5. Waiver policy

A waiver (`waivers/waivers.json`) suppresses ONE check on ONE interface field
or ONE assertion for ONE reason, with `approved_by`, `approved_utc`,
`spec_revision`, the vplan items it touches, and `resolves_when`. Rules:

1. A waiver may only cover behaviour the **spec does not define**. A defined
   requirement that the design violates is a finding, never a waiver.
2. Every waiver names the spec change that retires it (`resolves_when`); when
   that change lands, the waiver is removed by the next `validate_drop.py`
   run, not by hand.
3. Waivers are re-approved per spec revision: a waiver from revision A does not
   apply to revision B.
4. The approver is a named person (today: Jacob Zatopek); a waiver that
   changes a block from FAIL to PASS-with-waivers is listed in the drop report.

Open: W-001 (unmapped CSR read data). Pending decisions W-002/W-003 (see plan
§6 item 12) are not waivers until approved.

## 5b. Phase-partial drops

The Frontend delivers one phase at a time. A drop that lacks blocks is
validated with `validate_drop.py --partial`:

- every block the drop provides is resolved from the declared roots; nothing
  is substituted, ever;
- a path runs only when its whole closure is present (`standalone` paths
  take no closure and tie their cut edges from `standalone_ties`, each with a
  reason); every other path is **blocked**, named with the blocks it waits
  for — a blocked path is not a failure and not a pass;
- findings are emitted with `DROP_STATUS.json`; a finding owned by an absent
  block, or whose every path was blocked, is carried **untested** and stays
  open — a partial drop can never resolve what it did not test;
- partial reports live in `reports/partial/<head>/` and snapshot as
  `<head>-partial`; the reference for the next complete drop is always the
  newest complete one.

A phase is accepted when every path its blocks can run passes and the
block's standalone path (if any) passes; the verdict is explicitly scoped to
the blocks present.

## 5c. Gate-level (the backend's netlists)

A block's netlist (`6_final.v`) is accepted when every path that
instantiates the block passes with the netlist in the RTL's place
(`run_path.py --netlist`), judged by the same models, rules and assertions
as the RTL, with the platform's functional cell models and zero delay. A
netlist that passes RTL-equivalent behaviour but not timing is the
backend's finding (STA), not this gate's. Synthesis flattens the RTL's
unpacked-array ports into packed vectors with element 0 at the most
significant end (measured with `--probe` on the cmd_queue netlist,
2026-10-14); `run_path.py` wraps every netlist in a generated module with
the RTL's port shapes so the harness, monitors and assertions bind
unchanged. `tools/run_netlists.py` runs every block and writes
`reports/netlists/summary.json`.

Two attributions keep that verdict honest (2026-10-15). A pair that
fails on a stage that is not the netlist's block, exactly as the RTL-only
run of the same path fails, is `RTL-FAIL`: the RTL's defect carried into
the harness, not evidence about the netlist, and it does not count
against the block. And provenance is per block: a netlist is evidence
about its own block's RTL, so it is `STALE` only when that block's design
id differs from what it was cut from (`NETLISTS.json` per-block
`design_id`, or `--built-from-rev` from git history), whatever the other
blocks did. Current record (drop `efece348d04e`): all eleven netlists
pass every path the RTL passes; data_path's netlist reproduces the RTL's
read-capture defect (a correct netlist of defective RTL); refresh_ctrl's
is stale (RTL changed after the build).

Current (netlists built from drop 4b86c7cd3705, judged against
dab971c2aab9, 2026-10-14):

"Every path that instantiates the block" means every runnable path whose
simulated harness closure contains the block (declared blocks plus the
support the integration map adds): 116 block-path pairs, not the 60 the
declared lists alone give (2026-10-15).

| block | paths | result |
|---|---|---|
| addr_decoder 11, bank_tracker 11, calibration 3, cmd_gen 11, cmd_queue 11, config_regs 17, data_path 11, init_fsm 5, refresh_ctrl 13, wb_port 12 | 105/105 | PASS, no assertion fired |
| scheduler | 0/11 | FAIL: PROTO_002, TIMING_004, TIMING_005, TIMING_011, the pre-fix scheduler's signature. Judged against the drop it was cut from (`reports/netlists_vs_4b86/`), the netlist fires exactly the assertion counts its RTL did on every path: the netlist equals its RTL, and the RTL is the design before the Frontend's feedback-latency hold (a7cd3cb93546). Rebuild from the current drop |

Note on bank_tracker: its netlist is also pre-fix (per-bank tWTR gating
PRECHARGE, the RTL's TIMING_007), yet it passes all 11 closure paths. The
current scheduler's hold enforces the write-to-read turnaround itself, so
the surrounding RTL masks the old bank_tracker's gap. A gate-level verdict
is on the composed design, as the RTL verdict is; a masked defect in one
block's netlist is not a false pass, but it is not evidence the block is
right either, which is why the ask to rebuild it stands.

## 6. Formal

For the composed command path (`formal/chain_formal.sv`), every generated
timing/protocol assertion must be:

- **proven** (unbounded), or
- **bounded-proven** to ≥ 2 × the longest timing parameter in cycles at the
  spec clock (for tREFI and other long intervals, an abstraction with a
  documented assumption is acceptable), or
- a **counterexample filed as a finding** with its trace, triaged as legal-host
  (defect) or illegal-host (missing assumption, added and re-proved).

An `undetermined` result is a signoff blocker until one of the above holds.

Abstractions are allowed only as named on the `run_formal.py` command
line, and the report records every one under `abstractions`:

- a JasperGold `stopat` cut. A proof under a cut is sound (the cut design
  over-approximates the real one) and counts; a counterexample under a cut
  may be spurious, is marked so in the report, is never filed as a finding,
  and the property falls back to the simulation bar (silent on the
  baseline, fired by at least one seeded fault).
- an **assumed configuration** (`--stopat` on a configuration register plus
  `--assume` fixing it, with `--sva-param` scaling the assertion's bound to
  match; 2026-10-20). This is how a maximum-interval property such as
  tREFI, whose bound no bounded engine can cross (14 040 cycles against a
  reach of ~200), is proved: the interval is assumed shorter and the
  assertion's bound shrinks with it. A proof holds for the assumed
  configuration only and is recorded that way; it counts because the logic
  under proof (counter, saturate, postpone, preempt) does not depend on the
  constant, and the spec's real interval is measured in simulation (7.8 µs
  on the clean drop). The assumed value must keep every other enforced
  window satisfiable (tREFI above the enforced tRFC window), or the
  counterexample is the configuration's, not the design's.

A proof is about a design: `validate_drop.py` (step 4b) re-proves every
path that has ever been proved and has no report that applies to the
design under judgement, with the options of its last report, so a design
change never leaves `awaiting_formal` findings for a person to remember.

Current (efece348d04e, 2026-10-20):
- command path (`path_01`), concrete: 13 proven at infinite bound
  (the 12 timing/protocol properties and, since 2026-10-22, REF_002: never
  REFRESH with a bank open), REF_001 (an urgent refresh acknowledged
  within its spec-derived 184-cycle obligation) bounded-proven to depth
  2 948 against its own bar of 368, 0 counterexamples, 1 undetermined
  (tREFI at its 14 040-cycle bound), covers 15/15. The bounded bar is per
  property: twice that property's own bound, not twice the longest in the
  module. On 5661e03 this was 4 proven / 8 CEX; the Frontend's scheduler
  hold closed every counterexample.
- command path, assumed configuration (tREFI 516 nCK = 129 cycles, just
  above the enforced tRFC window; max_postpone 1, urgent at 1; assertion
  bound 258): 10 proven at infinite bound, tREFI **bounded-proven to depth
  9 272** (bar 516), 0 counterexamples; the postponed-refresh cover
  reached at 136 cycles. PROTO_001/002 are bounded to the same depth in
  this run and proven at infinite bound in the concrete one. A proof under an assumption
  holds for that configuration; the spec's interval is measured in
  simulation.
- boot path (`path_08`, init_fsm + calibration): CAL_001/CAL_002 proven
  concretely; with `u_init_fsm.wait_cnt` cut, INIT_001 (×2), INIT_002 and
  INIT_003 proven at infinite bound, covers 5/5; `a_INIT_002_init_done`
  graded by simulation (measures the cut wait).

## 7. Known-good reference and false-positive bar

The checkers themselves are signed off against UberDDR3 (`refdesigns/uberddr3/`):
0 assertion failures, 0 data-integrity mismatches, 0 host-to-pin address
mismatches, with the Micron model as the independent cross-check (last run
2026-10-13, validator cb2dc77: `reports/uberddr3/known_good_cb2dc77.json`,
path checkers 0 violations). Any change
to a generator or rule must re-run that suite and keep it at zero; a sanity
mutation must still fire.

## 8. Regression history

Every drop's reports, sim logs and observed traces are snapshotted under
`reports/drops/<commit>/`, and `tools/compare_drops.py` classifies each path
against the previous drop (same / fixed / changed / regression). A **regression**
row (a check that newly fails or grows) blocks the drop verdict until it is
either a filed finding or shown to be a stimulus/coverage-model change (the
comparison notes say which).

## 9. Signoff package contents

1. Drop stamp and resolver record (A1–A2).
2. Path verdict table with first failure per failing path.
3. Coverage: per-block code %, functional bins, exclusion list, targets met/not met.
4. Formal table per property.
5. Findings ledger: open, resolved-in-this-drop, introduced-in-this-drop; every open critical named.
6. Waivers in force with approver.
7. Known-good suite result for the checker version used.
8. Comparison against the previous drop.

`tools/dashboard_gen.py` renders 1–8 from the same JSON files; the package is
the dashboard plus the files it cites.
