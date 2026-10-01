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
| Path PASS | every stage checker passes, no assertion failure, no illegal coverage bin, no harness timeout, no X on a checked field |
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

Current measurement (drop 1fea117, baseline stimulus, before constrained-random
v2): design 75.1 %; scheduler 71.4 %, cmd_queue 58.4 %, bank_tracker 78.5 %,
wb_port 59.5 %, data_path 76.7 %; vplan 27/39 items fully covered. The gap to
target is what the closure loop and constrained-random v2 exist to close.

## 4. Exclusion rules

An uncovered item may be excluded from the target only for one of these
reasons, recorded in `coverage/exclusions.json` (to be created with the first
exclusion) with the item, the reason code and the approver:

| Code | Reason | Example |
|---|---|---|
| E-RESET | reachable only during reset or before initialisation completes, and covered by the init paths' assertions instead | default branch of a state machine |
| E-SPEC | the spec forbids the input that would reach it | ECC error handling with `ecc_mode = 0` |
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

Abstractions are allowed only as JasperGold `stopat` cuts named on the
`run_formal.py` command line; the report records them under `abstractions`.
A proof under a cut is sound (the cut design over-approximates the real one)
and counts; a counterexample under a cut may be spurious, is marked so in the
report, is never filed as a finding, and the property falls back to the
simulation bar (silent on the baseline, fired by at least one seeded fault).

Current (5661e03):
- command path (`path_01`): 4 proven, 8 CEX filed/attributed, 1 undetermined
  (tREFI).
- boot path (`path_08`, init_fsm + calibration): CAL_001/CAL_002 proven
  concretely; with `u_init_fsm.wait_cnt` cut, INIT_001 (×2), INIT_002 and
  INIT_003 proven at infinite bound, covers 5/5; `a_INIT_002_init_done`
  graded by simulation (measures the cut wait).

## 7. Known-good reference and false-positive bar

The checkers themselves are signed off against UberDDR3 (`refdesigns/uberddr3/`):
0 assertion failures, 0 data-integrity mismatches, 0 host-to-pin address
mismatches, with the Micron model as the independent cross-check. Any change
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
