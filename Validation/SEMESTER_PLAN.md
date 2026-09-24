# Validation: semester assessment, validation plan, integration plan

Written against the repo as of drop `b4d6f45` (2026-09-17), after reading all
three subsystems. Facts about the teammates' subsystems cite file paths so
they can be checked.

**Progress (2026-09-18).** Phase A: seeded-fault suite done (13/13 detectable
faults killed, 2 masked by open defects; `faults/`), determinism proven
(`tools/compare_drops.py --strict`, 16/16 paths identical incl. traces),
feedback loop steps 1–4 built (`findings/emit_findings.py`,
`findings/retry_adapter.py`, `tools/compare_drops.py`). All 20 paths now
carry first-class reports (single-hop paths derived from their host run;
path_07 has its own burst stimulus). One command runs a drop end to end:
`tools/validate_drop.py`.

**Progress (2026-09-24).** Phase A closed: the second preset spec
(`builds/ddr3_mc_800_x8_1lane_1rank/microarch_spec.json`, the Frontend's
`low-cost-embedded` preset: DDR3-800, x8, 1 byte lane, in-order, close-page)
went through every generator with zero code edits
(`tools/spec_swap_check.py`, report `reports/spec_swap_low_cost_embedded.json`).
Timing bounds, coverage bins, vplan targets and CSR reset values all moved with
the spec; no golden-only literal survived; intake gate reports the same 10 gaps
on both specs (so the compiler omits the same fields the golden spec does, a C2
item for Lehana); the width gate's expectation followed the spec (8-bit DQ).
Two observations for Phase B: (1) at the preset's 10 ns controller clock,
tRRD/tRTP/tWTR (TIMING_005/007/009) collapse to one cycle and `sva_gen.py`
correctly declines to emit them, so those three parameters are unverifiable by
SVA at controller-clock granularity for slow configurations; formal or a
DDR-clock monitor would be needed. (2) Six block covergroups and the transaction
schemas changed only in their provenance header, which is expected (they are
manifest-driven) but means a spec-only change to queue depth or lookahead is not
reflected in bins until the RTL drop for that spec exists.

**Progress (2026-09-24, Phase B started).** Olympus rejects both the stored
password and the local key, and no simulator or formal tool is installed on
this machine, so every sim/coverage/JasperGold item waits on credentials.
Started with the local item: the integration map is now DERIVED from manifest
`source` fields (`structural/integration_map_gen.py`, run by `validate_drop.py`
step 3). 50 of the 71 edges come from manifests; the 21 the manifests lack
live in `structural/integration_overrides.json` with glue/expr_glue/ties/
requires/stubs, and each is a filed finding (`findings/outbox/
integration_map_findings.json`: 5 manifest-gap findings covering 21 ports in
wb_port, cmd_queue, bank_tracker, refresh_ctrl, config_regs; 2 wrong-source
findings where data_path's manifest claims a direct driver the design cannot
use). Proof of equivalence: same 71-edge set, and all 17 runnable chain
harnesses regenerate byte-identical. `--check` detects a stale map;
`tests/test_integration_map_gen.py` (8 tests) pins the behaviour. UberDDR3 is
fetched to the scratchpad for the known-good target: it vendors the Micron
DDR3 model (`testbench/ddr3.sv`), is a 4:1 controller at 83–100 MHz with
SPEED_BIN presets for 1066/1333/1600, and ships SymbiYosys formal for its
Wishbone slave — the spec for its configuration is the next local step.

**Drop switch (2026-09-24).** From now on RTL drops come from
`Frontend2/OutputFolders` (Jacob). `spec/rtl_drop.json` roots, the
schema generator's default root and `faults/fault_catalog.json` now point
there; `Frontend/OutputFolders` is history. First Frontend2 drop = c8ac792
(HEAD 1fea117): same 11 blocks, byte-identical port lists, widths and
`source` coverage as b4d6f45; config_regs, init_fsm, bank_tracker and
refresh_ctrl are rewrites, the other seven changed only their headers.
Structural regression (`reports/validate_drop/1fea117_structural_only.log`):
9/9 catalogue blocks resolve; intake still 10 gaps; integration map, schemas,
monitors, SVA, coverage, vplan regenerate clean; wiring check 75/75; width
gate still fails on data_path DQ (32 vs 16, finding stays open); the five
status/boot chains reported BROKEN by `check_path_chains.py` are identical on
the old drop (catalogue has no config_regs status interfaces; pre-existing).
Static read of the rewrites: config_regs still has no reserved-bit write
mask (regression likely still open), scheduler re-grant code unchanged,
data_path width unchanged. Four seeded-fault sites moved with the rewrites
and were re-seeded (15/15 apply, all unique). **Simulation half not run:**
Olympus rejects the stored password and the local key; path runs, coverage,
findings v2 and the drop comparison wait on that.

**Regression on the first Frontend2 drop (2026-09-24, 1fea117 vs b4d6f45).**
Olympus login works once the password is parsed from `setup.env` correctly
(`sim_runner.py` now reads that file itself; the `KEY = "value"` form is not
shell-sourceable, which is all the earlier auth failures were). 17 paths in
1.0 min: 6 pass / 11 fail, no errors. Result after fixing three measurement
artifacts (below): **3 paths improved, 14 unchanged, 0 regressions.**
path_02/03/18: the X-valued data violations in wb_port and data_path are gone
and matched transactions rose (wb_port 32→52 of 104, data_path 9→26 of 48),
so `wb_port/DATA_001` and `data_path/DATA_001` auto-resolved
(`resolved_in: 1fea117`) — the first findings closed by a Frontend drop.
22 findings stay open (scheduler 8, config_regs 6, wb_port 4, data_path 3,
cmd_gen 1); the rewrites of bank_tracker / refresh_ctrl / init_fsm changed
no verdict. Code coverage 75.1% (init_fsm 46.6→89.4%, wb_port 76.0→59.5%,
others within ±4); vplan 27/39 covered, 12 partial.
Artifacts fixed: (1) snapshots archived only the JSON reports, not sim logs
or traces, so every assertion key looked *new* against the old drop —
`compare_drops.py --snapshot` now archives both, the comparison ignores
log-derived keys when only one side has a log, and b4d6f45 was backfilled
from the determinism re-run; (2) `emit_findings.py` resolved by taxonomy id
(every MISMATCH is DATA_001, so nothing ever resolved) — now by finding id
against the previous outbox; (3) `measure_coverage.py` merged every run ever
kept on the cluster, so a rewritten block counted old+new code (46% headline)
— `--since <run start>` restricts the merge to the drop's own runs and
`validate_drop.py` passes it.

---

## 1. Where the three subsystems actually are

### Frontend (Lehana) — `Frontend/`, `Frontend2/`, `Spec/`
- Four LangGraph phase pipelines (`Frontend/Agents/phase{1..4}_pipeline.py`),
  identical shape: generate → `validate_pN` → lint gate → sim gate, up to 4
  retries, retries re-run *all* generators of the phase.
- "Validation" inside the Frontend is **static regex checking of the
  generated RTL text** against spec-derived numbers (94 checks in phase 1),
  plus a lint agent over manifests (not RTL) and a one-testbench Xcelium run.
  Phase 3 has no sim gate; phase 4 has no validation agent (falls back to
  file-exists checks).
- Testbenches read the generated RTL to get expected values
  (`phase1_validation_agent.py:737` regexes `MR0_VAL` out of `init_fsm.sv`),
  so a generator bug and its "test" can agree. Frontend2's plan names this
  and fixes it, but no Frontend2 code exists yet.
- Retry feedback is a `retry_instructions[module].failed_checks` list of
  `{id, name, expected, actual}`. **Bug**: `config_regs_agent.py:425` reads a
  key (`validation_failures`) the real pipeline never writes, so config_regs
  retries are feedback-free. That is plausibly how the reserved-bit
  regression shipped.
- The spec is produced by one LLM choice step + a deterministic compiler
  (`microarch_compiler.py`); presets exist (`low-cost-embedded`, `balanced`,
  `high-performance`), so **variant specs are one command away**. Nothing in
  the Frontend consumes validation findings or an intake checklist.
- No assembled top level exists. Phase 2–4 manifests carry `source`
  connectivity; phase 1 manifests do not. No drop carries a git commit or the
  spec `revision`.

### Backend (Dawson) — `backend/`
- Input is a **bundle** (RTL + manifest) validated against
  `backend/schema/manifest.schema.json`; the set-level gate
  (`schema/validate_bundles.py`) checks connectivity via `source` and emits
  findings with an `owner` field (`frontend`|`backend`) and codes `SCH-*,
  NET-*, WID-*, GAP-*, DEP-*`. Bundles are copies of `Frontend/OutputFolders`.
- Flow is OpenROAD-flow-scripts on sky130hd; signoff = KLayout DRC clean +
  LVS match + pin audit, STA soft. Per-block results in
  `backend/signoff/results/<block>.json` with evidence logs.
- Outputs per block: `6_final.v` netlist, `6_final.spef`, `.gds/.def`,
  reports (`6_report.json` flat ORFS metrics). **No SDF, no gate-level
  simulation, no cell simulation models anywhere.** The manifest schema
  carries `assertions`/`coverage_points` "for the validation subsystem" but
  nothing reads them.
- `integration/ddr3_controller` is a scaffold top, explicitly "not
  functionally a memory controller"; `handoff/connectivity_worksheet.json`
  lists 111 unresolved slots waiting on `source` fields.

### Validation (Jacob) — `Validation/`
- Spec-as-data throughout: intake gate, schemas from manifests, generated
  monitors, generated SVA/coverage, register model, vplan (38 items), path
  definitions (20), integration map (75 connections), drop resolver.
- Agent-generated predictors/checkers (14, all gate-accepted, gates
  mutation-tested), transaction scoreboard, per-path runners, vManager
  regression, coverage rollup, findings outbox (15 open), waivers with named
  approver.
- Evidence: 20/20 paths judged, 34/38 vplan items covered, 72% design code
  coverage, four RTL defects confirmed at source, one regression caught
  after regeneration. 143 unit tests.

---

## 2. Is this an industry-standard approach?

Measured against a conventional DV methodology (verification plan → coverage
model → stimulus → checkers/reference models → assertions → regression and
triage → coverage closure → signoff):

| Practice | Status | Note |
|---|---|---|
| Verification plan traced to spec | **Yes** | vplan items carry `spec_ref`, `failure_ref`, coverage items, status |
| Functional coverage model | **Yes** | covergroups derived from spec; rollup writes vplan status |
| Code coverage | **Partial** | measured, no per-block targets, no exclusion methodology |
| Reference models / scoreboard | **Yes, unusual** | agent-generated models graded by spec-derived gates; the grading is the novel part and it is mutation-tested |
| Assertions (independent of DUT) | **Yes** | timing/protocol SVA recomputed from spec, bound not embedded |
| Constrained-random stimulus | **Weak** | random sequences are unconstrained draws of 19 transactions; directed walks carry most coverage |
| Regression management | **Partial** | vManager session exists; no history across drops, no pass/fail trend, no nightly |
| Triage → owner → fix → verify | **Designed, not built** | `findings/FEEDBACK_LOOP_DESIGN.md` |
| Formal property checking | **No** | JasperGold + ABVIP DDR3 are installed and unused |
| Gate-level simulation | **No** | backend has no cell models or SDF |
| Known-good reference (false-positive rate) | **No** | every design seen so far is broken |
| Signoff criteria written down | **No** | coverage goals, waiver policy and exit criteria are implicit |

Verdict: the structure is industry-shaped and in places ahead of a typical
student flow (spec-derived SVA, taxonomy-tagged findings, gate-graded models,
waivers with approvers). The gaps are the ones a review board would ask about
first: no proof it passes a correct design, no formal, no gate-level, no
written signoff bar, thin random stimulus.

---

## 3. Design improvements worth making

1. **One connectivity source of truth.** *(Done 2026-09-24 on our side.)*
   `integration_map.json` is generated from manifest `source` fields by
   `structural/integration_map_gen.py`; `glue`/`expr_glue`/`ties` and the
   edges manifests do not yet declare live in `integration_overrides.json`,
   and each such edge is a filed finding against the Frontend. The residue
   shrinks (and the generator flags redundant overrides) as phase-1 manifests
   gain `source`; that same change empties Dawson's 111 worksheet slots.
2. **Top-level DUT mode.** When an assembled `ddr3_controller.sv` exists
   (Frontend2 step 4 or Dawson's `generate_top`), the path harnesses should
   instantiate it and bind monitors hierarchically, so the wiring under test
   is theirs, not mine. Same paths, same checkers, one new harness mode.
3. **A drop stamp everyone writes.** `{git_commit, spec_revision,
   generator_versions, timestamp}` in every manifest and report. My resolver
   stamp is the seed; the Frontend and backend carry nothing today.
4. **One findings schema for the whole loop.** Backend findings (`owner`,
   `SCH-*`), Frontend `failed_checks`, and `validation-findings/2` should be
   the same record with different producers. The adapter in the feedback
   design is the bridge; the backend's `owner` field is the model.
5. **Formal on the generated SVA.** Every timing/protocol property I generate
   is a candidate for JasperGold proof on the owning block. Proofs replace
   "the random run happened to exercise tRRD" with "tRRD holds for all
   inputs". Cheap because the properties already exist.
6. **Constrained-random done properly.** Address-mapping-aware constraints
   (same bank different row for conflicts, same row for hits), refresh-pacing
   constraints, burst back-pressure, plus longer runs with coverage-guided
   seed selection through the closure loop.
7. **Signoff document.** Coverage targets per block, exclusion rules,
   waiver policy, drop acceptance criteria, and the list of paths that must
   pass. Written once, cited by the cockpit.

---

## 4. Validation plan (semester)

Exit criterion for each phase is stated so progress is measurable.

### Phase A — prove validation is correct (weeks 1–2)
- Seeded-fault suite on the current drop: 12–15 realistic mutants, 16 paths
  each, detection matrix, blame correctness. *Exit: ≥90% detected, every
  detection blamed on the mutated block.*
- Determinism: two runs of one drop, byte-identical reports. *Exit: zero diff.*
- Second spec via `microarch_cli.py --preset low-cost-embedded`: intake,
  schema, SVA, coverage, register model regenerate with no code changes.
  *Exit: zero edits; bounds and bins visibly change.*
- Feedback loop steps 1–3 (schema v2, adapter, `compare_drops`, localizer,
  triage). *Exit: the reserved-bit regression round-trips to `resolved_in`
  against a snapshot of the old config_regs.*

### Phase B — close the methodology gaps (weeks 3–5)
- UberDDR3 as the known-good target: spec for its configuration, slot-aware
  monitor for its 4-commands-per-cycle PHY interface, timing/protocol SVA,
  end-to-end data integrity, ABVIP cross-check at the DRAM pins. *Exit: zero
  false positives on the timing, protocol and data-integrity checks.*
- Formal: JasperGold proofs of the generated SVA on scheduler, cmd_gen and
  bank_tracker. *Exit: each property proven, bounded-proven, or a
  counterexample filed as a finding.*
- Constrained-random v2 + closure loop on scheduler/cmd_queue scopes.
  *Exit: per-block code coverage ≥85% with reviewed exclusions; functional
  100% of reachable bins; unreachable bins documented.*
- Integration map generated from manifest `source`; top-level harness mode.
  *Exit: the 20 paths run on the assembled top with the same verdicts.*
- Signoff document v1.

### Phase C — close the loop with both teammates (weeks 6–8)
- Full loop demo: spec → RTL → validation → findings → regenerate →
  re-validate, with `introduced_in`/`resolved_in` history shown in the
  cockpit. *Exit: at least one defect fixed by the Frontend from our finding
  alone and auto-closed.*
- Gate-level: backend `6_final.v` + sky130hd behavioral cell models, run the
  block harnesses on netlists (zero-delay first, SDF if ORFS writes it).
  *Exit: netlist verdicts equal RTL verdicts for every signed-off block.*
- Nightly vManager regression across seeds and generators with trend.

### Phase D — signoff (weeks 9+)
- Coverage closure report, findings ledger with dispositions, waiver
  approvals, drop provenance, vplan status at 100% measured. Final demo.

---

## 5. Integration plan

### Contracts to agree (owner → consumer)
| # | Contract | Producer | Consumer | Status |
|---|---|---|---|---|
| C1 | Drop stamp in every manifest/report (git commit, spec revision) | Frontend, Backend | Validation | proposal |
| C2 | Spec completeness checklist in the spec generator prompt | Validation | Frontend | ready (`spec/SPEC_COMPLETENESS_CHECKLIST.md`) |
| C3 | Findings v2 + `retry_instructions.json` adapter, per drop | Validation | Frontend feedback agent | designed |
| C4 | `source` on every consumer input port (phase 1 included) | Frontend | Backend, Validation | phase 2–4 done, phase 1 missing |
| C5 | Assembled top-level RTL | Frontend (or Backend `generate_top`) | Validation, Backend | not started; decide one owner |
| C6 | Validation verdict gates backend intake (PASS or PASS-with-waivers per block) | Validation | Backend | proposal; backend already has an intake gate to hook |
| C7 | Gate-level collateral: netlist path, cell models, SDF if available | Backend | Validation | not started |
| C8 | One findings schema with `owner` (frontend/backend/spec/validation) | all | all | proposal; backend's `owner` field is the model |

### Sequencing
1. **Week 1**: C2 and C3 to Lehana with the five open RTL findings and the
   `config_regs` retry-key bug; C1 proposal to both; C4 phase-1 gap to Lehana.
2. **Weeks 2–3**: Lehana's feedback agent consumes `retry_instructions.json`;
   first round trip on the reserved-bit regression. Dawson hooks C6: backend
   intake reads our per-block verdict file.
3. **Weeks 3–5**: C5 decided and built; integration map derived from
   `source`; top-level harness; Dawson's worksheet empties.
4. **Weeks 6–8**: C7; gate-level runs; full loop demo with all three.
5. **Weeks 9+**: signoff package.

### Loop test matrix (what "integrated" is proven by)
| Test | Proves |
|---|---|
| Regenerate config_regs with the mask fix → finding auto-closes | Validation → Frontend → Validation |
| Intake gate rejects a preset spec missing tMRD → generator adds it | Validation → Spec → Frontend |
| Backend refuses a block whose validation verdict is FAIL | Validation → Backend |
| Netlist of a signed-off block passes the same paths as its RTL | Backend → Validation |
| Phase-1 `source` lands → integration map regenerates → worksheet drops to 0 | Frontend → Backend + Validation |

### Risks
- Frontend2 is a rewrite with no code yet; if it slips, the adapter still
  feeds the current pipelines, so C3 does not depend on it.
- No assembled top may exist this semester; the block-level paths remain the
  fallback and are what has found every defect so far.
- Gate-level needs cell models Dawson has not sourced; zero-delay GLS on the
  Yosys netlist is the minimum viable version.
- UberDDR3 needs the Micron model download and a slot-aware monitor; if it
  costs more than a week, the seeded-fault suite plus formal give most of the
  same confidence.

---

## 6. Gaps in validation, in one list
1. False-positive rate unknown (no correct design seen) → UberDDR3.
2. System-level detection rate unknown → seeded-fault suite.
3. No formal → JasperGold on generated SVA.
4. No gate-level → C7.
5. Random stimulus is unconstrained and short → constrained-random v2.
6. Coverage has no targets or exclusion policy → signoff document.
7. No regression history → `compare_drops`, nightly vManager with trend.
8. Findings are hand-assembled → feedback loop steps 1–3.
9. ~~Integration map is hand-written → derive from `source`.~~ Done; 21 edges still carried as overrides until phase-1/2 manifests declare them.
10. Don't-care fields (PRE address) counted as mismatches → declared masks +
    intake rule.
11. Only one spec ever run → second preset spec.
12. Waivers W-002/W-003 undecided → human decision.
