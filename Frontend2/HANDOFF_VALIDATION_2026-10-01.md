# Handoff to Validation — 2026-10-01

From Frontend (Lehana) to Validation (Jacob). Replies to
`Validation/findings/HANDOFF_FRONTEND_2026-10-01.md` and
`HANDOFF_CONTRACT.md`. Each item says what changed in `Frontend2/`, what it
means for you, and what is still open. Nothing here was run on Olympus this
session; "tested" below means run locally, with the LLM calls mocked where
noted.

## 0. State of the drop in this push (read first)

`Frontend2/OutputFolders/` is **still a two-spec drop**. It is pushed as it
stands (generated artifacts, separate commit) so you can see it, not because
it is ready to validate:

| dir | blocks | `spec_revision` |
|---|---|---|
| `PHASE1RTL` | config_regs, init_fsm, wb_port | `compiled_ddr3800_x8_1lane_1rank` |
| `PHASE2RTL`–`PHASE4RTL` | the other 8 | `golden_ddr3_1600k_x8_2lane_1rank` |

`generated_spec.json` is `compiled_ddr3800_x8_1lane_1rank`, so the 8 golden
blocks are foreign to it (your `SPEC_MISMATCH`). Content-hash drop id of this
tree: `6277763e32a3`. We will regenerate all four phases from one spec before
the next drop; please do not spend a run on this tree.

## 1. One generation = one spec (your §1) — enforced now

- `full_pipeline.py` refuses to start Phase N>1 if any earlier phase's
  manifests carry a different `spec_revision` than the spec in use, and
  offers to re-run from Phase 1.
- `generate_top.py` refuses to build `TOPRTL/` from a mixed drop (tested
  against the tree above: it refuses and names the 3 Phase-1 blocks).
- End of a run: `generated_spec.json` is copied into the output dir
  (`drop.ship_spec`), the drop id is printed, and `TOPRTL` copies that differ
  from their phase output are listed. `generate_top` recopies every run, so a
  divergence only appears if it was not re-run.

## 2. Drop id — implemented, one discrepancy with the contract text

`Frontend2/scripts/drop.py: compute_drop_id()` is our own implementation (not
imported from Validation). It matches `rtl_drop.drop_id()` on the current
tree. **The contract says the hash covers "each block"; the code hashes only
the blocks in `Validation/txn/interface_catalog.json` (9 of 11: no
`addr_decoder`, no `bank_tracker`).** We matched the code. Consequence: a
change to `addr_decoder` or `bank_tracker` alone does not change the drop id.
Please confirm that is intended, or say which way to move.

## 3. Spec review before Phase 1 (your §4)

- `full_pipeline.py` now calls `validate_spec_stage.validate_spec` on **every**
  spec (an existing JSON as well as a synthesized one; the existing-JSON path
  was unvalidated before). Falls back to `dummy_validation_agent` with a
  warning if your module is not importable.
- FAIL blocks Phase 1. The 12 gaps print as advisory.
- Heads-up: running your stage from our flow writes
  `outbox/current/SPEC_REVIEW.json` and `outbox/intake_spec_gaps.json`, as
  designed. A local run of ours overwrote `SPEC_REVIEW.json` with the golden
  spec's review; we restored it with `git checkout`.
- **Your `--feedback` ask is done:** `microarch_cli.py --feedback
  <SPEC_REVIEW.json>` and `run_english(feedback=…)`. The model gets the
  blocking findings and open intake questions as structured lines.

## 4. Schema edits in `Spec/` (your §2) — please review, it is your contract too

`Spec/llmmc_microarchitecture.schema.json`:

1. The six `latency_model.*_nCK` fields now accept `["integer","string"]`.
   You recommended integer-only; that would fail the golden spec, which still
   stores derivation strings. Tightening to integer + a sibling `$formula`
   needs the golden spec converted first.
2. `data_path_mapping.pack_mode` enum went from 4 values to 16: `direct` plus
   `pack_<32|64|128>_to_<8|16|32|64|128>`. A second reason compiled specs
   failed review: x8 one-lane compiles to `pack_32_to_8`, not in the old
   enum. Kept an explicit enum because your checker does not evaluate
   `pattern`. The schema now says the name is valid, not that `data_path_gen`
   can build every combination.

After these, the golden spec and the compiled `generated_spec.json` both PASS
your review with 0 blocking (12 advisory on the golden spec).

## 5. Compiler restricted to `wishbone_pipelined`

`wb_port_gen.py` only builds the pipelined FSM and rejected a
`wishbone_classic` spec at generation. The compiler now rejects classic
(validity matrix, English-agent enum, user-facing text), matching your
pipelined driver. Selftest still 27/27. Other places the generators reject
what the compiler accepts, **not yet changed**: `burst_length=4`
(`data_path_gen`), bank count ≠ 8 (`bank_tracker_gen`), clock ratio ≠ 4:1.

## 6. Findings loop

- **Frontend Orchestrator** (`Frontend2/scripts/Orchestrator/`) reads
  `outbox/current/` per the contract, compares your `HANDOFF.json drop_id`
  with its own, and **refuses to dispatch fixes when they differ** (override
  `--allow-stale`). It also reads `DROP_STATUS.json`, `untested_in_this_drop`,
  `fix`, and `SPEC_REVIEW.json` blocking findings.
- It routes: spec findings → Microarch agent; Phase 1/2 RTL findings → the
  phase fix agents; Phase 3/4 and anything unclear → written to
  `ORCHESTRATOR/orchestrator_<stage>_report.json` for a human (no fix agent
  exists for Phases 3/4, so scheduler / cmd_gen / data_path findings
  escalate).
- Optional `run_validation` tool: after a human confirms, ships
  `generated_spec.json`, runs `validate_drop.py` with `VALIDATION_SPEC` set,
  and reloads `current/`. Only if our output dir is one of the `roots` in
  `rtl_drop.json`.
- **Your `--retry … --yes` ask (§5): partly done, deliberately not `--yes`.**
  Both phase fix agents accept `--findings <file>`; the file may be a
  `retry_instructions.json` as-is. They show your `fix` hint and the
  confidence. Patches are still human-approved: an unattended `--yes` means
  an LLM editing generator source unreviewed. Your flow detects `--retry` in
  `--help`; we did **not** add that name, so it will keep using the
  flattened error-report bridge. If you want it, say so and we will add
  `--retry` with `--yes` guarded (diff logged, re-verify on, revert on
  failure, off by default).
- Caution for the `observed` confidence class: your own §7 showed two
  findings (duplicate read, CTRL_STATUS) that were Validation-side. A fix
  agent pointed at those would have patched correct RTL.

## 7. Spec-gap mode in the Microarch agent (your §3)

New `microarch_gap_agent.py`: given spec-gap findings verbatim, proposes a
patch to `microarch_compiler.py` (diff, human `a`pprove), then gates it:
selftest, every preset's compiled spec unchanged except for added fields, and
every new spec path it claims is present. Failure restores the file. It asks
for an owner decision instead of inventing a value, and must not edit the
schema. Tested with a mocked model (bad edit, missing path, changed value,
good patch); never run against a real model.

**Not yet wired to `completeness_rules.json`**, so it does not use your
allowed-values table or pinned conventions as the authority. Next step.
Taxonomy gap: `failure_taxonomy` is copied from the golden spec JSON by
`_load_failure_taxonomy()`, not defined in the compiler. The agent is told to
add ids by merging inside the compiler; the compiler and the golden file will
then differ. Your call whether the taxonomy should move into the compiler.

## 8. Fail closed on SKIPPED (your §6)

A lint or sim gate that could not run (no `OLYMPUS_USER`/`OLYMPUS_KEY`, SSH
failure) now **fails** the phase in all four pipelines, and `generate_top.py`
returns 1 on a skipped lint. `ALLOW_SKIPPED_GATES=1` overrides on purpose;
the final report is then `"status": "PASS_UNVERIFIED"` with `skipped_gates`.
**If `flow.py` compares `phase{N}_final_report.json` `status` to exactly
`"PASS"`, it will now see `PASS_UNVERIFIED` in that case.** The stray root
file `yes` was already gone.

## 9. Phase 2 testbench audit

`Phase2/testbench_auditor.py` (deterministic, spec-only) and
`Phase2/testbench_fix_agent.py`, with a `TESTBENCH_AUDIT` gate in
`phase2_pipeline.py` (same shape as Phase 1). Narrower than Phase 1's: it
checks geometry localparams, address-slice vectors (from the spec's
`address_mapping`) and ZQCS values. The TB-owned directed timing constants
are not audited. Phase 2 report files are `phase2_`-prefixed; Phase 1's are
not (`lint_report.json`, `sim_report.json`, `tb_audit_report.json`), which
is why Phase 2's use a prefix: both write to the same `VALIDATIONREPORT/`.

## Questions for you

1. Drop id: catalog blocks (code) or every block (contract text)?
2. Do the two schema edits in §4 work for you? Integer + `$formula` later?
3. Does `flow.py` read the phase final-report `status` as exactly `PASS`?
4. `--retry` / `--yes`: want it, with the guardrails in §6?
5. DM polarity and the `ref_pending_cnt` width (3 bits vs `max_postpone` up to
   8) still have no agreed value. Which do you want?
