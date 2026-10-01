# Reply to Frontend — 2026-10-01 (evening)

From Validation (Jacob), answering `Frontend2/HANDOFF_VALIDATION_2026-10-01.md`.
Numbered as your questions; what changed on our side is marked **done**.

## Q1 — Drop id: every block (the contract), not the catalog's 9

You were right and the code was wrong. `rtl_drop.drop_id()` now hashes all
11 blocks of `Validation/spec/path_definitions.json` `blocks`
(`addr_decoder, bank_tracker, calibration, cmd_gen, cmd_queue, config_regs,
data_path, init_fsm, refresh_ctrl, scheduler, wb_port`); the contract text
says so explicitly now. **done.** Consequence for `drop.py:
compute_drop_id()`: switch its block list to the same 11 (the interface
catalog stays what it is — the blocks that own an interface — and is not
the list a drop is identified by). The id of the current tree is
`c85ae77d1d7c` under the new rule (was `6277763e32a3` under the old one on
your side; both are "wrong" for this tree since it is two specs, but they
should agree).

## Q2 — Schema edits: yes to both

- `latency_model.*_nCK` as `["integer","string"]`: fine. Both the golden
  spec and `generated_spec.json` now PASS review with 0 blocking (12
  advisory). Integer + `$formula` later, once the golden spec is converted —
  no hurry on our side.
- `pack_mode` enum of 16: fine. Our checker now evaluates `pattern`
  (and `minimum`/`maximum`) too, so a pattern would also have worked; keep
  the enum if you prefer it readable. **done.**

## Q3 — `PASS_UNVERIFIED`

`flow.py` never compared `status` to `"PASS"`; it keys on which report file
exists (`phase{N}_final_report.json` vs `phase{N}_error_report.json`). It
now also reads `status` and `skipped_gates` and records
`PASS_UNVERIFIED (lint, sim did not run on the Frontend side)` on the stage
and continues — our validation is the gate that does run. Fail-closed by
default is the right default; thank you. **done.**

## Q4 — `--findings` / `--yes`

- `flow.py` now looks for `--findings` first (`--retry` second, as a
  synonym) in the agent's `--help`, passes `retry_instructions.json` under
  it, and adds `--yes` only when the agent advertises it. Verified against
  the tree: Phase 1 and 2 agents → `--findings`, no `--yes`; 3 and 4 absent
  → halt. **done.**
- On unattended patches: the flow is Jacob's call and it is unattended —
  it answers the agent's `[a]pply` prompt with `a` today, so the human
  approval step is already bypassed from our side whether or not `--yes`
  exists. What stands in for the review is: the next validation round on
  the regenerated drop, the round cap (4), and your agent's own re-verify.
  So yes, please add `--yes` with your guardrails (diff logged, re-verify
  on, revert on failure, off by default); it is strictly better than a
  scripted `a`. Until then the scripted `a` stays.
- On `observed` findings: agreed, and the two you cite were ours. The
  package carries `confidence` per check precisely so an agent can treat
  `observed` differently from `confirmed`; our retry adapter marks every
  model-free check (assertion, rule, structural, repair-proven) `confirmed`.
  If you want, the agent could require `confirmed` to patch and only
  report `observed` — your call; the data is there.

## Q5 — DM polarity and `ref_pending_cnt` width (spec decisions; recommendations)

- **DM polarity:** `active_high_mask`. That is JESD79-3: DM = 1 masks the
  byte (it is not written), DM = 0 writes it. The checker's convention
  `active_high_mask` is what UberDDR3 does too. State it as
  `data_path_mapping.ddr_dm_polarity = "active_high_mask"` and the
  `data_path` DM findings become decidable (today they stay open on both
  sides).
- **`ref_pending_cnt`:** the field is `CTRL_STATUS[7:5]` (3 bits, 0–7) while
  `REFRESH_CONFIG.max_postpone` is 4 bits with reset 8 — the count can
  reach a value the field cannot show, and it is why our REF_001 (postpone
  budget exceeded) is unreachable on the current RTL. Recommendation: widen
  to 4 bits, `CTRL_STATUS[8:5]`, move `self_refresh_active` to bit 9,
  reserved `31:10`. The description already says "(0-8)". This changes the
  golden spec, the compiler's register template and `config_regs_gen`; our
  side regenerates its register model from the spec, nothing to change.

## Also noted

- §0: understood, no run spent on the two-spec tree. The flow's step 1b
  reports exactly what you describe (3 foreign blocks, 22 blocked paths) and
  files `SPEC_MISMATCH`; nothing else is judged.
- §3 `SPEC_REVIEW.json` overwrite: by design `outbox/current/` is "the newest
  result" from either side's run; the per-drop archive is the record. If
  your orchestrator wants the review tied to a drop, read
  `outbox/<spec_rev>/<drop_id>/` — `SPEC_REVIEW.json` is now archived
  there too, so `current/` being overwritten costs nothing. **done.**
- §6 Frontend Orchestrator refusing on a stale `drop_id`: exactly right.
- §7 gap agent not yet wired to `completeness_rules.json`: that file is the
  authority on the allowed values; when you wire it, the `options` list per
  rule is what to offer the owner, and the `consequence` text is what to
  show them.
- Taxonomy: moving `failure_taxonomy` into the compiler is fine with us —
  the only requirement validation has is that every id a checker files
  under exists in the spec it is judging against (the `TAXONOMY_*` intake
  rules say which).

## Open on our side

- Phase 3/4 findings still halt the flow until agents exist; the error
  reports are written for them in `VALIDATIONREPORT/` regardless.
- The final netlist-on-paths stage (backend output through our paths) is
  not built; Dawson's `backend/findings/outbox/` now exists in our format
  and is next to wire.
