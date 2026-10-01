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

**Progress (2026-09-29/30, "is validation itself right?").** Four sources of
evidence per check, gathered into one ledger (`agreement/check_ledger.py`,
`reports/check_ledger.json`, cockpit section): 36 of 51 checks now have
non-synthetic evidence on both sides (fired on something wrong, silent on
something right); 13 are silent-only (never seen to fire outside the gate),
1 fires-only, 1 gate-only, 0 false positives.
- *Repairs* (`repairs/`): three minimal fixes applied to a Validation-owned
  copy of drop 5661e03 — scheduler feedback-latency hold (R01), REFRESH gated
  on tRFC (R02), tWTR applied to READ (R03). Stacked, they turn 6 of 10
  command paths green and silence every scheduler check; nothing new fires.
  R02 and R03 are defects the Frontend has not reported yet (REFRESH not
  gated by tRFC; tWTR tracked per bank and applied to PRECHARGE instead of
  READ). What still fails after R03 is data_path (read return), wb_port
  (byte-enable spec gap) and config_regs (status-read spec gap).
- *Second models* (`agreement/second_opinion.py`, `model_agreement.py`): 12
  of 14 scopes have an independently generated model; disagreements on real
  traces found two primary-model bugs — path_19's checker treated a
  PRECHARGE to bank 7 as precharge-all (44 false PROTO_001/SCHED_001), and
  cmd_gen's predictor carried the row on PRECHARGE so A10 followed row bit 10
  (74 false mismatches sent to the Frontend). Both gates were extended
  (single-bank-precharge trace; declared constant bits + complementary drive
  patterns) and now reject those models; path_19 regenerated, cmd_gen
  pending. The primary config_regs predictor does not model cfg_refresh at
  all; the second one does (open).
- *Known-good path checkers* (`refdesigns/uberddr3/path_checkers_on_uberddr3.py`):
  the end-to-end checkers run on UberDDR3's host/pin streams. SCHED_004 as
  first written fired 314x on its legal look-ahead ACTIVATE; restated as
  "a CAS must land on the row its request asked for" (intake rule
  SCHED_SPECULATIVE_ACTIVATE added). Now 0 violations for path_19/path_20
  and their second models over 9216 requests. vManager session
  `~/vmanager_uberddr3` (6 tests, all green).
- *Oracle agreement* (`agreement/oracle_agreement.py`): PROTO_001/002 have
  three oracles (rule, assertion, formal) and agree on all 40 runs compared.
- Findings on 5661e03 after the fixes: 24 → 15 checks to the Frontend.
- The wb_port second model was rejected four times on one point it would not
  concede: it emits no `wb_rsp` for a READ until read data arrives, while the
  catalog derives `wb_rsp` one-per-host-access from `wb` alone. A read
  response does depend on `dp_rd_rsp`, which the wb_port predictor is not
  given; the gate's read expectation (and the primary model that satisfies
  it) needs a second look before the primary's wb_port read mismatches are
  treated as design defects.
- *2026-09-30 follow-up.* The wb_port rejection was the gate's: it demanded a
  read response from the request alone. The catalog now declares `wb_rsp`
  *completes on* `dp_rd_rsp` (gate drives request, expects nothing, drives
  the completion, expects one response with its data); the predictor prompt
  now carries the catalog's stream relationships and `model_guidance`;
  `req.mask` is don't-care on reads (intake gap). wb_port and cmd_gen
  predictors regenerated and accepted (cmd_gen's first attempt repeated the
  A10 mistake and was rejected by the extended gate — the gate works); wb_port
  second model accepted, agrees 41/41. Five seeded faults added for the
  silent-only rules (refresh before init, scheduler ignoring refresh, ZQCS
  before cal_done, short tZQinit, CAS without ACTIVATE): 20/20 killed. The
  tZQinit fault exposed a rule gap — command-to-command spacing cannot see
  init_done — closed with a new SVA rule kind (`event_rules`:
  `a_INIT_002_init_done`), silent on the correct boot. Ledger: 45/51 closed;
  left: REF_001 (needs a reachable starvation, blocked by the ref_pending_cnt
  width gap), TIMING_002/TIMING_012 (tRP equivalent at this clock; tREFI
  bound), data_path (second model disagrees on DM polarity, the open spec
  gap), and the cmd_gen second model (still generating).
- Gaps to close next: seeded faults for the 13 silent-only rules (PROTO_001,
  REF_001/003, SCHED_003, CAL_002, TIMING_002/012, INIT_002); regenerate
  cmd_gen and the wb_port second model (blocked today by a throttled API
  link over the VPN, ~4 tokens/s).
- *2026-09-30, later.* Repair-proven defects now ship as findings:
  `emit_findings.py` files `repair/<block>/<Rid>` records (anchors = the
  repair's edits, detectors `repair:<id>` + the checks it silenced) for R01
  (scheduler feedback hold), R02 (refresh gated on tRFC/all-idle) and R03
  (bank_tracker tWTR on read); 17 findings on 5661e03, retry_instructions
  carries `repair`/`fix`. Boot path brought under SVA + formal: two rule
  kinds added to the generator — `sequence_rules` (INIT_001 order parsed
  from the spec's init-sequence sentence → `a_INIT_001`/`a_INIT_001_then`,
  INIT_003 as an event → `a_INIT_003_init_done`) and `signal_groups`
  (ordering assertions for blocks with no command stream:
  `calibration_order_sva.sv`, CAL_001/CAL_002). Baseline path_08 stays
  silent; M14/M15/M18/M19 fire the new assertions. JasperGold on the
  init_fsm + calibration top (`run_formal.py --path path_08_init_to_cal`):
  concrete run proves CAL_001/CAL_002 at infinite bound, the five init
  properties are undetermined at bound 401 (the 40k/100k-cycle reset waits
  are `localparam`s no bounded engine crosses); with `--stopat
  u_init_fsm.wait_cnt` (a sound over-approximation, recorded in the report
  as `abstractions`) 6/7 proven at infinite bound, covers 5/5; the one cex
  (`a_INIT_002_init_done`) is the property that measures the cut wait and
  is marked spurious — simulation grades it (silent on the baseline, fires
  on M19). Ledger takes proofs under a cut as silent evidence and never a
  cex under one as fired evidence. Three faults added so the boot
  assertions are reachable (M21 ungated ZQCS: M18 alone could not trip
  `a_CAL_002` because the drop gates `zqcs_req` on `cal_done_r`
  structurally; M22 init_done in S_MR0; M23 MR0 after ZQCL): 23/23 killed.
  `seed_faults.py --only` now merges into the matrix instead of replacing
  it (a partial rerun had silently dropped 16 rows of ledger evidence).
  Ledger 49/57 closed; left: `a_INIT_002_init_done` (fires only — no
  known-good design binds the init group yet), TIMING_002/012, SCHED_002 on
  two checkers, REF_001 ×2, data_path (DM polarity spec gap).
- *2026-10-01 — Phase-1 integration readiness.* Asked whether a
  `PHASE1RTL`-only drop can be validated today. It could not: the
  orchestrator stopped on a drop missing any block, and only one of 20 paths
  (`path_14`) used Phase-1 blocks alone. Built:
  - **partial drops** — `validate_drop.py --partial` resolves what the drop
    provides, runs every path whose closure is present, lists the rest as
    `blocked (needs …)`, writes reports to `reports/partial/<head>/` (never
    mixed with full-drop reports), and emits findings with a
    `DROP_STATUS.json`: a previous finding whose block is absent or whose
    every path was blocked is carried **untested**, never resolved (the
    first attempt reported "22 resolved" for a drop that tested nothing of
    them — fixed before it could mislead a retry). The generators defer what
    an absent block owns (`integration_map_gen` keeps the edges as
    `deferred_connections`, `schema_gen --allow-missing`, `sva_gen`,
    `coverage_gen`, `block_coverage_gen`); `compare_drops --paths/--tag`
    keeps a partial snapshot from ever becoming the reference.
  - **standalone paths** — `path_21_wb_port_standalone` and
    `path_22_csr_standalone` instantiate one block with no support closure;
    every cut edge takes a `standalone_ties` entry from
    `integration_overrides.json` (with a why) or generation refuses. The
    first partial run proved the rule's worth: the partial map had deferred
    `wb_port.req_ready`'s edge, the harness fell back to the silent zero tie,
    and every write stalled.
  - A Phase-1-only copy of 5661e03 now runs 3 paths (14, 21, 22), all PASS,
    19 blocked, 0 findings, 24 carried untested, in under a minute.
  **Two of our own defects found on the way, both on Phase-1 findings I had
  called real the same morning:**
  - The "duplicate read request" wb_port finding (critical, 50 occurrences,
    on every drop since 1fea117) was the **driver**: it held `stb` until
    `ack` (classic Wishbone) against a B4 *pipelined* slave
    (`host_interface.interface_type: wishbone_pipelined`), so a read waiting
    for data became one request per cycle until the 16-deep tag FIFO filled.
    The catalog now declares the pipelined handshake (`drive.accept:
    !wb_stall_o`, `release_on_accept: [wb_stb_i]`, `complete: wb_ack_o`) and
    the request event is the accepted beat (`qualifier: cyc && stb &&
    !stall`), not the ack. `driver_gen` emits accept/wait tasks from that
    data. `req.data` joins `req.mask` as don't-care on reads.
  - The remaining wb_port "missing request" and the config_regs
    `CTRL_STATUS` findings were the **monitor's sampling point**: monitors
    sample 1 ns after the edge (post-NBA) so a registered output shows at
    its edge — right for outputs, wrong for an input the block samples when
    that input is combinational from same-edge state (`!wb_stall_o` from
    `cmd_queue.enq_ready`) or a level that changes at the edge a response was
    computed from (`csr_sts_level.ref_pending`). Those recorded a beat the
    slave had rejected, and a status change ahead of the read that predated
    it. Catalog streams can now declare `sample: pre_nba` (wb,
    csr_sts_level); the config_regs lesson (post-NBA default) stays pinned
    for every other stream.
  After both: wb_port 42/42 with its second model, config_regs stages pass
  on all 6 paths (path_12/13 now PASS outright), **Phase-1 blocks carry 0
  findings on 5661e03**; 12 findings remain, all scheduler / bank_tracker /
  cmd_queue / data_path. 23/23 faults still killed (blame now consults
  `rule_owners`, so a scheduler fault caught on cmd_gen's pins is blamed on
  the scheduler, as the feedback loop routes it). Ledger 50/57.
  Open after this: wb_port reads are judged standalone on the request
  stream only (no read data returns without data_path; the driver's bounded
  completion wait reports that as expected); config_regs second model still
  disagrees 21/57 (the primary passes everywhere — the second model is next
  to regenerate, with cmd_gen's).
- *2026-10-01, afternoon — second models.* The config_regs disagreement was
  the primary's: it predicts `csr_rsp` only, having been accepted on
  2026-09-03 before the `cfg_timing`/`cfg_refresh` broadcast streams existed,
  so a wrong timing broadcast would have passed its own stage and surfaced
  under bank_tracker's name. Two fixes in the harness, not the model: the
  agent now rejects a model whose INPUT/OUTPUT_IFACES differ from the scope's
  streams (the prompt stated the tuples; now it is a contract), and the
  register gate grades broadcasts (step 9: after a write that changes a
  mapped field, one update carrying every mapped field's current value;
  mutation-tested — wrong value, silent, swapped mapping all rejected;
  `tests/test_broadcast_gate.py`). config_regs second model regenerated on
  Opus, accepted first attempt; primary regenerated under the new contract.
  Regenerating the primary surfaced two more harness defects: (1) a
  write-to-read-only register was assumed to set `csr_err_o` by the new
  model and not by the drop — the spec names the violation (CSR_001) but
  never says the response flags it: intake gap `CSR_ACCESS_VIOLATION_ERR`
  filed, convention pinned in the catalog (`err` only on unmapped
  addresses) until decided; (2) change-qualified monitors zeroed their
  baseline during reset, so every run opened with a phantom `update`
  carrying reset values that no model could derive from the spec — the
  baseline now follows the wires through reset. `evaluate()` also mistook
  a model's own TypeError for a gate-signature mismatch; it now inspects
  the signature. After that: primary accepted first attempt, 131/131 on
  every config_regs path with the cfg_timing/cfg_refresh broadcasts judged
  for the first time; second model 131/131 on the same trace; cmd_gen
  second model accepted (attempt 2), agrees 51/51.
- *2026-10-01, evening — first drop from a synthesized spec.* Merging
  main (12bbe90) brought Lehana's Phase-1 rewrite and Dawson's top-level
  assembly (`TOPRTL/`). The map generator refused the drop: `wb_port.req_addr`
  28 bits, `addr_decoder.req_addr` 29. Root cause is not a width bug: the
  Phase-1 blocks were generated from a **compiled spec**
  (`Frontend2/OutputFolders/generated_spec.json`, rev
  `compiled_ddr31333_x16_1lane_1rank`: DDR3-1333, x16, one lane, 167 MHz,
  28-bit host address, queue depth 4) while Phases 2–4 and TOPRTL are still
  the golden 1600K design, and `Spec/` — what validation reads — is golden.
  Validation had no check for any of this. Now it does:
  - the resolver reads each block's `spec_revision` (manifest, else the RTL
    `// Spec:` header) and the drop's shipped spec; `validate_drop` names
    the spec it judges against, lists **foreign** blocks (another revision),
    blocks every path that touches one, and files `spec_mismatch`
    (critical) per foreign block — a design assembled from two specs has no
    single contract. On the merged drop against the golden spec: 0 runnable,
    22 blocked, 3 foreign (config_regs, init_fsm, wb_port).
  - the whole flow takes the spec as data: `VALIDATION_SPEC=<path>` (21
    tools, one override each). **Against the compiled spec the Phase-1
    blocks pass 3/3** (`path_14`, `path_21`, `path_22`; register walk
    131/131 with the compiled reset values, init SVA regenerated at the
    compiled clock) and the 8 golden blocks are the foreign ones — the
    first spec→RTL→validation loop on a spec nobody hand-wrote.
  - the resolver no longer picks between differing copies of a block by
    file age (it had chosen PHASE1RTL over TOPRTL by mtime): identical
    copies are one file, differing copies resolve only through
    `rtl_dirs_preferred` (the phase directories) or refuse.
  - width-inconsistent manifest edges are findings (`width_mismatch`,
    blamed by the width rules; `host_interface.address_width_bits` now
    rules `wb_adr_i`/`req_addr`), kept out of the wiring, and every path
    across them is blocked — never truncated to make a harness compile.
    Width conformance runs in step 3; structural findings (spec, width,
    manifest audit) reach findings v2 and `retry_instructions.json`; a
    foreign block gets only its spec-mismatch finding. Any run with a
    blocked path is isolated like a partial one (its own report dir), so a
    stale report never speaks for a path that did not run.
  - 12 overrides the new manifests made redundant were removed; the map is
    now 72 manifest edges + 0 overrides.
  Open: the drop must be regenerated from ONE spec before anything beyond
  Phase 1 can be judged; `TOPRTL/` copies will diverge from the phase
  outputs until then. Compiled-spec intake still reports the same 12 gaps.
- *Drop identity and the handoff place (Lehana's question, 2026-10-01).*
  Outbox folders and report stamps were named by `git rev-parse HEAD` of
  the validator's checkout — after a merge, Jacob's commit, not hers; and
  the loop will not go through git at all once everything runs on one
  machine. Now a drop is named by its **content**: sha256 over each block's
  RTL + manifest (first 12 hex), computable by either side from the files
  alone (`rtl_drop.drop_id`); git HEAD and the manifests' commits are kept
  in the stamp as information only. The merged drop is `a58933561396`. The
  Frontend reads one fixed place, `findings/outbox/current/`
  (`HANDOFF.json` with the drop id + spec revision, `retry_instructions.json`,
  `findings_v2.json`, `DROP_STATUS.json`), refreshed by every run; the
  per-drop archive stays at `outbox/<spec_revision>/<drop_id>/`. Contract
  written for the Frontend: `findings/HANDOFF_CONTRACT.md`. `untested`
  findings are now carried across drops until a run decides them (they
  had been dropped after one carry).
- *Spec-review stage (2026-10-01, late).* `Frontend2/scripts/full_pipeline.py`
  calls a stub (`dummy_validation_agent.validate_spec`) between spec
  synthesis and Phase 1, reserved for this subsystem. Implemented as
  `spec/validate_spec_stage.py` with that contract: schema (required /
  types / enums, no jsonschema dependency), JESD79-3 conformance with the
  spec's own `[check]` claims recomputed, register-map self-consistency
  including TIMING_* reset fields == `$derived_cycles`, the compiler's own
  consistency checks, and the intake gate as advisory with
  `requires_human_review`. Golden: PASS, 12 advisory. Lehana's compiled
  1333 spec: JEDEC 25/25, registers consistent, but **6 schema violations**
  — `latency_model.*_nCK` are numbers where the shared schema says string
  (a formula with its derivation). Routed as blocking because `Spec/` is the
  contract every agent generates against; whether to relax the schema or
  fix the compiler is theirs to decide. Now step 2 of `validate_drop.py`.
  Contract section 2b documents the two-line hookup.
- *Second spec as a regression target (2026-10-01).* The compiled 1333 spec
  is the first spec nobody hand-wrote that validation has run end to end.
  Under it the 7 Phase-1 seeded faults (M07/M08 config_regs — M07 re-seeded
  to the compiled TIMING_0 reset 0x21180909 — M10 wb_port, M14/M19/M22/M23
  init_fsm) are all killed on the Phase-1 paths (14/21/22), by checkers
  that were derived from that spec at run time, not from golden. Every
  Phase-1 fault now also lists a Phase-1-only path, `seed_faults --paths`
  restricts a run to what the drop can run, and matrix rows carry
  `spec_revision`. That is the evidence behind "spec as data": nothing in
  the fault suite, the gates or the generators was touched to move specs.
- *Top-level orchestrator (2026-10-01).* `flow.py` at the repo root drives
  the whole loop through each subsystem's own entry points,
  non-interactively: `microarch_cli.py` (English / preset / choices) →
  `validate_spec_stage.py` → `phase{1..4}_pipeline.py` (stdin: spec, drop
  dir) + `generate_top.py` → `validate_drop.py` on the run's drop against
  the spec it ships → feedback agent → `backend/agents/pipeline.py` on
  `drop/TOPRTL` → final netlist validation. One directory per run
  (`runs/<id>/`: spec/, drop/, validation/round_N/, backend/,
  RUN_STATE.json, flow.log), fixed caps, `--resume` after a halt. Findings go
  back through the Frontend's own repair agents: the phase validation
  agents (`Phase{1,2}/phase{N}_validation_agent.py`) read that phase's
  error report, so `findings/to_frontend_error_report.py` renders our
  package in that shape and the flow answers their apply/re-verify prompts;
  spec-review findings go back to the microarch agent through the request
  text (its only revision input). Edges with no counterpart yet halt with
  the artifact in place: phases 3–4 (no agent), the backend→frontend change
  format (Jacob: wait for Dawson's), and our own netlist-on-paths stage
  (NOT_IMPLEMENTED; needs sky130hd cell models on Olympus). Exercised for real through stages 1–2: a `--preset balanced`
  run synthesizes a spec and halts at the review on the compiled spec's
  six `latency_model` schema violations; `--spec` golden passes the review
  and halts before RTL generation for want of `OLYMPUS_KEY` (the phase
  pipelines prompt for a password otherwise). 12 state-machine tests with
  every subsystem faked at the subprocess boundary (`tests/test_flow.py`).

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

**Phase B: known-good reference done (2026-09-24).** UberDDR3 runs under
Xcelium on Olympus (`refdesigns/uberddr3/`, one functionally neutral patch
for its constant functions): its self-check passes (4608 W / 4608 R, the 4
fails are its injected errors) with 0 Micron-model timing errors. Our 14
spec-derived assertions, generated from a spec of ITS configuration
(`builds/uberddr3_ddr3-667_x16_2lane_1rank/`, zero code edits) and bound at
the DRAM pins on the DDR clock (`sva_gen.py --clock ddr`), report **0
failures over 15946 observed commands** (2635 ACT, 2569 PRE, 5825 WR, 4878
RD, 30 REF, 8 MRS, 1 ZQCL) — the exit criterion for timing/protocol. The
first run had 19 false positives, all ours and all fixed in the generator:
PROTO_001 did not know JEDEC MPR-mode reads (MR3 A2) need no open row;
TIMING_012 fired on X before the testbench drove RESET#. A third apparent
problem (a quarter of the pin trace missing) was an anchored grep meeting the
Micron model's newline-less echo; `trace_extract.py` fixed too. Evidence:
`reports/uberddr3/known_good_1fea117.json`, runbook `refdesigns/uberddr3/README.md`.
Data integrity added the same day (`refdesigns/uberddr3/uberddr3_wb_monitor.sv`,
`check_data_integrity.py`, `reports/uberddr3/data_integrity_1fea117.json`): 0
read mismatches over 4608 reads against a byte-enable-aware host memory model,
and 9216/9216 host requests matched in order to a CAS at the DRAM pins with
the spec-mapped row/bank/column. **Phase B known-good item complete.** A
sanity mutation (spec tRCD 60 ns) fires 2347 TIMING_001 and nothing else.
Still open: a directed stress of UberDDR3's tRRD/tFAW gap (it enforces tRRD
at 7.5 ns where JEDEC needs 4 nCK = 12 ns, and never enforces tFAW).
JasperGold 24 and Cadence VIPCAT are installed on the compute nodes
(`/opt/coe/cadence/JASPERGOLD240/bin/jg`, mounted there only), so the formal
item can start.

**Seeded faults on the Frontend2 drop (2026-09-24).** 15 faults, 4 of them
re-seeded at new sites after the rewrites: 13/13 detectable killed, blame
correct on every kill, 2 still masked by the same open defects
(scheduler_regrant masks M12, data_path_width masks M13), none survived
(`reports/faults/fault_matrix.json`, drop_root Frontend2/OutputFolders).

**Formal (started).** `chain_harness_gen.py --formal` emits `formal/chain_formal.sv`:
the command path's 9 blocks wired per the integration map with host inputs and
DRAM data free and CSR/status tied, so the generated `cmd_gen_sva.sv` is
proved over ALL host request streams on the composed scheduler + bank_tracker
+ cmd_gen, not on cmd_gen alone (whose inputs would be unconstrained).
First JasperGold run (20 min budget, trace limit 200; `reports/formal/`):
13 assertions — **4 proven for all inputs** (tRCD, tRP, tRAS, tFAW), **8
counterexamples**, 1 undetermined (tREFI: bound 23400 cycles exceeds the trace
limit; needs an abstraction). Shallow CEXs at 6 cycles from reset (tRC, tRFC,
double-activate) are the defects simulation already reports; deep CEXs at
136–139 cycles include two simulation never saw (PROTO_001 CAS to a closed
bank, TIMING_008 tWR) — traces exported for triage: a legal host sequence
makes them new findings, an illegal one means the top needs Wishbone-master
assumptions. 24/25 covers reachable. **Triage done (all 8 traces):** both are real under a
protocol-legal host — the scheduler READs a bank one cycle after PRECHARGing
it (PROTO_001) and PRECHARGEs a bank one cycle after WRITEing it (tWR) —
filed as `findings/outbox/.../formal_cmd_path_findings.json`: the first two
defects found by formal that no simulation stimulus reached; the other six
CEXs (tRC, tRFC, double-ACT, tRRD, tWTR, tRTP) are two-command witnesses of
the findings simulation already has. Formal findings
now flow through `emit_findings.py` (detector `formal:jaspergold`) into
findings v2 and the Frontend's retry instructions. One command runs the flow:
`tools/run_formal.py` (generate formal top, package, JasperGold on Olympus,
parse the RESULTS table into `reports/formal/`). tREFI: JasperGold reports
`undetermined` at bound 201 = no violation reachable within 200 cycles; the
full 23400-cycle bound needs a counter abstraction, recorded as the one
signoff blocker in this table.

**Constrained-random v2 (2026-09-24).** `closure/random_v2.py`: address
locality from `memory_geometry` (row hit / same-bank conflict / bank switch
profiles), back-pressure bursts of 2 x queue depth, paced 0-3 idle runs,
read/write pairs to one address, drains; still seeded, legal, reads no
coverage; pluggable as `--stimulus random_v2` and the closure loop's
`--arm constrained`. Batch 1 (path_19/04/07 x seeds 1-4, 400 requests each,
12 runs, ~1 min each) merged with the drop baseline (`reports/crv2/`):
**scheduler 71.4 → 92.0 %, cmd_queue 58.4 → 89.1 %, design 75.1 → 85.2 %**
(scheduler, cmd_queue and design targets in `SIGNOFF.md` met); bank_tracker
78.5 % unchanged. Batch 2 (path_18/20/03 x seeds 5-8, 12 more runs)
merged with everything: **scheduler 93.7 %, cmd_queue 91.6 %, wb_port 59.5 →
87.1 %, data_path 76.7 → 92.9 %, design 89.5 %** — every `SIGNOFF.md` block
target met except bank_tracker (78.5 %, unmoved by 24 runs: its remaining
code is the precharge-all path, which the harness ties off because the
design never drives it (filed integration gap), and window/timer branches
host traffic cannot reach — exclusion candidates E-SPEC/E-DEAD, to be settled
by formal cover, not more seeds). `reports/crv2/summary.json`. Functional: the timing at-minimum bins stay at 50 %
— the design never issues at the exact minimum spacing under host stimulus;
whether those bins are reachable is a formal-cover question (E-DEAD
candidates under `SIGNOFF.md` §4), not a seeds question.

**First round trip with the Frontend closed (2026-09-24, drop 5661e03).**
Lehana's reply (`Frontend2/VALIDATION_INTEGRATION_PLAN.md`) shipped manifest
stamps (C1), phase-1 `source` (C4: 60/72 edges now manifest-derived), the
scheduler re-grant fix, refresh-with-open-banks, the DQ-width redesign and
reserved-bit masking. Regression: **24 → 15 open findings, 10 auto-resolved,
8 paths improved, 0 regressions**; width gate 23/23; seeded faults **15/15 killed, 0 masked** (the re-grant
and DQ fixes unmasked M12 and M13).
Three apparent regressions were ours and are fixed: SCHED_001 was
end-of-window starvation (settle 64 → 400 on host-driven paths), the DM
mismatches were the predictor carrying byte enables through instead of JEDEC
DM polarity, and PRE row-address bits are now a declared don't-care
(catalog `dont_care`, plan gap #10 closed). Read responses under fr_fcfs are
aligned by aux tag. Formal on 5661e03: same 4 proven / 8 CEX — the two
formal-only defects are NOT closed by the re-grant guard; the emitter now
carries formal findings until a formal run on the drop proves them. Reply
to Lehana appended to `findings/HANDOFF_FRONTEND_2026-09-24.md`.

**Signoff document v1 written:** `SIGNOFF.md` (drop acceptance, verdict
levels, per-block coverage targets, exclusion codes, waiver policy, formal
bar, known-good bar, regression rule, package contents).

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
| Constrained-random stimulus | **Yes** | `random_v2.py`: address-aware profiles, back-pressure bursts, pacing; 12 runs took scheduler/cmd_queue from 71/58 % to 92/89 % |
| Regression management | **Partial** | vManager session exists; no history across drops, no pass/fail trend, no nightly |
| Triage → owner → fix → verify | **Yes (one round trip done)** | 10 findings auto-resolved by a Frontend drop from our package; formal findings carried until re-proved |
| Formal property checking | **Started** | JasperGold on the composed command path: 4 of 13 generated SVA proven for all inputs, 8 CEX (6 match sim findings, 2 new, under triage), tREFI needs abstraction |
| Gate-level simulation | **No** | backend has no cell models or SDF |
| Known-good reference (false-positive rate) | **Yes (timing/protocol)** | UberDDR3 + Micron model at the DRAM pins: 0 assertion failures, 0 model errors, 15946 commands |
| Signoff criteria written down | **Yes (v1)** | `SIGNOFF.md`: acceptance, verdicts, targets, exclusions, waivers, formal bar, package |

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
1. ~~False-positive rate unknown (no correct design seen) → UberDDR3.~~ Measured: 0 timing/protocol false positives after two generator fixes; 0 data-integrity mismatches; host↔pin addresses consistent 9216/9216.
2. ~~System-level detection rate unknown → seeded-fault suite.~~ 23/23 killed on drop 5661e03, blame correct on all; every assertion and rule the ledger tracks has at least one fault that fires it except REF_001 (unreachable starvation) and TIMING_002/012.
3. ~~No formal → JasperGold on generated SVA.~~ Command path (4 proven / 8 cex filed / 1 undetermined) and boot path (6/7 proven under a documented wait-counter cut, CAL_001/002 concretely); `run_formal.py --path <p> [--stopat sig]`.
4. No gate-level → C7.
5. ~~Random stimulus is unconstrained and short → constrained-random v2.~~ Done (`closure/random_v2.py`); scheduler/cmd_queue over 85 %.
6. ~~Coverage has no targets or exclusion policy → signoff document.~~ `SIGNOFF.md` v1.
7. No regression history → `compare_drops`, nightly vManager with trend.
8. Findings are hand-assembled → feedback loop steps 1–3.
9. ~~Integration map is hand-written → derive from `source`.~~ Done; 21 edges still carried as overrides until phase-1/2 manifests declare them.
10. ~~Don't-care fields (PRE address) counted as mismatches → declared masks + intake rule.~~ Done: `interface_catalog.json` `dont_care`, applied by the scoreboard before alignment.
11. ~~Only one spec ever run → second preset spec.~~ Lehana's compiled DDR3-1333/x16/1-lane spec (`VALIDATION_SPEC=Frontend2/OutputFolders/generated_spec.json`): Phase-1 paths 3/3 pass, the 7 Phase-1 seeded faults 7/7 killed by checkers derived from that spec (register map with its reset values, init SVA at its clock), JEDEC 25/25. Phases 2–4 wait for RTL from the same spec; the fault matrix now records the spec revision per row.
12. Waivers W-002/W-003 undecided → human decision.
