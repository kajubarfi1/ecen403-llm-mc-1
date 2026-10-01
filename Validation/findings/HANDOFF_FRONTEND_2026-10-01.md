# Handoff to Frontend — 2026-10-01

From Validation (Jacob). Everything below was found by running the top-level
flow (`flow.py` at the repo root) against the current `Frontend2/` tree and
the merged drop. Nothing in `Frontend2/` was changed by us; each item says
what we see, what we need, and what we already do on our side meanwhile.

The contract this refers to: `Validation/findings/HANDOFF_CONTRACT.md`
(where we read the drop, how a drop is named, where you read results).

---

## 1. The drop is built from two specs

The Phase-1 blocks in `Frontend2/OutputFolders/PHASE1RTL/` were generated
from `generated_spec.json` (rev `compiled_ddr31333_x16_1lane_1rank`:
DDR3-1333, x16, one byte lane, 167 MHz, 28-bit host address). Phases 2–4 and
`TOPRTL/` are still the golden `golden_ddr3_1600k_x8_2lane_1rank` design.
Every manifest says so in `spec_revision`, and it shows at the first seam:
`wb_port.req_addr` is 28 bits, `addr_decoder.req_addr` is 29.

A design assembled from two specs has no single contract, so validation
blocks every path that crosses the seam and files `SPEC_MISMATCH` per block
(`outbox/current/retry_instructions.json`).

**Ask:** one generation = one spec, all four phases and the top from the same
`generated_spec.json`. When a phase is regenerated alone, it is regenerated
from the spec the rest of the drop was built from. `TOPRTL/` copies must be
the phase outputs they claim to be (today `TOPRTL/wb_port.sv` is the golden
one while `PHASE1RTL/wb_port.sv` is the compiled one; we read the phase
directories and never the copies, but the copies should not diverge).

## 2. Compiled specs fail the shared schema on `latency_model`

`microarch_compiler.compile_spec()` writes the six `latency_model.*_nCK`
fields (`read_hit_latency_nCK`, `read_miss_latency_nCK`,
`read_empty_latency_nCK`, `write_hit_latency_nCK`,
`write_to_read_turnaround_nCK`, `read_to_write_turnaround_nCK`) as integers
(e.g. `23`). `Spec/llmmc_microarchitecture.schema.json` declares them as
strings — a formula with its derivation, as the golden spec has it:
`"pipeline_latency*4 + CL + BL/2 + 2 = 2*4 + 11 + 4 + 2 = 25 nCK"`.

The spec-review stage (section 4) checks every spec against that schema, so
today every compiled spec fails review before any RTL is generated. JEDEC
(25/25) and the register map (reset values = `$derived_cycles`) are fine.

**Decision needed (team, it is `Spec/`):** either
- the schema changes those six to `integer` (nCK) — our recommendation; a
  number is what every tool consumes, and the derivation can go in a sibling
  `"$formula"` string — or
- the compiler emits the formula string.

Either is a few lines. Until one lands, the flow only runs with a
hand-written spec (`flow.py --spec …`).

## 3. Fields the compiler should emit (the intake gaps)

The spec review carries 12 open questions as advisory. The microarch agent
cannot answer them (they are not choices); the compiler's template can, by
emitting the field. We judge the RTL under a pinned convention for each one
until the spec states it. Field, allowed values, and what it decides:

| field | values | decides |
|---|---|---|
| `csr_register_map.unmapped_read_data` | `zero` / `all_ones` / `undefined` / `last_written` | what a read of an undeclared offset returns |
| `csr_register_map.unmapped_write_behavior` | `ignored_with_error` / `ignored_silently` / `error_only` | a write to an undeclared offset |
| `csr_register_map.access_violation_error` | `flagged` / `silent` | does a write to a read-only register set `csr_err_o` (CSR_001 names the violation, not the flag) |
| `csr_register_map.read_byte_enable_semantics` | `ignored` / `must_be_full` / `masks_data` | byte enables on a read |
| `csr_register_map.status_read_sampling` | `previous_edge` / `same_cycle` | which cycle's status a read returns |
| `data_path_mapping.ddr_dm_polarity` | `active_high_mask` / `active_high_enable` | DM = "mask this byte" or "write this byte" |
| `controller_architecture.speculative_activate` | `allowed` / `forbidden` | may the scheduler ACTIVATE a row no queued request asked for |
| `timing_model.tMRD`, `timing_model.tMOD` | ns (JESD79-3: tMRD = 4 nCK, tMOD = max(12 nCK, 15 ns)) | MRS-to-MRS and MRS-to-command spacing in init |
| `failure_taxonomy.categories[]` | ids `SCHED_001..` | a scheduler family: dropped request, invented command, out-of-order service, starvation |
| `failure_taxonomy.categories[]` | an id naming `tREFI` | every stated timing parameter needs a failure a checker can file under |
| `block_interfaces` (section) | per hop: from/to ports, widths | the 19 block-to-block hops that only `path_definitions.json` and the manifests declare today |

Current pinned conventions (what the RTL is judged under meanwhile):
`unmapped_read_data = zero`, `unmapped_write_behavior = ignored_with_error`,
`access_violation_error = silent`, `read_byte_enable_semantics = ignored`,
`status_read_sampling = previous_edge`, `speculative_activate = allowed`.
DM polarity has no convention: `data_path` findings on DM stay open until
the spec says.

`Validation/spec/completeness_rules.json` is the machine-readable form of
this table (and `python3 Validation/spec/spec_completeness.py --checklist`
prints it).

## 4. The spec-review stage before Phase 1

`full_pipeline.py` calls `Microarch/dummy_validation_agent.validate_spec`
after synthesis. Validation's implementation of that stage keeps the same
contract and replaces it:

```python
sys.path.insert(0, "<repo>/Validation/spec")
from validate_spec_stage import validate_spec
result = validate_spec(spec, compile_result)   # {"status", "findings", "validator", "review"}
```

FAIL = schema violation, JESD79-3 violation (rules recomputed from the
numbers; the spec's own `[check]` claims re-derived), register map
inconsistent with itself or with `timing_model.$derived_cycles`, failed
compiler consistency check, or no `revision`. PASS may carry
`[gap:…]` findings (section 3). The full review is written to
`Validation/findings/outbox/current/SPEC_REVIEW.json`.

**Ask (small):** a way to hand the review back to the microarch agent other
than the request text. Today `flow.py` re-runs `microarch_cli.py` with the
original request plus the blocking findings appended, because text is the
agent's only revision input. A `--feedback <SPEC_REVIEW.json>` option on
`microarch_cli.py` / `run_english()` would let the agent see the structured
findings (which field, which rule) instead of prose.

## 5. Regeneration from `retry_instructions.json`

Validation results are read from one place:
`Validation/findings/outbox/current/` — `HANDOFF.json` (drop id, spec
revision, status), `retry_instructions.json`, `findings_v2.json`,
`DROP_STATUS.json`. The drop id is a content hash of the drop's files (recipe
in the contract), so you can check you are reading the result of the drop
you just wrote.

Today your repair agents (`Phase{1,2}/phase{N}_validation_agent.py`) read
`VALIDATIONREPORT/phase{N}_error_report.json` and need a person at the
`[a]pply / [r]etry / [s]kip` prompt. The flow bridges that: it renders our
package as that error report (one "test" per failed check, with expected /
actual, spec reference, source anchor and reproduction) and answers the
prompts with "apply". That works, but the agent sees a flattened text where
the package has structure.

**Ask:** the agents consume the package directly and run unattended, for
all four phases:

```
phase{N}_validation_agent.py --retry <retry_instructions.json> --output-dir <drop> --spec <spec> --yes
```

`flow.py` already detects `--retry` in an agent's `--help` and switches to
it, so nothing changes on our side when it lands. Per failed check the
package gives: `id`, `name` (the spec requirement), `expected`, `actual`,
`severity`, `confidence` (`confirmed` = model-free evidence; `observed` = a
predictor disagreed), `spec_ref`, `anchor[]` (file / line / signal in the
drop), `repro` (a command), `fix` (when a repair proved it), `owner_candidates`,
`occurrences`, `paths`. `untested_in_this_drop[]` lists earlier findings this
drop could not re-check; `requires_human_review` means a spec gap or waiver
needs a person, not a regeneration. Phases 3 and 4 have no agent today, so a
scheduler / cmd_gen / data_path finding halts the flow.

## 6. Running unattended

- The phase pipelines prompt for an Olympus password unless `OLYMPUS_USER`
  and `OLYMPUS_KEY` (a private-key path) are exported; a scripted run dies
  at that prompt. `flow.py` refuses to start Phase 1 without them. Fine as
  is — just so you know the orchestrator depends on it.
- `generate_top.py` returns 0 when its lint is SKIPPED (SSH failure); the
  phase reports likewise route `SKIPPED` to pass. The flow prints those
  `SKIPPED` states; they are not treated as a pass of the gate.
- A root file named `yes` (a 23 KB spec) was committed in "Frontend stuff" —
  the CLI's `write spec? [path]` prompt answered with "yes". Harmless; delete
  it.

## 7. Already done on our side, in case you see different numbers

- The Wishbone driver and monitor are now B4 *pipelined* (the spec's
  `interface_type`). The "duplicate read request" finding reported on every
  drop since 1fea117 was our driver holding `stb` until `ack`; wb_port had
  no such defect. Likewise the config_regs `CTRL_STATUS` finding was our
  monitor's sampling point. Phase-1 blocks carry **no findings** on the
  current drop.
- The 12 overrides in `integration_overrides.json` your manifests made
  redundant (every input now declares its `source`) are removed; the map is
  72 manifest edges, 0 overrides. Thank you — that was ask #5 of the
  September handoff.
- Against the compiled 1333 spec (`VALIDATION_SPEC=…/generated_spec.json`),
  the Phase-1 blocks pass all three Phase-1 paths and all seven Phase-1
  seeded faults are still caught by checkers derived from that spec. Your
  compiler's `$derived_cycles` and the TIMING register reset values agree.
