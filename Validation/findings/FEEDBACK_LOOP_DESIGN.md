# RTL findings: detect → localize → triage → hand off → verify

How a validation failure becomes something the Frontend's feedback agent can
act on, and how we know on the next drop whether it did.

**Status (2026-09-18).** Steps 1–4 are implemented and run on drop `b4d6f45`:

| Piece | File | What it does today |
|---|---|---|
| schema | `findings/findings_schema_v2.json` | the v2 record, required fields listed |
| localize + triage + package | `findings/emit_findings.py` | re-judges every failing stage, keys one finding per (owner, check id), owner from `rule_owners` in the rule files, expected/actual from the scoreboard line, anchors from a search of the owner's RTL for the failing ports, repro from the run, confidence from the evidence class, history from `reports/drops/` snapshots; register-bus mismatches are split per register name from the spec |
| hand off | `findings/retry_adapter.py` | `retry_instructions.json` in the Frontend's `failed_checks` shape, per owner module, with anchor / repro / confidence as extra keys |
| verify | `tools/compare_drops.py` | per-path regression / fixed / stimulus classification and the snapshot history the emitter reads |

Output lives at `findings/outbox/<spec_revision>/<drop>/` (`findings_v2.json`,
`retry_instructions.json`) with a `latest` pointer. Not yet built: the
mechanism paragraph (step 3's agent call) and the Frontend-side consumer.

## 1. What the consumer needs

Lehana's Frontend2 plan makes one thing LLM-backed: a **feedback agent** that,
"given a structured failure (check id, expected, actual, owning module +
function anchor) and that module's generator source file, produces a scoped
patch to the implicated function only". Today's pipelines already carry a
narrower version of that contract: `retry_instructions[module].failed_checks`
= `[{id, name, pass, expected, actual}]`, replaced whole on each attempt, with
`requires_human_review` when retries run out.

So the handoff is not prose. It is, per finding:

| Field | Why the fixer needs it |
|---|---|
| **owning module** | which generator to patch; a chain-run failure must be blamed on one block, not the path |
| **check id** | stable identity across retries: taxonomy id + rule id (`REF_002`, `SCHED_002`, `CSR_001/reserved_bits`) |
| **requirement + spec clause** | the sentence the RTL violates, and the JSON path it came from, so the fix targets the spec and not our model |
| **expected vs actual** | concrete values at the first failing transaction, in the block's own port names |
| **source anchor** | file, line range, construct (`always_comb` selection over `q_valid`) — what to look at first |
| **mechanism** | one paragraph: how the observed sequence arises from the anchor; marked *confirmed* (read at source) or *hypothesis* |
| **repro** | stimulus file, harness, xrun command, first-failure cycle, trace window: enough to reproduce without our scoreboard |
| **drop identity** | git commit + per-block file the verdict was taken on (the resolver stamp) |
| **status history** | introduced in / first seen / last seen / resolved in, so a regression is visible as one |

Everything above except *mechanism* is deterministic; *mechanism* is the one
place an agent adds value, and its citations (lines, signals) are checkable.

## 2. Pipeline

```
 run_path / rerun_scope           existing: monitors, scoreboard, checkers, SVA, coverage
        │  violations (taxonomy id, txn refs), assertion hits, X-values
        ▼
 1. LOCALIZE   blame one block; find first failure; window the trace; anchor in source
        ▼
 2. TRIAGE     dedupe by signature; classify; severity; regression vs previous drop; route
        ▼
 3. PACKAGE    repro bundle + expected/actual + spec clause + (agent) mechanism with citations
        ▼
 4. HAND OFF   findings/outbox/<spec_rev>/<drop>/  → findings v2 + retry_instructions.json adapter
        ▼
 5. VERIFY     next drop: rerun, compare; auto-resolve fixed, auto-open regressions, keep history
```

### 1. Localize (deterministic)

- **Blame from structure.** A composed path is judged stage by stage; the
  first failing stage whose upstream stages passed owns the defect (path_02:
  wb_port passes, addr_decoder passes, cmd_queue+scheduler fails → scheduler
  side). For a joint stage (`cmd_queue+scheduler`) the checker's rule decides:
  SCHED_002 "matches no enqueued request" implicates the issuer, not the queue.
  Each stage rule in `stage_invariant_rules.json` gains an `owner` field so this
  is data, not a heuristic.
- **First failure.** The earliest violation (by `seq`) with the N transactions
  before it, across every stream in the trace, plus the simulator time. That
  window is the repro's "look here".
- **Source anchor.** Port names in the failing transaction map to signals in
  the owning block's RTL (the manifest gives the port → the RTL gives the
  always blocks that assign it). Report the assignment sites as candidate
  anchors, ranked by proximity to the violated field. No LLM here.
- **Regression detection.** Compare this drop's verdict per (path, stage,
  rule) against the previous drop's report. New failure = regression,
  stamped `introduced_in: <drop>`; vanished failure = resolved.

### 2. Triage (deterministic)

- **Signature** = (owner block, check id, normalized detail). One finding per
  signature per drop; occurrences counted, paths listed. The 1,494 SCHED
  violations on path_20 are one finding.
- **Class**: `rtl_defect` (checker/SVA/X against a spec-derived expectation),
  `spec_gap` (intake gate or undetermined comparison), `integration_gap`
  (map glue, missing consumer), `stimulus_issue` (our sequence drove something
  the spec forbids), `drop_incomplete`, `infra` (build/elab error). Only
  `rtl_defect` and `integration_gap` route to the Frontend.
- **Severity** from the taxonomy entry; `critical` for data corruption or
  JEDEC timing.
- **Confidence**: `confirmed` when the mechanism was read at source or the
  evidence is model-free (X on a pin, an independent SVA), `observed` when only
  the checker says so. The Frontend agent can weight retries by this.
- **Human review** when class is `spec_gap`, when a waiver would be needed, or
  when the same finding has survived N drops.

### 3. Package

- **Repro bundle** per finding: the sequence JSON, generated driver and
  harness, the exact xrun line, the resolver stamp, and a `first_failure`
  block (`cycle`, `time_ns`, trace window). Shrinking (drop stimulus steps
  while the violation persists) is a later step; a first-failure prefix is
  already a large reduction.
- **Expected / actual** in the block's port vocabulary, taken from the
  scoreboard's comparison or the checker's violation, never restated by hand.
- **Mechanism (agent, Opus).** Prompt = requirement, spec clause, anchor
  candidates, trace window, the owning block's RTL. Output = mechanism
  paragraph + cited lines + a fix hypothesis. Gate: every cited line must
  exist and mention a signal from the trace window; otherwise the paragraph is
  dropped and the finding ships without it. Agents propose, structure proves.

### 4. Hand off

- `validation-findings/2`: today's fields plus `owner_module`, `check_id`,
  `requirement`, `spec_ref`, `expected`, `actual`, `anchor[]`, `mechanism{}`,
  `repro{}`, `confidence`, `introduced_in`, `first_seen`, `last_seen`,
  `resolved_in`, `occurrences`, `paths[]`.
- **Adapter** to the Frontend's existing shape: `retry_instructions.json` per
  drop, `{module: {module, failed_checks:[{id, name, pass:false, expected,
  actual, anchor, repro}]}}`, `requires_human_review` mirrored. Their pipelines
  read this without change; the feedback agent reads the v2 finding for depth.
- **Location**: `Validation/findings/outbox/<spec_rev>/<drop_commit>/`, with
  `latest` pointing at the newest drop. The Frontend decides whether it pulls
  from the repo or we open a PR onto their branch with the file.

### 5. Verify on retry

Every drop: fetch, `rtl_drop.py` check, rerun, `compare_drops.py`. A finding
whose check passes on the new drop is closed with `resolved_in`; a check that
newly fails opens a finding with `introduced_in`; a finding that neither
appears nor is exercised is `not_exercised` (coverage says the situation was
never created), which is itself a signal that the retry changed stimulus
reachability.

## 3. Worked example (from this drop)

**SCHED_002 / owner scheduler / confirmed.** Requirement: no CAS may issue
that matches no enqueued request (proposed taxonomy SCHED_002; stage rule
`cmd_queue_scheduler`). Expected: one `sched_cmd.command` per accepted
`cq_enq`; actual: 29 grants for 19 enqueues, first duplicate at seq 41
(`WR bank=0 col=24 aux=0x5`). Anchor: `scheduler.sv` always_comb selection over
`q_valid` (no granted-slot mask); `deq_grant <= 1'b1` registered; `cmd_queue.sv`
clears `mem_valid[deq_idx]` one cycle after grant. Mechanism: during the clear
cycle the slot is still valid and is re-selected. Repro: path_01 seed 1, 19
writes, first failure at 1.2 µs. Introduced: unknown (present since the first
judged drop); last seen b4d6f45.

**CSR_001 / owner config_regs / confirmed / regression.** Introduced in
b4d6f45. Expected `REFRESH_CONFIG` read `0x1ff` after writing `0xffffffff`;
actual `0xffffffff`. Anchor: `config_regs.sv:230` byte-lane write without the
field mask that `dce7b40:176` had. Repro: register walk, path_12.

## 4. Build order

1. **Schema v2 + adapter + compare_drops** — small, unblocks the loop; the
   Frontend can consume it the same day.
2. **Localizer** — owner from stage rules, first-failure window, anchor
   candidates from manifest → RTL assignment search.
3. **Triage** — signature dedupe, class/severity/confidence, regression stamps,
   history carried across drops.
4. **Repro bundles** — assemble from the per-run work dirs we already keep.
5. **Mechanism agent** with the citation gate.
6. **Wire to Frontend2's feedback agent** with Lehana: agree the anchor
   semantics once generators become scripts (RTL line ranges are what we can
   give; the RTL-construct → generator-function map is theirs).

## 5. Questions for the Frontend side

- Does the feedback agent want one finding per module per drop, or every
  occurrence? (Proposal: one, with occurrences and paths listed.)
- Where does it read from: the repo path above, a PR, or a message?
- When generators are scripts, is an RTL line range enough of an anchor, or
  should we also name the manifest port and the spec field?
- Who closes a finding: our verify step (check passes on the new drop) or a
  human? (Proposal: ours, with `resolved_in`; humans handle spec gaps.)
