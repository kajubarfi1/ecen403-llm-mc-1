# Validation handoff contract (Frontend ⇄ Validation)

One local tree, no git in the loop. The Frontend writes a drop; validation
reads it in place and writes its result to one fixed place; the Frontend
reads that place on every iteration.

## 1. Where validation takes the drop from

`Validation/spec/rtl_drop.json` → `roots` (today: `Frontend2/OutputFolders`).
Inside a root, a block is `<PHASEnRTL>/<block>.sv` + `<block>_manifest.json`.
Validation reads **only** those directories (`rtl_dirs_preferred`); a copy
elsewhere (e.g. `TOPRTL/`) is never chosen over them.

The drop may be partial (Phase 1 only). Blocks that are absent are reported
absent, never substituted; paths that need them are `blocked`, not failed.

The drop should ship the spec it was generated from as
`<root>/generated_spec.json`. Every manifest's `spec_revision` must equal
that spec's `revision`; a block from another revision is **foreign** and
gets one finding (`SPEC_MISMATCH`) and nothing else.

A revision is a name; the content is what Validation judges against. The
**spec id** is sha256 of the spec's canonical JSON (sorted keys, no
whitespace), first 16 hex digits (`Validation/spec/spec_identity.py`).
Validation records it next to every `spec_revision` it writes (handoff,
findings, model provenance). The revision must change whenever the content
does: when the shipped spec carries a known revision with a different id,
Validation adopts the shipped spec (it is what the RTL was generated from)
and files one `SPEC_REVISION_REUSED` finding (2026-10-08: `CTRL_STATUS`
grew a bit and the intake fields were added under one revision string).

## 2. What names a drop

`drop_id` = first 12 hex digits of SHA-256 over, for each block in sorted
name order: the block name, the bytes of `<block>.sv`, the block name, the
bytes of `<block>_manifest.json`. "Each block" is **every block of the
design** — the 11 listed in `Validation/spec/path_definitions.json`
`blocks` (`addr_decoder, bank_tracker, calibration, cmd_gen, cmd_queue,
config_regs, data_path, init_fsm, refresh_ctrl, scheduler, wb_port`), not
only the 9 the interface catalog names (fixed 2026-10-01; ids before that
date covered 9). Nothing from git, nothing from timestamps. **Bytes are
hashed with CRLF normalised to LF** (2026-10-08: a Windows checkout
computed a different id for the same files), so the id is the same on
every teammate's machine. Same files → same id; one changed byte → a new
drop. Reference implementation: `Validation/structural/rtl_drop.py: drop_id()`.

**`design_id`** answers the other question, "did the design change": the
same hash with the volatile parts left out — RTL lines that only carry the
generation timestamp (`// Generated ...`) and the manifest's provenance keys
(`generated_utc`, `git_commit`, `generated_by`, `generator_version`), the
manifest hashed as canonical JSON. A regeneration with no spec change mints
a new `drop_id` (new timestamps) but the same `design_id`
(`a7cd3cb93546` and `4b86c7cd3705` are one design). Both ids are in
`HANDOFF.json`; findings history keys on `drop_id`, "nothing was rebuilt"
is read from `design_id`. Reference: `rtl_drop.py: design_id()`.

```python
import hashlib, os
def drop_id(root, blocks):               # blocks: all 11 names, any order
    h = hashlib.sha256()
    for b in sorted(blocks):
        for fn in (f"{b}.sv", f"{b}_manifest.json"):
            p = find(root, fn)           # the phase directory's copy
            if p: h.update(b.encode()); h.update(open(p, "rb").read())
    return h.hexdigest()[:12]
```

## 2b. The spec-review stage (before Phase 1)

`full_pipeline.py` runs a validation stage right after microarch synthesis,
today through `Microarch/dummy_validation_agent.validate_spec`. Validation's
implementation keeps the same contract:

```python
sys.path.insert(0, "<repo>/Validation/spec")
from validate_spec_stage import validate_spec
result = validate_spec(spec, compile_result)   # {"status", "findings", "validator", "review"}
```

`status: FAIL` (stop before Phase 1): a schema violation against
`Spec/llmmc_microarchitecture.schema.json`, a JESD79-3 violation or a false
`$consistency_checks` claim, a register map that disagrees with itself or
with `timing_model.$derived_cycles`, a failed compiler consistency check, or
no `revision`.

`status: PASS` may still carry `[gap:decision] ...` findings: questions the
spec leaves open (unmapped CSR reads, DM polarity, tMRD/tMOD, ...). Validation
judges the RTL under a pinned convention meanwhile; the synthesis agent can
close most of them by stating the field named in the finding. They are also
written to `Validation/findings/outbox/current/SPEC_REVIEW.json`
(`requires_human_review`, the JEDEC table, the gap list with the field each
one asks for).

The same review is step 2 of `validate_drop.py` on the spec the drop is
judged against.

## 3. How validation is invoked

```
python3 Validation/tools/validate_drop.py            # complete drop
python3 Validation/tools/validate_drop.py --partial  # some blocks absent
VALIDATION_SPEC=<root>/generated_spec.json python3 Validation/tools/validate_drop.py --partial
```

The third form judges the drop against the spec it ships instead of
`Validation/spec/llmmc_microarchitecturespec_filled.json`.

## 4. Where the Frontend reads the result

**`Validation/findings/outbox/current/`** — always the newest result:

| file | what |
|---|---|
| `HANDOFF.json` | `drop_id`, `design_id`, `spec_revision`, `spec_id`, `status` (PASS/FAIL), `failed_modules`, `generated_utc`, path of the archive |
| `retry_instructions.json` | per module: `failed_checks[]` with `id`, `name`, `expected`, `actual`, `severity`, `confidence`, `spec_ref`, `anchor[]` (file/line/signal in the drop), `repro`, `fix` (when a repair proved it), `owner_candidates`; `requires_human_review`; `untested_in_this_drop[]`; `drop_status` (partial runs) |
| `findings_v2.json` | the full records behind every check |
| `DROP_STATUS.json` | present when paths were blocked: which blocks are absent / foreign, which paths ran, which wait and why |

The loop: read `HANDOFF.json`, confirm `drop_id` equals the id of the drop
just written (else validation has not run on it yet), then act on
`retry_instructions.json`.

`flow.py` (repo root) does this for the Frontend today: it renders the
package as each failing phase's `VALIDATIONREPORT/phase{N}_error_report.json`
(`Validation/findings/to_frontend_error_report.py`; `failure_stage:
BEHAVIORAL_SIMULATION`, one "test" per failed check with expected/actual,
anchor and repro) and runs `Phase{N}/phase{N}_validation_agent.py
--output-dir <drop> --spec <spec>` with every proposal applied, then
regenerates those phases and validates again. `status: PASS` with no `failed_modules` means
every path that could run passed; look at `DROP_STATUS.json` for what could
not run yet.

Archive of every result: `Validation/findings/outbox/<spec_revision>/<drop_id>/`
(same files). `outbox/<spec_revision>/latest` names the newest `drop_id`
for that revision.

## 5. Meaning of a check's `confidence`

- `confirmed` — model-free evidence (an assertion, a rule, a structural
  check, a repair that silenced it). Fix it.
- `observed` — a transaction predictor disagreed with the design. Real in
  every case so far after validation's own fixes, but it is a model's word.

`untested_in_this_drop` are earlier findings this drop could not re-check
(block absent or every path through it blocked). They are still open.
