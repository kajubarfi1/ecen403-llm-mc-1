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

## 2. What names a drop

`drop_id` = first 12 hex digits of SHA-256 over, for each block in sorted
name order: the block name, the bytes of `<block>.sv`, the block name, the
bytes of `<block>_manifest.json`. Nothing from git, nothing from timestamps.
Same files → same id; one changed byte → a new drop. Reference
implementation: `Validation/structural/rtl_drop.py: drop_id()`.

```python
import hashlib, os
def drop_id(root, blocks):               # blocks: the names, any order
    h = hashlib.sha256()
    for b in sorted(blocks):
        for fn in (f"{b}.sv", f"{b}_manifest.json"):
            p = find(root, fn)           # the phase directory's copy
            if p: h.update(b.encode()); h.update(open(p, "rb").read())
    return h.hexdigest()[:12]
```

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
| `HANDOFF.json` | `drop_id`, `spec_revision`, `status` (PASS/FAIL), `failed_modules`, `generated_utc`, path of the archive |
| `retry_instructions.json` | per module: `failed_checks[]` with `id`, `name`, `expected`, `actual`, `severity`, `confidence`, `spec_ref`, `anchor[]` (file/line/signal in the drop), `repro`, `fix` (when a repair proved it), `owner_candidates`; `requires_human_review`; `untested_in_this_drop[]`; `drop_status` (partial runs) |
| `findings_v2.json` | the full records behind every check |
| `DROP_STATUS.json` | present when paths were blocked: which blocks are absent / foreign, which paths ran, which wait and why |

The loop: read `HANDOFF.json`, confirm `drop_id` equals the id of the drop
just written (else validation has not run on it yet), then act on
`retry_instructions.json`. `status: PASS` with no `failed_modules` means
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
