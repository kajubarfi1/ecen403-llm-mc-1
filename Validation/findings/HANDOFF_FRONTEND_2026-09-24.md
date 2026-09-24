# Validation → Frontend handoff (2026-09-24, drop `b4d6f45`)

> **Update, same day:** your Frontend2 drop (`c8ac792`, validated as `1fea117`)
> ran through the full regression. 3 paths improved, 14 unchanged, 0
> regressions. `wb_port/DATA_001` and `data_path/DATA_001` auto-closed —
> the first findings resolved by one of your drops. The 22 that remain are
> the same defects listed in §2; the current package is now
> `findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/1fea117/`.

From Jacob (Validation) to Lehana (Frontend). Everything below is checkable:
each item names the file that carries the evidence. Five asks, ordered by
how much they unblock; the first two are the ones the semester plan needs
in the next two weeks.

| # | Ask | Contract | Size | Unblocks |
|---|---|---|---|---|
| 1 | Consume `retry_instructions.json` from our outbox on retry | C3 | one adapter in the phase pipelines + one key rename | the full spec → RTL → validation → regenerate loop |
| 2 | Fix the open RTL defects below (anchors and repros are in the package) | — | per-module | two masked fault checks, clean data path, first auto-closed finding |
| 3 | Make the spec compiler emit the ten fields the intake gate asks for | C2 | ~10 constants + 2 taxonomy entries in `microarch_compiler.py` | strict intake; waiver W-001 closes itself |
| 4 | Put `source` on every consumer port in phase-1 manifests | C4 | manifest template change | Dawson's 111 worksheet slots; our integration map becomes derived |
| 5 | Stamp every manifest with git commit + spec revision | C1 | manifest template change | regression history across drops |

---

## 1. Consume our findings on retry (C3)

**Where.** `Validation/findings/outbox/<spec_revision>/<drop>/retry_instructions.json`,
with `Validation/findings/outbox/<spec_revision>/latest` naming the current drop.
Today: `outbox/golden_ddr3_1600k_x8_2lane_1rank/b4d6f45/`.

**Shape.** It is already in your `retry_instructions[module].failed_checks`
form, so a phase pipeline can read it exactly as it reads its own validation
agent's output:

```json
{
  "status": "FAIL", "pipeline": "validation", "drop": "b4d6f45",
  "failed_modules": ["cmd_gen", "config_regs", "data_path", "scheduler", "wb_port"],
  "retry_instructions": {
    "cmd_gen": {
      "module": "cmd_gen", "attempt": 1, "drop": "b4d6f45",
      "failed_checks": [
        { "id": "MISMATCH/ddr_cmd[addr]",
          "name": "cmd_gen must produce the transactions the spec-derived model predicts",
          "pass": false,
          "expected": "ddr_cmd.command addr=0x38c0 bank=0x6 cmd=0x2",
          "actual":   "ddr_cmd.command addr=0x0 bank=0x6 cmd=0x2",
          "severity": "major", "confidence": "observed",
          "anchor": [{"file": "Frontend/OutputFolders/PHASE3RTL/cmd_gen.sv", "line": 85, "signal": "ddr_cmd"}],
          "occurrences": 80,
          "paths": ["path_01_write_cmd", "path_02_read_cmd", "path_18_full_write", "path_20_refresh_preempt"],
          "repro": {"path": "path_01_write_cmd", "command": "python3 Validation/tools/run_path.py --path path_01_write_cmd ..."},
          "finding_id": "cmd_gen/MISMATCH/ddr_cmd[addr]" }
      ],
      "message": "1 check(s) failed on drop b4d6f45; ..."
    }
  }
}
```

`id`, `name`, `expected`, `actual` are the four keys your agents already
read; `severity`, `confidence`, `anchor`, `repro`, `occurrences`, `paths`
are extra and can be ignored or fed to the prompt.

**One key rename on your side.** `config_regs_agent.py:425` reads
`retry_instructions.get("validation_failures")`; the other three LLM agents
read `failed_checks`. `phase1_validation_agent.py:289-293` papers over it by
writing both keys, but our adapter (and anything else that produces retry
instructions) writes only `failed_checks`. Please make `config_regs_agent`
read `failed_checks` and drop the double write.

**What "closed" means.** We do not close a finding by hand. On the next drop
we rerun the same paths; a check that now passes gets `resolved_in: <commit>`
and a check that regresses gets `introduced_in: <commit>`
(`Validation/tools/compare_drops.py`). So the loop test is simply: regenerate
a module against our instructions, land the drop, and the finding should
auto-close on our side with no message from either of us.

**Questions I need answered** (from `findings/FEEDBACK_LOOP_DESIGN.md` §5):
1. One finding per module per drop with `occurrences` and `paths` listed
   (what we emit now), or every occurrence as its own check?
2. Where does the feedback agent read from: the repo path above, or do you
   want it copied into `Frontend/OutputFolders/VALIDATIONREPORT/`?
3. When generators become scripts (Frontend2), is an RTL file + line range
   enough of an anchor, or do you want the manifest port and spec field too?
4. Agreed that our verify step closes findings, and humans only handle
   spec-gap findings?

---

## 2. Open RTL defects on `b4d6f45`, in the order that helps most

The full records (mechanism, spec clause, expected/actual, repro command) are
in `findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/*_findings.json` and the
same facts in `b4d6f45/findings_v2.json` (24 open: 15 critical, 3 major,
6 minor, across scheduler 8, config_regs 6, wb_port 5, data_path 4, cmd_gen 1).

| Priority | Module | Defect | Why first |
|---|---|---|---|
| 1 | cmd_queue + scheduler | Scheduler re-selects a granted slot during the one-cycle dequeue window; requests are dropped (19 enqueued, 16 dequeued). `scheduler_regrant_findings.json` | Masks our seeded fault M12; every scheduler finding in v2 traces to it |
| 2 | data_path | `ddr_dq_o`/`ddr_dq_i` are 32 bits; spec `ddr_channel_width_bits` = 16 with `pack_32_to_16`. `data_path_width_findings.json` | Structural; masks M13; every data_path mismatch is downstream of it |
| 3 | data_path | Write data dropped under back-to-back host writes (buffers 31 of 32). `data_path_write_overflow_findings.json` | Critical, independent of #2 |
| 4 | data_path | Read path emits duplicate and X-valued responses per burst. `data_path_read_findings.json` | Critical |
| 5 | scheduler | REFRESH issued while banks have open rows; command issued before tRFC. `refresh_open_banks_findings.json` | Critical, JEDEC violation |
| 6 | cmd_gen | Bank-tracker feedback carries no bank for PRE/RD/WR. `integration_fb_bank_findings.json` | Integration; bank_tracker cannot track |
| 7 | calibration / top | Nothing consumes calibration's ZQCS request. `zqcs_no_consumer_findings.json` | Integration; periodic ZQ can never happen |
| 8 | config_regs | Regression: regenerated config_regs stores writes to reserved bits of RW registers (the mask `dce7b40:176` had is gone). `config_regs_reserved_bits_findings.json` | The regression that motivated the loop; first candidate for the round-trip test |

The wb_port items in v2 (5 critical) look like one root cause: the request the
port emits does not match the Wishbone transaction the model predicts for
`addr/data/mask/we`; see `wb_port/MISMATCH/req[...]` in `findings_v2.json`
for expected/actual and the anchor.

---

## 3. Spec compiler completeness (C2)

Our intake gate (`python3 Validation/spec/spec_completeness.py --spec <file>`)
reports **the same ten gaps** on the golden spec and on the compiler's
`low-cost-embedded` output (`builds/ddr3_mc_800_x8_1lane_1rank/microarch_spec.json`),
so the compiler is omitting exactly what the hand-written spec omitted. The
full checklist with rationale: `python3 Validation/spec/spec_completeness.py --checklist`
(same text as `Validation/spec/SPEC_COMPLETENESS_CHECKLIST.md`).

**Emit as constants (standard-determined; no decision needed).**

| Field | Value | Source |
|---|---|---|
| `timing_model.tMRD` | 4 nCK, stated in ns (4 × tCK) | JESD79-3 |
| `timing_model.tMOD` | max(12 nCK, 15 ns), stated in ns | JESD79-3 |
| `data_path_mapping.ddr_dm_polarity` | `active_high_mask` | JESD79-3 (DM=1 masks the byte; host `sel` is the inverse) |

**Emit after a one-time decision (you and I pick once; then it is a constant).**

| Field | Options | My proposal |
|---|---|---|
| `csr_register_map.unmapped_read_data` | zero / all_ones / undefined / last_written | `zero` |
| `csr_register_map.unmapped_write_behavior` | ignored_with_error / ignored_silently / error_only | `ignored_with_error` |
| `csr_register_map.read_byte_enable_semantics` | ignored / must_be_full / masks_data | `ignored` |
| `csr_register_map.status_read_sampling` | previous_edge / same_cycle | `previous_edge` (registered design) |

Waiver W-001 has `resolves_when` tied to `unmapped_read_data`; it closes
itself when the field lands.

**Vocabulary (template additions to `failure_taxonomy`).**
- A `SCHED_` family: dropped request, invented command, refresh never
  serviced (our checkers report these under proposed SCHED_001..003).
- One violation id per `timing_model` parameter; today tREFI has none, so the
  refresh-interval assertion reports under a proposed TIMING_012.

**One new field, please.** `phy_interface.commands_per_controller_cycle`
(integer; `1` for this design). We found that at the low-cost preset's 10 ns
controller clock, tRRD/tRTP/tWTR are one cycle, which is satisfied by
construction only because the design issues at most one command per
controller cycle. The generated SVA needs that stated to record the property
as "satisfied by construction" rather than skipping it, and UberDDR3-style
four-slot interfaces need it to compute separation in slots.

**Deferred.** `INTERFACE_CONTRACTS` (a `block_interfaces` section) is real but
belongs with the top-level/connectivity work (C4/C5), not this batch.

---

## 4. `source` on phase-1 manifests (C4)

`Frontend/OutputFolders/PHASE1RTL/{init_fsm,config_regs,wb_port}_manifest.json`
carry zero `source` fields; phase 2–4 manifests carry them. The backend's set
gate and our integration map both key on `source`. When phase 1 has them,
`backend/handoff/connectivity_worksheet.json` empties and we can generate
`integration_map.json` from manifests instead of maintaining 75 edges by hand.

## 5. Drop stamp (C1)

Every manifest (and ideally every report you write) should carry
`{"git_commit": "<sha>", "spec_revision": "<spec.revision>", "generated_utc": ...}`.
We currently recover the commit ourselves (`Validation/structural/rtl_drop.py`);
`introduced_in` / `resolved_in` history is only as trustworthy as that stamp.

---

## Small things

- `Frontend/microarch_cli.py --out <path>` treats the path as a **file** and
  writes `microarch_report.json` next to its parent; `microarch_compiler.py --out`
  treats it as a **directory**. One of them should change; I moved the
  low-cost-embedded output into `builds/ddr3_mc_800_x8_1lane_1rank/` by hand
  to match the other builds.
- When convenient, an RTL drop generated from
  `builds/ddr3_mc_800_x8_1lane_1rank/microarch_spec.json` would let us run
  the seeded-fault suite on a second configuration. Our generators already
  pass on that spec with zero code changes
  (`Validation/reports/spec_swap_low_cost_embedded.json`).

## How to run our side

```
python3 Validation/tools/validate_drop.py            # resolve → intake → regenerate → sim → findings → compare
python3 Validation/tools/validate_drop.py --skip-sim  # re-judge existing traces
python3 Validation/tools/spec_swap_check.py --spec <candidate spec>   # prove generators follow a new spec
python3 Validation/spec/spec_completeness.py --spec <spec> [--findings out.json]
```
