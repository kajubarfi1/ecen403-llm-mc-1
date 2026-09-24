# Validation Integration Plan

Diagnosis of Jacob's handoff (`Validation/findings/HANDOFF_FRONTEND_2026-09-24.md`)
against `Frontend2`, plus the fixes that came out of it. Started as diagnosis-only;
items 1-5 below (manifest stamps/source, both scheduler bugs, the data_path DQ-width
redesign, and config_regs reserved-bit masking) have since been **implemented and
real-verified** against Olympus (Verilator lint + Cadence Xcelium sim, all 11 modules,
0 errors, 0 test failures). Items still open are marked accordingly.

One scoping note that still applies: several of Jacob's file paths point at `Frontend/`
(the original, partly-LLM-driven pipeline), not `Frontend2` (this rebuild). Where the
underlying defect is in shared logic it applies to both; where it's specific to the
LLM-agent retry mechanism, it does not apply to `Frontend2` as designed.

## Status summary

| # | Item | Status |
|---|---|---|
| §5 | Drop stamp on every manifest (C1) | ✅ DONE |
| §4 | `source` on phase-1 manifests (C4) | ✅ DONE |
| Defect 1 | Scheduler regrant during dequeue window | ✅ DONE |
| Defect 5 | REFRESH issued while banks active | ✅ DONE |
| Defect 2 | data_path DQ/channel width | ✅ DONE |
| Defect 8 | config_regs reserved-bit write masking | ✅ DONE |
| Defect 6 | cmd_gen bank feedback | Already correct, confirmed by inspection |
| §1 | Consume `retry_instructions.json` | Deferred — blocked on Feedback Agent (unbuilt) |
| §3 | Spec compiler completeness (C2) | Deferred — not a `Frontend2`/RTL issue |
| — | data_path write overflow, duplicate reads, wb_port req mismatches, ZQCS consumer | Not independently re-verified; re-run `validate_drop.py` for a fresh list before diagnosing |

---

## §5 — Drop stamp on every manifest (C1) ✅ DONE

Built `Frontend2/scripts/manifest_stamp.py`: a `stamp(spec)` helper returning
`{"git_commit", "spec_revision", "generated_utc"}` (commit via `git rev-parse HEAD`,
revision from the spec's own `revision` field, timestamp via UTC `isoformat()`). Wired
into all 11 generators' `generate_manifest()` via `**stamp(self.spec)` — each generator
inserts its own parent directory onto `sys.path` to reach the shared helper regardless
of whether it's imported via a pipeline or run standalone.

Real-verified: every one of the 11 regenerated manifests carries a live commit hash and
the golden spec's `revision` (`golden_ddr3_1600k_x8_2lane_1rank`).

## §4 — `source` on phase-1 manifests (C4) ✅ DONE

Added `source` annotations to `Phase1/{config_regs,wb_port}_gen.py`'s manifests for
every port with a real, currently-implemented Frontend2 producer:
- `config_regs`: `sts_init_done`←`init_fsm.init_done`, `sts_cal_done`←`calibration.cal_done`,
  `sts_cal_fail`←`calibration.cal_fail`, `sts_ref_pending_cnt`←`refresh_ctrl.ref_pending_cnt`,
  `sts_ref_starve_event`←`refresh_ctrl.ref_starve_flag`, `sts_init_fail_event`←`init_fsm.init_fail`.
- `wb_port`: `req_ready`←`cmd_queue.enq_ready`, `rsp_valid`/`rsp_rdata`/`rsp_aux`←
  `data_path.rd_rsp_valid`/`rd_rsp_data`/`rd_rsp_aux`.

Left unsourced (correctly): `sts_bist_done`/`sts_bist_fail`/`sts_bist_fail_addr`,
`sts_self_refresh_active`, `sts_ecc_ce_count`/`sts_ecc_ue_event` — no Frontend2 generator
implements BIST, self-refresh, or ECC logic yet, so there's no real producer to name.
`init_fsm.enable` also stays unsourced — nothing in Frontend2 currently drives it (a
top-level/integration-time signal). Don't guess a producer that doesn't exist yet.

---

## §2 — Open RTL defects

### Defect 1 — Scheduler re-selects a granted slot during the dequeue window ✅ DONE

**Fix.** Added a same-cycle "just granted" guard in `scheduler.sv`'s candidate
classification: `recently_granted = deq_grant && (deq_idx == i)` (both scheduler's own
registered outputs from the prior cycle), ANDed into `is_cas_ready[i]`. This blocks the
just-dequeued entry from being reselected for exactly the cycle where `cmd_queue` hasn't
yet reflected the dequeue, without touching `cmd_queue`'s own timing.

**A real second bug surfaced by this fix, also fixed.** With the guard in place, a
single-entry grant becomes a genuine one-cycle pulse (correct — nothing else remains to
select the next cycle). Several *existing* tests (T06-08, T21/23, T25) had been checking
a fixed `wc(2)`-cycle delay, written against the old (buggy) behavior where an
unguarded grant could stay asserted indefinitely. Real Xcelium caught this immediately
(8 tests failed on the first re-run). Fixed by switching those tests to a polling task
(`wait_cmd`, waits for the next `cmd_valid` pulse and captures its fields — same
"poll, don't hand-count cycles" pattern used earlier this session for data_path's
read-response checks) instead of a fixed-delay direct check.

Real-verified: scheduler 37/37 (was 32; +2 for a new dedicated regrant-guard test).

### Defect 5 — REFRESH issued while banks have open rows ✅ DONE

**Fix.** Added `wire all_banks_idle = ~(|bank_is_active);` (bank_is_active was already
an existing scheduler input — no new port needed). Both REF-selecting priority branches
(urgent and normal) now check it: if idle, issue `REF` as before; if not, force-precharge
the lowest-numbered active + precharge-ready bank instead (a new `CMD_PRE` path, distinct
from the existing row-miss-driven PRE since it isn't tied to any queue entry — carries
only a bank, via new `sel_from_queue`/`sel_bank` signals threaded into the
output-registration stage). Never issues a raw un-gated REF while any bank is active.

Added 4 new tests (`RefBlock`) directly exercising this: urgent refresh with an active
bank produces PRE targeting that bank (not REF), and REF only fires once the bank
reports idle. Also had to fix the *existing* T17-18 (`UrgRef`) test, which had
originally been asserting the old buggy behavior (REF immediately despite an active
bank) — simplified it back to a clean idle-banks sanity check, since the active-bank
case is now covered properly by the new tests.

### Defect 2 — `ddr_dq_o`/`ddr_dq_i` pin width ✅ DONE

**Root cause, more precisely than originally diagnosed.** Two bugs stacked: (1) the
generator read a field named `dq_width_bits`, which doesn't exist anywhere in the spec
schema — the real field is `data_path_mapping.ddr_channel_width_bits` (16 for this
spec's x8/2-lane config) — so `DQ_WIDTH` always silently fell back to a hardcoded
default (8); (2) even so, the port declarations were hardcoded to `[DATA_WIDTH-1:0]`
(32 bits) regardless of the `DQ_WIDTH` parameter's value, so the parameter was never
actually connected to anything.

**Fix.** Read the real field (`ddr_channel_width_bits`, with a geometry-derived
fallback: `device_width_bits × byte_lanes`). Ports now correctly `[DQ_WIDTH-1:0]`.
Introduced a new, conceptually distinct parameter `WORD_BEATS = DATA_WIDTH / DQ_WIDTH`
(2 for this spec) — deliberately *not* reusing `BURST_CTRL_CYC` (which encodes an
unrelated fact: BL8 length vs. clock ratio, and only numerically coincided with the
packing ratio for this one spec). Rewrote the write-drive FSM to drive the correct
`DQ_WIDTH`-wide half of the host word each beat (low half first, `pack_32_to_16`,
little-endian) with a matching per-beat data-mask slice, and the read-capture FSM to
shift-assemble `WORD_BEATS` channel-width captures into one real host word before
pushing exactly one FIFO entry per word (previously it pushed one entry per beat, each
only half-real — this is very likely what showed up downstream as duplicate/X-valued
read responses in Jacob's system-level checks).

Also rewrote the previously-trivial Section B (write) and F (DM) testbench checks —
`check("...", 1)` placeholders — into real per-beat verification, using a small
monitor (`wr_beat_q`/`dm_beat_q`, populated via `always @(posedge clk) if(ddr_dq_oe)`)
that captures every driven beat for inspection, rather than trying to hand-time which
exact cycle to sample.

Real-verified: data_path 29/29 (was 26; new real per-beat write/DM checks), lint clean
(2 harmless UNUSED warnings on `rd_shift_r`'s upper bits, only needed for `WORD_BEATS >
2`, and `ddr_dqs_i`, unmodeled PHY signal — same class as other already-accepted
harmless warnings in this codebase).

### Defect 8 — config_regs reserved-bit write masking ✅ DONE

**Root cause, more precisely.** Every register in the spec's `csr_register_map` already
declares its unused bit positions as an explicit field literally named `"reserved"` —
the original fix attempt (treating "bits not covered by any field" as reserved) computed
an all-zero mask for every register, since the reserved bits *are* covered by a field,
just one named `"reserved"`. Fixed by specifically excluding fields named `"reserved"`
(case-insensitive) from the writable-bits set, in addition to any genuine gap bits.

**Fix.** `_derive_parameters()` now computes a per-register `reserved_mask`. Applied on
write for every plain RW register and for `CTRL_CONFIG` (the one register with its own
bespoke write path, for the self-clearing WO bits): `reg <= (csr_dat_i & ~mask) | (reg &
mask)`, pinning reserved bits at whatever they held (their reset value, since nothing
else ever writes them). Verified masks: `CTRL_CONFIG` 0xFFFFFF00, `REFRESH_CONFIG`
0xFFFFFE00, `BIST_CONFIG` 0xFFFFFFF0, `BIST_ADDR_START`/`BIST_ADDR_END` 0xE0000000; the
four `TIMING_*` registers and `ERROR_STATUS` are fully bit-packed (mask 0, no reserved
positions) — correctly computed as no-ops for those.

Added a new Section J to the testbench: writes `0xFFFFFFFF` to every register with a
non-zero reserved mask, checks the reserved bits read back at their reset value while
the writable bits took the write.

Real-verified: config_regs 41/41 (was 36; +5 new reserved-bit tests, one per affected
register).

### Defect 6 — cmd_gen bank feedback
**Status: confirmed already correct**, via direct read of `Phase3/cmd_gen_gen.py` — its
`fb_pre_bank`/`fb_rd_bank`/`fb_wr_bank` are correctly assigned `sched_bank` in the
`SCMD_PRE`/`SCMD_RD`/`SCMD_WR` case branches. No fix needed. This module was rewritten
earlier this session (the `issue()` task off-by-one fix, see `IMPLEMENTATION_PLAN.md`'s
Phase 3 section) — plausible this finding predates that pass. Recommend re-running
`Validation/tools/validate_drop.py` to confirm it auto-closes rather than assuming.

### Not independently re-verified — unchanged from the original diagnosis pass
- **data_path write overflow / duplicate read responses** — the FIFO-per-beat root
  cause for duplicate reads was fixed as part of Defect 2 above; worth re-running
  Jacob's checkers now before assuming either finding is still open.
- **wb_port `req[...]` mismatches** — Jacob's own update said `DATA_001` already
  auto-closed; get a fresh count before diagnosing further.
- **calibration / ZQCS unconsumed** — still not a per-module bug. No top-level
  integration exists yet (`IMPLEMENTATION_PLAN.md` Step 4) — every module is tested in
  isolation, so *no* inter-module signal has a consumer right now. Closes itself once
  Step 4 is built.

---

## §1 — Consume `retry_instructions.json` on retry (C3)
**Status: unchanged — deferred, not a bug.** See original reasoning: `Frontend2` has no
retry loop by design (deterministic generators reproduce the same output on the same
input), so this is blocked on the not-yet-built Feedback Agent, not something to fix in
the generators themselves.

## §3 — Spec compiler completeness (C2)
**Status: unchanged — not a `Frontend2` issue.** Belongs to `microarch_compiler.py` /
the spec synthesis track. Two of the four fields are pure JEDEC constants; the other two
need a one-time decision with Jacob (his proposed defaults look reasonable).
