# LVS + DRC for ORFS sky130hd — working configuration

The ORFS-shipped `platforms/sky130hd/lvs/sky130hd.lylvs` has never produced a
valid result here. This directory holds the configuration that does, and the
evidence that it passes good layouts and fails deliberately broken ones.
DRC scripts and evidence are in `../drc/`.

## Result (batch run 2026-09-10, flow image openroad/orfs:latest = 26Q1)

All 11 blocks, produced end to end by `pipeline_batch.py` with the new validator
(sign-off results written 12:24 to 13:03):

| block | LVS | nets / pins compared | black-boxed inst. | audit: pins / feedthroughs | DRC |
|---|---|---|---|---|---|
| addr_decoder | match | 31 / 31 | 0 | 60/60, 25/25 | 0 |
| bank_tracker | match | 4184 / 287 | 4 | 287/287 | 0 |
| calibration | match | 103 / 8 | 0 | 9/9 | 0 |
| cmd_gen | match | 283 / 102 | 0 | 106/106 | 0 |
| cmd_queue | match | 1996 / 595 | 2 | 595/595 | 0 |
| config_regs | match | 1225 / 333 | 0 | 333/333 | 0 |
| data_path | match | 2508 / 173 | 0 | 173/173 | 0 |
| init_fsm | match | 199 / 28 | 1 | 36/36 | 0 |
| refresh_ctrl | match | 222 / 46 | 0 | 46/46 | 0 |
| scheduler | match | 5030 / 753 | 4 | 754/754 | 0 |
| wb_port | match | 537 / 189 | 0 | 221/221, 32/32 | 0 |

Evidence: `evidence_2026-09-10_batch.log`, generated from each block result file.

**Why these numbers differ from the first table made earlier the same day.** That table
was measured by hand on the April 25 layouts. The batch rebuilt every block from unchanged
RTL, and 8 of 11 netlists changed: same flip-flops, different gate mapping (config_regs
went from 1,883 to 1,225 compared nets). During the April runs the repair, tuner and
optimizer steps had written extra settings into config.mk (5 to 13 lines per block; for
example, on 2026-03-31 the Fmax optimizer tightened config_regs from a 10 ns to a 1.912 ns
clock). The packager rewrites config.mk from scratch on every run, so the batch used clean
defaults. Both layout sets passed. The layouts above are current and reproducible from the
code alone; the hand-run evidence for the April layouts is in `evidence_2026-09-10.log`
and `evidence_2026-09-10_cmd_gen_init_fsm.log`. The negative controls below were run on
the April layouts with the same deck and scripts.

cmd_gen and init_fsm were first re-run on 2026-09-10 after the `_normalize_rtl` fix; their
old GDS (built from RTL missing ddr_addr/init_addr) is kept as
`flow/{results,logs,reports}/sky130hd/<block>_stale_0421`.

## Negative controls (every one must FAIL — all do)

| check | mutation | blocks | outcome |
|---|---|---|---|
| LVS | swap a flip-flop's CLK and D | config_regs, cmd_queue, cmd_gen, init_fsm | mismatch |
| LVS | delete one cell | config_regs, cmd_queue, cmd_gen, init_fsm | mismatch |
| LVS | swap inputs on a black-boxed cell | scheduler, cmd_queue | mismatch |
| audit | pair each feedthrough with the wrong partner | addr_decoder, wb_port | 0 accepted |
| DRC | inject 3 illegal met1 shapes into a GDS copy | config_regs | 6 violations (m1.1, m1.2, m1.6) |

## Deck changes (sky130hd_fixed.lylvs vs vendor)

1. `report()` -> `report_lvs()` — vendor deck never wrote an LVS database.
2. `connect(METnPIN, METnTXT)` + `connect(METn, METnPIN)` (n=1..5, LI) — pin labels sit
   on pin-purpose shapes the vendor deck never bound; 268/333 pins were lost.
3. `connect_global(PTAP, "VNB")` — p-taps contact the substrate; without it the
   substrate never joins VSS and every cell's bulk mismatches.
4. `netlist.simplify` -> `make_top_level_pins` + `combine_devices` (no purge) — purge
   deletes pin-only nets (feedthroughs, unused ports) and device-less circuits.
5. `blank_circuit` for a2111oi_2, a211oi_4, o211ai_4, a21oi_2 — SkyWater's GDS for these
   cells has more transistors than its own CDL (split series branches), so they are
   compared by pin connectivity only (11 instances in the 2026-09-10 batch). All other cells: transistor level.

## Reference-netlist prep (prep_reference.py)

OpenROAD's `write_cdl` and KLayout's SPICE reader lose information the layout keeps:
- tap cells removed (no devices); antenna diodes removed (deck has no diode extraction;
  72 instances in the 2026-09-10 batch: bank_tracker 5, cmd_queue 1, config_regs 1, data_path 1, scheduler 64)
- `conb_1` ties: CDL `short` means the nets are joined — instance removed, nets joined
- `assign` feedthroughs dropped by write_cdl — nets joined (pin names preserved)
- library `.SUBCKT`s included only if instantiated, copied verbatim from the vendor CDL

## Known blind spot and how it is covered

KLayout's comparison does not check nets that touch only pins (verified: cutting a
feedthrough still "matches"). `audit_pins.rb` covers it: every schematic pin must exist
as a layout label, and both ends of every pin-to-pin `assign` must share one layout net.

## Limitations to state in any writeup

- 11 cell instances verified at pin level only (vendor GDS/CDL disagree for 4 cells).
- 72 antenna diodes excluded from LVS.
- Block timing in the table above is optimistic: those runs used a constraint.sdc with only
  the clock, so only register-to-register paths were timed. Since 2026-09-10 the packager
  writes ORFS-style input and output delays (20% of the period on every port), so the next
  batch run times port paths too. Checked on cmd_gen: the old file left 87 endpoints and 39
  inputs unconstrained, the new one leaves none.
- addr_decoder has no flip-flops and no clock, so there is nothing to time. Since 2026-09-10
  the pipeline reports its STA as N/A (no timing paths) instead of a PASS.
- DRC/LVS decks are the ORFS-bundled KLayout decks (with the fixes above), not a
  foundry-certified sign-off deck.

## Pipeline integration (2026-09-10)

`agents/pipeline.py` validator_node runs these checks through `signoff/signoff_runner.py`
inside the ORFS container, in the order DRC, then LVS plus pin audit, then STA.

- A check that cannot run (Docker off, deck missing, CDL cannot be generated, results
  stale) returns ERROR and halts the pipeline. Previously such cases reported PASS.
- Outputs per design: `<out_root>/validator/<design>/signoff/` holds signoff_result.json,
  drc.lyrdb, lvs.lvsdb, reference.cdl, extracted.cir and one log per step.
- Pre-change code: `agents/pipeline.py.bak_2026-09-10` (later steps: `*.bak_2026-09-10_*`).
- STA that cannot determine slack halts as NOT VERIFIED (it used to warn and pass), and a
  missing slack value is no longer read as 0 ns. A block with nothing to time reports N/A.
- The Fmax tuner rewrites the period in both SDC styles and warns if it finds none.

Tested 2026-09-10: validator_node gives PASS on cmd_gen, and NOT VERIFIED (halt) with
USE_DOCKER=0 and with a missing design config. The runner matches the manual numbers
on config_regs and addr_decoder, and its self-test (`--mutate swap`) fails LVS as required.

Run the runner alone (from the ORFS flow directory, inside the container):

    python3 /signoff/signoff_runner.py --design <block> --platform sky130hd --out <dir> [--mutate swap|delete]

## Upstream

Deck items 1–3 would break LVS for any ORFS sky130hd design; worth reporting to ORFS.

## Full-chip sign-off (2026-09-16)

The integration scaffold `ddr3_controller` (11 blocks flattened, generated by
`integration/generate_top.py`) went through the same pipeline as a leaf block and
signed off clean:

    DRC   PASS  0 violations                     315 s KLayout
    LVS   PASS  match, 13528 nets / 556 pins      59 s
    audit PASS  601/601 pins in layout, 32/32 pin-to-pin feedthroughs
    STA   PASS  WNS +1.70 ns, TNS 0, hold +0.44 ns

Layout: die 801,338 um2 (0.90 x 0.90 mm), 23,587 std cells, 23.9% utilization,
0 routing violations, 50.7 mW, Fmax 120.5 MHz. GDS 25,491,450 bytes.

Reference netlist prep on the full chip: 10,174 taps, 51 diodes, 13 tie cells,
32 feedthroughs, 7 pin aliases, 144 library cells, no missing definitions.

Black-boxed in LVS are layout-only cells with no schematic counterpart: VIA arrays,
`__fill_*`, `__tapvpwrvgnd_1`, `__diode_2` and `__conb_1`. These carry no device-level
connectivity to compare, so flattening them is correct, not a skipped check.

This is an integration scaffold, not a functionally complete controller: it wires the
50 connections the frontend declared and promotes the remaining 111 signals to chip
pins. It is structurally a real chip; `calibration` and `data_path` still drive nothing
internally until the frontend backfills the `source` fields.

## Stale-artifact failure and the two provenance checks (2026-09-17)

A full 11-block batch run exposed a bug in the backend, not in the decks.

**What happened.** ORFS make died at `3_1_place_gp_skip_io` with
`mv: cannot stat .../3_1_place_gp_skip_io.tmp.log` — a filesystem race on the Docker
bind mount under 11 parallel containers. The flow still rewrote `6_final.odb`,
`6_final.def` and `6_final.v`, but the GDS merge never ran, so `6_final.gds` stayed at
its 2026-09-10 version. The runner then hit this:

    [runner] GDS exists despite exit_code=2 - treating as success.

Existence was being read as proof of completion. DRC and LVS went on to certify
week-old geometry for 10 of 11 blocks, reporting 8 PASS. Only `addr_decoder`, which
finished early enough to avoid the race, exited 0 and produced a current layout.
The same staleness explains why WNS was unchanged from the previous batch: the final
timing report is generated from `6_final.sdc`, also left at its pre-I/O-delay version.

Three blocks (`bank_tracker`, `data_path`, `scheduler`) failed instead of passing,
because CDL generation tried to rebuild the missing upstream steps and exceeded the
900 s sign-off timeout. The halt gate refused to certify what it could not rebuild —
working as designed.

**Fix 1, runner provenance** (`agents/pipeline.py`, backup `.bak_2026-09-17_runner`).
A non-zero make exit is still allowed to be overridden by a finished GDS, because ORFS
does exit non-zero on late cosmetic failures. But the GDS must be one *this run* wrote.
`_gds_is_from_this_run` applies two independent tests: the GDS must not predate the
moment make launched (host clock), and must not be older than `6_final.def` (same-run
consistency, immune to host/container clock skew). A legitimate override is recorded in
`runner_result["gds_exit_override"]` so it is never indistinguishable from a clean run.

**Fix 2, sign-off provenance** (`signoff/signoff_runner.py`, backup `.bak_2026-09-17`).
`assert_gds_is_current` runs before any check. ORFS writes the final artifacts in a fixed
order with the merged GDS last (`6_final.odb -> .def -> .v -> .gds`), so in a complete run
the GDS is the newest of the four. If any of the others is newer, the merge did not run
and sign-off halts. This is independent of the runner, so a stale layout cannot be
certified regardless of what invoked the flow.

The two checks cover different faults: the runner catches a layout left over from an
earlier run; the sign-off check catches a layout inconsistent with the netlist beside it.
A block whose whole artifact set is old but self-consistent is correctly still signable.

**Verified** on the real files: the three blocks rebuilt at low parallelism are accepted,
`cmd_gen`, `config_regs` and `wb_port` (stale GDS, fresh netlist) are halted, and the
DEF-consistency test still catches all three with the clock test disabled.

**Operational note.** Run the batch at reduced parallelism. `--max_workers 2` completed
the GDS merge cleanly on all three large blocks; the default of one worker per block
(11 here) triggered the race.

## Result (batch run 2026-09-17) — current code, all layouts rebuilt

The first batch in which every block was built and verified by the same run, with the
runner and sign-off provenance checks both active. All 11 pass.

| block | LVS | nets / pins | black-boxed | audit: pins / feedthroughs | DRC | STA |
|---|---|---|---|---|---|---|
| addr_decoder | match | 31 / 31 | 0 | 60/60, 25/25 | 0 | N/A n/a (no timing paths) |
| bank_tracker | match | 4192 / 287 | 4 | 287/287 | 0 | PASS 3.683 ns |
| calibration | match | 104 / 8 | 0 | 9/9 | 0 | PASS 6.508 ns |
| cmd_gen | match | 282 / 102 | 0 | 106/106 | 0 | PASS 6.363 ns |
| cmd_queue | match | 1995 / 595 | 2 | 595/595 | 0 | PASS 5.424 ns |
| config_regs | match | 1229 / 333 | 0 | 333/333 | 0 | PASS 5.211 ns |
| data_path | match | 2493 / 173 | 0 | 173/173 | 0 | PASS 3.442 ns |
| init_fsm | match | 198 / 28 | 1 | 36/36 | 0 | PASS 5.799 ns |
| refresh_ctrl | match | 222 / 46 | 0 | 46/46 | 0 | PASS 4.252 ns |
| scheduler | match | 5094 / 753 | 4 | 754/754 | 0 | PASS 0.886 ns |
| wb_port | match | 537 / 189 | 0 | 221/221, 32/32 | 0 | PASS 4.136 ns |

Evidence: `evidence_2026-09-17_batch.log`. Machine-readable results for every block are
committed under `signoff/results/<block>.json` — these are the files the table is
generated from, not a transcription of them.

Timing in this table is the first to include port paths (the packager now writes input
and output delays at 20% of the period). Earlier runs timed only register-to-register
paths, so WNS and Fmax in the 2026-09-10 table above were optimistic: scheduler, for
example, reported 1072 MHz then and 110 MHz here. The DRC, LVS and audit columns are
unaffected by that change.
