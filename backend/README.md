# DDR3 Controller — Backend (RTL to signed-off GDSII)

Takes an RTL bundle from the frontend and returns a placed, routed, verified layout:
synthesis through GDSII on OpenROAD-flow-scripts (sky130hd), then DRC, LVS, a pin audit
and static timing. A check that cannot run halts the pipeline instead of reporting PASS.

Owner: Dawson Carpenter. Subsystem of the ECEN 403 agentic memory-controller project.

## Status (2026-09-17)

All 11 blocks and the full-chip integration scaffold pass every check:

| | DRC | LVS | pin audit | STA |
|---|---|---|---|---|
| 11 blocks | 0 violations | match | all pins, all feedthroughs | pass (worst +0.89 ns, scheduler) |
| ddr3_controller | 0 violations | match, 13528 nets / 556 pins | 601/601 pins | pass, +1.70 ns |

Full-chip layout: 0.90 x 0.90 mm, 23,587 cells, 0 routing violations, 50.7 mW,
Fmax 120.5 MHz. Images in `integration/images/`.

`ddr3_controller` is an **integration scaffold**, not a functionally complete controller.
It wires the 50 connections the frontend declared in the block manifests and promotes the
remaining 111 signals to chip pins, so it builds and signs off as a real chip, but
`calibration` and `data_path` still drive nothing internally. It gets wired properly when
the frontend backfills the `source` fields — see `handoff/connectivity_worksheet.json`.

## Layout

    agents/        pipeline (LangGraph): intake -> packager -> runner -> reporter -> validator
    bundles/       one directory per block: RTL + manifest, as received from the frontend
    schema/        manifest.schema.json — the frontend/backend contract, plus its validator
    signoff/       DRC and LVS decks, scripts, negative controls, evidence logs, results
    integration/   top-level generator, generated scaffold, rendered layout images
    handoff/       what the frontend still owes (connectivity, name gaps)
    BAD_BLOCKS/    deliberately broken bundles used to prove intake rejects them

## Running it

Needs Docker and the ORFS image `openroad/orfs:latest`. Copy `env.template` to
`agents/.env` and set `ORFS_DIR` and `ANTHROPIC_API_KEY`. The `.env` is gitignored and
must stay that way — this repository is public.

    cd agents
    python pipeline.py --bundle_dir ../bundles/cmd_gen        # one block
    python pipeline_batch.py --max_workers 2                  # all 11

**Use `--max_workers 2`.** The default of one worker per block triggers a filesystem race
on the Docker bind mount that kills the GDS merge; see the README in `signoff/lvs/`.

Generated output lands in `pipeline_out/` and in the ORFS tree, both gitignored. Rebuild
rather than expecting layouts in the repo; the committed evidence records every result.

## Verification

The LVS deck shipped with ORFS never produced a valid result here. `signoff/lvs/README.md`
documents the four defects, the fixes, and the negative controls that prove each check can
fail — a swapped flip-flop clock, a deleted cell, a mispaired feedthrough and injected
illegal geometry all have to be caught, and are. It also covers a blind spot in KLayout
itself (nets touching only pins are never compared) and the pin auditor written to close it.

Evidence lives in `signoff/lvs/evidence_*.log` and `signoff/drc/`, with the raw per-block
results in `signoff/results/<block>.json`.

## Known limitations

- 11 cell instances are verified at pin level only; SkyWater's GDS and CDL disagree for
  four cells.
- 72 antenna diodes are excluded from LVS.
- These are the ORFS-bundled KLayout decks with the fixes above, not a foundry-certified
  sign-off deck.
- Six RTL issues found while packaging are listed in `handoff/` and still owed to the
  frontend, including a 24-bit refresh interval truncated to 13 bits.
