# Top-Level Module — What the Backend Needs

Backend → Frontend, 2026-09-24. Supersedes the connectivity sections of
`FRONTEND_REQUEST_2026-09-24.md` now that the frontend owns the top level.

---

## The short version

You own `ddr3_controller`. Send it as a **bundle**: one `.sv` that instantiates the 11
blocks, plus a manifest with `"kind": "top"` listing every source file. The backend
synthesises and signs off whatever you send, unmodified.

**This makes your job smaller, not bigger.** Read §5 before you spend time on the
111-slot connectivity worksheet — most of it stops mattering once you own the top.

A complete, working example of the exact format is already in the repo:

    backend/integration/ddr3_controller/ddr3_controller.sv
    backend/integration/ddr3_controller/manifest.json

That scaffold has been built and signed off end to end — 0.90 × 0.90 mm, 23,587 cells,
DRC clean, LVS match, timing met. Copy its shape and it will work.

---

## 1. The RTL file

A single SystemVerilog file declaring `module ddr3_controller`, instantiating all 11
blocks, and wiring them. Requirements:

- **Module name must be `ddr3_controller`** and must match `module_name` in the manifest.
- **Instantiate all 11 blocks**: `addr_decoder`, `bank_tracker`, `calibration`, `cmd_gen`,
  `cmd_queue`, `config_regs`, `data_path`, `init_fsm`, `refresh_ctrl`, `scheduler`,
  `wb_port`. Block module names must match their manifests exactly.
- **Use named port connections** (`.clk(clk)`), not positional. Positional connections
  are a silent-miswire risk and the backend cannot catch them.
- **Declare internal wires explicitly.** Implicit nets are an error under the synthesis
  frontend we use.
- **Ports on the top module are chip pins.** Anything you expose becomes physical I/O.
- **Drive every input.** An undriven input synthesises to a constant or a floating net
  and will show up as a timing or LVS surprise, not a clean error.

Synthesis is Yosys with the `slang` SystemVerilog frontend, so full SV elaboration is
available — packed and unpacked arrays, structs, parameters, generate blocks. If you use
something it rejects, send it anyway and the backend will report the exact error.

## 2. The manifest

Same schema as a block manifest (`backend/schema/manifest.schema.json`), with two
differences: `kind` is `"top"`, and `file` is a **list**.

```json
{
  "module_name": "ddr3_controller",
  "kind": "top",
  "file": [
    "ddr3_controller.sv",
    "addr_decoder.sv",
    "bank_tracker.sv",
    "calibration.sv",
    "cmd_gen.sv",
    "cmd_queue.sv",
    "config_regs.sv",
    "data_path.sv",
    "init_fsm.sv",
    "refresh_ctrl.sv",
    "scheduler.sv",
    "wb_port.sv"
  ],
  "dependencies": ["addr_decoder", "bank_tracker", "..."],
  "parameters": {},
  "clock_period_ns": 10.0,
  "ports": {
    "clock_reset": [
      { "name": "clk",   "width": 1, "dir": "input" },
      { "name": "rst_n", "width": 1, "dir": "input" }
    ],
    "external_in":  [ { "name": "wb_adr_i", "width": 32, "dir": "input"  } ],
    "external_out": [ { "name": "ddr_addr", "width": 15, "dir": "output" } ]
  }
}
```

Rules that matter:

- **`file` order is passed to the synthesiser unchanged.** Put the top first.
- **Paths are relative to the bundle directory.** Ship the block `.sv` files alongside the
  top, or use relative paths as the scaffold does.
- **Every filename must be unique.** They are all copied into one directory; duplicate
  basenames are rejected (error `IO-011`).
- **Exactly one bundle in the set may be `"kind": "top"`** (error `SET-020`).
- **`ports` must list every port on the top module**, grouped however you like. Group names
  are free-form; only `clock_reset` is special, and the backend reads it to find the clock.
- **Widths**: an integer for a packed port, or `"NxM"` for an unpacked array of N entries
  of M bits.

## 3. What the backend does with it

1. **Intake** validates the manifest against the schema and cross-checks it against the RTL
   — that every listed file exists, that `module_name` is declared in one of them, and that
   the manifest port list matches the RTL port declarations.
2. **Packager** writes the ORFS config and the SDC, and copies the sources.
3. **Runner** executes synthesis → floorplan → placement → CTS → routing → GDSII.
4. **Sign-off** runs DRC, LVS, a pin audit and static timing, and halts rather than
   reporting a pass if any of them cannot run.

Anything that fails comes back as a structured finding with a code, an owner, and a
suggested fix. You will get told exactly which port on which module, not "synthesis
failed".

## 4. `clock_period_ns` — please include it

Missing on all 11 block manifests today, and on nothing else does the backend have to
invent a number. Without it we default to **10.0 ns (100 MHz)** and raise warning `OR-003`.

That means **every timing result we have reported is against a target we chose, not one
the spec requires.** The full chip currently makes 120 MHz and the tightest block has
0.89 ns of slack — but those numbers are only meaningful if 10 ns is actually the goal.

One number per manifest. If the spec states a target frequency, that is the value. If
blocks are meant to run at different rates, say so, because that is a multi-clock design
and it changes the constraints substantially.

## 5. What this means for the connectivity worksheet

**Most of it stops mattering.** The 111 open slots in
`connectivity_worksheet_2026-09-24.json` existed so the backend could *infer* the wiring
and generate the top itself. If you write the top, the wiring is in your RTL and the
backend reads it directly.

What we still want, and why:

- **`ports` on every block manifest** — still required. Intake cross-checks it against the
  RTL, which is what catches a port renamed in one place and not the other.
- **`source` fields** — now advisory rather than required. They are still valuable as a
  machine-readable statement of intent: the backend can compare what your manifests *say*
  is connected against what your top-level RTL actually wires, and flag disagreements. That
  is a real check that nothing else in the project performs. But it is no longer blocking.
- **`dependencies`** — keep it consistent with the sources if you keep the sources. Two
  blocks currently disagree (`cmd_gen` lists `bank_tracker` but takes nothing from it;
  `refresh_ctrl` takes from `init_fsm` without listing it).

So: **top-level RTL first, worksheet second.** If time is short, the worksheet can wait.

## 6. Three specific things in the current RTL

**`addr_decoder` has no `clock_reset` port group.** Every other block has one. It may
genuinely be combinational — it has no flip-flops — in which case nothing needs to change,
but please confirm, because the backend currently cannot distinguish "no clock" from
"clock not declared".

**Three connections look missing** — same port name, right direction, no `source`:

| input | probable driver |
|---|---|
| `cmd_queue.deq_grant` | `scheduler.deq_grant` |
| `cmd_queue.deq_idx` | `scheduler.deq_idx` |
| `refresh_ctrl.ref_ack` | `scheduler.ref_ack` |

If your top-level RTL wires these, ignore this. If it does not, they are probably bugs.

**Findings from the April RTL, not yet re-checked against Frontend2.** These were real
then; they may or may not have survived regeneration:

- `refresh_ctrl` truncates the 24-bit `cfg_tREFI_nCK` to 13 bits
- `data_path` never reads `ddr_dqs_i`
- `calibration.cal_fail` is hardwired to 0
- `wb_port` uses `rsp_aux` only inside an assertion, and ignores `wb_bte_i`
- `config_regs` never reads `csr_sel_i`, `sts_ecc_ce_count`, `sts_bist_fail_addr`
- `cmd_gen.sched_we` is unused

## 7. Things that will cause trouble, worth knowing in advance

- **No `inout` ports currently exist anywhere.** The DDR3 data bus is modelled as separate
  in and out ports. If the top level introduces true bidirectional pads, tell us — it
  changes how the backend handles I/O and it is not currently exercised.
- **Avoid a top level that needs logic of its own** where you can. Muxes, arbiters and
  width adapters at the top are fine in RTL, but they are design decisions the backend
  cannot check for intent, so keep them deliberate and documented.
- **Tie-offs**: if an input is meant to sit at a constant, write it explicitly
  (`.foo(1'b0)`). Leaving it unconnected is not the same thing and will not be caught.
- **Yosys FSM extraction does not terminate** on the flattened 11-block design — it ran
  over 30 minutes at full CPU with no progress, though each block alone passes in seconds.
  The backend works around this with `"orfs_config": {"SYNTH_ARGS": "-nofsm"}` in the
  manifest. Include that in your top-level manifest or the run will hang.

## 8. How to check your work before sending

The validator is in the repo and runs in seconds, no Docker or toolchain needed:

    python backend/schema/validate_bundles.py --bundles_root <your bundle dir> --worksheet ws.json

It reports schema errors, width mismatches across connections, unresolved sources,
duplicate module names, and connectivity coverage. Exit code is non-zero on error. If it
passes, intake on our side will almost certainly pass too.

---

## Backend status, for context

All 11 blocks and a full-chip assembly currently sign off clean: DRC 0 violations, LVS
match, pin audit complete, timing met. That is against the April RTL, so it demonstrates
the flow rather than describing the current design. Re-baselining on Frontend2 takes about
an hour and is not a bottleneck.

Send the top-level bundle whenever it is ready, even if it is incomplete or you expect it
to fail — an early failure with a specific error code is more useful to both of us than a
late success.
