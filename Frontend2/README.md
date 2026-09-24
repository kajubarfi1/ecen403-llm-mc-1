# Frontend2

Deterministic RTL-generation pipelines for the DDR3 memory controller, verified against
real Verilator lint and real Cadence Xcelium simulation on TAMU Olympus — no LLM calls,
no retry loops. This is a from-scratch rebuild of `Frontend/`, the original pipeline.

## Why this exists

`Frontend/` generated RTL for 11 controller modules across 4 phases. Of those, 4 modules
(`init_fsm`, `config_regs`, `bank_tracker`, `refresh_ctrl`) called an LLM (Claude) to
assemble the RTL. Looking closely at those 4 agents' own prompts, each one already
contained a "HARD NAMING CONTRACT" — every port name, parameter value, localparam, and
often entire code blocks marked "copy verbatim" — computed in Python and simply handed
to the model as text. There was no actual design decision left for an LLM to make; it
was pure template assembly. `Frontend2` converts every module to a deterministic Python
script instead. The only piece that should ever be LLM-backed is a not-yet-built
"Feedback Agent" that will read a validation failure and patch the specific generator
function responsible — patching code from a diagnostic is a real judgment call; template
assembly from a fixed contract is not.

Because nothing here is LLM-driven, there is **no retry loop** anywhere. A deterministic
script given the same spec produces byte-identical output every time, so retrying it
against a validation failure would just reproduce the identical failure. Every pipeline
routes a failure straight to a labeled terminal node (`generation_failure` /
`lint_failure` / `sim_failure`) with a human-readable report instead.

Full design rationale and build history: [`IMPLEMENTATION_PLAN.md`](IMPLEMENTATION_PLAN.md).

## Architecture

All 4 phases follow the same shape:

```
[N parallel RTL generation scripts, all deterministic]
        |
        v
  generation check  ── failure ──> generation_failure (terminal)
        |
        v
  lint_gate (real Verilator --lint-only, via SSH/Slurm on Olympus)
        |
        ├── FAIL ──> lint_failure (terminal)
        v
  sim_gate (real Cadence Xcelium simulation, via SSH/Slurm on Olympus)
        |
        ├── FAIL ──> sim_failure (terminal)
        v
     success (terminal)
```

Each phase is a [LangGraph](https://langchain-ai.github.io/langgraph/) `StateGraph`.
Every failure node writes a `phaseN_error_report.json`; every success writes a
`phaseN_final_report.json`. Nothing retries — a failure means a real bug in a
generator, a testbench, or the spec, and needs a human to fix it and re-run.

### Modules per phase

| Phase | Modules | Own testbench, or shared `tb_generator.py`? |
|---|---|---|
| 1 | `init_fsm`, `config_regs`, `wb_port` | Shared `Phase1/tb_generator.py` (spec-only) |
| 2 | `addr_decoder`, `calibration`, `refresh_ctrl`, `bank_tracker` | Shared `Phase2/tb_generator.py` (spec-only) |
| 3 | `cmd_queue`, `scheduler`, `cmd_gen` | Each generator writes its own via `generate_tb()` |
| 4 | `data_path` | Its own generator writes its own via `generate_testbench()` |

A "spec-only" testbench generator reads *only* the microarchitecture spec JSON — never
the RTL it's checking. This is deliberate: a testbench that derives its expected values
by reading the RTL it's supposed to verify can rubber-stamp a wrong value the generator
computed, since both sides agree by construction. Phases 3 and 4 don't need a shared
generator because each module's own script already owns its testbench end to end, and
nothing else writes to that same output path (no race).

### Repo layout

```
Frontend2/
├── README.md                      (this file)
├── IMPLEMENTATION_PLAN.md          full build history, design decisions, bugs found+fixed
├── scripts/
│   ├── full_pipeline.py            <- run this: chains all 4 phases with checkpoints
│   ├── simulator.py                XceliumSimulator: SSH+Slurm -> real Cadence Xcelium
│   ├── verilator_lint.py           VerilatorLint: SSH+Slurm -> real Verilator --lint-only
│   ├── Phase1/
│   │   ├── init_fsm_gen.py
│   │   ├── config_regs_gen.py
│   │   ├── wb_port_gen.py
│   │   ├── tb_generator.py
│   │   └── phase1_pipeline.py
│   ├── Phase2/  (addr_decoder_gen.py, calibration_gen.py, refresh_ctrl_gen.py,
│   │             bank_tracker_gen.py, tb_generator.py, phase2_pipeline.py)
│   ├── Phase3/  (cmd_queue_gen.py, scheduler_gen.py, cmd_gen_gen.py, phase3_pipeline.py)
│   └── Phase4/  (data_path_gen.py, phase4_pipeline.py)
└── OutputFolders/                  default output location (generated, not committed)
    ├── PHASE1RTL/   .sv + _tb.sv + _manifest.json per module
    ├── PHASE2RTL/
    ├── PHASE3RTL/
    ├── PHASE4RTL/
    └── VALIDATIONREPORT/           lint + sim + final/error reports for every phase
```

## Required materials

1. **Python with `langgraph` and `paramiko` installed.** On this machine that's
   Anaconda's interpreter, **not** the project's own `Frontend/.venv`:
   ```
   /Users/lehanar/opt/anaconda3/bin/python3
   ```
   (`uv run` or a bare `python3` on `PATH` may resolve to an environment missing one or
   both of these packages — check with `python3 -c "import langgraph, paramiko"` before
   assuming it'll work.)

2. **SSH access to TAMU Olympus** (`olympus.ece.tamu.edu`), where real Verilator and
   real Cadence Xcelium actually run (via Slurm — neither tool is available locally or
   on the Olympus head node directly). An **ed25519 key with no passphrase**:
   ```bash
   ssh-keygen -t ed25519 -f ~/.ssh/id_ed25519_olympus2 -N ""
   ssh-copy-id -i ~/.ssh/id_ed25519_olympus2 <your_netid>@olympus.ece.tamu.edu
   ```
   A passphrase-protected key will fail — nothing here can type a passphrase
   interactively.

3. **Two environment variables**, set before running anything:
   ```bash
   export OLYMPUS_USER=<your_netid>
   export OLYMPUS_KEY=~/.ssh/id_ed25519_olympus2
   ```
   Put these in `~/.zshrc` (or equivalent) so new terminals pick them up automatically.

4. **A filled microarchitecture spec JSON** — e.g.
   `Spec/llmmc_microarchitecturespec_filled.json` — matching
   `Spec/llmmc_microarchitecture.schema.json`. Every generator and testbench derives its
   parameters purely from this file; nothing here has an implicit default spec.

5. **No `ANTHROPIC_API_KEY` needed.** Everything in `Frontend2` is deterministic — this
   is only relevant if you're also touching `Frontend/`'s original LLM-driven agents.

## Usage

### Option A — run everything (recommended)

`full_pipeline.py` prompts once for the spec path and output directory, then runs
Phase 1 → 2 → 3 → 4 in order, pausing after each one to show you where its RTL and
validation report landed:

```bash
export OLYMPUS_USER=<your_netid>
export OLYMPUS_KEY=~/.ssh/id_ed25519_olympus2
/Users/lehanar/opt/anaconda3/bin/python3 Frontend2/scripts/full_pipeline.py
```

```
Spec JSON path: Spec/llmmc_microarchitecturespec_filled.json
Output dir (Enter for ./output): Frontend2/OutputFolders
```

After each phase you get a checkpoint:

```
==============================================================
  PHASE 1 PASSED
==============================================================
  RTL:        .../Frontend2/OutputFolders/PHASE1RTL
  Validation: .../Frontend2/OutputFolders/VALIDATIONREPORT

  [c] continue to Phase 2   [r] review report   [q] quit
  >
```

- `c` — move on to the next phase.
- `r` — print that phase's report JSON inline, then show the menu again.
- `q` — stop here (exits `0` if the last phase run passed, `1` if it failed).

If a phase **fails**, the menu only offers `[r] review report` / `[q] quit` — the
pipeline will not auto-continue past a real bug, since nothing here is LLM-driven and a
failure means an actual defect in a generator, testbench, or the spec.

**Don't run two invocations (or a manual single-phase run) against the same output
directory at the same time** — two processes writing the same generated file
concurrently can corrupt it. Each run's output directory is otherwise fully
self-contained and safe to inspect afterward.

### Option B — run a single phase

Each phase pipeline is also runnable standalone (useful when iterating on one phase
after a failure, without re-running everything before it):

```bash
export OLYMPUS_USER=<your_netid>
export OLYMPUS_KEY=~/.ssh/id_ed25519_olympus2
/Users/lehanar/opt/anaconda3/bin/python3 Frontend2/scripts/Phase2/phase2_pipeline.py
```

```
Spec JSON path: Spec/llmmc_microarchitecturespec_filled.json
Output dir (Enter for ./output): Frontend2/OutputFolders
```

Or non-interactively:
```bash
echo "Spec/llmmc_microarchitecturespec_filled.json
Frontend2/OutputFolders" | /Users/lehanar/opt/anaconda3/bin/python3 Frontend2/scripts/Phase2/phase2_pipeline.py
```

### Reading the output

- `PHASEN RTL/<module>.sv` — generated RTL
- `PHASEN RTL/<module>_tb.sv` — its spec-only testbench
- `PHASEN RTL/<module>_manifest.json` — port list, parameters, dependencies
- `VALIDATIONREPORT/phaseN_final_report.json` — written on success
- `VALIDATIONREPORT/phaseN_error_report.json` — written on failure, names the failing
  stage (`GENERATION` / `LINT` / `BEHAVIORAL_SIMULATION`) and module(s)
- `VALIDATIONREPORT/phaseN_lint_report.json`, `phaseN_sim_report.json` (Phase 1 uses
  bare `lint_report.json` / `sim_report.json` — an intentional naming quirk from
  Phase 1 predating the `phaseN_` prefix convention adopted for Phases 2–4)

## Troubleshooting

- **`ModuleNotFoundError: No module named 'langgraph'`** (or `paramiko`) — you're
  running the wrong Python interpreter. Use the Anaconda one explicitly (see
  *Required materials* above).
- **`can't open file '.../phase2_pipeline.py'`** — you're passing a relative path from
  the wrong working directory (e.g. still `cd`'d into `Phase1/`). Either `cd` to the
  repo root first, or pass an absolute path.
- **SSH connection hangs or times out** — check `nc -z -w 5 olympus.ece.tamu.edu 22`
  before assuming a code bug; Olympus has had transient outages independent of anything
  here.
- **A phase fails at the lint or sim gate** — this is real: Verilator or Xcelium found
  an actual defect. Read the named `phaseN_error_report.json`, and/or the full
  `<module>_xrun.log` on the remote work directory (SSH in and check
  `~/cadence_agent_work/`), then fix the generator or testbench directly and re-run.
  See `IMPLEMENTATION_PLAN.md` for examples of real bugs found and fixed this way.
