# Getting Started with LLM Memory Controller

---

## Contents

1. [Introduction](#1-introduction)
2. [System Requirements](#2-system-requirements)
3. [Installation](#3-installation)
4. [Quick Start](#4-quick-start)
5. [Recovering from a Halted Run](#5-recovering-from-a-halted-run)
6. [Command Reference](#6-command-reference)
7. [Validation Subsystem: Standalone Use](#7-validation-subsystem-standalone-use)

---

## 1. Introduction

LLM Memory Controller generates a DDR3 memory controller, from requirements
through physical layout, with a single command. You describe the controller
you need in an interactive session, in plain English, and the tool asks
follow-up questions until it can propose a complete microarchitecture
specification. Once you accept the specification, the tool carries the design
through each stage of the hardware design flow without further input:

```
Requirements ─► Microarchitecture Specification ─► Specification Review
             ─► RTL Generation ─► RTL Validation
             ─► Physical Design (RTL to GDSII) ─► Final Netlist Validation
```

The tool verifies its own output at every stage. When a check fails, it
attempts a bounded number of automatic corrections. If the issue cannot be
resolved automatically, the run halts and records the cause, so that you can
address it and resume from the point of failure.

### 1.1 What you will need

Before you begin, confirm that you have, or can obtain, each item below:

- [ ] A macOS or Linux workstation with Python 3.10 or later
- [ ] A TAMU NetID with access to the Olympus compute cluster (`olympus.ece.tamu.edu`)
- [ ] Access to the TAMU network, either on campus or through the TAMU VPN
- [ ] An Anthropic API key
- [ ] Docker and OpenROAD-flow-scripts

Section 2 explains what each item is used for.

---

## 2. System Requirements

| Requirement | Purpose | When it is required |
|---|---|---|
| macOS or Linux, Python 3.10+ | Runs the tool | Always |
| Anthropic API key | Conducts the interactive design session and performs automatic RTL corrections | Always |
| TAMU NetID with Olympus access | Runs RTL lint (Verilator) and simulation (Cadence Xcelium) on the TAMU Olympus cluster | Whenever RTL is generated |
| TAMU network connection (on campus or TAMU VPN) | Reaches the Olympus cluster | Whenever RTL is generated |
| Docker | Hosts the physical design toolchain | Always |
| OpenROAD-flow-scripts | Performs synthesis, placement, routing and sign-off | Always |

Python 3.10 is the minimum supported version. Confirm your version with
`python3 --version`.

If you do not have access to Olympus, contact your course instructor or the
Department of Electrical and Computer Engineering IT staff.

---

## 3. Installation

### 3.1 Obtain the source code

```bash
git clone https://github.com/kajubarfi1/ecen403-llm-mc-1.git
cd ecen403-llm-mc-1
```

Run all commands in this guide from the repository root unless a step states
otherwise.

### 3.2 Create a Python environment (recommended)

A dedicated virtual environment ensures that the tool uses the same Python
interpreter into which its dependencies are installed.

```bash
python3 -m venv .venv
source .venv/bin/activate
```

Activate this environment in each new terminal session before you use the
tool.

### 3.3 Install the Python dependencies

```bash
python3 -m pip install langgraph langchain-core paramiko anthropic jsonschema
python3 -m pip install -r backend/requirements.txt
```

### 3.4 Install the physical design toolchain

1. Install [Docker](https://docs.docker.com/get-docker/) and confirm that it
   is running.
2. Pull the OpenROAD container image:

   ```bash
   docker pull openroad/orfs:latest
   ```

3. Clone [OpenROAD-flow-scripts](https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts)
   to a location of your choice. You will need its path in Section 3.5.

### 3.5 Create the configuration file

The tool reads its settings from environment variables. Values exported in your
shell take precedence. Otherwise, the tool reads them from a file named `.env`
in the repository root.

Create `.env` in the repository root with the following contents, substituting
your own values:

```bash
# Anthropic API: interactive design session and automatic RTL corrections
ANTHROPIC_API_KEY=sk-ant-...

# TAMU Olympus cluster: RTL lint and simulation
OLYMPUS_USER=<your_tamu_netid>
OLYMPUS_KEY=/Users/<you>/.ssh/id_ed25519_olympus2

# Physical design: Docker and OpenROAD-flow-scripts
USE_DOCKER=1
ORFS_DIR=/path/to/OpenROAD-flow-scripts
```

> **Important:** `.env` contains credentials and is excluded from version
> control. Do not commit it or share it.

### 3.6 Configure SSH access to Olympus

If you are off campus, connect to the TAMU VPN before you complete these steps,
and keep it connected whenever you run the tool.

The tool connects to Olympus without supervision, so it requires an SSH key
**without a passphrase**. It cannot respond to a passphrase or password prompt.

1. Generate a dedicated key:

   ```bash
   ssh-keygen -t ed25519 -f ~/.ssh/id_ed25519_olympus2 -N ""
   ```

2. Install the key on Olympus:

   ```bash
   ssh-copy-id -i ~/.ssh/id_ed25519_olympus2 <your_tamu_netid>@olympus.ece.tamu.edu
   ```

3. Confirm that you can log in without being prompted for a password:

   ```bash
   ssh -i ~/.ssh/id_ed25519_olympus2 <your_tamu_netid>@olympus.ece.tamu.edu exit
   ```

   You will be prompted for your NetID password when you install the key
   (step 2), but not when you test it (step 3).

### 3.7 Verify the Python dependencies

Complete this check and the one in Section 3.8 before your first run.

```bash
python3 -c "import langgraph, paramiko, anthropic, jsonschema; print('ok')"
```

The command should print `ok`. If it reports `ModuleNotFoundError`, confirm
that your virtual environment is active and repeat Section 3.3.

### 3.8 Verify the configuration

A dry run displays the planned stages and reports which settings the tool has
detected. It does not generate anything.

```bash
python3 flow.py --dry-run
```

The final line of the output summarizes your configuration:

```
env: ANTHROPIC_API_KEY set, OLYMPUS_KEY set, USE_DOCKER 1
```

Resolve any setting that is reported as `MISSING` or `unset` before you
continue.

---

## 4. Quick Start

This section walks you through starting the pipeline, choosing the controller
you want to build, and reading the results.

### 4.1 Prepare your session

Complete these steps each time you open a new terminal session:

1. If you are off campus, connect to the TAMU VPN.
2. Confirm that Docker is running.
3. Change to the repository root and activate your Python environment:

   ```bash
   cd ecen403-llm-mc-1
   source .venv/bin/activate
   ```

### 4.2 Start the pipeline

Start the pipeline with a single command:

```bash
python3 flow.py
```

The tool opens an interactive session in which you specify the controller you
want to build:

1. **Choose a primary goal.** Select `performance`, `power`, `cost` or
   `balanced`. The tool displays the configuration it recommends for that goal.
2. **Describe your requirements.** Add any specific requirements in plain
   English, for example *"DDR3-1600, 4Gb devices, two ranks, with ECC"*, or
   press Enter to accept the recommendations.
3. **Answer clarifying questions.** If your requirements are ambiguous or
   incomplete, the tool asks follow-up questions before it proposes a design.
4. **Review the proposed specification.** The tool displays the resulting
   microarchitecture and the results of its consistency checks. Enter `y` to
   view the complete specification JSON.
5. **Accept or refine.** When prompted `use this spec for the run?`, press
   Enter to accept. Enter `n` to keep refining your requirements.

Within the session, the following commands are also available:

| Command | Description |
|---|---|
| `preset <name>` | Use a predefined configuration (see Option B in Section 4.3) |
| `presets` | List the available presets |
| `goal` | Choose a different primary goal |
| `modifiable` | Show which parameters can be changed safely |
| `quit` | End the session without starting a run |

Once you accept a specification, the pipeline continues on its own through
specification review, RTL generation, validation and physical design. The tool
prints a timestamped line as each stage starts and finishes, along with its
result (`PASS`, `FAIL` or `HALT`). A complete run, including physical sign-off,
typically takes about one hour.

When the run completes successfully, the final line reads:

```
COMPLETE: spec, RTL, GDSII and netlist validated.
```

If the specification does not pass its review, the tool displays the findings
and reopens the session so that you can revise your requirements. If the run
halts for any other reason, the last lines of output give the reason and the
command to resume it. See Section 5.

### 4.3 Other ways to specify a design

The interactive session in Section 4.2 is the recommended way to specify a
design. You can also provide the design directly on the command line, which
skips the session and is useful for repeat runs and scripted use. Choose one
of the following options for each run.

#### Option A: Natural-language description

Describe the controller you need in plain English:

```bash
python3 flow.py "DDR3-1333, x16 devices, one byte lane, optimized for low power"
```

You may also state the primary design objective with `--goal`, which accepts
`performance`, `power`, `cost` or `balanced`:

```bash
python3 flow.py "Controller for a video frame buffer" --goal performance
```

If the tool needs more information, it opens the interactive session so that
you can answer its questions.

#### Option B: Predefined configuration

Presets are validated reference configurations that span common use cases:

```bash
python3 flow.py --preset <name>
```

| Preset | Speed Grade | Density | Ranks | Byte Lanes | ECC | Scheduler |
|---|---|---|---|---|---|---|
| `low-cost-embedded` | DDR3-800 | 2Gb | 1 | 1 | Disabled | In-order |
| `balanced` | DDR3-1333 | 2Gb | 1 | 2 | Disabled | FR-FCFS |
| `default` | DDR3-1600 | 2Gb | 1 | 2 | Disabled | FR-FCFS |
| `high-performance` | DDR3-1600 | 4Gb | 2 | 4 | Enabled | FR-FCFS |
| `server-grade` | DDR3-1600 | 4Gb | 4 | 8 | Enabled | FR-FCFS |

All presets use x8 DRAM devices.

#### Option C: Parameter file

To control individual parameters, supply them in a JSON file:

```bash
python3 flow.py --choices my_choices.json
```

[Spec/customizable_parameters_guide.md](Spec/customizable_parameters_guide.md)
lists every configurable parameter. It also identifies which parameters are
fixed by the JEDEC DDR3 standard and which are derived from your other
choices.

#### Option D: Existing specification

If you already have a complete microarchitecture specification, the tool skips
specification synthesis and begins at the specification review:

```bash
python3 flow.py --spec Spec/llmmc_microarchitecturespec_filled.json
```

#### Preview a specification without starting a run

The specification explorer runs the same interactive session as Section 4.2
but does not start the pipeline. Use it to explore designs and save
specifications for later runs.

```bash
# Interactive session
python3 Frontend2/scripts/Microarch/microarch_cli.py

# Review a description without writing any files
python3 Frontend2/scripts/Microarch/microarch_cli.py "DDR3-1600, 4Gb, ECC" --no-write

# Save a specification for later use
python3 Frontend2/scripts/Microarch/microarch_cli.py --preset server-grade --out my_spec.json
```

You can then supply a saved specification to a full run with
`python3 flow.py --spec my_spec.json` (Option D).

### 4.4 Understand the output

Each run creates its own directory, `runs/<timestamp>-<name>/`, with the
following contents:

| Path | Contents |
|---|---|
| `RUN_STATE.json` | Outcome of every stage and, if the run halted, the reason |
| `flow.log` | Complete log of the run. The interactive session is not recorded here |
| `spec/` | The accepted microarchitecture specification (`generated_spec.json`), a summary of how it was derived (`microarch_report.json`) and the specification review |
| `drop/` | Generated RTL and testbenches. `drop/TOPRTL/` contains the assembled top-level controller |
| `validation/round_N/` | Validation reports, one directory per correction round |
| `backend/` | Physical design reports and layout (GDSII) outputs |

To place a run in a specific directory, use `--run-dir <path>`.

---

## 5. Recovering from a Halted Run

The tool halts, rather than producing an unverified result, when a check fails
and cannot be corrected automatically or when a required tool or credential is
unavailable.

### 5.1 Identify the cause

```bash
cat runs/<run_id>/RUN_STATE.json     # the "halt" field gives the stage and reason
tail -50 runs/<run_id>/flow.log
```

### 5.2 Resume the run

After you address the cause, resume the run from the stage at which it stopped:

```bash
python3 flow.py --resume runs/<run_id>
```

If you modified the generated RTL by hand, include `--revalidate` so that your
changes are validated before the run proceeds:

```bash
python3 flow.py --resume runs/<run_id> --revalidate
```

### 5.3 Common issues

| Symptom | Resolution |
|---|---|
| `needs ANTHROPIC_API_KEY` | Add the key to `.env` (Section 3.5), or specify the design with `--preset`, `--choices` or `--spec`. Without the key, the interactive session accepts presets only |
| `OLYMPUS_KEY MISSING`, or the run waits at a password prompt | Set `OLYMPUS_USER` and `OLYMPUS_KEY`, and confirm the key has no passphrase (Section 3.6) |
| Connection to Olympus times out | If you are off campus, connect to the TAMU VPN and retry |
| `needs USE_DOCKER=1` | Complete the physical design setup (Sections 3.4 and 3.5) |
| Specification review fails | The requested parameters conflict. In the interactive session, the tool shows the findings and reopens the session so that you can revise your requirements. With a preset, parameter file or existing specification, read the review in `spec/`, correct the input and start a new run |
| The run halts because the interactive session ended without accepting a spec | You ended the session before accepting a specification. Start a new run with `python3 flow.py` |
| `an interactive spec session needs a terminal` | Run the tool from an interactive terminal, or specify the design on the command line (Section 4.3) |
| `ModuleNotFoundError` | Activate your virtual environment and repeat Section 3.3 |

---

## 6. Command Reference

```
python3 flow.py [design input] [options]
```

### Design input (choose one, or omit for the interactive session)

| Argument | Description |
|---|---|
| *(none)* | Open the interactive session (Section 4.2) |
| `"<description>"` | Plain-English description of the controller |
| `--preset <name>` | Predefined configuration (Section 4.3, Option B) |
| `--choices <file>` | JSON file of design parameters |
| `--spec <file>` | Existing microarchitecture specification |

### Options

| Option | Description |
|---|---|
| `--goal <goal>` | Primary design objective: `performance`, `power`, `cost` or `balanced` |
| `--dry-run` | Display the planned stages and detected configuration, then exit |
| `--backend-mode <mode>` | Physical design depth: `contract` (seconds), `synth` (minutes), `build` (about one hour, including sign-off) or `full` (`build` plus optimization) |
| `--phases <N[,N]>` | Generate only the specified RTL phases, for partial checks. Physical design is skipped |
| `--validate-per-phase` | Validate after each RTL phase as well as at the end |
| `--max-rtl-rounds <N>` | Maximum automatic RTL correction attempts (default: 4) |
| `--max-backend-rounds <N>` | Maximum physical design correction attempts (default: 2) |
| `--run-dir <path>` | Directory for this run's output |
| `--resume <path>` | Resume a halted run |
| `--revalidate` | With `--resume`, revalidate RTL that changed since the last validation |

For the complete list of options, run `python3 flow.py --help`.

---

## 7. Validation Subsystem: Standalone Use

`flow.py` runs validation for you. This section is for running it on its own:
to judge an RTL drop without regenerating it, to re-judge after a checker
changed, or to run the checks that validate the validation itself. Everything
here runs from the repository root.

### 7.1 What it does

Validation never writes RTL. From the microarchitecture specification and the
drop's manifests it generates the whole environment, then judges the drop:

| Generated from the spec and manifests | Judged by |
|---|---|
| Transaction monitors on every block interface | A transaction scoreboard comparing the trace against reference models |
| Timing and protocol assertions (SVA), functional coverage | Assertion results, coverage against the verification plan |
| Reference models and legality checkers, written by an LLM and accepted only by gates that grade them against the spec | Two independent models per scope, which must agree |
| Stimulus sequences per path (register walks, bursts, refresh stress, constrained random) | 22 end-to-end paths through the 11 blocks |

Results are written as **findings**: each has an owner block, a confidence,
source anchors, a reproduction command and a history across drops. The
Frontend reads them from one place, `Validation/findings/outbox/current/`.
That directory is the latest run and nothing else, never a ledger: every
file in it is rewritten by each complete run (history is
`outbox/<revision>/<drop>/` and each finding's `first_seen` / `last_seen` /
`resolved_in`).

### 7.2 Additional setup

Validation uses the same Olympus account as Section 3.6. Its tools read the
settings from your shell, or from `Validation/setup.env` when they are run
on their own (the file is excluded from version control):

```bash
# Validation/setup.env
OLYMPUS_USER=<your_tamu_netid>
OLYMPUS_KEY=/Users/<you>/.ssh/id_ed25519_olympus2     # or OLYMPUS_PASSWORD=...
ANTHROPIC_API_KEY=sk-ant-...                           # only to regenerate a model
ANTHROPIC_MODEL=claude-opus-4-6                        # model for generated checkers
```

One extra dependency beyond Section 3.3, and one optional install:

```bash
python3 -m pip install python-dotenv
python3 Validation/tools/install_sky130_models.py    # once; only for gate-level runs (Section 7.5)
```

Confirm the setup without simulating anything:

```bash
python3 Validation/tools/validate_drop.py --dry-run
python3 -m unittest discover -s Validation/tests -p "test_*.py"     # about 290 tests, under a second
```

### 7.3 Validate the RTL drop

The drop is whatever `Frontend2/OutputFolders/` holds (or the directory named
by `VALIDATION_RTL_DROP_ROOTS`, which `flow.py` sets to the run's `drop/`).

```bash
python3 Validation/tools/validate_drop.py                 # full: simulate every path on Olympus (1 to 3 minutes)
python3 Validation/tools/validate_drop.py --skip-sim      # re-judge the last traces (seconds; after a checker changed)
python3 Validation/tools/validate_drop.py --partial       # a drop with blocks missing (a single Frontend phase)
python3 Validation/tools/validate_drop.py --paths path_01_write_cmd path_22_csr_standalone
```

The nine steps print as they run: resolve the drop, review the spec, regenerate
the environment, re-grade the models, simulate, roll up coverage, emit
findings, compare with the previous drop, refresh the dashboard. The last line
is the verdict:

```
  drop a7cd3cb93546: 19 pass / 0 fail / 0 error in 1.6 min; log Validation/reports/validate_drop/a7cd3cb93546.log
```

Where to look afterwards:

| Path | Contents |
|---|---|
| `Validation/findings/outbox/current/HANDOFF.json` | drop id, design id, spec id, PASS or FAIL, failed modules |
| `Validation/findings/outbox/current/retry_instructions.json` | per failed module: the checks, expected versus actual, anchors, a fix when a repair proved one |
| `Validation/findings/outbox/current/findings_v2.json` | every finding in full |
| `Validation/reports/paths/<path>_report.json` | the stage-by-stage verdict of one path |
| `Validation/reports/dashboard.html` | the cockpit: paths, coverage, formal, faults, findings, drop history |

A drop is identified by its content (`drop_id`), never by git. Two drops with
the same `design_id` are the same design regenerated. The validator stops,
rather than judging, when the drop is inconsistent: a block from another spec
revision, a manifest naming a port that does not exist, or a model the spec
no longer supports (it regenerates the model first; `--no-model-regen` stops
instead).

### 7.4 One path at a time

For debugging, run a single path with a chosen stimulus and keep the work
directory:

```bash
python3 Validation/tools/run_path.py --path path_19_row_conflict
python3 Validation/tools/run_path.py --path path_01_write_cmd --stimulus random_v2 --seed 7 --drives 400
python3 Validation/tools/run_path.py --path path_05_scheduler_refresh_loop --judge-only   # re-judge, no simulation
python3 Validation/tools/run_path.py --path path_22_csr_standalone --probe "u_config_regs.reg_timing_0@0:2000"
```

The path list is `Validation/spec/path_definitions.json`; `--help` lists the
stimulus generators.

### 7.5 Gate-level: the backend's netlists through the same paths

The backend's per-block netlists live at `backend/outputs/<block>/6_final.v`.
A netlist is accepted when every path that instantiates the block passes with
the netlist in the RTL's place, judged by the same models and assertions:

```bash
python3 Validation/tools/run_path.py --path path_21_wb_port_standalone --netlist wb_port=backend/outputs/wb_port/6_final.v
```

`flow.py` runs this for every block as its final stage.

### 7.6 Validating the validation

These are the checks that say whether the checkers themselves can be trusted.
Run them after any change to a generator, a rule or a model:

```bash
# Seeded faults: 23 catalogued RTL mutations must each be caught, and blamed on the right block
python3 Validation/faults/seed_faults.py --jobs 4                # simulates (10 to 20 minutes)
python3 Validation/faults/seed_faults.py --judge-only            # re-judge after a checker changed

# Two independent models per scope must agree on every recorded trace
python3 Validation/agreement/model_agreement.py

# A known-good open-source controller (UberDDR3) under our assertions: 0 failures expected
python3 Validation/refdesigns/uberddr3/path_checkers_on_uberddr3.py --log <txn log>   # see its README for the Olympus run

# Formal (JasperGold on Olympus): every generated assertion proven, bounded, or filed as a finding
python3 Validation/tools/run_formal.py --path path_01_write_cmd
# A maximum-interval property no bounded engine can cross (tREFI: 14 040 cycles) is
# proved under an assumed, shorter configuration with the assertion bound scaled to
# match; the report records every cut, assumption and parameter as an abstraction
python3 Validation/tools/run_formal.py --path path_01_write_cmd --time 40m \
    --stopat u_config_regs.reg_timing_3 --stopat u_config_regs.reg_refresh_config \
    --assume "u_config_regs.reg_timing_3 == 32'h00020404" \
    --assume "u_config_regs.reg_refresh_config == 32'h00000111" \
    --sva-param TIMING_012_BOUND=258 --sva-param TIMING_012_INTERVAL=129
```

A proof is about a design: `validate_drop.py` (step 4b) re-proves every
path that has ever been proved and has no report that applies to the drop
under judgement, with the same abstractions as its last report, so a
regeneration never leaves proofs stale (`--skip-formal` to defer it,
`--formal-time` for the per-path limit). Do not pass `--trace` unless you
want a cap: JasperGold shuts the whole proof down when an engine reaches
it, and every open property comes back `undetermined` at that bound.

Results land in `Validation/reports/faults/fault_matrix.json`,
`reports/model_agreement.json`, `reports/uberddr3/` and `reports/formal/`.

### 7.7 Regenerating a model

Reference models and checkers are generated by an LLM and accepted only when
a spec-derived gate finds no fault in them. `validate_drop.py` does this
automatically when a model no longer passes its gate under the drop's spec.
To do it by hand, or to see the prompt a model is built from:

```bash
python3 Validation/agents/predictor_agent.py --scope config_regs --dry-run     # show the prompt, call nothing
python3 Validation/agents/predictor_agent.py --scope config_regs               # generate, grade, accept or retry
python3 Validation/agreement/second_opinion.py --scope config_regs            # its independent twin
```

Set `LLM_PROVIDER=tamu` to use the TAMU gateway instead of a personal Anthropic
key. A model that the gate rejects after every retry is reported as a
generation failure, never as a verdict on the design.

### 7.8 Common issues

| Symptom | Resolution |
|---|---|
| `no Olympus account` | Put `OLYMPUS_USER` and `OLYMPUS_KEY` (or `OLYMPUS_PASSWORD`) in `Validation/setup.env`, or export them |
| `ssh connect attempt N failed`, then `TimeoutError` | Olympus is unreachable: connect to the TAMU VPN. Connection resets under load are retried automatically |
| `STOP: the drop does not provide every block` | A partial drop: add `--partial`, or point `VALIDATION_RTL_DROP_ROOTS` at a complete one |
| `FOREIGN spec rev` or `SPEC_MISMATCH` findings | A block was generated from another spec revision; regenerate the drop from one spec |
| `STALE <scope> ... regenerating` | The spec changed under a model; the agent regenerates it. Needs an API key or `LLM_PROVIDER=tamu` |
| `a generator refused the drop` | A manifest is inconsistent with the RTL (a `source` naming a missing port). The log names the port; it is a Frontend finding, not a simulation failure |
| `path verdict : rc=2` for some paths | Those paths did not simulate (infrastructure). Their findings are carried as untested; rerun with `--paths` |

