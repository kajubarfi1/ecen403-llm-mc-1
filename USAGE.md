# Getting Started with LLM Memory Controller

---

## Contents

1. [Introduction](#1-introduction)
2. [System Requirements](#2-system-requirements)
3. [Installation](#3-installation)
4. [Quick Start](#4-quick-start)
5. [Recovering from a Halted Run](#5-recovering-from-a-halted-run)
6. [Command Reference](#6-command-reference)

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
