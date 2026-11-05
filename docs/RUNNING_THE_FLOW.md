# Running the full flow on one machine

Operational runbook for driving `flow.py` end to end -- Frontend spec synthesis
through Backend GDSII and back into Validation -- from a single laptop, so the
rest of the team does not need OpenROAD, Docker, or a local PDK.

Written 2026-11-05 by Backend (Dawson). Each stage's status below is measured,
not assumed; what has not been run end to end says so.

## 0. What actually has to be installed where

Worth reading before anything else, because only **one** of the three
subsystems needs heavy local tooling.

| Subsystem | Runs where | Needs locally |
|---|---|---|
| **Frontend** (spec synthesis, RTL generation, repair agents) | local Python | `ANTHROPIC_API_KEY`; its phase pipelines also reach Olympus to simulate |
| **Backend** (RTL to GDSII, DRC/LVS/STA) | local Docker + ORFS | Docker, the `openroad/orfs` image, an ORFS checkout |
| **Validation** (paths, formal, netlist re-sim) | **remote: `olympus.ece.tamu.edu`** | nothing but SSH -- `xrun`/IMC/JasperGold are Cadence tools on Olympus |

So the asymmetry is: **Validation was never a local-install problem.** It runs
over SSH under your own TAMU NetID. Only the Backend needs the heavy local
stack, and that is already on this machine.

## 1. One-time setup

### 1.1 The flow venv

`flow.py` drives every subsystem with `sys.executable`, so a single interpreter
must satisfy all three at once. The backend's own venv is deliberately **not**
reused: it produced the first 200 MHz sign-off and is left untouched.

```powershell
py -3 -m venv C:\Users\dawca\llmmc_flow_venv
```

```powershell
C:\Users\dawca\llmmc_flow_venv\Scripts\python.exe -m pip install "langgraph==1.0.10" "langchain-core==1.2.17" "jsonschema==4.26.0" paramiko anthropic
```

The three pins match the backend venv exactly, so the backend behaves
identically under either interpreter. `paramiko` is Validation's SSH transport;
`anthropic` is the Frontend's agents. It lives outside OneDrive on purpose --
a venv inside a synced folder generates constant sync churn.

**Done on this machine.** Verified: all four imports load, and `flow.py`,
`run_path.py`, `validate_drop.py` and `sim_runner.py` all compile.

### 1.2 Credentials

Two files, neither ever committed (`.gitignore` covers `*.env` and `setup.env`;
**the repo is public**).

- **Anthropic key** -- already present in the backend's own `.env`. Nothing to
  do, and deliberately **not copied** into this repo: duplicating a live key
  into a public repo's working tree is an avoidable risk, so `run_flow.ps1`
  reads it where it already lives.
- **Olympus** -- `Validation\setup.env`, created as a template with the fields
  blank. **You fill this in; it is the one remaining setup step.**

`OLYMPUS_USER` is **your own NetID** -- nobody needs to share an account.

`OLYMPUS_KEY` must be a **passphrase-less private key**, not a password. This
is not a preference: `flow.py` halts the run if it is unset, because the
Frontend phase pipelines prompt for a password and a non-interactive run cannot
answer a prompt.

```powershell
ssh-keygen -t ed25519 -f $env:USERPROFILE\.ssh\olympus -N '""'
```

```powershell
type $env:USERPROFILE\.ssh\olympus.pub | ssh NETID@olympus.ece.tamu.edu "mkdir -p ~/.ssh; cat >> ~/.ssh/authorized_keys; chmod 600 ~/.ssh/authorized_keys"
```

```powershell
ssh -i $env:USERPROFILE\.ssh\olympus NETID@olympus.ece.tamu.edu "hostname"
```

That last command must print a hostname **without asking for a password**. If
it prompts, the flow will halt at `rtl_generation`.

Then set in `Validation\setup.env`:

```
OLYMPUS_USER=your_netid
OLYMPUS_KEY=C:\Users\dawca\.ssh\olympus
```

### 1.3 sky130 gate models on Olympus (only for netlist re-simulation)

Needed once, and only for the final gate-level stage -- Olympus has no sky130
PDK, so Xcelium cannot elaborate the backend's netlists without the cell
models.

```powershell
C:\Users\dawca\llmmc_flow_venv\Scripts\python.exe Validation\tools\install_sky130_models.py --check
```

If `--check` says they are absent, drop `--check` to install. The installer's
own smoke test compiles a real netlist against the library, so a clean run is
proof it works rather than just proof it copied files.

## 2. Running it

Everything goes through the launcher, which loads both env files, defaults
`USE_DOCKER=1`, reports readiness without printing any secret, and then hands
off to `flow.py`. All arguments pass straight through.

```powershell
.\run_flow.ps1 --spec Spec\llmmc_microarchitecturespec_filled.json --dry-run
```

```powershell
.\run_flow.ps1 --spec Spec\llmmc_microarchitecturespec_filled.json
```

**Use `--spec` with the golden spec to reproduce the signed-off chip.** This
matters more than it looks: `--preset balanced` is **DDR3-1333**, not the
DDR3-1600 the project has signed off. A preset run generates revision
`compiled_ddr31333_x8_2lane_1rank_1ebcc694`, while the golden spec is
`golden_ddr3_1600k_x8_2lane_1rank`. Mixing them is how a config_regs
"mismatch" appears that is really two speed bins being compared to each other.

Other useful forms:

```powershell
.\run_flow.ps1 "DDR3-1600 x8, two byte lanes, balanced"
```

```powershell
.\run_flow.ps1 --spec Spec\llmmc_microarchitecturespec_filled.json --skip-backend
```

```powershell
.\run_flow.ps1 --resume runs\RUN_ID
```

Every run lives in `runs/<run_id>/` with `RUN_STATE.json` recording each
stage's outcome. A halt is not a crash: deal with what stopped it and resume.
Exit 2 means halted.

## 3. The stages, and what each one costs

| # | Stage | Where | Rough time |
|---|---|---|---|
| 1 | `spec_synthesis` | local | seconds (preset/spec) or one LLM call (English) |
| 2 | `spec_review` | local | seconds |
| 3 | `rtl_generation` | local + Olympus sim | minutes per phase |
| 4 | `rtl_validation` | Olympus | ~20 paths |
| 4b | `formal` (opt-in, `--formal`) | Olympus JasperGold | 20-60 min |
| 5 | `frontend_regeneration` | local LLM agents | capped at 4 rounds |
| 6 | `backend` | local Docker/ORFS | **~30-50 min** for the top |
| 7 | `backend_to_frontend` | local | edge; capped at 2 rounds |
| 8 | `final_validation` | Olympus | see the caveat below |

`--backend-mode` selects `contract` (seconds, no Docker), `synth`, `build`
(the default: full P&R plus DRC/LVS/STA sign-off) or `full` (build plus
autotuners).

## 4. Verified so far, and the one real gap

**Verified on this machine 2026-11-05**, through the launcher, with no Olympus
key set:

```
spec_synthesis   PASS   DDR3-1333H derived, 27/27 consistency checks
spec_review      PASS   0 blocking, 3 advisory; JEDEC 25 pass / 0 fail
rtl_generation   HALT   OLYMPUS_KEY unset  <-- expected, needs 1.2
```

So the orchestrator, the venv and the credential loading all work. Stages 3
onward are gated on the Olympus key and have **not** been run through
`flow.py` yet.

### The gap: stage 8 cannot judge a top-level netlist

A real architectural hole, not a configuration problem, and worth stating
plainly because it sits exactly where "fully validated final chip" would land.

Stage 6 builds the **assembled top** (`drop/TOPRTL`), producing one top-level
netlist. Stage 8 swaps **per-block** netlists into the validation paths, and
`find_netlists()` explicitly excludes both `TOPRTL` and `ddr3_controller`. With
a top-level-only build there is nothing to swap, so it halts with:

> the backend produced no per-block netlist to run ... A top-level netlist
> needs a top-level path, not built yet.

The flow's author knew this; it is one of two edges documented up front as
waiting on a counterpart. Closing it needs **one** of:

1. **Per-block backend builds in addition to the top.** The drop already
   carries the blocks (`drop/PHASE1RTL` through `drop/PHASE4RTL`), so bundles
   can be cut from the run's own drop and built with `pipeline_batch.py`,
   giving `runner/<block>/6_final.v` for stage 8 to swap in. Cost: 11 extra
   builds, roughly 5-6 hours, plus a `flow.py` change.
2. **A top-level validation path** that instantiates `ddr3_controller` whole.
   That is Validation's to define, and it does not exist yet.

Until one of those lands, the defensible claim is:

> top-level GDSII with DRC 0, LVS match, and STA closed at 200 MHz (typical
> corner), plus RTL-level functional validation across 23 paths

which is what the project has. What is **not** yet available is gate-level
re-simulation of the assembled top.

## 5. Standing caveats that travel with any result

- **Single corner.** The platform ships one liberty file,
  `sky130_fd_sc_hd__tt_025C_1v80.lib` -- typical process, 25 C, 1.80 V. No slow
  or fast corner, no voltage or temperature sweep. Always say "at the typical
  corner."
- **The sign-off chip used `CORE_UTILIZATION 35`**, which is not the packager
  default of 20. A default build does **not** reproduce the 200 MHz PASS. To
  reproduce it, put `CORE_UTILIZATION: "35"` in the bundle's `manifest.json`
  `orfs_config` -- the packager writes the default first and appends
  `orfs_config` after, and Make takes the last assignment.
- **Backend runs must stay sequential.** Every bundle shares the module name
  `ddr3_controller` and ORFS keys its results path on `DESIGN_NAME`, so
  concurrent builds overwrite each other. This is unfixed.
