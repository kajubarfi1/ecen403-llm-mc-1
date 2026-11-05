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

To get all the way through stage 8, add `--per-block-netlists` (see 4.1):

```powershell
.\run_flow.ps1 --spec Spec\llmmc_microarchitecturespec_filled.json --per-block-netlists
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
| 6b | `backend_per_block` (opt-in, `--per-block-netlists`) | local Docker/ORFS | **~1 h**, 11 blocks at 2 workers |
| 7 | `backend_to_frontend` | local | edge; capped at 2 rounds |
| 8 | `final_validation` | Olympus | see the caveat below |

`--backend-mode` selects `contract` (seconds, no Docker), `synth`, `build`
(the default: full P&R plus DRC/LVS/STA sign-off) or `full` (build plus
autotuners).

## 4. What is verified, and what is not

**Verified on this machine 2026-11-05**, through the launcher, with no Olympus
key set:

```
spec_synthesis   PASS   DDR3-1333H derived, 27/27 consistency checks
spec_review      PASS   0 blocking, 3 advisory; JEDEC 25 pass / 0 fail
rtl_generation   HALT   OLYMPUS_KEY unset  <-- expected, needs 1.2
```

So the orchestrator, the venv and the credential loading all work. Stages 3, 4,
5, 7 and 8 are gated on the Olympus key and have **not** been run through
`flow.py` yet -- that is the honest state, and setting up 1.2 is what unblocks
it.

Stage 6b was exercised separately in `contract` mode (4.1). Stage 6 itself has
run many times outside `flow.py`: that is how the 200 MHz sign-off was produced.
What has never run is the whole chain in one command.

### 4.1 Stage 8 and the top-level netlist: closed, behind a flag

Stage 6 builds the **assembled top**, which gives one top-level netlist. Stage 8
swaps **per-block** netlists into the validation paths, and `find_netlists()`
deliberately excludes `TOPRTL` and `ddr3_controller` because no top-level
validation path exists yet. So a top-level-only build leaves stage 8 nothing to
swap, and it halts.

**`--per-block-netlists` closes that.** After the top-level build passes, it
cuts a bundle for each block out of this run's own drop and builds them with
`pipeline_batch.py` into the same `out_root`, so `runner/<block>/6_final.v`
appears for stage 8 to swap in.

Three design points worth knowing:

- **Bundles come from the run's own drop**, not from `backend/bundles/`. A
  per-block bundle is just `<block>.sv` plus `<block>_manifest.json`, which is
  exactly what each `drop/PHASE*RTL` directory already holds. `backend/bundles/`
  drifts and is written by the Frontend, so cutting from the drop is what keeps
  the netlists provenance-matched to the RTL being judged -- which stage 8
  enforces anyway, refusing netlists whose drop is not the one it is judging.
- **It is non-fatal.** These builds exist to produce netlists, not verdicts; the
  top-level build is the sign-off. A block that misses timing standalone still
  routes and still writes `6_final.v` -- the scheduler has historically failed
  standalone at 5 ns while the assembled top closed -- so an STA FAIL here does
  not halt a run whose top passed.
- **It needs `--backend-mode build` or `full`.** `contract` and `synth` do not
  place and route, so they cannot produce a netlist; the stage says so rather
  than reporting a failure.

Cost is about an hour: 11 blocks at `SAFE_MAX_WORKERS = 2`. Off by default, so
an ordinary run stays at the top-level build.

**Verified 2026-11-05** in `contract` mode (seconds, no Docker): all 11 bundles
cut from the drop, all 11 discovered by `pipeline_batch`, intake 10 PASS + 1
PASS_WITH_WARNINGS and **0 FAIL**. The one warning is `addr_decoder`, which is
purely combinational and has no clock port -- expected, not a defect. A full
`build`-mode run of stage 6b has **not** been done yet.

The alternative fix, still worth having, is a **top-level validation path** that
instantiates `ddr3_controller` whole. That is Validation's to define and does
not exist. Until it does, `--per-block-netlists` buys gate-level confidence
block by block, not on the assembled top.

### 4.2 A bug this flushed out

Running stage 6b for real exposed a pre-existing crash in `flow.py`'s `sh()`,
the helper every stage uses to run a subsystem. It used `text=True` with no
encoding, so subprocess output was decoded with the Windows locale codec
(cp1252). The backend's own status line contains a U+2192 arrow, so reading
stage 6's output died with `UnicodeDecodeError` **before the stage could return
a verdict** -- after the build had already run. Fixed by decoding UTF-8 with
`errors="replace"`.

This would have hit the first real end-to-end run on Windows at stage 6, an
hour in, and it is the reason to run a new stage for real rather than trust that
it reads correctly.

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
