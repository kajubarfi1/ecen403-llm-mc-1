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

**Either credential works**: `OLYMPUS_KEY`, a path to a **passphrase-less**
private key, or `OLYMPUS_PASSWORD`. A passphrase-protected key is not an
option, because a non-interactive run cannot answer a prompt.

Prefer the key. Fall back to the password only if sshd refuses your key --
which does happen, for reasons invisible from a user shell (see 1.2.1). Be
deliberate about it: that is your NetID password in plaintext on disk, and a
NetID password unlocks a great deal more than Olympus. The file is gitignored
so it will not reach the public repo, but anything that can read your user
profile can read it.

Note `OLYMPUS_PASSWORD` only became real in `ff03df9`. Before that it was
documented in `USAGE.md` but never read anywhere in `Frontend2` -- a
password-only setup authenticated with nothing and failed every time.

```powershell
ssh-keygen -t ed25519 -f $env:USERPROFILE\.ssh\olympus -N '""'
```

```powershell
$k = Get-Content $env:USERPROFILE\.ssh\olympus.pub; ssh NETID@olympus.ece.tamu.edu "mkdir -p ~/.ssh; chmod go-w ~; chmod 700 ~/.ssh; echo '$k' >> ~/.ssh/authorized_keys; chmod 600 ~/.ssh/authorized_keys"
```

```powershell
ssh -o BatchMode=yes -i $env:USERPROFILE\.ssh\olympus NETID@olympus.ece.tamu.edu "hostname"
```

`BatchMode=yes` disables password prompts, so that command either prints a
hostname or fails immediately with the reason -- it cannot sit waiting at a
prompt and look like a hang.

### 1.2.1 If sshd refuses a correct key

This happened on `dawsoncarpenter@olympus` on 2026-11-05 and cost an hour, so
it is written down. The symptom in `ssh -v` is:

```
debug1: Offering public key: ...\.ssh\olympus ED25519 SHA256:...
debug1: Authentications that can continue: publickey,password
```

Key offered, no `Server accepts key`, straight back to the method list.

What that is **not** -- all checked, with evidence, so they need not be
rechecked: the wrong key (compare `ssh-keygen -lf` on your `.pub` against the
fingerprint in the `Offering` line, and the installed line on the server);
`StrictModes` (home, `~/.ssh` and `authorized_keys` must be owner-only, and
were); a passphrase; Windows refusing the private key (that prints
`too open`); or SELinux on an NFS home (`getsebool use_nfs_home_dirs` was
**on**, and `restorecon` has nothing to change because the label comes from the
mount, not the file).

What it probably **is**, and none of it is visible from a user shell:
`/etc/ssh/sshd_config` returned `Permission denied`, which means a centrally
managed config -- so `AuthorizedKeysFile` may point somewhere other than
`~/.ssh/authorized_keys`, keys may come from an `AuthorizedKeysCommand`
directory lookup, or a `Match` block may gate `PubkeyAuthentication`.

Two traps specific to Windows while installing a key:
- **`ssh-copy-id` does not ship with Windows OpenSSH.** Doing it by hand with
  `type key.pub | ssh host "cat >> ..."` puts the key on ssh's stdin while ssh
  also wants to prompt you for a password, and `type` emits CRLF -- a key line
  ending in `
` is invalid to sshd. Pass the key as an argument instead:
  `$k = Get-Content ...pub; ssh host "echo '$k' >> ~/.ssh/authorized_keys"`.
- On that NFS mount, `chmod 600` did not take -- the file stayed `-rwx------`.
  Still owner-only, so harmless for `StrictModes`, but do not trust the mode
  you asked for.

**The fallback is `OLYMPUS_PASSWORD`**, which works and is the pragmatic
answer when the key route is administratively closed. Verified on this account
2026-11-05: password auth reaches `olympus-login.engr.tamu.edu`, `srun`
allocates on the `adademic` partition, and `xrun 24.03-s013` is visible from a
compute node.

### 1.2.2 A parser bug this exposed, now fixed

Worth knowing, because the symptom named nothing useful. With the unused
credential left blank (`OLYMPUS_KEY=`), `sim_runner._from_setup_env` read its
value as `#` and handed paramiko a key file by that name:

```
FileNotFoundError: [Errno 2] No such file or directory: '#'
```

The regex was `r'^\s*' + key + r'\s*=\s*"?([^"\n]*?)"?\s*$'` under `re.M`.
`\s` matches newlines, so the `\s*` after the `=` crossed the line break and
the capture group took the next non-blank line -- a comment -- as the value.
The real credential sat unused two lines below, and nothing in the error
mentioned `setup.env`, or which key, or that a credential had been found at
all.

Fixed by using `[^\S\n]*` (horizontal whitespace only), so an empty value reads
as absent and `_setting()` falls through to the next source. The other readers
of `setup.env` are line-based and were never affected. A blank line is harmless
now, but deleting the credential you are not using is still tidier.

Then set in `Validation\setup.env`:

```
OLYMPUS_USER=your_netid
OLYMPUS_KEY=C:\Users\dawca\.ssh\olympus
```

or, for the password route:

```
OLYMPUS_USER=your_netid
OLYMPUS_PASSWORD=your_netid_password
```

**Uncomment the line you use** -- every loader skips anything starting with
`#`, so a filled-in but still-commented `# OLYMPUS_PASSWORD=...` reads as
absent and the gate reports no credential at all.

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

**Done on this account 2026-11-05**: 233 cell models and 94 include dirs under
`~/cadence_agent_work/sky130`, smoke test OK -- the `wb_port` netlist compiles.
The `*W,DLCVAR ... Invalid environment variable ''` line is a `cds.lib`
warning, not a failure.

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
