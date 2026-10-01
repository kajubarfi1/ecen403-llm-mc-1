# UberDDR3 as the known-good reference

Every design this subsystem had validated before 2026-09-24 was broken, so the
false-positive rate of the checkers was unknown. UberDDR3
(github.com/AngeloJacobo/UberDDR3) is an open-source DDR3 controller that runs a
real Micron DDR3 behavioural model to a self-checking finish. Here it is the
answer to "what do our spec-derived assertions say about a design that works?"

## What is here

| File | Role |
|---|---|
| `../../builds/uberddr3_ddr3-667_x16_2lane_1rank/microarch_spec.json` | Our spec of UberDDR3's *simulated* configuration: 8Gb x16, 2 byte lanes, 12 ns controller / 3 ns DDR clock (4:1), CL=CWL=5, its SPEED_BIN=3 nanosecond table. Compiled by the Frontend compiler from the nearest choices, then overridden to these values. |
| `generated/cmd_gen_sva_pins.sv` | Our timing/protocol assertions generated from that spec with `sva_gen.py --clock ddr --suffix _pins`: bounds in DDR clocks, one command per tCK. |
| `uberddr3_pin_sva.sv` | Adapter + bind: maps CS#/RAS#/CAS#/WE#/BA/A at the DRAM pins onto our `ddr_cmd` encoding (identical to the JEDEC truth table), instantiates the assertions on the DDR clock, and prints a TXN trace of every pin command. |
| `xcelium_compat.patch` | Xcelium rejects UberDDR3's constant functions (`$rtoi($ceil())` and localparams declared later). Functionally neutral patch; Icarus/Vivado need nothing. |
| `../../reports/spec_swap_uberddr3.json` | Proof our generators accept the spec with zero code edits. |

## Running it (Olympus)

```
# once: upload the repo (scratchpad clone + patch applied) to ~/uberddr3/UberDDR3
# scripts live in ~/cadence_agent_work: run_uber.sh (plain), run_uber_sva.sh (with our assertions)
python3 - <<'EOF'
import sys; sys.path.insert(0, 'Validation/agents')
from sim_runner import CadenceSSHAgent
a = CadenceSSHAgent(); a.connect()
a.upload_file('Validation/refdesigns/uberddr3/uberddr3_pin_sva.sv', 'uberddr3_pin_sva.sv')
a.upload_file('Validation/refdesigns/uberddr3/generated/cmd_gen_sva_pins.sv', 'cmd_gen_sva_pins.sv')
print(a.srun('bash ~/cadence_agent_work/run_uber_sva.sh', timeout=1700)['stdout'])
EOF
```
The script prints UberDDR3's own summary (writes/reads/success/fails), our
assertion failures by name, and the Micron model's ERROR lines. The Micron
model is the independent cross-check: it enforces JEDEC timing at the same
pins, so an assertion of ours that fires with no Micron error is *our*
false positive (or a JEDEC deviation the model tolerates), and one that
fires alongside a Micron error is a true positive.

UberDDR3's testbench ends in `$stop`; the scripts pass `-input run_exit.tcl`
(`run; exit`) so the Slurm job does not sit at the Xcelium prompt.

## What the first runs taught (2026-09-24)

UberDDR3 self-check: 4608 writes, 4608 reads, 4604 success, 4 fails = its 4
deliberately injected errors; Micron model: 0 errors. Known-good confirmed.

First assertion run: 19 failures, all ours.
1. **PROTO_001 x14 (READ to a bank with no open row).** JEDEC Multi-Purpose
   Register mode (MR3 A2): a controller calibrates its read path with READs
   that return a fixed pattern and need no ACTIVATE. UberDDR3 does exactly
   this during init; our rule did not know MPR exists. Fix in `sva_gen.py`:
   `mpr_en` tracked from MRS-to-MR3, READs allowed while set. Our own
   init_fsm never uses MPR, so this could only have been learned from a
   design that does.
2. **TIMING_012 x5 (tREFI) at 13–25 ns.** The testbench's DDR3 RESET# is not
   yet driven in the first cycles, so the tracking registers were X and an X
   in the checked expression is a failure. Fix: tracking state initialised at
   declaration as well as on reset. Applies to every generated tracker.
3. **A quarter of the pin trace looked missing.** It was not: the Micron
   model echoes each command without a newline, so our TXN line was appended
   to its text and an anchored `grep '^TXN'` skipped it. Same latent bug in
   `txn/trace_extract.py`, now unanchored. Real trace: 15946 commands —
   2635 ACT, 2569 PRE, 5825 WR, 4878 RD, 30 REF, 8 MRS, 1 ZQCL.

4. **Xcelium rejects a declaration initialiser on an `always_ff` variable**
   (MULAXX, two drivers). The generated trackers are plain clocked `always`
   blocks with initialisers instead.

**Final run: 0 assertion failures, 0 Micron errors, 15946 commands observed**
(`../../reports/uberddr3/known_good_1fea117.json`). A sanity mutation (spec
tRCD raised to 60 ns) is run to show the bound assertions do fire on this
design when the spec disagrees with it.

Observations about UberDDR3 itself: it enforces tRRD at 7.5 ns, but at a 3 ns
clock JEDEC requires max(4 nCK, 7.5 ns) = 12 ns; it does not enforce tFAW at
all. Neither produced an assertion failure in this configuration (its
scheduling never gets close), and the Micron model agrees.

## Data integrity (done 2026-09-24)

`uberddr3_wb_monitor.sv` (bound on the testbench's Wishbone port) and
`check_data_integrity.py` add two checks over the same log
(`../../reports/uberddr3/data_integrity_1fea117.json`):

1. Host memory model, byte-enable aware, reads checked against the model as
   it stood when the read was accepted: **0 mismatches over 4608 reads**.
2. Host-to-pin address consistency: every post-calibration host request
   mapped through the spec's {row, bank, column} must match, in order, a CAS
   at the DRAM pins with that bank and column while that bank's open row
   (tracked from ACT/PRE at the pins) is the mapped row:
   **9216 of 9216 matched, 0 errors**.

Two more lessons from building it: a write acknowledgement carries X on the
read-data bus (parse x/z digits, decide by request kind), and a memory model
must be walked in request order — applying all writes first compares a read
against a later rewrite (128 phantom mismatches until fixed).

## Next

- Stress the tRRD/tFAW gap: a stimulus that activates four banks back to back
  should make both our assertion and the Micron model fire together.
- Use this harness as the template for gate-level runs on our own blocks.
