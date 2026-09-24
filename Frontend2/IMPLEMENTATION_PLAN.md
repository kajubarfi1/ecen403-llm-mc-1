# Frontend2 — Implementation Plan

## Target architecture (per phase, all 4 phases identical shape)

```
RTL Generation Scripts (deterministic, one per module)
        |
        v
   Verilator Lint Script  <---- real static analysis (verilator --lint-only),
        |                       not the current manifest-diff checker
        v
   [gate: lint clean?]
        |
        v
   Simulator Script  <---- runs testbenches (below) against the RTL
        ^
        |
   Testbench Generator Script <---- SOLO: reads ONLY the spec,
                                     never reads the generated RTL
        |
   [on any lint or sim failure]
        v
   Feedback Agent  ----patches----> the specific RTL Generation Script
        |
        +---------------------> loop back to RTL Generation Scripts
```

Only the **Feedback Agent** is actually LLM-backed. Everything else —
generation, lint, testbench generation, simulation, final assembly — is a
deterministic script. Named accordingly below (no more "agent" on things
that aren't).

After Phase 4's loop closes clean: **Integration/Assembly Script** builds
the final top-level RTL from every phase's modules + manifests.

## Why this differs from today's `Frontend/`

- Today's testbench generation reads the *generated RTL* to build its own
  checks (e.g. `phase1_validation_agent.py`'s `generate_init_fsm_tb` regexes
  `MR0_VAL`/`MR2_VAL` out of `init_fsm.sv` itself). A generator bug and its
  "test" can agree with each other. The solo/spec-only testbench generator
  fixes this.
- Today's `lint_agent.py` has 8 checks, but 5 of them (L-001, L-002, L-006,
  L-007, L-008) depend on a `source: "module.port"` field on each manifest
  port that **no generator currently populates** — confirmed zero manifests
  anywhere have it. Those checks silently no-op. Real Verilator linting plus
  fixing this data gap are both needed.
- Today's retry loop re-prompts an LLM hoping for a different sample. The
  feedback agent instead patches the *generator script* — a real, durable
  fix, and it applies uniformly once init_fsm/config_regs are scripts too.

## Step-by-step build order

### Step 0 — Shared infrastructure (build once, used by all 4 phases)
1. **Manifest schema v2**: add a `source` field (`"module_name.port_name"`)
   to every consumer-side port in every generator's manifest output. This
   unblocks both real lint checks and the final assembly script. Touch all
   11 generators' `generate_manifest()` methods.
2. **Verilator wrapper** (`Frontend2/scripts/verilator_lint.py`): shells
   out to `verilator --lint-only -sv <file>.sv`, parses warnings/errors into
   the same report shape the pipelines already expect (so downstream code
   doesn't need to change), non-zero exit → lint failure.
3. **Spec-only testbench generator base** (`Frontend2/scripts/Phase1/tb_generator.py`)
   — built. Covers init_fsm/config_regs/wb_port, verified against the golden
   spec. Details:
   given just the module name + spec JSON, emit a testbench. Refactor the
   existing `generate_*_tb` methods out of `phase1_validation_agent.py` and
   strip the RTL-reading step — recompute expected values (e.g. MR0/MR2
   encodings) from the spec directly instead of regexing the generated file.
4. **Feedback agent core** (`Frontend2/scripts/feedback_agent.py`): given a
   structured failure (check id, expected, actual, owning module + function
   anchor) and that module's generator source file, produces a scoped patch
   to the implicated function only — not a full-file rewrite. This is the
   piece with no prior art in `Frontend/`; needs the most design care.
5. **Manifest → connectivity graph helper**: once step 1 lands, a small
   utility that resolves `source` references across all manifests in a
   directory — reused by both the real lint checks and the final assembly
   agent.

### Step 1 — Convert the remaining LLM agents to scripts
Per `[[rtl-agent-determinism-ranking]]`, in order of ease:
1. `config_regs` (~95% deterministic) — the "hard naming contract" the
   current prompt already enforces becomes literal template code.
2. `init_fsm` (~90%) — the fixed 8-state JEDEC sequence becomes a direct
   template; no LLM call needed.
3. `refresh_ctrl` (~80%) — port the counter/threshold logic; more structural
   judgment was going into the old prompt, so budget more time to get the
   force-refresh/starve-flag logic right without an LLM checking your work.
4. `bank_tracker` (~55%, most complex — 8 replicated per-bank FSMs, tFAW
   window, cross-bank permission logic) — convert last, once the pattern
   from the other 3 is proven, and expect this one to take real design work,
   not just templating.

### Step 2 — Phase 1 (reference implementation of the new pattern) ✅ DONE
Build the full loop for Phase 1 first, since it's the smallest phase (3
modules) and proves the pattern before replicating it 3 more times:
1. Copy `wb_port_agent.py` into `Frontend2/scripts/` as-is (already a script).
2. Bring over the newly-scripted `init_fsm`/`config_regs` from Step 1.
3. Wire: gen scripts → `verilator_lint` → (`tb_generator` in parallel)
   → simulator script (reuse `cadence_ssh_agent.py`'s transport, or evaluate
   swapping to local Icarus/Verilator simulation now that lint is already
   local+fast) → on failure, `feedback_agent` patches the specific script →
   re-run.
4. New `phase1_pipeline.py` (LangGraph) reflecting this graph shape.

Real-verified against Olympus: Verilator lint PASS, Xcelium sim PASS
(init_fsm 11/11, config_regs 36/36, wb_port 4/4).

### Step 3 — Phase 2, 3, 4
Same pattern, in order. Phase 3 and 4 are simpler since every module there
is already deterministic — no LLM-to-script conversion needed, so those
phases are mostly "wire the new validation stages," not "build new
generators."

**Phase 2 ✅ DONE.** Built `Frontend2/scripts/Phase2/tb_generator.py`
(spec-only, one method per module — addr_decoder/calibration had none
before; refresh_ctrl/bank_tracker's cfg_t*_nCK are runtime inputs so the TB
drives small directed constants, not spec-scale ones) and
`phase2_pipeline.py` (same graph shape as Phase 1, with a `gen_testbenches`
node since none of the 4 generators write their own TB). Real-verified
against Olympus: Verilator lint PASS (2 harmless UNUSED warnings — see
open items below), Xcelium sim PASS — addr_decoder 24/24, calibration
8/8, refresh_ctrl 10/10, bank_tracker 31/31. One real bug found and fixed
in `tb_generator.py`'s bank_tracker FAW-window test: `do_act()` spans 2
clock edges per call (assert, then deassert-on-next-edge), so the wait-time
arithmetic for the tFAW-window-reopens check needs `tFAW - 6` (3 subsequent
ACTs × 2 edges), not `tFAW - 3` — and tFAW itself needed raising from 6 to
10 so the oldest FAW slot doesn't fully drain before the 4th ACT lands.

**Phase 3 ✅ DONE.** Built `phase3_pipeline.py` — no `gen_testbenches`
node, since each of the 3 generators (`cmd_queue_gen.py`, `scheduler_gen.py`,
`cmd_gen_gen.py`) already writes its own `generate_tb()` output from its
own `run()`; nothing else writes to that path, so there's no race to guard
against. Real-verified against Olympus: Verilator lint PASS (1 harmless
UNUSED warning on `cmd_gen`'s `sched_we`), Xcelium sim PASS — cmd_queue
32/32, scheduler 31/31, cmd_gen 36/36. Two real bugs found and fixed:
1. `_parse_xrun_output()` in `phase3_pipeline.py` only recognized Phase
   1/2's `tb_generator.py` self-report convention (`[PASS]`/`[FAIL]`/
   `ALL N TESTS PASSED`). Phase 3's own `generate_tb()` methods (ported
   as-is, untouched this session) use a different convention
   (`V T01 PASS:`/`X T01 FAIL:`/`== N/M passed ==`) — cmd_queue and
   scheduler were genuinely passing 32/32 and 31/31 on the very first run
   but got reported as sim-gate failures (0 passed, 0 failed parsed) until
   the parser was taught to recognize both conventions.
2. `cmd_gen_gen.py`'s `generate_tb()` `issue()` task had a genuine
   off-by-one: it waited one extra `@(posedge clk)` after deasserting
   `sched_valid` before any check ran. Since `ddr_cmd` is a 1-cycle strobe
   (reverts to NOP the very next cycle after `sched_valid` deasserts, not
   held), every check read the DUT one cycle after its output had already
   reverted to NOP — symptom was every failing check reporting the
   identical `ddr=0111` (NOP) regardless of which command was actually
   issued. Fixed by removing the extra edge so checks land immediately
   after the sampling edge, matching the convention used everywhere else
   in this codebase (config_regs_tb, bank_tracker_tb's `do_act()`, etc.).

**Phase 4 ✅ DONE.** Built `phase4_pipeline.py` — same no-`gen_testbenches`
shape as Phase 3, since `data_path_gen.py`'s own `run()` already writes its
own testbench (note: via `generate_testbench()`, not `generate_tb()` like
Phase 3's generators — different method name, same self-contained pattern,
matters only if you're grepping). Real-verified against Olympus: Verilator
lint PASS (1 harmless UNUSED warning on `ddr_dqs_i`, an unmodeled PHY
signal), Xcelium sim PASS — data_path 26/26. Three real bugs found and
fixed, none touched this session before now:
1. `generate_testbench()` had a genuine SystemVerilog syntax error: inside
   a `begin...end` block it declared `logic saw_oe; saw_oe = 0;` (decl +
   statement on one line) immediately followed by another `logic [...]
   captured_dq;` declaration — Xcelium enforces declarations-before-
   statements within a block, so a decl appearing after a statement is a
   parse error (`*E,BADDCL`). Fixed by hoisting the declaration before the
   statement; `captured_dq` itself was also dead (declared, never read or
   written) and was dropped.
2. Every read-path check (Sections C, E, G, H2) shared a timing bug:
   `ddr_dq_i` was driven with the target data *after* waiting `CL_CTRL + 1`
   edges from the read command, but the RTL's read-capture FSM actually
   samples `ddr_dq_i` `CL_CTRL` edges after the command — one edge too
   early relative to when the TB set the data, so the FIFO always captured
   the reset default (0) instead of the injected value. Compounding this,
   `rd_rsp_valid` has no backpressure (the FIFO auto-pops every cycle it's
   non-empty), so the valid pulse is transient and had already drained by
   the time each check ran 5+ cycles later — `rd_rsp_valid` read back 0 and
   `rd_rsp_data`/`rd_rsp_aux` read back X (never-written FIFO slots).
   Rather than hand-computing the exact capture edge again (fragile — that
   exact class of arithmetic is what caused the bug), fixed by adding two
   helper tasks: `issue_rd_cmd_data()` holds `ddr_dq_i` stable across the
   whole transaction so timing can't matter, and `wait_rd_rsp()` polls for
   the valid pulse instead of guessing a fixed delay. All four sections
   rewritten to use them.
3. `FIFO_PTR_W = max(1, RD_FIFO_DEPTH.bit_length())` — same root-cause bug
   class as wb_port's `TAG_PTR_WIDTH` (Phase 1): the value doubles as both
   the wraparound-safe pointer's extra-bit width (wants `index_width+1`,
   which `N.bit_length()` happens to give) and the array index width for
   `wr_buf`/`rd_fifo` (wants exactly `index_width`) — for `RD_FIFO_DEPTH=16`
   that's 5 either way, but indexing a 16-entry array only needs 4 bits, so
   `wr_wptr[4:0]`/`rd_wptr[4:0]` can reach 16–31 once a pointer has counted
   past 16 total pushes since reset, indexing out of bounds. Verilator's
   `%Warning-WIDTH` caught it (6 instances); no behavioral test pushed past
   16 total entries in one reset epoch so simulation didn't. Fixed with
   `(RD_FIFO_DEPTH - 1).bit_length()`, identical fix shape to wb_port's.

### Step 4 — Integration/Assembly Script
Once all 4 phases populate `source` annotations consistently: read every
manifest across all phases, instantiate every module under one top-level
`ddr3_controller.sv`, wire consumer ports to producer ports per `source`,
promote any unmatched port to the top-level port list. Deterministic —
it's a pure function of the manifests, not an LLM call.

### Step 5 — Full pipeline verification
Run all 4 phases end-to-end against the existing golden spec
(`Spec/llmmc_microarchitecturespec_filled.json`), confirm the assembled
top-level module lints clean and the full behavioral testbench suite passes,
then re-run against a few edge-of-range Tier1/2/3 spec variations (via
`microarch_compiler.py`) to sanity-check the newly-converted generators
outside the one golden config they were built against.

## Open design questions to resolve as we build (not blocking Step 0)
- Simulator script: keep Cadence Xcelium via SSH (current), or evaluate
  Icarus/Verilator simulation now that lint is local — affects turnaround
  time significantly during development.
- Feedback agent: does it auto-apply patches and re-run, or propose a diff
  for review before it lands? (Bears on blast radius — it's editing shared
  generator source, not one throwaway RTL file.)
