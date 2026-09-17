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
2. **Verilator wrapper** (`Frontend2/Agents/verilator_lint.py`): shells
   out to `verilator --lint-only -sv <file>.sv`, parses warnings/errors into
   the same report shape the pipelines already expect (so downstream code
   doesn't need to change), non-zero exit → lint failure.
3. **Spec-only testbench generator base** (`Frontend2/Agents/tb_generator.py`):
   given just the module name + spec JSON, emit a testbench. Refactor the
   existing `generate_*_tb` methods out of `phase1_validation_agent.py` and
   strip the RTL-reading step — recompute expected values (e.g. MR0/MR2
   encodings) from the spec directly instead of regexing the generated file.
4. **Feedback agent core** (`Frontend2/Agents/feedback_agent.py`): given a
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

### Step 2 — Phase 1 (reference implementation of the new pattern)
Build the full loop for Phase 1 first, since it's the smallest phase (3
modules) and proves the pattern before replicating it 3 more times:
1. Copy `wb_port_agent.py` into `Frontend2/Agents/` as-is (already a script).
2. Bring over the newly-scripted `init_fsm`/`config_regs` from Step 1.
3. Wire: gen scripts → `verilator_lint` → (`tb_generator` in parallel)
   → simulator script (reuse `cadence_ssh_agent.py`'s transport, or evaluate
   swapping to local Icarus/Verilator simulation now that lint is already
   local+fast) → on failure, `feedback_agent` patches the specific script →
   re-run.
4. New `phase1_pipeline.py` (LangGraph) reflecting this graph shape.

### Step 3 — Phase 2, 3, 4
Same pattern, in order. Phase 3 and 4 are simpler since every module there
is already deterministic — no LLM-to-script conversion needed, so those
phases are mostly "wire the new validation stages," not "build new
generators."

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
