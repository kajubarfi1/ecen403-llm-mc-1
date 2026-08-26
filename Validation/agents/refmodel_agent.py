"""
Reference Model Agent
======================
Reads the microarchitecture spec JSON and a requested validation scope,
then uses an LLM to generate a Python reference model with self-test.

Scopes supported: config_regs, wb_port, init_sequence, addr_decoder, refresh_ctrl
(more can be added by extending SCOPE_PROMPTS)

Usage:
    python3 refmodel_agent.py \
        --spec llmmc_microarchitecturespec_filled.json \
        --scope config_regs \
        --output-dir ./validation_output \
        --api-key YOUR_KEY

Author: Validation Subsystem — Agent 3a (Reference Model)
"""

import argparse
import json
import os
import sys
import requests
import re
import subprocess
from typing import Any, Dict, List
from llm_client import call_llm, strip_fences


# =============================================================================
# Spec Helpers
# =============================================================================

def load_spec(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def extract_context(spec: dict, scope: str) -> dict:
    """Pull only the spec sections this scope needs."""
    ctx = {
        "scope": scope,
        "implementation_targets": spec.get("implementation_targets", {}),
    }

    if scope == "config_regs":
        ctx["csr_register_map"] = spec.get("csr_register_map", {})
        ctx["controller_architecture"] = spec.get("controller_architecture", {})

    elif scope == "wb_port":
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["controller_architecture"] = spec.get("controller_architecture", {})
        ctx["memory_geometry"] = spec.get("memory_geometry", {})

    elif scope == "init_sequence":
        ctx["initialization_sequence"] = spec.get("initialization_sequence", {})
        ctx["timing_model"] = spec.get("timing_model", {})
        ctx["clocking_model"] = spec.get("clocking_model", {})

    elif scope == "addr_decoder":
        ctx["memory_geometry"] = spec.get("memory_geometry", {})
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["data_path_mapping"] = spec.get("data_path_mapping", {})

    elif scope == "refresh_ctrl":
        ctx["controller_architecture"] = spec.get("controller_architecture", {})
        ctx["timing_model"] = spec.get("timing_model", {})

    elif scope == "path_backpressure":
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["controller_architecture"] = spec.get("controller_architecture", {})
        ctx["memory_geometry"] = spec.get("memory_geometry", {})

    elif scope.startswith("path_"):
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["controller_architecture"] = spec.get("controller_architecture", {})
        ctx["memory_geometry"] = spec.get("memory_geometry", {})
        ctx["timing_model"] = spec.get("timing_model", {})

    return ctx


# =============================================================================
# System Prompt
# =============================================================================

SYSTEM_PROMPT = """You are a hardware verification engineer. You write Python reference models for DDR3 memory controller blocks.

Rules:
- Derive behavior ONLY from the spec provided. Never guess.
- Output a single complete Python file. No placeholders, no TODOs, no "..." ellipsis.
- Include all imports (json, os at minimum).
- The file must be directly runnable: python3 <file>.py
- Include a run_self_test() that prints per-test PASS/FAIL and ends with a summary line containing exactly "ALL TESTS PASSED" if all pass.
- The __main__ block runs self-test only. Vector generation is handled by a separate agent.
- Use descriptive variable names and comments referencing spec fields."""


# =============================================================================
# Scope-Specific Prompts
# =============================================================================

def build_prompt(scope: str, ctx: dict, spec_path: str = None) -> str:
    spec_json = json.dumps(ctx, indent=2)

    # Try loading generated prompt file (from path_scope_generator)
    if spec_path and scope.startswith("path_") and scope != "path_backpressure":
        gen_prompt = os.path.join(
            os.path.dirname(spec_path), "..", "scopes", scope, "generated", "refmodel_prompt.txt"
        )
        if os.path.exists(gen_prompt):
            with open(gen_prompt) as f:
                template = f.read()
            return template.replace("{spec_json}", spec_json)

    if scope == "config_regs":
        return f"""Generate a Python reference model for the CSR register block of a DDR3 memory controller.

SPEC (CSR register map and controller config):
{spec_json}

Build a ConfigRegsModel class that models all 11 registers exactly as defined in csr_register_map.

=== DATA STRUCTURE ===

Store registers as a dict keyed by offset (integer). Each register contains a list of
field dicts. Each field dict has keys: "name", "hi", "lo", "access", "reset", "value".
Parse the spec's "bits" string (e.g. "15:0" or "5") into integer hi/lo.

On reset(), set every field's "value" to its "reset".

To assemble a 32-bit register value from fields:
    val = 0
    for f in fields:
        mask = (1 << (f["hi"] - f["lo"] + 1)) - 1
        val |= (f["value"] & mask) << f["lo"]

=== MANDATORY write() IMPLEMENTATION ===

YOU MUST USE THIS EXACT LOGIC for the write() method. Do NOT deviate.
This is the #1 source of bugs — copy this pseudocode precisely:

    def write(self, addr, data):
        data = data & 0xFFFFFFFF
        if addr not in self._regs:
            return False  # unmapped — write silently dropped

        for f in self._regs[addr]["fields"]:
            width = f["hi"] - f["lo"] + 1
            fmask = (1 << width) - 1
            write_bits = (data >> f["lo"]) & fmask

            if f["access"] == "RO":
                pass  # IGNORE — never modified by bus write
            elif f["access"] == "RW":
                f["value"] = write_bits
            elif f["access"] == "RW1C":
                f["value"] = f["value"] & (~write_bits & fmask)
            elif f["access"] == "WO":
                f["value"] = 0  # accept write side-effect, then self-clear
        return True

CRITICAL POINTS about write():
- RO fields are SKIPPED (pass). They are NEVER modified by bus writes. Only inject_status() can change them.
- RW1C: the operation is  current_value AND (NOT write_bits). Writing 1 CLEARS the bit. Writing 0 leaves it unchanged.
- WO: the field is immediately cleared to 0 after the write (self-clear). It always reads as 0.
- A single register (e.g. ERROR_STATUS at 0x1C) contains a MIX of RO and RW1C fields.
  You MUST handle each field independently — do NOT apply one access type to the whole register.

=== MANDATORY read() IMPLEMENTATION ===

    def read(self, addr):
        if addr not in self._regs:
            return (True, 0xDEADBEEF)  # unmapped — RTL returns 0xDEADBEEF, bus acks
        val = 0
        for f in self._regs[addr]["fields"]:
            if f["access"] == "WO":
                continue  # WO fields always read as 0
            mask = (1 << (f["hi"] - f["lo"] + 1)) - 1
            val |= (f["value"] & mask) << f["lo"]
        return (True, val & 0xFFFFFFFF)

=== inject_status() ===

    def inject_status(self, reg_name, field_name, value):
        # Look up register by name, find the field, set f["value"] = value & fmask
        # This is the ONLY way to change RO fields (simulates hardware input).

=== WORKED EXAMPLE — ERROR_STATUS (offset 0x1C) ===

ERROR_STATUS fields: ecc_ce_count(15:0, RO), ecc_ue_flag(16, RW1C), ref_starve_flag(17, RW1C), init_fail_flag(18, RW1C), bist_fail_addr(31:19, RO).

Scenario A: All fields 0 at reset. write(0x1C, 0xFFFFFFFF). Then read(0x1C).
  - ecc_ce_count (RO): SKIPPED by write. Stays 0.
  - ecc_ue_flag (RW1C): value=0, write_bits=1 → 0 & ~1 = 0. Stays 0.
  - ref_starve_flag (RW1C): same → 0.
  - init_fail_flag (RW1C): same → 0.
  - bist_fail_addr (RO): SKIPPED. Stays 0.
  → read returns 0x00000000. NOT 0x0000FFFF, NOT 0xFFF80000.

Scenario B: inject all 3 flags=1. read → 0x00070000.
Scenario C: write(0x1C, 0x00010000) → clears ecc_ue only → read 0x00060000.

=== MANDATORY SELF-TESTS (run_self_test) ===

run_self_test() must verify ALL of the following. Do NOT skip or simplify any test.
Each test must print PASS or FAIL and the test number.

1. All 11 registers read back their correct reset values
2. Write 0xFFFFFFFF to CTRL_STATUS (all RO) — read back must be 0x00000000
3. Write 0xFFFFFFFF to TIMING_0 (all RW) — read back must be 0xFFFFFFFF
4. Write 0x12345678 to TIMING_0, read back 0x12345678, then reset, read back reset value
5. Inject ecc_ue_flag=1, ref_starve_flag=1, init_fail_flag=1 into ERROR_STATUS, read back, verify bits 18:16 = 0x00070000
6. After test 5: write 0x00010000 to ERROR_STATUS (RW1C clear ecc_ue only), read back must be 0x00060000
7. Write to CTRL_CONFIG with bist_start=1 (bit 5), read back — bit 5 must be 0 (WO self-clear)
8. Write 0xFFFFFFFF to BIST_ADDR_START — bits 31:29 are reserved RO, must read back 0x1FFFFFFF
9. Read unmapped address 0x2C — must return (True, 0xDEADBEEF)
10. Write unmapped address 0x30 — must return False (write dropped)
11. *** CRITICAL *** Reset, then write(0x1C, 0xFFFFFFFF), then read(0x1C) — MUST return 0x00000000
    (If your model returns ANYTHING other than 0, your write() is broken. Go re-read the
     mandatory write() implementation above and copy it exactly.)
12. Reset, inject ecc_ue_flag=1, then write(0x1C, 0xFFFFFFFF), then read(0x1C) — MUST return 0x00000000
    (RW1C fields had 1, write-1 clears them to 0. RO fields stay 0.)
13. Walking-ones on ERROR_STATUS (0x1C): Reset, then for EACH of bit 0, bit 8, bit 15, bit 19, bit 31:
    write(0x1C, 1<<N), then read(0x1C) — ALL must return 0x00000000.
    These bits land in RO fields (ecc_ce_count, bist_fail_addr), so writes are ignored.
    If ANY returns non-zero, your write() is using the REGISTER-level access type instead of
    the PER-FIELD access type. Fix it: iterate fields, check each field's access independently.
14. Walking-ones on CTRL_CONFIG (0x04): Reset, write(0x04, 1<<0), read(0x04) — must return 0x00000001
    (sched_policy is RW). Then write(0x04, 1<<5), read(0x04) — must return 0x00000000
    (bist_start is WO, self-clears). Then write(0x04, 1<<8), read(0x04) — must return 0x00000000
    (reserved is RO, ignored).

Print exactly "ALL TESTS PASSED" if all 14 tests pass."""

    elif scope == "wb_port":
        return f"""Generate a Python reference model for the Wishbone Port Interface (wb_port) of a DDR3 memory controller.

SPEC (host interface config):
{spec_json}

The wb_port translates pipelined Wishbone bus transactions into internal request descriptors for the command queue.

Build a WishbonePortModel class that models the PROTOCOL RULES, not cycle-accurate timing.

Interface (from block diagram):
  Host side in:  wb_cyc_i, wb_stb_i, wb_we_i, wb_adr_i[28:0], wb_dat_i[31:0], wb_sel_i[3:0], wb_bte_i[1:0], wb_cti_i[2:0]
  Host side out: wb_ack_o, wb_dat_o[31:0], wb_stall_o, wb_err_o
  Queue side out: req_valid, req_we, req_addr[28:0], req_wdata[31:0], req_wmask[3:0], req_aux[3:0]
  Queue side in:  req_ready
  Response in:    rsp_valid, rsp_rdata[31:0], rsp_aux[3:0]

Model these protocol rules:
1. Transaction acceptance: when cyc=1 and stb=1, a transaction is presented.
   - If req_ready=1 (queue not full): accept it, assert req_valid with req_addr=wb_adr_i, req_we=wb_we_i, req_wdata=wb_dat_i, req_wmask=wb_sel_i
   - If req_ready=0: assert wb_stall_o, do NOT assert req_valid
2. Write transactions: req_we=1, data flows host->queue. Ack immediately.
3. Read transactions: req_we=0, response comes back via complete_read(). Read data stored internally until read back.
4. Backpressure: wb_stall_o = NOT req_ready (when stb is active)
5. Error: wb_err_o for invalid conditions (optional, can always be 0 for basic model)
6. Burst support: wb_cti_i indicates burst type (000=classic, 010=incrementing, 111=end of burst)
   - For incrementing burst, address increments by 4 bytes each beat
   - max_burst_length = 8 from spec

CRITICAL — MANDATORY METHOD SIGNATURES (the vector generator depends on these exact names and signatures):

    def reset(self):
        '''Reset all internal state.'''

    def present_transaction(self, cyc: int, stb: int, we: int, adr: int,
                           dat: int, sel: int, cti: int, bte: int,
                           req_ready: int) -> dict:
        '''Present one Wishbone bus cycle.
        Returns dict with keys: wb_ack_o, wb_dat_o, wb_stall_o, wb_err_o,
                                req_valid, req_we, req_addr, req_wdata, req_wmask, req_aux'''

    def complete_read(self, rsp_valid: int, rsp_rdata: int, rsp_aux: int) -> dict:
        '''Deliver read response from downstream. Returns dict with keys: wb_ack_o, wb_dat_o'''

    def get_pending_read_count(self) -> int:
        '''Return number of outstanding read requests awaiting response.'''

Do NOT rename these methods or change their signatures. The vector generation executor calls them by exact name.

run_self_test() must verify:
1. Single write: present write transaction with req_ready=1, verify req_valid=1, req_addr matches, req_wdata matches, req_wmask matches
2. Single read: present read transaction, verify req_valid=1, req_we=0. Then complete_read with data, verify wb_dat_o matches
3. Backpressure: present transaction with req_ready=0, verify wb_stall_o=1 and req_valid=0
4. Burst write: present 4 incrementing writes (cti=010 then 111), verify addresses increment by 4
5. No transaction: cyc=0, verify req_valid=0 and wb_stall_o=0
6. Stb without cyc: cyc=0, stb=1, verify req_valid=0 (invalid bus state)
7. get_pending_read_count: present 2 reads, verify count=2, complete both, verify count=0

Print exactly "ALL TESTS PASSED" if all pass."""

    elif scope == "init_sequence":
        return f"""Generate a Python reference model for the Init/Reset FSM (init_fsm) of a DDR3 memory controller.

SPEC (initialization sequence and timing):
{spec_json}

The init_fsm runs the JEDEC DDR3 initialization sequence. This model is a SEQUENCE CHECKER — it watches a log of output events and verifies ORDERING and MINIMUM TIMING constraints from the JEDEC spec, NOT exact cycle numbers.

Build an InitFsmChecker class that validates a recorded sequence of init FSM events.

The init FSM outputs: init_done, init_fail, init_cmd_valid, init_cmd[3:0], init_addr[14:0], init_bank[2:0], init_cke, init_reset_n

JEDEC MINIMUM TIMING CONSTRAINTS (all in controller cycles at 5ns, 4:1 DDR ratio):
- Reset hold: >= 200us = 40000 controller cycles (MINIMUM, RTL may hold longer)
- CKE delay after reset release: >= 500us = 100000 controller cycles (MINIMUM)
- tXPR after CKE: >= 136 nCK = 34 controller cycles (MINIMUM)
- tMRD between MRS commands: >= 4 nCK = 1 controller cycle (MINIMUM)
- tZQinit after ZQCL: >= 512 nCK = 128 controller cycles (MINIMUM)

CRITICAL DESIGN PRINCIPLE: JEDEC timing values are MINIMUMS. The RTL is allowed to take
MORE cycles than the minimum. The reference model must check ">=" not "==".
An RTL that deasserts reset at cycle 40005 instead of 40000 is CORRECT.
An RTL that deasserts reset at cycle 39999 is WRONG.

Expected ORDERING (from spec, order is strict):
  1. init_reset_n = 0 at start
  2. init_reset_n = 1 (after >= 40000 cycles)
  3. init_cke = 1 (after >= 100000 cycles from reset release)
  4. Wait >= tXPR (34 controller cycles) after CKE rise
  5. MRS to MR2: init_cmd_valid=1, init_bank=3'd2
  6. MRS to MR3: init_cmd_valid=1, init_bank=3'd3
  7. MRS to MR1: init_cmd_valid=1, init_bank=3'd1
  8. MRS to MR0: init_cmd_valid=1, init_bank=3'd0 (DLL reset)
  9. ZQCL command: init_cmd_valid=1
  10. init_done = 1 (after >= tZQinit from ZQCL)

Event log format (list of dicts):
  {{"cycle": int, "signal": str, "value": int}}
  e.g. {{"cycle": 0, "signal": "init_reset_n", "value": 0}}
       {{"cycle": 40003, "signal": "init_reset_n", "value": 1}}   # 40003 >= 40000, OK
       {{"cycle": 140005, "signal": "init_cke", "value": 1}}
       {{"cycle": 140040, "signal": "mrs", "value": 2}}  # ba=2 means MR2
       ...

Methods:
- check_sequence(event_log: list[dict]) -> dict with "passed": bool, "violations": list[str]
  Checks:
  a) init_reset_n starts low (value=0) at or before cycle 0
  b) init_reset_n stays low for >= 40000 cycles (reset_rise_cycle >= 40000)
  c) init_cke goes high >= 100000 cycles AFTER init_reset_n rises (cke_rise_cycle >= reset_rise_cycle + 100000)
  d) First MRS (MR2) occurs >= 34 controller cycles AFTER cke_rise_cycle
  e) MRS ORDER is MR2(ba=2) -> MR3(ba=3) -> MR1(ba=1) -> MR0(ba=0) — strict ordering
  f) Each MRS occurs AFTER the previous one (cycle ordering, not exact spacing)
  g) ZQCL follows MR0
  h) init_done asserts >= 128 controller cycles AFTER ZQCL
  i) init_fail never asserts (value must be 0 in all events)

  TOLERANCE: Allow up to 10 extra controller cycles on each minimum timing boundary.
  The model checks "actual >= minimum" not "actual == exact".

- generate_golden_log() -> list[dict]
  Produce a known-good event log with timing at the MINIMUMS (exact boundary).
  This is used for self-test only.

- get_timing_constraints() -> dict
  Return the minimum cycle counts: {{"reset_hold_min": 40000, "cke_delay_min": 100000,
  "txpr_min": 34, "tzqinit_min": 128}}

run_self_test() must verify:
1. Golden log (at exact minimums) passes check_sequence with no violations
2. Golden log with +5 extra cycles on each phase also passes (RTL taking slightly longer is OK)
3. Swapped MR order (MR3 before MR2) is caught as violation
4. Short reset hold (1000 cycles instead of 40000) is caught
5. Short CKE delay (50000 instead of 100000) is caught
6. Missing ZQCL is caught
7. init_done before ZQCL+tZQinit is caught
8. init_fail in a correct sequence is caught as violation
9. tXPR violation (MRS too soon after CKE) is caught

Print exactly "ALL TESTS PASSED" if all pass."""

    elif scope == "path_backpressure":
        return f"""Generate a Python reference model for the backpressure path of a DDR3 memory controller.

This models the INTEGRATION between two blocks:
  - wb_port: accepts Wishbone transactions, generates internal requests
  - cmd_queue: stores up to 16 pending requests, signals backpressure when full

SPEC:
{spec_json}

Build a BackpressurePathModel class that models the two-block interaction:

1. The cmd_queue has a fixed depth of 16 entries.
2. When a valid Wishbone write/read is presented (cyc=1, stb=1) and the queue is not full:
   - The request is accepted (enqueued)
   - wb_ack_o = 1, wb_stall_o = 0
   - queue_count increments
3. When the queue is full (queue_count == 16):
   - wb_stall_o = 1, wb_ack_o = 0
   - The request is NOT accepted
   - The host must hold the transaction until stall deasserts
4. When deq_grant is pulsed with deq_idx=N:
   - That entry is removed, queue_count decrements
   - If queue was full, enq_ready reasserts next cycle
5. Each enqueued entry records: row, col, bank (decoded from address), we, aux

Address decode (inline, row-bank-column mapping for 29-bit byte address):
  - Bits [3:0]: byte offset (ignored)
  - Bits [6:4]: bank[2:0]
  - Bits [16:7]: col[9:0]
  - Bits [28:17]: row[14:0]

MANDATORY METHOD SIGNATURES:

    def reset(self):
        # Reset queue to empty, all outputs deasserted.

    def enqueue(self, cyc: int, stb: int, we: int, addr: int,
                dat: int, sel: int) -> dict:
        # Present a Wishbone transaction.
        # Returns dict with keys: wb_ack_o, wb_stall_o, wb_err_o,
        #                         req_valid, queue_count, queue_full

    def dequeue(self, idx: int) -> dict:
        # Remove entry at index idx.
        # Returns dict with keys: queue_count, queue_full, enq_ready

    def get_entry(self, idx: int) -> dict:
        # Return entry at index idx.
        # Returns dict with keys: valid, we, row, col, bank, aux

    def get_queue_count(self) -> int:
        # Return current occupancy.

    def is_full(self) -> bool:
        # Return True if queue_count == 16.

run_self_test() must verify:
1. After reset: queue_count=0, queue_full=False
2. Single enqueue: present write, verify ack=1, stall=0, queue_count=1
3. Fill to 16: enqueue 16 entries, verify queue_count=16, queue_full=True
4. Stall on 17th: present transaction when full, verify stall=1, ack=0
5. Dequeue one: dequeue entry 0, verify queue_count=15, queue_full=False
6. Accept after dequeue: present transaction, verify accepted
7. Address decode: enqueue addr=0x00020070, verify row, col, bank fields
8. Entry integrity: enqueue 4 distinct addresses, verify get_entry
9. Drain all: dequeue all, verify queue_count=0
10. Re-fill after drain: enqueue 8 entries, verify queue_count=8

Print exactly "ALL TESTS PASSED" if all pass."""

    else:
        return f"""Generate a Python reference model for the {scope} scope of a DDR3 memory controller.

SPEC:
{spec_json}

Include a model class, run_self_test() with "ALL TESTS PASSED" on success, and a runnable __main__ block.
No vector generation — just the model and self-test."""


# =============================================================================
# Agent
# =============================================================================

class RefModelAgent:
    """Generates and validates a Python reference model for one scope."""

    def __init__(self, spec_path: str, scope: str, output_dir: str):
        self.spec_path = spec_path
        self.scope = scope
        self.output_dir = output_dir
        self.spec = load_spec(spec_path)
        self.ctx = extract_context(self.spec, scope)
        self.refmodel_path = None
        os.makedirs(output_dir, exist_ok=True)

    def log(self, msg: str):
        print(f"[RefModelAgent][{self.scope}] {msg}")

    def generate(self) -> str:
        # Ask the LLM to produce the reference model. Retries on syntax errors.
        import ast as _ast
        self.log("Generating reference model...")
        prompt = build_prompt(self.scope, self.ctx, self.spec_path)
        max_attempts = 3
        last_err = None
        code = ""
        for attempt in range(1, max_attempts + 1):
            messages = [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
            ]
            if attempt > 1 and last_err:
                messages.append({
                    "role": "user",
                    "content": f"Previous attempt produced this Python syntax error:\nline {last_err}\n\nReturn the COMPLETE corrected file. Make sure every line is syntactically valid Python and the response is not truncated. Output the full module from top to bottom, including the if __name__ == '__main__' block."
                })
            raw = call_llm(messages, max_tokens=16000)
            code = strip_fences(raw)
            try:
                _ast.parse(code)
                self.refmodel_path = os.path.join(self.output_dir, f"{self.scope}_refmodel.py")
                with open(self.refmodel_path, "w", encoding="utf-8") as f:
                    f.write(code)
                self.log(f"Saved \u2192 {self.refmodel_path}")
                if attempt > 1:
                    self.log(f"(succeeded on attempt {attempt}/{max_attempts})")
                return self.refmodel_path
            except SyntaxError as e:
                last_err = f"{e.lineno}: {e.msg}"
                self.log(f"Attempt {attempt}/{max_attempts}: syntax error ({last_err}), retrying...")
        # All attempts failed - write the last broken version for inspection
        self.refmodel_path = os.path.join(self.output_dir, f"{self.scope}_refmodel.py")
        with open(self.refmodel_path, "w", encoding="utf-8") as f:
            f.write(code)
        self.log(f"All {max_attempts} attempts produced syntax errors. Last: {last_err}")
        return self.refmodel_path
        #ensure self-test entry-point exists
        with open(self.refmodel_path, "r") as _rf:
            _refcontent = _rf.read()
        if 'if __name__ == "__main__"' not in _refcontent:
            if 'def run_self_test' in _refcontent:
                with open(self.refmodel_path, "a") as _rf:
                    _rf.write('\n\nif __name__ == "__main__":\n    run_self_test()\n')
                self.log("Auto-appended __main__ block (was missing)")


    def validate(self) -> bool:
        """Run the model's self-test."""
        if not self.refmodel_path:
            self.log("ERROR: Nothing to validate")
            return False

        self.log("Running self-test...")
        abs_path = os.path.abspath(self.refmodel_path)
        try:
            result = subprocess.run(
                [sys.executable, abs_path],
                capture_output=True, text=True, timeout=30,
                cwd=os.path.dirname(abs_path)
            )
        except subprocess.TimeoutExpired:
            self.log("TIMEOUT: self-test took >30s")
            return False

        print(result.stdout)
        if result.stderr.strip():
            print(f"STDERR:\n{result.stderr}")

        passed = "ALL TESTS PASSED" in result.stdout
        if not passed:
            p_count = total = 0
            # Pattern A: "Tests run: N, Passed: P, Failed: F"
            m = re.search(r"Tests?\s+run:\s*(\d+)[^\d]*Passed:\s*(\d+)[^\d]*Failed:\s*(\d+)", result.stdout, re.IGNORECASE)
            if m:
                total = int(m.group(1))
                p_count = int(m.group(2))
            else:
                # Pattern B: "Passed: P, Failed: F" or "P passed ... F failed"
                m = re.search(r"(?:Passed:\s*)?(\d+)\s*(?:passed|tests? passed)[^\d]*(?:Failed:\s*)?(\d+)\s*(?:failed|tests? failed)", result.stdout, re.IGNORECASE)
                if m:
                    p_count = int(m.group(1))
                    f_count = int(m.group(2))
                    total = p_count + f_count
                else:
                    # Pattern C: "Results: P/T" or "N/M passed"
                    m2 = re.search(r"(?:Results?:\s*)?(\d+)[/\s]+(\d+)\s*(?:passed|tests?)?", result.stdout)
                    if m2:
                        p_count = int(m2.group(1))
                        total = int(m2.group(2))
            if total > 0 and p_count == total:
                self.log(f"Self-test PASSED ({p_count}/{total})")
                return True
            if total > 0:
                self.log(f"Self-test FAILED ({p_count}/{total} = {int(100*p_count/total)}%)")
            else:
                self.log("Self-test FAILED (no pass/fail count found)")
            return False
        self.log("Self-test PASSED")
        return passed

    def fix(self, max_attempts: int = 3) -> bool:
        """Send failures back to LLM for correction."""
        for attempt in range(1, max_attempts + 1):
            self.log(f"Fix attempt {attempt}/{max_attempts}...")

            with open(self.refmodel_path, "r") as f:
                current_code = f.read()

            abs_path = os.path.abspath(self.refmodel_path)
            try:
                result = subprocess.run(
                    [sys.executable, abs_path],
                    capture_output=True, text=True, timeout=30,
                    cwd=os.path.dirname(abs_path)
                )
                error_output = result.stdout + "\n" + result.stderr
            except subprocess.TimeoutExpired:
                error_output = "TIMEOUT: script took >30 seconds"
            except Exception as e:
                error_output = f"Exception: {e}"

            raw = call_llm([
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": f"""This reference model has failures. Fix it and return the COMPLETE corrected Python file.

CURRENT CODE:
```python
{current_code}
```

OUTPUT WHEN RUN:
```
{error_output}
```

SPEC CONTEXT:
{json.dumps(self.ctx, indent=2)}

Rules:
- Fix the logic so ALL tests pass. Do not remove tests — fix the model.
- Reset values must be computed from field-level reset_value, not from register-level reset_value.
- MANDATORY: The fixed model MUST preserve the existing class that has step() and reset() methods.
  DO NOT rename the class. DO NOT remove the step() method. DO NOT change its signature.
  The vector executor finds the model by searching for a class with both reset() and step() methods.
  If you rename the class or remove step(), vector generation will fail.
- MANDATORY: Keep the run_self_test() function and the if __name__ == "__main__" block.

DDR3 behavioral rules (use these to fix edge cases):
- Pipeline latency: scheduler decision at cycle N appears at cmd_gen output at cycle N+2 (2-stage pipe).
- Timing counters load the FULL cfg_t*_nCK value and decrement by 1 each cycle. Done when reaching 0, not 1.
- Refresh: when ref_ack is asserted, postpone_cnt MUST decrement by 1. If it was 3 before REF, it is 2 after.
- RFC timing: cnt_rfc loads cfg_tRFC_nCK (not tRFC-1). Decrements each cycle. refresh_in_progress while cnt_rfc > 0.
- Starve flag: ref_starve_flag asserts when postpone_cnt >= cfg_max_postpone (>=, not >).
- Bank tracker uses raw DDR cycle values directly without clock domain conversion.
- Return the entire file, not just the diff."""},
            ])

            code = strip_fences(raw)
            with open(self.refmodel_path, "w", encoding="utf-8") as f:
                f.write(code)

            if self.validate():
                return True

        self.log(f"Could not fix after {max_attempts} attempts")
        return False

    def run(self) -> dict:
        """Full pipeline: generate → validate → fix if needed."""
        report = {
            "scope": self.scope,
            "spec_source": self.spec_path,
            "status": "unknown",
            "refmodel_path": None,
            "errors": [],
        }

        try:
            self.generate()
            report["refmodel_path"] = self.refmodel_path

            if self.validate():
                report["status"] = "success"
            else:
                self.log("Attempting auto-fix...")
                if self.fix(max_attempts=3):
                    report["status"] = "success_after_fix"
                else:
                    report["status"] = "failed"
                    report["errors"].append("Self-test failed after 3 fix attempts")

        except Exception as e:
            report["status"] = "error"
            report["errors"].append(str(e))
            self.log(f"ERROR: {e}")

        # Save report
        report_path = os.path.join(self.output_dir, f"{self.scope}_refmodel_report.json")
        with open(report_path, "w") as f:
            json.dump(report, f, indent=2)

        self.log(f"Done. Status: {report['status']}")
        return report


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Reference Model Agent")
    parser.add_argument("--spec", required=True, help="Path to spec JSON")
    parser.add_argument("--scope", required=True,
                        choices=["config_regs", "wb_port", "init_sequence",
                                 "addr_decoder", "refresh_ctrl"],
                        help="Block to generate model for")
    parser.add_argument("--output-dir", default="./validation_output",
                        help="Output directory")
    parser.add_argument("--api-key", help="TAMU AI API key")
    parser.add_argument("--model", help="Model ID override")

    args = parser.parse_args()

    global API_KEY, MODEL_ID
    if args.api_key:
        API_KEY = args.api_key
    if args.model:
        MODEL_ID = args.model

    agent = RefModelAgent(args.spec, args.scope, args.output_dir)
    report = agent.run()

    print("\n" + "=" * 60)
    print(f"Scope:  {report['scope']}")
    print(f"Status: {report['status']}")
    print(f"Model:  {report.get('refmodel_path', 'N/A')}")
    if report["errors"]:
        for e in report["errors"]:
            print(f"Error:  {e}")
    print("=" * 60)


if __name__ == "__main__":
    main()