"""
Vector Generator Agent (LLM-Driven)
=====================================
Uses an LLM to generate a test plan (stimulus sequences), then executes
that plan against the validated reference model to compute expected outputs.

The LLM decides WHAT to test. The reference model decides WHAT IS CORRECT.

Pipeline:
  1. LLM reads spec -> generates test plan (JSON list of operations)
  2. Agent executes test plan against reference model
  3. Agent records {stimulus, expected_output} as vectors
  4. Export to hex + JSON for testbench consumption

Usage:
    python3 vector_gen_agent.py \
        --scope config_regs \
        --model-dir ./validation_output \
        --output-dir ./validation_output \
        --spec ../Spec/llmmc_microarchitecturespec_filled.json \
        --api-key YOUR_KEY

Author: Validation Subsystem — Agent 3b (Vector Generator)
"""

import argparse
import importlib.util
import json
import os
import sys
import requests
from datetime import datetime
from typing import List, Dict, Any
from dotenv import load_dotenv
from llm_client import call_llm
load_dotenv()


# =============================================================================
# LLM Communication
# =============================================================================

def strip_fences(text: str) -> str:
    """Remove markdown code fences and any preamble/postamble."""
    text = text.strip()
    fence_markers = ["```json", "```python", "```"]
    for marker in fence_markers:
        start_idx = text.find(marker)
        if start_idx >= 0:
            code_start = start_idx + len(marker)
            end_idx = text.find("```", code_start)
            if end_idx >= 0:
                return text[code_start:end_idx].strip()
            else:
                return text[code_start:].strip()
    # No fences found — try to find a JSON array in the text
    bracket_start = text.find("[")
    if bracket_start >= 0:
        # Find the matching closing bracket
        depth = 0
        for i in range(bracket_start, len(text)):
            if text[i] == "[":
                depth += 1
            elif text[i] == "]":
                depth -= 1
                if depth == 0:
                    return text[bracket_start:i+1].strip()
    return text



# =============================================================================
# Helpers
# =============================================================================

def load_module_from_file(filepath: str, module_name: str):
    """Dynamically import a Python module from a file path."""
    spec = importlib.util.spec_from_file_location(module_name, filepath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load_spec(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def write_hex(vectors: list, filepath: str):
    with open(filepath, "w") as f:
        for v in vectors:
            f.write(v["hex_line"] + "\n")
    print(f"  Wrote {len(vectors)} vectors -> {filepath}")


def write_json(vectors: list, filepath: str, scope: str, fmt: str, spec_path: str):
    manifest = {
        "scope": scope,
        "generator": "vector_gen_agent_llm",
        "spec_source": os.path.basename(spec_path) if spec_path else "unknown",
        "generated_at": datetime.now().isoformat(),
        "vector_count": len(vectors),
        "hex_format": fmt,
        "vectors": vectors,
    }
    with open(filepath, "w") as f:
        json.dump(manifest, f, indent=2)
    print(f"  Wrote {len(vectors)} vectors -> {filepath}")


# =============================================================================
# Test Plan Prompts
# =============================================================================

SYSTEM_PROMPT = """You are a hardware verification engineer generating test stimulus for a DDR3 memory controller.

You output ONLY a JSON array of test operations. No explanation, no markdown, no commentary."""


def build_testplan_prompt(scope: str, spec_context: dict, spec_path: str = None) -> str:
    """Build the prompt that asks the LLM to generate a test plan."""

    # Try loading generated prompt file (from path_scope_generator)
    if spec_path and scope.startswith("path_") and scope != "path_backpressure":
        gen_prompt = os.path.join(
            os.path.dirname(spec_path), "..", "scopes", scope, "generated", "testplan_prompt.txt"
        )
        if os.path.exists(gen_prompt):
            with open(gen_prompt) as f:
                template = f.read()
            return template.replace("{spec_json}", json.dumps(spec_context, indent=2))

    if scope == "config_regs":
        return f"""Generate a comprehensive test plan for the CSR register block of a DDR3 memory controller.

SPEC (register map):
{json.dumps(spec_context, indent=2)}

Output a JSON array of test operations. Each operation is one of:
  {{"op": "reset"}}
  {{"op": "write", "addr": <int>, "data": <int>, "comment": "<why>"}}
  {{"op": "read", "addr": <int>, "comment": "<why>"}}
  {{"op": "inject", "reg": "<name>", "field": "<name>", "value": <int>, "comment": "<why>"}}

Address values are decimal integers (0 for 0x00, 4 for 0x04, 8 for 0x08, etc).
Data values are decimal integers.

=== CRITICAL: MIXED-ACCESS REGISTERS ===
Some registers contain fields with DIFFERENT access types. Each field is handled independently:
- ERROR_STATUS (addr 28): ecc_ce_count(15:0)=RO, flags(18:16)=RW1C, bist_fail_addr(31:19)=RO
  Writing to RO fields is IGNORED. Walking-ones on bits 0-15 or 19-31 will read back as 0.
- CTRL_STATUS (addr 0): ALL fields are RO — bus writes change nothing.
- CTRL_CONFIG (addr 4): bits 4:0=RW, bits 7:5=WO (self-clear to 0), bits 31:8=RO.

DO NOT use walking-ones or walking-zeros on ERROR_STATUS, CTRL_STATUS, or CTRL_CONFIG.
Only use walking patterns on ALL-RW registers like TIMING_0 (addr 8), TIMING_1 (addr 12),
TIMING_2 (addr 16), TIMING_3 (addr 20).

Generate at least 250 operations covering (this is IMPORTANT — do NOT generate fewer than 250):
1. Read all 11 registers after reset to verify reset values
2. Write 0xFFFFFFFF (4294967295) to every register, read back (tests RO masking, RW acceptance)
3. Write 0x00000000 to every register, read back
4. Walking-ones pattern (write 1<<N for N=0..31) on TIMING_0 (addr 8) — all-RW, safe
5. Walking-zeros pattern on TIMING_1 (addr 12) — all-RW, safe
6. RW1C testing: inject ecc_ue_flag, ref_starve_flag, init_fail_flag into ERROR_STATUS, read to confirm, then selectively clear each one
7. WO self-clear: write bist_start, force_refresh, force_self_ref bits in CTRL_CONFIG (addr 4), read back to verify they read as 0
8. Reserved bit masking: write 0xFFFFFFFF to registers with reserved fields (CTRL_CONFIG, REFRESH_CONFIG, BIST_CONFIG, BIST_ADDR_START), verify reserved bits read as 0
9. Boundary values for multi-bit fields: write max to tREFI_nCK (24-bit), write max to BIST address range
10. Unmapped address reads (addr 44, 48, 64, 255) — expect 0xDEADBEEF
11. Sequential write-read-write-read to same register
12. Cross-register independence: write to TIMING_0, verify TIMING_1 unchanged

Output ONLY the JSON array."""

    elif scope == "wb_port":
        return f"""Generate a comprehensive test plan for the Wishbone Port Interface of a DDR3 memory controller.

SPEC (host interface):
{json.dumps(spec_context, indent=2)}

Output a JSON array of test operations. Each operation is:
  {{"op": "reset"}}
  {{"op": "write", "addr": <int>, "data": <int>, "sel": <int>, "cti": <int>, "bte": <int>, "comment": "<why>"}}
  {{"op": "read", "addr": <int>, "sel": <int>, "cti": <int>, "bte": <int>, "comment": "<why>"}}
  {{"op": "idle", "cyc": 0, "stb": 0, "comment": "<why>"}}

CTI values: 0=classic, 2=incrementing_burst, 7=end_of_burst
BTE values: 0=linear
sel is a 4-bit byte select mask (15 = all bytes)
All values are decimal integers.

Generate at least 50 operations covering:
1. Single classic write then read at same address (verify data round-trip)
2. Multiple addresses across the address space (0, 256, 4096, 65536, near max 33554428)
3. Byte-masked writes: write full word, then partial write with sel=1, sel=2, sel=4, sel=8, sel=3, sel=5, sel=10, sel=12, read back each
4. Linear burst write of 4 beats (cti=2,2,2,7), then read back each address
5. Linear burst write of 8 beats (max burst length), read back
6. Idle cycles: cyc=0 between transactions
7. Various data patterns: 0, 4294967295, 2779096485, 1515870810, 305419896
8. Back-to-back writes to adjacent addresses
9. Read from unwritten address (expect 0)
10. Write then overwrite same address, read back final value

Output ONLY the JSON array."""

    elif scope == "init_sequence":
        return f"""Generate a comprehensive test plan for the DDR3 Init/Reset FSM.

SPEC (initialization sequence):
{json.dumps(spec_context, indent=2)}

The init_fsm outputs events over time. JEDEC timing values are MINIMUMS — the RTL may
take MORE cycles than the minimum and still be correct. Tests must check ordering and
minimum-timing constraints, NOT exact cycle numbers.

Output a JSON array of test operations:
  {{"op": "reset"}}
  {{"op": "check_not_yet", "cycle": <int>, "signal": "<n>", "value": <int>, "comment": "<why>"}}
  {{"op": "wait_for", "signal": "<n>", "value": <int>, "timeout": <int>, "comment": "<why>"}}
  {{"op": "check_order", "first_signal": "<n>", "first_value": <int>, "second_signal": "<n2>", "second_value": <int>, "min_gap": <int>, "comment": "<why>"}}
  {{"op": "final_check", "signal": "<n>", "value": <int>, "comment": "<why>"}}

Signals: init_reset_n, init_cke, mrs (value=bank addr), init_done, init_fail

IMPORTANT: Do NOT use "zqcl" as a signal. ZQCL is an internal command whose encoding
is implementation-specific. Instead, test the SPEC-LEVEL guarantee: init_done must
arrive at least 130 controller cycles after the last MRS (MR0), which covers the
ZQCL command + tZQinit wait. This keeps tests spec-driven, not implementation-driven.

Operation semantics:
- check_not_yet: at this exact cycle, signal must NOT yet equal value (too-early check)
- wait_for: advance simulation until signal equals value, FAIL if timeout cycles elapse
- check_order: verify first event happened before second with >= min_gap cycles between
- final_check: at end of simulation, verify signal equals value

Timing (MINIMUM controller cycles at 5ns, 4:1 DDR ratio):
- Reset hold: >= 40000 cycles
- CKE delay after reset release: >= 100000 cycles
- tXPR after CKE: >= 34 controller cycles
- MRS order: MR2(ba=2) -> MR3(ba=3) -> MR1(ba=1) -> MR0(ba=0) (strict)
- init_done after last MRS (MR0): >= 130 cycles (ZQCL issue + tZQinit=128 + margin)

Generate these checks:
1. reset
2. check_not_yet cycle=39999: init_reset_n must still be 0
3. wait_for init_reset_n=1, timeout=42000
4. check_not_yet at reset_rise+99999: init_cke must be 0
5. wait_for init_cke=1, timeout=150000
6. check_order: init_reset_n=1 before init_cke=1, min_gap=100000
7. wait_for mrs value=2 (MR2), timeout=1000
8. check_order: init_cke=1 before mrs=2, min_gap=34 (tXPR)
9. wait_for mrs=3 (MR3), timeout=100
10. check_order: mrs=2 before mrs=3, min_gap=0 (ordering)
11. wait_for mrs=1 (MR1), timeout=100
12. check_order: mrs=3 before mrs=1, min_gap=0 (ordering)
13. wait_for mrs=0 (MR0), timeout=100
14. check_order: mrs=1 before mrs=0, min_gap=0 (ordering)
15. wait_for init_done=1, timeout=1000
16. check_order: mrs=0 before init_done=1, min_gap=130 (ZQCL + tZQinit + margin)
17. final_check: init_fail=0

Output ONLY the JSON array."""

    elif scope == "path_backpressure":
        return f"""Generate a test plan for the backpressure path (wb_port + cmd_queue integration).

SPEC:
{json.dumps(spec_context, indent=2)}

The cmd_queue holds up to 16 entries. When full, wb_port asserts wb_stall_o.

Output a JSON array of test operations:
  {{"op": "reset"}}
  {{"op": "write", "addr": <int>, "data": <int>, "comment": "<why>"}}
  {{"op": "read", "addr": <int>, "comment": "<why>"}}
  {{"op": "dequeue", "idx": <int>, "comment": "<why>"}}
  {{"op": "check_stall", "expected_stall": <0|1>, "expected_count": <int>, "comment": "<why>"}}

All values are decimal integers. Address is a 29-bit byte address.

Generate at least 60 operations covering:
1. Reset
2. Single write — verify no stall
3. Fill queue to 16 with writes to distinct addresses (addr = i*128 for i=0..15)
4. check_stall: expected_stall=1, expected_count=16
5. Attempt 17th write while full
6. Dequeue entry 0
7. check_stall: expected_stall=0, expected_count=15
8. Write one more (succeeds)
9. Dequeue entries 0-7 (drain half)
10. Fill again with 8 writes
11. Drain all 16
12. check_stall: expected_stall=0, expected_count=0
13. Rapid fill-drain cycles
14. Address variety: 0, 0x100, 0x1000, 0x10000, near max

Output ONLY the JSON array."""


    else:
        return f"""Generate a test plan for the {scope} scope. Spec: {json.dumps(spec_context, indent=2)}
Output ONLY a JSON array of test operations."""


# =============================================================================
# Extract spec context (same logic as refmodel_agent)
# =============================================================================

def extract_context(spec: dict, scope: str) -> dict:
    ctx = {"scope": scope}

    if scope == "config_regs":
        ctx["csr_register_map"] = spec.get("csr_register_map", {})
    elif scope == "wb_port":
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["memory_geometry"] = spec.get("memory_geometry", {})
    elif scope == "init_sequence":
        ctx["initialization_sequence"] = spec.get("initialization_sequence", {})
        ctx["timing_model"] = spec.get("timing_model", {})
        ctx["clocking_model"] = spec.get("clocking_model", {})

    elif scope == "path_backpressure":
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["memory_geometry"] = spec.get("memory_geometry", {})

    elif scope.startswith("path_"):
        ctx["host_interface"] = spec.get("host_interface", {})
        ctx["memory_geometry"] = spec.get("memory_geometry", {})
        ctx["timing_model"] = spec.get("timing_model", {})

    return ctx


# =============================================================================
# Test Plan Executors (run ops against reference models, record vectors)
# =============================================================================

def execute_config_regs(ops: list, model_dir: str, spec: dict = None) -> list:
    """Execute config_regs test plan against the reference model."""
    mod = load_module_from_file(
        os.path.join(model_dir, "config_regs_refmodel.py"),
        "config_regs_refmodel"
    )
    try:
        model = mod.ConfigRegsModel(spec)
    except TypeError:
        model = mod.ConfigRegsModel()
    vectors = []

    def vec(op, addr, wdata, expected, comment=""):
        line = f"{op:02X} {addr:02X} {wdata:08X} {expected:08X}"
        vectors.append({
            "op": op, "addr": addr, "wdata": wdata, "expected": expected,
            "comment": comment, "hex_line": line,
        })

    for step in ops:
        op_type = step.get("op", "")
        comment = step.get("comment", "")

        if op_type == "reset":
            model.reset()
            _wide_ecc_ce = 0
            _wide_bist_addr = 0
            vec(0x00, 0x00, 0x00000000, 0x00000000, comment or "RESET")

        elif op_type == "write":
            addr = int(step.get("addr", 0))
            data = int(step.get("data", 0)) & 0xFFFFFFFF
            model.write(addr, data)
            vec(0x02, addr, data, 0x00000000, comment)

        elif op_type == "read":
            addr = int(step.get("addr", 0))
            valid, expected = model.read(addr)
            vec(0x01, addr, 0x00000000, expected if valid else 0x00000000, comment)

        elif op_type == "inject":
            reg = step.get("reg", "")
            field = step.get("field", "")
            value = int(step.get("value", 0))

            # ecc_ce_count and bist_fail_addr are RO fields in ERROR_STATUS
            # with NO corresponding input ports on the config_regs RTL module.
            # They are driven by internal modules (BIST engine, ECC logic) that
            # don't exist in isolated block-level testing.  Skip injecting them
            # into the reference model so subsequent reads correctly expect 0.
            UNDRIVEN_FIELDS = {
                ("ERROR_STATUS", "ecc_ce_count"),
                ("ERROR_STATUS", "bist_fail_addr"),
            }

            if (reg, field) not in UNDRIVEN_FIELDS:
                try:
                    model.inject_status(reg, field, value)
                except (ValueError, KeyError, TypeError):
                    pass  # Skip invalid injects silently

            # Encode inject data as a bitmask matching the testbench do_inject task:
            #   bit 0:  sts_init_done          (CTRL_STATUS.init_done)
            #   bit 1:  sts_cal_done           (CTRL_STATUS.cal_done)
            #   bit 2:  sts_cal_fail           (CTRL_STATUS.cal_fail)
            #   bit 3:  sts_bist_done          (CTRL_STATUS.bist_done)
            #   bit 4:  sts_bist_fail          (CTRL_STATUS.bist_fail)
            #   bit 7:5: sts_ref_pending_cnt   (CTRL_STATUS.ref_pending_cnt)
            #   bit 8:  sts_self_refresh_active(CTRL_STATUS.self_refresh_active)
            #   bit 16: sts_ecc_ue_event       (ERROR_STATUS.ecc_ue_flag)
            #   bit 17: sts_ref_starve_event   (ERROR_STATUS.ref_starve_flag)
            #   bit 18: sts_init_fail_event    (ERROR_STATUS.init_fail_flag)
            #
            # Build the inject word from current model state of all injectable fields
            INJECT_FIELD_MAP = {
                ("CTRL_STATUS", "init_done"):           0,
                ("CTRL_STATUS", "cal_done"):            1,
                ("CTRL_STATUS", "cal_fail"):            2,
                ("CTRL_STATUS", "bist_done"):           3,
                ("CTRL_STATUS", "bist_fail"):           4,
                ("CTRL_STATUS", "ref_pending_cnt"):     5,  # 3-bit field at bits 7:5
                ("CTRL_STATUS", "self_refresh_active"): 8,
                ("ERROR_STATUS", "ecc_ue_flag"):       16,
                ("ERROR_STATUS", "ref_starve_flag"):   17,
                ("ERROR_STATUS", "init_fail_flag"):    18,
            }

            inject_word = 0
            for (r, f), bit_pos in INJECT_FIELD_MAP.items():
                try:
                    fval = model.get_field(r, f)
                    if fval is None:
                        fval = 0
                except Exception:
                    fval = 0
                if r == "CTRL_STATUS" and f == "ref_pending_cnt":
                    inject_word |= (fval & 0x7) << bit_pos
                else:
                    inject_word |= (fval & 0x1) << bit_pos

            vec(0x03, 0x00, inject_word, 0x00000000, comment or f"INJECT {reg}.{field}={value}")

            # Emit opcode 0x04 to drive wide RO status signals.
            # ecc_ce_count and bist_fail_addr have no RTL input ports in
            # block-level testing, so always drive zeros.
            vec(0x04, 0x00, 0x00000000, 0x00000000, f"INJECT_WIDE (no drivable wide fields in block test)")

    return vectors


def execute_wb_port(ops: list, model_dir: str, spec: dict = None) -> list:
    """Execute wb_port test plan against the reference model."""
    mod = load_module_from_file(
        os.path.join(model_dir, "wb_port_refmodel.py"),
        "wb_port_refmodel"
    )
    model = mod.WishbonePortModel()
    vectors = []

    def vec(op, addr, wdata, expected, comment=""):
        line = f"{op:02X} {addr:08X} {wdata:08X} {expected:08X}"
        vectors.append({
            "op": op, "addr": addr, "wdata": wdata, "expected": expected,
            "comment": comment, "hex_line": line,
        })

    def encode_status(ack, stall, err=0):
        return (int(err) << 2) | (int(stall) << 1) | int(ack)

    for step in ops:
        op_type = step.get("op", "")
        comment = step.get("comment", "")

        if op_type == "reset":
            model.reset()
            vec(0x00, 0x00000000, 0x00000000, 0x00000000, comment or "RESET")

        elif op_type == "write":
            addr = int(step.get("addr", 0))
            data = int(step.get("data", 0)) & 0xFFFFFFFF
            sel = int(step.get("sel", 15))
            cti = int(step.get("cti", 0))
            bte = int(step.get("bte", 0))
            r = model.present_transaction(1, 1, 1, addr, data, sel, cti, bte, req_ready=1)
            vec(0x02, addr, data,
                encode_status(r.get('wb_ack_o', 0), r.get('wb_stall_o', 0)),
                comment)

        elif op_type == "read":
            addr = int(step.get("addr", 0))
            sel = int(step.get("sel", 15))
            cti = int(step.get("cti", 0))
            bte = int(step.get("bte", 0))
            # Phase 1: present read request
            r = model.present_transaction(1, 1, 0, addr, 0, sel, cti, bte, req_ready=1)
            # Phase 2: complete read — consume pending if any
            if model.get_pending_read_count() > 0:
                model.complete_read(1, 0, 0)
            # wb_port is a protocol translator, NOT a memory. Read data depends on
            # whatever the downstream module returns via rsp_rdata, which doesn't
            # exist in isolated block testing. Use 0xDEAD_XXXX as don't-care sentinel
            # so the testbench skips data comparison. Protocol checks (ack, stall,
            # handshake timing) are still validated.
            vec(0x01, addr, 0x00000000, 0xDEAD0000, comment)

        elif op_type == "idle":
            cyc = int(step.get("cyc", 0))
            stb = int(step.get("stb", 0))
            r = model.present_transaction(cyc, stb, 0, 0, 0, 0, 0, 0, req_ready=1)
            vec(0x03, 0x00000000, 0x00000000,
                encode_status(r.get('wb_ack_o', 0), r.get('wb_stall_o', 0)),
                comment)

    return vectors


def execute_init_sequence(ops: list, model_dir: str, spec: dict = None) -> list:
    """Execute init_sequence test plan — converts ops directly to vectors.
    
    New opcode scheme (range-based, not exact-cycle):
      0x00 = reset
      0x01 = check_not_yet (at cycle C, signal S must NOT equal V)
      0x02 = wait_for (wait until signal S == V, timeout T cycles from current)
      0x03 = check_order (verify event A before event B with >= min_gap)
      0x04 = final_check (at end, signal S must equal V)
    
    Vector format: OO PPPPPPPP SSSSSSSS VVVVVVVV
      OO = opcode
      PPPPPPPP = param (cycle for check_not_yet, timeout for wait_for, min_gap for check_order)
      SSSSSSSS = signal_id (or packed first_sig|second_sig for check_order)
      VVVVVVVV = value (or packed first_val|second_val for check_order)
    """
    vectors = []

    SIGNAL_MAP = {
        "init_reset_n": 0, "init_cke": 1, "mrs": 2,
        "zqcl": 3, "init_done": 4, "init_fail": 5,
    }

    def vec(op, param, signal_id, value, comment=""):
        line = f"{op:02X} {param:08X} {signal_id:08X} {value:08X}"
        vectors.append({
            "op": op, "param": param, "signal_id": signal_id, "value": value,
            "comment": comment, "hex_line": line,
        })

    for step in ops:
        op_type = step.get("op", "")
        comment = step.get("comment", "")

        if op_type == "reset":
            vec(0x00, 0, 0, 0, comment or "RESET")

        elif op_type == "check_not_yet":
            cycle = int(step.get("cycle", 0))
            signal = step.get("signal", "")
            value = int(step.get("value", 0))
            sig_id = SIGNAL_MAP.get(signal, 0xFF)
            vec(0x01, cycle, sig_id, value, comment)

        elif op_type == "wait_for":
            timeout = int(step.get("timeout", 1000))
            signal = step.get("signal", "")
            value = int(step.get("value", 0))
            sig_id = SIGNAL_MAP.get(signal, 0xFF)
            vec(0x02, timeout, sig_id, value, comment)

        elif op_type == "check_order":
            min_gap = int(step.get("min_gap", 0))
            first_sig = step.get("first_signal", "")
            first_val = int(step.get("first_value", 0))
            second_sig = step.get("second_signal", "")
            second_val = int(step.get("second_value", 0))
            # Pack: signal_id = (first_sig_id << 16) | second_sig_id
            # value = (first_val << 16) | (second_val & 0xFFFF)
            fs_id = SIGNAL_MAP.get(first_sig, 0xFF)
            ss_id = SIGNAL_MAP.get(second_sig, 0xFF)
            packed_sig = (fs_id << 16) | ss_id
            packed_val = ((first_val & 0xFFFF) << 16) | (second_val & 0xFFFF)
            vec(0x03, min_gap, packed_sig, packed_val, comment)

        elif op_type == "final_check":
            signal = step.get("signal", "")
            value = int(step.get("value", 0))
            sig_id = SIGNAL_MAP.get(signal, 0xFF)
            vec(0x04, 0, sig_id, value, comment)

        # Backward compatibility: old opcodes still work
        elif op_type == "expect":
            cycle = int(step.get("cycle", 0))
            signal = step.get("signal", "")
            value = int(step.get("value", 0))
            sig_id = SIGNAL_MAP.get(signal, 0xFF)
            vec(0x01, cycle, sig_id, value, comment)

        elif op_type == "negative_check":
            cycle = int(step.get("cycle", 0))
            signal = step.get("signal", "")
            value = int(step.get("value", 0))
            sig_id = SIGNAL_MAP.get(signal, 0xFF)
            vec(0x01, cycle, sig_id, value, comment)  # reuse check_not_yet

    return vectors


# =============================================================================
# Scope registry
# =============================================================================

def execute_path_backpressure(ops: list, model_dir: str, spec: dict = None) -> list:
    """Execute path_backpressure test plan against the reference model."""
    mod = load_module_from_file(
        os.path.join(model_dir, "path_backpressure_refmodel.py"),
        "path_backpressure_refmodel"
    )
    model = mod.BackpressurePathModel()
    vectors = []

    def vec(op, addr, wdata, expected, comment=""):
        line = f"{op:02X} {addr:08X} {wdata:08X} {expected:08X}"
        vectors.append({
            "op": op, "addr": addr, "wdata": wdata, "expected": expected,
            "comment": comment, "hex_line": line,
        })

    for step in ops:
        op_type = step.get("op", "")
        comment = step.get("comment", "")

        if op_type == "reset":
            model.reset()
            vec(0x00, 0, 0, 0, comment or "RESET")

        elif op_type == "write":
            addr = int(step.get("addr", 0))
            data = int(step.get("data", 0)) & 0xFFFFFFFF
            r = model.enqueue(1, 1, 1, addr, data, 0xF)
            expected = (
                (int(r.get("queue_full", 0)) << 7) |
                (int(r.get("wb_stall_o", 0)) << 6) |
                (int(r.get("wb_ack_o", 0)) << 5) |
                (int(r.get("queue_count", 0)) & 0x1F)
            )
            vec(0x02, addr, data, expected, comment)

        elif op_type == "read":
            addr = int(step.get("addr", 0))
            r = model.enqueue(1, 1, 0, addr, 0, 0xF)
            expected = (
                (int(r.get("queue_full", 0)) << 7) |
                (int(r.get("wb_stall_o", 0)) << 6) |
                (int(r.get("wb_ack_o", 0)) << 5) |
                (int(r.get("queue_count", 0)) & 0x1F)
            )
            vec(0x01, addr, 0, expected, comment)

        elif op_type == "dequeue":
            idx = int(step.get("idx", 0))
            r = model.dequeue(idx)
            expected = (
                (int(r.get("queue_full", 0)) << 7) |
                (int(r.get("enq_ready", 1)) << 5) |
                (int(r.get("queue_count", 0)) & 0x1F)
            )
            vec(0x03, idx, 0, expected, comment)

        elif op_type == "check_stall":
            expected_stall = int(step.get("expected_stall", 0))
            expected_count = int(step.get("expected_count", 0))
            expected = (
                (int(model.is_full()) << 7) |
                (expected_stall << 6) |
                (expected_count & 0x1F)
            )
            vec(0x04, 0, 0, expected, comment)

    return vectors


def _build_packer(packing_spec):
    """Build a pack function from a packing spec list.
    
    Args:
        packing_spec: list of {name, width, lo, hi} dicts from hex_format.json
    
    Returns:
        A function that takes a dict of signal values and returns a packed int.
    """
    def pack(signals):
        packed = 0
        for p in packing_spec:
            name = p["name"]
            lo = p["lo"]
            width = p["width"]
            mask = (1 << width) - 1
            packed |= (int(signals.get(name, 0)) & mask) << lo
        return packed
    return pack


def execute_generic_path(ops: list, model_dir: str, spec: dict = None, scope: str = "") -> list:
    """Generic executor for generated path scopes.
    
    Uses hex_format.json for packing (never trusts the LLM's packing code).
    Only uses the refmodel for reset() and step() — behavioral model only.
    """
    import inspect

    # Load refmodel
    mod = load_module_from_file(
        os.path.join(model_dir, f"{scope}_refmodel.py"),
        f"{scope}_refmodel"
    )

    # Find model class with reset() and step()/cycle()/tick()
    # Find model class — prefer class with step(), fall back to other method names
    model = None
    step_method_name = 'step'
    
    RESET_NAMES = ('reset', 'apply_reset', 'do_reset', 'reset_state')
    STEP_NAMES = ('step', 'cycle', 'tick', 'clock_tick', 'process', 'advance',
                  'advance_cycles', 'update', 'clock', 'run_cycle', 'next_cycle')
    
    def _find_method(cls, names):
        for n in names:
            if hasattr(cls, n):
                return n
        return None
    
    # First pass: prefer class with step()
    for name in dir(mod):
        obj = getattr(mod, name)
        if not isinstance(obj, type):
            continue
        reset_name = _find_method(obj, RESET_NAMES)
        if reset_name and hasattr(obj, 'step'):
            model = obj()
            step_method_name = 'step'
            if reset_name != 'reset':
                model.reset = getattr(model, reset_name)
            break
    
    # Second pass: any class with alt reset + alt step
    if model is None:
        for name in dir(mod):
            obj = getattr(mod, name)
            if not isinstance(obj, type):
                continue
            reset_name = _find_method(obj, RESET_NAMES)
            if not reset_name:
                continue
            step_name = _find_method(obj, STEP_NAMES)
            if step_name:
                model = obj()
                step_method_name = step_name
                if reset_name != 'reset':
                    model.reset = getattr(model, reset_name)
                break
    if model is None:
        raise ValueError(f"No class with reset() and step()/cycle()/tick() in {scope}_refmodel.py")
    
    # Alias to step for uniform access
    if step_method_name != 'step':
        model.step = getattr(model, step_method_name)

    # Load packing spec from hex_format.json
    hex_fmt_path = os.path.join(model_dir, "..", "scopes", scope, "generated", "hex_format.json")
    if not os.path.exists(hex_fmt_path):
        raise ValueError(f"hex_format.json not found at {hex_fmt_path}")

    with open(hex_fmt_path) as f:
        hex_fmt = json.load(f)

    pack_inputs = _build_packer(hex_fmt.get("input_packing", []))
    pack_outputs = _build_packer(hex_fmt.get("output_packing", []))

    # Build a safe caller that handles any method signature
    sig = inspect.signature(model.step)
    step_param_names = [p for p in sig.parameters if p != 'self']
    has_kwargs = any(
        sig.parameters[p].kind == inspect.Parameter.VAR_KEYWORD
        for p in sig.parameters
    )

    def safe_step(signals=None):
        """Call model.step() with whatever signature it has."""
        if signals is None:
            signals = {}
        if has_kwargs:
            return model.step(**signals) or {}
        else:
            call_args = {p: int(signals.get(p, 0)) for p in step_param_names}
            return model.step(**call_args) or {}

    vectors = []
    last_result = {}  # Cache outputs from most recent drive/step

    for step_op in ops:
        op_type = step_op.get("op", "")
        comment = step_op.get("comment", "")

        if op_type == "reset":
            model.reset()
            last_result = {}
            vectors.append({
                "hex_line": "00 00000000 00000000 00000000",
                "op": 0, "comment": comment or "RESET",
            })

        elif op_type == "drive":
            signals = step_op.get("signals", {})
            packed_in = pack_inputs(signals)
            last_result = safe_step(signals)
            packed_out = pack_outputs(last_result)
            vectors.append({
                "hex_line": f"01 00000000 {packed_in:08X} {packed_out:08X}",
                "op": 1, "comment": comment,
            })

        elif op_type == "check":
            # Advance one cycle — the testbench does @(posedge clk) then samples.
            last_result = safe_step()
            packed_out = pack_outputs(last_result)
            vectors.append({
                "hex_line": f"02 00000000 00000000 {packed_out:08X}",
                "op": 2, "comment": comment,
            })

        elif op_type == "step":
            cycles = int(step_op.get("cycles", 1))
            for _ in range(cycles):
                last_result = safe_step()
            packed_out = pack_outputs(last_result)
            vectors.append({
                "hex_line": f"03 {cycles:08X} 00000000 {packed_out:08X}",
                "op": 3, "comment": comment,
            })

    return vectors


EXECUTORS = {
    "config_regs":        execute_config_regs,
    "wb_port":            execute_wb_port,
    "init_sequence":      execute_init_sequence,
    "path_backpressure":  execute_path_backpressure,
}

HEX_FMTS = {
    "config_regs":       "OO AA WWWWWWWW EEEEEEEE (op addr wdata expected)",
    "wb_port":           "OO AAAAAAAA WWWWWWWW EEEEEEEE (op addr wdata expected)",
    "init_sequence":     "OO PPPPPPPP SSSSSSSS VVVVVVVV (op param signal_id value)",
    "path_backpressure": "OO AAAAAAAA WWWWWWWW EEEEEEEE (op addr wdata expected_status)",
}


# =============================================================================
# Agent
# =============================================================================

class VectorGenAgent:
    """LLM-driven vector generator with deterministic model execution."""

    def __init__(self, scope: str, spec_path: str, model_dir: str, output_dir: str):
        self.scope = scope
        self.spec_path = spec_path
        self.model_dir = model_dir
        self.output_dir = output_dir
        self.spec = load_spec(spec_path)
        self.ctx = extract_context(self.spec, scope)
        os.makedirs(output_dir, exist_ok=True)

    def log(self, msg: str):
        print(f"[VectorGenAgent][{self.scope}] {msg}")

    def generate_test_plan(self) -> list:
        """Ask the LLM to generate a test plan based on the spec."""
        self.log("Asking LLM to generate test plan...")
        prompt = build_testplan_prompt(self.scope, self.ctx, self.spec_path)

        raw = call_llm([
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ])

        if not raw or not raw.strip():
            self.log("ERROR: LLM returned empty response")
            raise ValueError("LLM returned empty response")

        self.log(f"Raw LLM response length: {len(raw)} chars, first 200: {raw[:200]!r}")

        cleaned = strip_fences(raw)

        # Parse JSON — retry once if it fails
        try:
            ops = json.loads(cleaned)
        except json.JSONDecodeError as e:
            self.log(f"JSON parse failed: {e}. Retrying with clarification...")
            raw2 = call_llm([
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
                {"role": "assistant", "content": raw},
                {"role": "user", "content": "That was not valid JSON. Please output ONLY a JSON array with no other text, no markdown fences, no commentary."},
            ])
            cleaned2 = strip_fences(raw2)
            ops = json.loads(cleaned2)

        if not isinstance(ops, list):
            raise ValueError(f"Expected JSON array, got {type(ops)}")

        self.log(f"LLM generated {len(ops)} test operations")

        # Save raw test plan for traceability
        plan_path = os.path.join(self.output_dir, f"{self.scope}_testplan.json")
        with open(plan_path, "w") as f:
            json.dump(ops, f, indent=2)
        self.log(f"Test plan saved -> {plan_path}")

        return ops

    def execute_plan(self, ops: list) -> list:
        """Run the test plan against the reference model."""
        self.log(f"Executing {len(ops)} operations against reference model...")
        if self.scope in EXECUTORS:
            executor = EXECUTORS[self.scope]
            vectors = executor(ops, self.model_dir, self.spec)
        else:
            self.log(f"Using generic executor for generated scope '{self.scope}'")
            vectors = execute_generic_path(ops, self.model_dir, self.spec, self.scope)
        self.log(f"Produced {len(vectors)} vectors")
        return vectors

    def export(self, vectors: list):
        """Write hex and JSON vector files."""
        hex_path = os.path.join(self.output_dir, f"{self.scope}_vectors.hex")
        json_path = os.path.join(self.output_dir, f"{self.scope}_vectors.json")
        fmt = HEX_FMTS.get(self.scope, "unknown")

        write_hex(vectors, hex_path)
        write_json(vectors, json_path, self.scope, fmt, self.spec_path)

    def run(self) -> dict:
        """Full pipeline: LLM test plan -> model execution -> vector export."""
        report = {
            "scope": self.scope,
            "status": "unknown",
            "vector_count": 0,
            "errors": [],
        }

        try:
            ops = self.generate_test_plan()
            vectors = self.execute_plan(ops)
            self.export(vectors)

            report["status"] = "success"
            report["vector_count"] = len(vectors)

        except Exception as e:
            report["status"] = "error"
            report["errors"].append(str(e))
            self.log(f"ERROR: {e}")

        # Save report
        report_path = os.path.join(self.output_dir, f"{self.scope}_vectorgen_report.json")
        with open(report_path, "w") as f:
            json.dump(report, f, indent=2)

        self.log(f"Done. Status: {report['status']}, vectors: {report['vector_count']}")
        return report


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Vector Generator Agent (LLM-Driven)")
    parser.add_argument("--scope", required=True,
                        help="Validation scope")
    parser.add_argument("--model-dir", required=True,
                        help="Directory containing {scope}_refmodel.py")
    parser.add_argument("--output-dir", default=None,
                        help="Output directory (defaults to model-dir)")
    parser.add_argument("--spec", required=True,
                        help="Path to spec JSON")
    parser.add_argument("--api-key", help="TAMU AI API key")
    parser.add_argument("--model", help="Model ID override")

    args = parser.parse_args()

    global API_KEY, MODEL_ID
    if args.api_key:
        API_KEY = args.api_key
    if args.model:
        MODEL_ID = args.model

    output_dir = args.output_dir or args.model_dir

    agent = VectorGenAgent(args.scope, args.spec, args.model_dir, output_dir)
    report = agent.run()

    print("\n" + "=" * 60)
    print(f"Scope:   {report['scope']}")
    print(f"Status:  {report['status']}")
    print(f"Vectors: {report['vector_count']}")
    if report["errors"]:
        for e in report["errors"]:
            print(f"Error:   {e}")
    print("=" * 60)


if __name__ == "__main__":
    main()