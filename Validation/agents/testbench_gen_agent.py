"""
Testbench Generator Agent
============================
Generates SystemVerilog testbenches that:
  1. Read a PORT MANIFEST (JSON) from the frontend — no RTL parsing needed
  2. Generate clock and reset
  3. Read hex vectors from file ($fscanf)
  4. Drive DUT inputs per vector opcode
  5. Compare DUT outputs against expected values
  6. Print PASS/FAIL summary

KEY DESIGN: The agent reads the frontend-provided PORT MANIFEST to get exact
port names, widths, and directions. The reference model and spec are NOT used
for port info — this agent's only job is to generate a structurally correct
testbench that matches the real DUT ports.

Usage:
    python3 testbench_gen_agent.py \
        --scope config_regs \
        --manifest ./Frontend/config_register_output/config_regs_manifest.json \
        --spec ./spec/llmmc_microarchitecturespec_filled.json \
        --output-dir ./scopes/config_regs/ \
        --api-key YOUR_KEY

Author: Validation Subsystem — Agent 3c (Testbench Generator)
"""

import argparse
import json
import os
import re
import sys
import requests
from datetime import datetime
from llm_client import call_llm



# =============================================================================
# LLM Communication
# =============================================================================

def strip_fences(text: str) -> str:
    """Remove markdown code fences, <think> blocks, and any preamble/postamble."""
    # Remove <think>...</think> blocks
    text = re.sub(r'<think>.*?</think>', '', text, flags=re.DOTALL)
    # Remove markdown fences
    text = re.sub(r'^```\w*\n?', '', text, flags=re.MULTILINE)
    text = re.sub(r'^```\s*$', '', text, flags=re.MULTILINE)
    text = text.strip()
    # Trim preamble before first SV keyword
    for marker in ['`timescale', 'module ']:
        idx = text.find(marker)
        if idx > 0 and idx < 200:
            text = text[idx:]
            break
    return text



# =============================================================================
# Manifest Loading & Conversion
# =============================================================================

def load_manifest(manifest_path: str) -> dict:
    """Load frontend port manifest JSON."""
    with open(manifest_path, "r", encoding="utf-8") as f:
        return json.load(f)


def manifest_to_port_list(manifest: dict) -> str:
    """
    Convert manifest JSON into a human-readable port list string
    for inclusion in the LLM prompt. Groups ports by category.
    """
    lines = []
    module_name = manifest.get("module_name", "unknown")
    params = manifest.get("parameters", {})

    lines.append(f"Module: {module_name}")
    if params:
        lines.append(f"Parameters: {json.dumps(params)}")
    lines.append("")

    for group_name, ports in manifest.get("ports", {}).items():
        lines.append(f"--- {group_name} ---")
        for p in ports:
            name = p["name"]
            width = p["width"]
            direction = p["dir"]
            if width == 1:
                lines.append(f"  {direction:6s}  logic              {name}")
            else:
                lines.append(f"  {direction:6s}  logic [{width-1:>2d}:0]       {name}")
        lines.append("")

    return "\n".join(lines)


def manifest_to_sv_declarations(manifest: dict) -> str:
    """
    Generate SystemVerilog signal declarations from manifest.
    Gives the LLM exact declarations to copy.
    """
    lines = []
    for group_name, ports in manifest.get("ports", {}).items():
        lines.append(f"    // {group_name}")
        for p in ports:
            name = p["name"]
            width = p["width"]
            if width == 1:
                lines.append(f"    logic                    {name};")
            else:
                lines.append(f"    logic [{width-1:>2d}:0]             {name};")
        lines.append("")
    return "\n".join(lines)


def manifest_to_dut_instance(manifest: dict) -> str:
    """
    Generate the DUT instantiation string from manifest.
    Guarantees exact port matching.
    """
    module_name = manifest.get("module_name", "unknown")

    lines = []
    lines.append(f"    {module_name} dut (")

    # Port connections — all ports across all groups
    all_ports = []
    for group_name, ports in manifest.get("ports", {}).items():
        for p in ports:
            all_ports.append(p["name"])

    port_strs = [f"        .{name}({name})" for name in all_ports]
    lines.append(",\n".join(port_strs))
    lines.append("    );")

    return "\n".join(lines)


# =============================================================================
# Spec helpers
# =============================================================================

def load_spec(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


# =============================================================================
# Scope-specific protocol descriptions
# =============================================================================

SCOPE_PROTOCOLS = {
    "config_regs": """VECTOR HEX FILE FORMAT: config_regs_vectors.hex
Each line: OO AA WWWWWWWW EEEEEEEE
  OO = opcode (8 bits): 00=reset, 01=read, 02=write, 03=inject, 04=inject_wide
  AA = register address (8 bits)
  WWWWWWWW = write data (32 bits)
  EEEEEEEE = expected read data (32 bits, used for read ops)

TESTBENCH BEHAVIOR:
- On opcode 00 (reset): Assert rst_n=0 for 4 cycles, then release. Reset all sts_* inputs to 0.
- On opcode 02 (write): Drive csr_cyc_i=1, csr_stb_i=1, csr_we_i=1, csr_adr_i=addr, csr_dat_i=wdata, csr_sel_i=4'hF. Wait for csr_ack_o. Deassert bus.
- On opcode 01 (read): Drive csr_cyc_i=1, csr_stb_i=1, csr_we_i=0, csr_adr_i=addr, csr_sel_i=4'hF. Wait for csr_ack_o. Compare csr_dat_o with expected. Deassert bus.
- On opcode 03 (inject): Drive the sts_* status input pins from wdata bits:
  bit0=sts_init_done, bit1=sts_cal_done, bit2=sts_cal_fail, bit3=sts_bist_done, bit4=sts_bist_fail,
  bits[7:5]=sts_ref_pending_cnt, bit8=sts_self_refresh_active.
  For error event pulses: bit16=sts_ecc_ue_event, bit17=sts_ref_starve_event, bit18=sts_init_fail_event (pulse for 1 cycle then deassert).
- On opcode 04 (inject_wide): Drive wide RO status inputs from wdata bits:
  bits[15:0]=sts_ecc_ce_count (16-bit counter), bits[28:16]=sts_bist_fail_addr (13-bit address).
  These are level-driven (not pulsed). Just assign them and hold.

IMPORTANT RULES:
- csr_sel_i: connect and tie to 4'hF for all transactions
- All cfg_* outputs: declare signals and connect them (they don't need checking, just connection)
- Use $fscanf to read the hex file line by line
- Track total_tests, pass_count, fail_count (only count read ops as tests)
- On mismatch: $display with "MISMATCH", vector number, address, expected vs actual (use "Actual" for the DUT value)
- At end: print "PASS: X/Y" or "FAIL: X/Y" summary
- Use $value$plusargs("VECTORS=%s", vector_file) for vector filename, default "config_regs_vectors.hex"
- Add a watchdog timeout (100000 cycles)
- Module name: config_regs_tb""",

    "wb_port": """VECTOR HEX FILE FORMAT: wb_port_vectors.hex
Each line: OO AAAAAAAA WWWWWWWW EEEEEEEE
  OO = opcode (8 bits): 00=reset, 01=read, 02=write, 03=idle
  AAAAAAAA = byte address (32 bits)
  WWWWWWWW = write data (32 bits)
  EEEEEEEE = expected value (32 bits). For writes: expected ack status. For reads: expected read data OR 0xDEAD0000 = DON'T CARE (skip data comparison).

TESTBENCH BEHAVIOR:
- req_ready tied to 1 (no backpressure)
- On opcode 00 (reset): Assert rst_n=0 for 4 cycles, release
- On opcode 02 (write): Drive wb_cyc_i=1, wb_stb_i=1, wb_we_i=1, wb_adr_i=addr, wb_dat_i=wdata, wb_sel_i=4'hF. Wait for wb_ack_o. Check ack received (always PASS if ack arrives).
- On opcode 01 (read): Drive wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=addr. Wait for wb_ack_o. If expected == 32'hDEAD0000, skip data comparison (print "Read PASS (don't-care)") and count as PASS. Otherwise compare wb_dat_o against expected.
- On opcode 03 (idle): Just advance one clock cycle, no bus activity.

READ DATA DON'T-CARE RULE:
The wb_port is a protocol translator, NOT a memory. In isolated testing there is no
downstream memory, so read data content is unpredictable. Vectors use 0xDEAD0000 as
a sentinel meaning "don't check data, only verify the ack/handshake completed."
The testbench MUST check: if (expected == 32'hDEAD0000) skip data compare, else compare.

IMPORTANT:
- Use $fscanf, track pass/fail
- $value$plusargs for vector filename, default "wb_port_vectors.hex"
- Watchdog timeout, Module name: wb_port_tb
- NEVER use non-blocking assignments (<=) with associative arrays, dynamic arrays, or queues. Xcelium forbids this. Use blocking assignments (=) for all associative array writes (e.g. mem[addr] = data, NOT mem[addr] <= data).""",

    "init_sequence": """VECTOR HEX FILE FORMAT: init_sequence_vectors.hex
Each line: OO PPPPPPPP SSSSSSSS VVVVVVVV
  OO = opcode:
    00 = reset (ignore other fields)
    01 = check_not_yet: at cycle P, signal S must NOT equal V. PASS if != V, FAIL if == V.
    02 = wait_for: starting from current sim cycle, wait until signal S equals V.
         P = timeout in controller cycles. FAIL if timeout elapses before match.
         PASS when signal matches. Record the cycle when it matched for later order checks.
    03 = check_order: verify event A happened before event B with >= P cycle gap.
         S = packed (first_sig_id[31:16] | second_sig_id[15:0])
         V = packed (first_value[31:16] | second_value[15:0])
         P = minimum gap in controller cycles.
         Use recorded cycles from previous wait_for results.
         PASS if second_cycle - first_cycle >= P. FAIL otherwise.
    04 = final_check: at current sim time, signal S must equal V. Simple equality check.
  PPPPPPPP = parameter (cycle/timeout/min_gap depending on opcode)
  SSSSSSSS = signal_id or packed signal pair
  VVVVVVVV = expected value or packed value pair

SIGNAL ID MAP:
  0 = init_reset_n
  1 = init_cke  
  2 = mrs (composite: {init_cmd_valid, init_bank} — extract init_cmd_valid as bit[3], init_bank as bits[2:0])
  3 = zqcl (composite: {init_cmd_valid, init_cmd} — check init_cmd_valid=1 and init_cmd matches ZQCL encoding)
  4 = init_done
  5 = init_fail

TESTBENCH BEHAVIOR:
- Event-based: DUT runs autonomously after reset. cmd_gen_ready tied to 1.
- Read ALL vectors into arrays at time 0.
- Process vectors sequentially (not all at once).
- For wait_for (opcode 02): loop each clock cycle checking the signal. Store the cycle
  when the signal matches in an associative-style array keyed by (signal_id, value) for
  later check_order lookups. CRITICAL: do NOT use associative arrays with non-blocking
  assignments. Use plain reg arrays indexed by signal_id.
- For check_order (opcode 03): unpack the signal IDs and values, look up stored cycles,
  compute gap.
- Track total pass/fail. Print summary at end.

SIGNAL SAMPLING for mrs (signal_id=2):
  The vector value field for mrs contains the expected bank address (0,1,2,3).
  Sample: actual = {dut.init_cmd_valid, dut.init_bank}
  A match means init_cmd_valid==1 AND init_bank==expected_value.
  
SIGNAL SAMPLING for zqcl (signal_id=3):  
  The vector value field for zqcl is 1 (meaning "ZQCL issued").
  A match means init_cmd_valid==1 AND init_cmd equals the ZQCL command encoding.
  Check the RTL manifest for the actual cmd encoding.

IMPORTANT:
- NEVER use non-blocking assignments (<=) with associative arrays
- Use $value$plusargs for vector filename, default "init_sequence_vectors.hex"
- Module name: init_sequence_tb
- Print state transitions when FSM state signal changes (for debugging)
- Overall simulation timeout: 800000 controller cycles""",

    "path_backpressure": """VECTOR HEX FILE FORMAT: path_backpressure_vectors.hex
Each line: OO AAAAAAAA WWWWWWWW EEEEEEEE
  OO = opcode (8 bits):
    00 = reset
    01 = read request (enqueue read into cmd_queue via wb_port)
    02 = write request (enqueue write into cmd_queue via wb_port)
    03 = dequeue (remove entry at index AAAAAAAA[3:0] from cmd_queue)
    04 = check_stall (verify backpressure status without bus activity)
  AAAAAAAA = byte address (32 bits) for write/read, or dequeue index
  WWWWWWWW = write data (32 bits)
  EEEEEEEE = expected status (packed):
    bit [7]   = expected queue_full
    bit [6]   = expected wb_stall_o
    bit [5]   = expected wb_ack_o (for write/read) or enq_ready (for dequeue)
    bits [4:0] = expected queue_count

TESTBENCH ARCHITECTURE:
This testbench instantiates BOTH wb_port and cmd_queue wired together.
There is NO wrapper module — the testbench wires the two modules directly.

Use these EXACT signal declarations and instantiations:

```systemverilog
    // Clock and reset
    logic clk, rst_n;

    // Wishbone bus (driven by testbench)
    logic        wb_cyc_i, wb_stb_i, wb_we_i;
    logic [28:0] wb_adr_i;
    logic [31:0] wb_dat_i;
    logic [3:0]  wb_sel_i;
    logic [1:0]  wb_bte_i;
    logic [2:0]  wb_cti_i;

    // Wishbone outputs (from wb_port)
    logic        wb_ack_o, wb_stall_o, wb_err_o;
    logic [31:0] wb_dat_o;

    // Internal wiring: wb_port -> cmd_queue
    logic        req_valid, req_we;
    logic [28:0] req_addr;
    logic [31:0] req_wdata;
    logic [3:0]  req_wmask;
    logic [3:0]  req_aux;
    logic        req_ready;   // cmd_queue -> wb_port (backpressure)

    // Read response (tie off — no data_path in this scope)
    logic        rsp_valid;
    logic [31:0] rsp_rdata;
    logic [3:0]  rsp_aux;

    // Address decode (inline combinational)
    wire [14:0] dec_row  = req_addr[28:17];
    wire [9:0]  dec_col  = req_addr[16:7];
    wire [2:0]  dec_bank = req_addr[6:4];

    // Queue status outputs
    logic        enq_ready;
    logic [15:0] entry_valid;
    logic [4:0]  queue_count;
    logic        queue_empty, queue_full;

    // Queue dequeue interface (driven by testbench)
    logic        deq_grant;
    logic [3:0]  deq_idx;

    // Tie off read response
    assign rsp_valid = 1'b0;
    assign rsp_rdata = 32'h0;
    assign rsp_aux   = 4'h0;

    // Backpressure wire
    assign req_ready = enq_ready;

    wb_port u_wb_port (
        .clk(clk), .rst_n(rst_n),
        .wb_cyc_i(wb_cyc_i), .wb_stb_i(wb_stb_i), .wb_we_i(wb_we_i),
        .wb_adr_i(wb_adr_i), .wb_dat_i(wb_dat_i), .wb_sel_i(wb_sel_i),
        .wb_bte_i(wb_bte_i), .wb_cti_i(wb_cti_i),
        .wb_ack_o(wb_ack_o), .wb_dat_o(wb_dat_o),
        .wb_stall_o(wb_stall_o), .wb_err_o(wb_err_o),
        .req_valid(req_valid), .req_we(req_we), .req_addr(req_addr),
        .req_wdata(req_wdata), .req_wmask(req_wmask), .req_aux(req_aux),
        .req_ready(req_ready),
        .rsp_valid(rsp_valid), .rsp_rdata(rsp_rdata), .rsp_aux(rsp_aux)
    );

    cmd_queue u_cmd_queue (
        .clk(clk), .rst_n(rst_n),
        .enq_valid(req_valid), .enq_we(req_we),
        .enq_row(dec_row), .enq_col(dec_col), .enq_bank(dec_bank),
        .enq_aux(req_aux),
        .enq_ready(enq_ready),
        .entry_valid(entry_valid),
        .entry_row(), .entry_col(), .entry_bank(), .entry_we(), .entry_aux(),
        .queue_count(queue_count), .queue_empty(queue_empty), .queue_full(queue_full),
        .deq_grant(deq_grant), .deq_idx(deq_idx)
    );
```

TESTBENCH BEHAVIOR:
- On opcode 00 (reset): Assert rst_n=0 for 4 cycles, release.
  Deassert all Wishbone inputs. Set deq_grant=0.
- On opcode 02 (write): Drive wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
  wb_adr_i=addr, wb_dat_i=wdata, wb_sel_i=4'hF, wb_cti_i=0, wb_bte_i=0.
  Wait 1 cycle. Sample status. Compare against expected. Deassert wb_stb_i.
  Wait 1 idle cycle before next vector.
- On opcode 01 (read): Same as write but wb_we_i=0, wb_dat_i=0.
- On opcode 03 (dequeue): Set deq_grant=1, deq_idx=addr[3:0]. Pulse for 1 cycle.
  Set deq_grant=0. Wait 1 cycle. Sample queue_count, queue_full, enq_ready.
  Compare against expected.
- On opcode 04 (check_stall): No bus activity. Just sample queue_full,
  wb_stall_o, queue_count. Compare against expected.

STATUS COMPARISON:
  For opcodes 01/02: actual = {queue_full, wb_stall_o, wb_ack_o, queue_count[4:0]}
  For opcode 03:     actual = {queue_full, 1'b0, enq_ready, queue_count[4:0]}
  For opcode 04:     actual = {queue_full, wb_stall_o, 1'b0, queue_count[4:0]}
  On mismatch: $display("MISMATCH vec=%0d op=0x%02X expected=0x%02X actual=0x%02X", ...)

IMPORTANT:
- Use $fscanf to read vectors line by line
- $value$plusargs("VECTORS=%s", vector_file) with default "path_backpressure_vectors.hex"
- Track total_tests, pass_count, fail_count
- Watchdog timeout: 200000 cycles
- Module name: path_backpressure_tb
- NEVER use non-blocking assignments (<=) with associative arrays
- Port names must match EXACTLY — do not rename anything""",
}


# =============================================================================
# Prompt Builder — uses manifest (NOT RTL)
# =============================================================================

SYSTEM_PROMPT = """You are an expert hardware verification engineer writing SystemVerilog testbenches.

You output ONLY synthesizable/simulatable SystemVerilog code. No explanation, no markdown fences, no commentary outside of code comments.

The testbench must:
1. Be self-contained in a single file
2. Generate clock and reset
3. Read vectors from a hex file using $fscanf
4. Drive DUT inputs according to the vector opcode
5. Compare DUT outputs against expected values
6. Track pass/fail counts
7. Print a summary at end of simulation
8. Use $finish to end simulation
9. Match the DUT port list EXACTLY as provided — do not rename, add, or remove any ports

Xcelium coding rules (MANDATORY — violating these causes compile errors):
- NEVER use non-blocking assignments (<=) with associative arrays, dynamic arrays, or queues. Use blocking (=) instead.
- NEVER initialize signals in an initial block if they are also driven by an always_ff block. This causes Xcelium MULAXX "multiple drivers to always_ff output" errors. Instead, initialize those signals ONLY in the reset branch of the always_ff block.
- If you use always_ff, ALL assignments to its output signals must come from that single always_ff block — no initial blocks, no other always blocks."""


def build_prompt(scope: str, manifest: dict, spec: dict, error_context: str = None, spec_path: str = None) -> str:
    """
    Build a testbench generation prompt using the port manifest.
    No RTL file is read — all port info comes from the manifest JSON.
    
    Args:
        scope: Validation scope name
        manifest: Frontend port manifest dict
        spec: Microarchitecture spec dict
        error_context: Optional triage feedback from a previous failed attempt.
                       Injected into the prompt so the LLM avoids the same mistake.
        spec_path: Path to spec JSON (used to locate generated files).
    """
    # Integration scopes: protocol contains full instantiation, skip manifest helpers
    if scope.startswith("path_"):
        protocol_desc = SCOPE_PROTOCOLS.get(scope)
        if protocol_desc is None and spec_path:
            gen_protocol = os.path.join(
                os.path.dirname(spec_path), "..", "scopes", scope, "generated", "tb_protocol.txt"
            )
            if os.path.exists(gen_protocol):
                with open(gen_protocol) as f:
                    protocol_desc = f.read()
        if protocol_desc is None:
            raise ValueError(f"No protocol for integration scope: {scope}")
        clk = spec["clocking_model"]
        return (
            f"Generate a SystemVerilog testbench for the {scope} integration test "
            f"of a DDR3 memory controller.\n\n"
            f"CLOCK: {clk['controller_clock_period_ns']}ns period "
            f"({clk['$derived']['controller_frequency_MHz']}MHz)\n\n"
            f"{protocol_desc}\n\n"
            f"Output ONLY the SystemVerilog code."
        )

    module_name = manifest.get("module_name", "unknown")
    clk = spec["clocking_model"]

    # Get scope protocol description
    protocol_desc = SCOPE_PROTOCOLS.get(scope)
    if protocol_desc is None:
        raise ValueError(f"Unknown scope: {scope}. Available: {list(SCOPE_PROTOCOLS.keys())}")

    # Build structured port info from manifest
    port_list = manifest_to_port_list(manifest)
    sv_declarations = manifest_to_sv_declarations(manifest)
    dut_instance = manifest_to_dut_instance(manifest)

    # Build error context block if we have triage feedback from a prior retry
    error_block = ""
    if error_context:
        error_block = f"""
╔══════════════════════════════════════════════════════════════════╗
║  PREVIOUS ATTEMPT FAILED — YOU MUST FIX THE FOLLOWING ERROR    ║
╚══════════════════════════════════════════════════════════════════╝
{error_context}

You MUST avoid this exact problem in your new output. Do NOT repeat
the same coding pattern that caused this failure.
"""

    return f"""Generate a SystemVerilog testbench for the {module_name} module of a DDR3 memory controller.
{error_block}
DUT PORT LIST (from frontend manifest — you MUST use these EXACT names and widths):
{port_list}

SIGNAL DECLARATIONS (copy these exactly into your testbench):
```systemverilog
{sv_declarations}
```

DUT INSTANTIATION (copy this exactly into your testbench):
```systemverilog
{dut_instance}
```

CLOCK: {clk['controller_clock_period_ns']}ns period ({clk['$derived']['controller_frequency_MHz']}MHz)

{protocol_desc}

CRITICAL: Use the signal declarations and DUT instantiation provided above EXACTLY.
Do not rename, reorder, or omit any ports.
Xcelium coding rule: NEVER use non-blocking assignments (<=) with associative arrays, dynamic arrays, or queues. Use blocking (=) instead.
Xcelium coding rule: NEVER initialize signals in an initial block if they are also driven by always_ff. Use the reset branch of always_ff instead.

Output ONLY the SystemVerilog code."""


# =============================================================================
# Agent
# =============================================================================

class TestbenchGenAgent:
    """LLM-driven testbench generator. Reads frontend port manifest for DUT ports."""

    def __init__(self, scope: str, manifest_path: str, spec_path: str, output_dir: str):
        self.scope = scope
        self.manifest_path = manifest_path
        self.spec_path = spec_path
        self.output_dir = output_dir
        self.spec = load_spec(spec_path)
        if isinstance(manifest_path, list):
            self.manifest = {}
        else:
            self.manifest = load_manifest(manifest_path)
        os.makedirs(output_dir, exist_ok=True)

    def log(self, msg: str):
        print(f"[TbGenAgent][{self.scope}] {msg}")

    @staticmethod
    def _remove_conflicting_assigns(sv_code: str) -> str:
        """Remove 'assign' statements for signals that are also procedurally assigned.
        Xcelium ICDPAV error occurs when a signal has both continuous and procedural drivers."""
        import re
        lines = sv_code.split('\n')
        
        # Find all signals procedurally assigned inside tasks/functions
        procedural_signals = set()
        in_task = False
        for line in lines:
            stripped = line.strip()
            if re.match(r'(task|function)\b', stripped):
                in_task = True
            if in_task:
                # Match: signal_name = expr;  or  signal_name <= expr;
                m = re.match(r'(\w+)\s*<?=\s*', stripped)
                if m:
                    procedural_signals.add(m.group(1))
            if stripped.startswith('endtask') or stripped.startswith('endfunction'):
                in_task = False
        
        # Remove assign statements for those signals
        filtered = []
        removed = 0
        for line in lines:
            stripped = line.strip()
            # Match: assign signal_name = ...;
            m = re.match(r'assign\s+(\w+)\s*=', stripped)
            if m and m.group(1) in procedural_signals:
                removed += 1
                continue
            filtered.append(line)
        
        if removed > 0:
            print(f"[TbSanitizer] Removed {removed} conflicting assign statements")
        
        return '\n'.join(filtered)

    def generate(self, error_context: str = None) -> dict:
        """Generate testbench via LLM using port manifest.
        
        Args:
            error_context: Optional string from triage agent describing what went
                           wrong on a previous attempt. Injected into the LLM prompt
                           so the model avoids repeating the same mistake.
        """
        report = {
            "scope": self.scope,
            "status": "unknown",
            "output_file": None,
            "manifest_file": self.manifest_path,
            "module_name": None,
            "errors": [],
            "timestamp": datetime.now().isoformat(),
        }

        try:
            # Step 1: Read manifest
            module_name = self.manifest.get("module_name", "unknown")
            report["module_name"] = module_name

            all_ports = []
            for group_name, ports in self.manifest.get("ports", {}).items():
                all_ports.extend(ports)
            self.log(f"Manifest: {module_name} — {len(all_ports)} ports across "
                     f"{len(self.manifest.get('ports', {}))} groups")

            if error_context:
                self.log(f"Retry mode — injecting triage feedback ({len(error_context)} chars)")

            # Step 2: Build prompt with manifest ports + optional error context
            prompt = build_prompt(self.scope, self.manifest, self.spec,
                                  error_context=error_context, spec_path=self.spec_path)
            self.log(f"Prompt built ({len(prompt)} chars). Calling LLM...")

            # Step 3: Call LLM
            raw = call_llm([
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
            ])

            sv_code = strip_fences(raw)

            # Step 4: Basic validation — retry if no module found
            if "module " not in sv_code:
                self.log("WARNING: No module found in output. Retrying...")
                raw2 = call_llm([
                    {"role": "system", "content": SYSTEM_PROMPT},
                    {"role": "user", "content": prompt},
                    {"role": "assistant", "content": raw},
                    {"role": "user", "content": "That output was not valid SystemVerilog. Output ONLY the complete testbench module from `module` to `endmodule`. No markdown."},
                ])
                sv_code = strip_fences(raw2)

            # Step 5: Verify DUT instantiation references correct module
            if module_name not in sv_code:
                self.log(f"WARNING: '{module_name}' not found in generated testbench")
                report["errors"].append(f"Module name '{module_name}' not found in output")

            # Step 6: Verify all ports are present in generated code
            missing_ports = []
            for group_name, ports in self.manifest.get("ports", {}).items():
                for p in ports:
                    if p["name"] not in sv_code:
                        missing_ports.append(p["name"])
            if missing_ports:
                self.log(f"WARNING: {len(missing_ports)} ports missing from generated TB: "
                         f"{missing_ports[:5]}{'...' if len(missing_ports) > 5 else ''}")
                report["errors"].append(f"Missing ports: {missing_ports}")

            # Step 7: Write output
            out_filename = f"{self.scope}_tb.sv"
            out_path = os.path.join(self.output_dir, out_filename)
            with open(out_path, "w") as f:
                sv_code = self._remove_conflicting_assigns(sv_code)
                f.write(sv_code)
            self.log(f"Wrote testbench -> {out_path}")

            report["status"] = "success"
            report["output_file"] = out_path

        except Exception as e:
            report["status"] = "error"
            report["errors"].append(str(e))
            self.log(f"ERROR: {e}")

        # Save report
        report_path = os.path.join(self.output_dir, f"{self.scope}_tbgen_report.json")
        with open(report_path, "w") as f:
            json.dump(report, f, indent=2)

        self.log(f"Done. Status: {report['status']}")
        return report


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Testbench Generator Agent")
    parser.add_argument("--scope", required=True,
                        help="Validation scope (e.g. config_regs, wb_port, init_sequence)")
    parser.add_argument("--manifest", required=True,
                        help="Path to frontend port manifest JSON")
    parser.add_argument("--spec", required=True,
                        help="Path to spec JSON")
    parser.add_argument("--output-dir", required=True,
                        help="Output directory for generated testbench")
    parser.add_argument("--api-key", help="TAMU AI API key")
    parser.add_argument("--model", help="Model ID override")

    args = parser.parse_args()

    global API_KEY, MODEL_ID
    if args.api_key:
        API_KEY = args.api_key
    if args.model:
        MODEL_ID = args.model

    # Validate scope has a protocol definition
    if args.scope not in SCOPE_PROTOCOLS:
        print(f"ERROR: Unknown scope '{args.scope}'. Available: {list(SCOPE_PROTOCOLS.keys())}")
        sys.exit(1)

    agent = TestbenchGenAgent(args.scope, args.manifest, args.spec, args.output_dir)
    report = agent.generate()

    print("\n" + "=" * 60)
    print(f"Scope:    {report['scope']}")
    print(f"Module:   {report['module_name']}")
    print(f"Manifest: {args.manifest}")
    print(f"Status:   {report['status']}")
    if report["output_file"]:
        print(f"Output:   {report['output_file']}")
    if report["errors"]:
        for e in report["errors"]:
            print(f"Error:    {e}")
    print("=" * 60)


if __name__ == "__main__":
    main()