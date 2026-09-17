#!/usr/bin/env python3
"""
+======================================================================+
|             INIT / RESET FSM AGENT  (LLM-driven, RTL-only)           |
|                                                                      |
|  Phase 1 RTL Generation Agent -- Claude-powered                      |
|  Generates: init_fsm.sv + init_fsm_manifest.json                     |
|                                                                      |
|  Testbench generation has been removed -- the validation agent       |
|  produces its own _tb.sv from the RTL + spec.                        |
|                                                                      |
|  Requires: pip install anthropic                                    |
|  Env:      ANTHROPIC_API_KEY                                         |
+======================================================================+
"""

from __future__ import annotations

import json
import os
import re
import math
import time
from pathlib import Path
from datetime import datetime
from typing import Optional

try:
    import anthropic
except ImportError as e:
    raise ImportError(
        "The LLM-based init_fsm_agent requires the 'anthropic' package.\n"
        "Install with: pip install anthropic"
    ) from e


MODEL_DEFAULT = os.environ.get("CLAUDE_MODEL", "claude-sonnet-4-5")
MAX_TOKENS    = 16000


class InitFsmAgent:
    """LLM-driven init FSM generator. Constructor-compatible with the
    original template agent; accepts an optional `retry_instructions`
    dict so the pipeline's retry loop can feed back failed checks."""

    def __init__(
        self,
        spec_path: str,
        output_dir: str = "./output",
        retry_instructions: dict | None = None,
        model: str = MODEL_DEFAULT,
        temperature: float | None = None,
        max_attempts: int = 2,
    ):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.init_seq = self.spec["initialization_sequence"]
        self.clocking = self.spec["clocking_model"]
        self.timing   = self.spec["timing_model"]
        self.geometry = self.spec["memory_geometry"]

        self.retry_instructions = retry_instructions or {}
        self.model = model
        self.max_attempts = max_attempts

        if temperature is not None:
            self.temperature = temperature
        elif retry_instructions:
            self.temperature = 0.3
        else:
            self.temperature = 0.7

        self.p = self._derive_parameters()
        self.client = anthropic.Anthropic()

    # ================================================================
    # Parameter derivation (deterministic — same math as the original)
    # ================================================================
    def _derive_parameters(self) -> dict:
        p = {}
        tCK_ns         = self.clocking["$derived"]["tCK_ns"]
        ctrl_period_ns = self.clocking["controller_clock_period_ns"]
        ratio          = self.clocking["clock_ratio_ddr_to_controller"]

        p["tCK_ns"]      = tCK_ns
        p["CTRL_PERIOD"] = ctrl_period_ns
        p["CLK_RATIO"]   = ratio

        reset_us = self.init_seq["reset_hold_us"]
        cke_us   = self.init_seq["cke_delay_us"]
        tXPR_ns  = self.init_seq["tXPR_ns"]
        tZQ_ns   = self.init_seq["tZQinit_ns"]

        p["RESET_HOLD_US"]  = reset_us
        p["CKE_DELAY_US"]   = cke_us
        p["tXPR_ns"]        = tXPR_ns
        p["tZQinit_ns"]     = tZQ_ns

        p["WAIT_RESET"] = math.ceil(reset_us * 1000 / ctrl_period_ns)
        p["WAIT_CKE"]   = math.ceil(cke_us   * 1000 / ctrl_period_ns)
        p["WAIT_TXPR"]  = math.ceil(tXPR_ns        / ctrl_period_ns)
        p["WAIT_ZQCL"]  = math.ceil(tZQ_ns         / ctrl_period_ns)

        max_wait = max(p["WAIT_RESET"], p["WAIT_CKE"], p["WAIT_TXPR"], p["WAIT_ZQCL"])
        p["CTR_WIDTH"]  = max(1, max_wait.bit_length())
        p["MAX_WAIT"]   = max_wait
        p["DDR_ADDR_W"] = max(self.geometry["row_bits"], self.geometry["column_bits"])
        p["DDR_BANK_W"] = self.geometry["bank_bits"]

        p["MR0_HEX"] = self._encode_mr0()
        p["MR1_HEX"] = self._encode_mr1()
        p["MR2_HEX"] = self._encode_mr2()
        p["MR3_HEX"] = self._encode_mr3()

        # ZQCL command address: bit 10 must be 1 (long calibration), all
        # other bits 0. Computed in Python so the LLM does not have to
        # count bits in a binary literal — a known failure mode where
        # the LLM placed the '1' at bit 9 instead of bit 10.
        zqcl_val = (1 << 10)
        hex_width = (p["DDR_ADDR_W"] + 3) // 4  # nibbles needed
        p["ZQCL_ADDR_HEX"] = f"{zqcl_val:0{hex_width}X}"
        return p

    def _encode_mr0(self) -> str:
        mr0 = self.init_seq["mode_registers"]["MR0"]
        cl = mr0["cas_latency_cycles"]
        wr_nCK = math.ceil(mr0["write_recovery_ns"] / self.clocking["$derived"]["tCK_ns"])
        cl_map = {5:0b0001,6:0b0010,7:0b0011,8:0b0100,9:0b0101,10:0b0110,11:0b0111,13:0b1000,14:0b1001}
        wr_map = {5:0b001,6:0b010,7:0b011,8:0b100,10:0b101,12:0b110,14:0b111,16:0b000}
        cl_enc = cl_map.get(cl, 0b0111)
        wr_enc = wr_map.get(wr_nCK, 0b110)
        val  = 0
        val |= (cl_enc & 1) << 2
        val |= ((cl_enc >> 1) & 0b111) << 4
        val |= 1 << 8
        val |= (wr_enc & 0b111) << 9
        val |= (1 if mr0.get("precharge_pd_mode") == "fast_exit" else 0) << 12
        return f"{val:04X}"

    def _encode_mr1(self) -> str:
        mr1 = self.init_seq["mode_registers"]["MR1"]
        val = 0
        val |= (0 if mr1.get("dll_enable", True) else 1)
        if mr1.get("output_drive_strength") == "RZQ_7":
            val |= 1 << 1
        rtt_map = {"disabled":0,"RZQ_4":1,"RZQ_2":2,"RZQ_6":3,"RZQ_12":4,"RZQ_8":5}
        rtt = rtt_map.get(mr1.get("rtt_nom", "RZQ_4"), 1)
        val |= (rtt & 1) << 2
        val |= ((rtt >> 1) & 1) << 6
        val |= ((rtt >> 2) & 1) << 9
        if mr1.get("write_leveling_enable", False):
            val |= 1 << 7
        return f"{val:04X}"

    def _encode_mr2(self) -> str:
        mr2 = self.init_seq["mode_registers"]["MR2"]
        cwl_enc = mr2["cas_write_latency_cycles"] - 5
        rtt_wr_map = {"disabled":0,"RZQ_4":1,"RZQ_2":2}
        rtt_wr = rtt_wr_map.get(mr2.get("rtt_wr","RZQ_4"), 1)
        val = ((cwl_enc & 0b111) << 3) | ((rtt_wr & 0b11) << 9)
        return f"{val:04X}"

    def _encode_mr3(self) -> str:
        mr3 = self.init_seq["mode_registers"]["MR3"]
        val = (1 << 2) if mr3.get("mpr_enable", False) else 0
        return f"{val:04X}"

    # ================================================================
    # Prompt construction
    # ================================================================
    def _validator_contract(self) -> str:
        """The validator regex-matches specific identifiers AND the auto-
        generated testbench assumes a specific FSM encoding. List both
        explicitly so the LLM cannot accidentally diverge."""
        p = self.p
        return f"""
HARD NAMING CONTRACT (the downstream validator pattern-matches these
identifiers — do not rename or alias them):

  Module name:                init_fsm
  Localparam wait counts (MUST appear with exactly these names and values):
    localparam WAIT_RESET   = {p['WAIT_RESET']};
    localparam WAIT_CKE     = {p['WAIT_CKE']};
    localparam WAIT_TXPR    = {p['WAIT_TXPR']};
    localparam WAIT_ZQCL    = {p['WAIT_ZQCL']};
  Mode register values (MUST appear with these names and exact hex):
    localparam [{p['DDR_ADDR_W']-1}:0] MR0_VAL = {p['DDR_ADDR_W']}'h{p['MR0_HEX']};
    localparam [{p['DDR_ADDR_W']-1}:0] MR1_VAL = {p['DDR_ADDR_W']}'h{p['MR1_HEX']};
    localparam [{p['DDR_ADDR_W']-1}:0] MR2_VAL = {p['DDR_ADDR_W']}'h{p['MR2_HEX']};
    localparam [{p['DDR_ADDR_W']-1}:0] MR3_VAL = {p['DDR_ADDR_W']}'h{p['MR3_HEX']};
  Parameter:
    parameter DDR_ADDR_W = {p['DDR_ADDR_W']};

REQUIRED FSM ENCODING (the auto-generated testbench checks state values
numerically — these values are MANDATORY, not suggestions):

    typedef enum logic [3:0] {{
        S_IDLE       = 4'd0,   // before enable; init_reset_n=0, init_cke=0
        S_RESET_LOW  = 4'd1,   // RESET# low for WAIT_RESET cycles
        S_RESET_HIGH = 4'd2,   // RESET# high, CKE low, for WAIT_CKE cycles
        S_TXPR_WAIT  = 4'd3,   // CKE high, wait WAIT_TXPR cycles
        S_MR2        = 4'd4,
        S_MR3        = 4'd5,
        S_MR1        = 4'd6,
        S_MR0        = 4'd7,
        S_ZQCL       = 4'd8,
        S_ZQCL_WAIT  = 4'd9,   // wait WAIT_ZQCL cycles
        S_DONE       = 4'd14   // init_done asserted ONLY here
    }} state_t;

    The S_DONE = 4'd14 encoding is REQUIRED. Do not renumber it.

CRITICAL OUTPUT BEHAVIOR (the testbench checks all of these):
  - init_reset_n MUST be low whenever state == S_IDLE OR state == S_RESET_LOW.
    It must go high in S_RESET_HIGH and stay high for the rest of init.
  - init_cke MUST be low whenever state IN {{S_IDLE, S_RESET_LOW, S_RESET_HIGH}}.
    It must go high in S_TXPR_WAIT and stay high.

  - init_cmd_valid MUST be COMBINATIONAL (driven from `always_comb`, not
    registered). It MUST be high in EXACTLY these states and ONLY these:
    {{S_MR2, S_MR3, S_MR1, S_MR0, S_ZQCL}}. It MUST be 0 in EVERY other
    state, especially S_TXPR_WAIT, S_ZQCL_WAIT, S_DONE, S_IDLE, S_RESET_LOW,
    and S_RESET_HIGH. Drive it from the combinational state-decode case
    block; do NOT register it (registering causes a one-cycle bleed into
    the wait state, which fails the "spurious cmd_valid" check).

  - When issuing ZQCL in state S_ZQCL, init_addr MUST equal exactly
    {p['DDR_ADDR_W']}'h{p['ZQCL_ADDR_HEX']} — this hex value has bit 10 set
    (long calibration mode per JEDEC) and all other bits zero. Use this
    HEX literal verbatim. Do NOT hand-write a binary literal like
    15'b0000_0100_0000_000 — counting bits in long binary literals is
    error-prone and will place the '1' at the wrong position. The
    testbench checks `init_addr[10] === 1'b1` at the moment ZQCL fires.

  - init_done MUST be asserted ONLY in S_DONE (state == 4'd14) and held high
    there. It must be 0 in every other state, including S_IDLE.
  - On reset (rst_n low) or before enable, state must be S_IDLE (4'd0).

  Required output port:        output logic init_done
  ZQCL command:                The literal token "ZQCL" must appear
                                in source (state name or comment is OK)
"""

    def _required_ports(self) -> str:
        p = self.p
        return f"""
═══════════════════════════════════════════════════════════════════
CRITICAL: MODULE HEADER MUST BEGIN EXACTLY LIKE THIS
═══════════════════════════════════════════════════════════════════
The first non-comment line of your output MUST be `module init_fsm #(`
followed by the parameter block, THEN the port list. If you write
`module init_fsm (` (no `#(...)` block), DDR_ADDR_W and DDR_BANK_W
will be undeclared identifiers when the port list references them on
lines 9-10, and xrun will fail to parse the file. The compile error
looks like: *E,UNDIDN 'DDR_ADDR_W': undeclared identifier.

COPY THIS HEADER VERBATIM (only the body inside the module is yours
to write):

  module init_fsm #(
      parameter int DDR_ADDR_W = {p['DDR_ADDR_W']},
      parameter int DDR_BANK_W = {p['DDR_BANK_W']},
      parameter int CTR_WIDTH  = {p['CTR_WIDTH']}
  ) (
      input  logic                    clk,
      input  logic                    rst_n,            // active-low async reset
      input  logic                    enable,           // start init when high
      output logic                    init_done,
      output logic                    init_fail,
      output logic                    init_cmd_valid,
      output logic [3:0]              init_cmd,         // {{cs_n, ras_n, cas_n, we_n}}
      output logic [DDR_ADDR_W-1:0]   init_addr,        // MR data / row address
      output logic [DDR_BANK_W-1:0]   init_bank,        // MR select for MRS commands
      output logic                    init_cke,
      output logic                    init_reset_n,
      output logic [3:0]              init_state        // for debug
  );

The `#(parameter int DDR_ADDR_W = ...)` block is NOT optional. It
MUST appear before the `(` that opens the port list.
═══════════════════════════════════════════════════════════════════
"""

    def _build_prompt(self) -> str:
        p = self.p
        spec_slice = {
            "initialization_sequence": self.init_seq,
            "clocking_model": self.clocking,
            "memory_geometry": self.geometry,
            "timing_model": {k: v for k, v in self.timing.items()
                             if k in ("tCK_ns", "CL_cycles", "CWL_cycles", "tRFC", "speed_bin")},
        }

        retry_block = ""
        if self.retry_instructions:
            failed = self.retry_instructions.get("failed_checks", [])
            retry_block = (
                "\n\nPREVIOUS ATTEMPT FAILED these validator checks. "
                "Fix them while preserving everything that passed:\n"
            )
            for c in failed[:20]:
                retry_block += (
                    f"  - [{c.get('id','?')}] {c.get('name','?')}\n"
                    f"      expected: {c.get('expected','?')}\n"
                    f"      actual:   {c.get('actual','?')}\n"
                )

        return f"""You are generating SYNTHESIZABLE SystemVerilog for a DDR3-1600
memory controller initialization FSM. Implement the JEDEC JESD79-3F
section 4.6 power-up sequence:

  RESET# low ({p['RESET_HOLD_US']} us = {p['WAIT_RESET']} ctrl cycles)
  -> RESET# high, hold CKE low ({p['CKE_DELAY_US']} us = {p['WAIT_CKE']} cycles)
  -> CKE high, wait tXPR ({p['tXPR_ns']} ns = {p['WAIT_TXPR']} cycles)
  -> issue MR2, MR3, MR1, MR0 (in that order; MR0 includes DLL reset)
  -> issue ZQCL with A10=1, wait tZQinit ({p['tZQinit_ns']} ns = {p['WAIT_ZQCL']} cycles)
  -> assert init_done (held high, only in S_DONE)

DDR3 command encoding (cs_n, ras_n, cas_n, we_n):
  MRS  = 4'b0000
  ZQCL = 4'b0110 (with A10 = 1)
  NOP  = 4'b0111
  DES  = 4'b1xxx (deselect — drive cs_n high)

{self._required_ports()}
{self._validator_contract()}

SPEC SLICE (authoritative for all numeric values):
{json.dumps(spec_slice, indent=2)}
{retry_block}

OUTPUT FORMAT:
Return ONLY a single SystemVerilog file inside a ```systemverilog code
fence. No prose before or after. The file must compile cleanly with
xrun -sysv. Use `always_ff` / `always_comb`, no latches, no blocking
assignments in sequential blocks."""

    # ================================================================
    # LLM call + extraction
    # ================================================================
    def _call_llm(self, prompt: str) -> str:
        last_err = None
        for attempt in range(1, self.max_attempts + 1):
            try:
                msg = self.client.messages.create(
                    model=self.model,
                    max_tokens=MAX_TOKENS,
                    temperature=self.temperature,
                    messages=[{"role": "user", "content": prompt}],
                )
                text = "".join(b.text for b in msg.content if getattr(b, "type", "") == "text")
                if text.strip():
                    return text
                last_err = "empty response"
            except Exception as e:  # noqa: BLE001
                last_err = str(e)
                time.sleep(2 ** attempt)
        raise RuntimeError(f"LLM call failed after {self.max_attempts} attempts: {last_err}")

    @staticmethod
    def _extract_sv(text: str) -> str:
        for tag in ("systemverilog", "verilog", "sv", ""):
            pat = rf"```{tag}\s*\n(.*?)```" if tag else r"```\s*\n(.*?)```"
            m = re.search(pat, text, re.DOTALL)
            if m:
                return m.group(1).strip() + "\n"
        return text.strip() + "\n"

    @staticmethod
    def _sv_sanity_check(rtl: str) -> str | None:
        """Return an error description string if the RTL has a known
        compile-breaking pattern, else None. These checks catch issues
        that would waste cluster sim time if not caught locally."""
        # Check 1: module header has #(...) parameter block before port list
        m = re.search(r"module\s+init_fsm\s*([^;]+?);", rtl, re.DOTALL)
        if not m:
            return "Could not find `module init_fsm` declaration in output."
        header = m.group(1)
        if "#(" not in header:
            return (
                "Module header is missing the parameter block `#(...)`. "
                "You wrote `module init_fsm (` but it must be "
                "`module init_fsm #( parameter int DDR_ADDR_W = ..., "
                "parameter int DDR_BANK_W = ..., parameter int CTR_WIDTH = ... ) (`. "
                "Without this, DDR_ADDR_W and DDR_BANK_W are undeclared "
                "when the port list references them, and xrun fails to parse."
            )
        # Check 2: port list actually references the parameters
        if "DDR_ADDR_W" not in header or "DDR_BANK_W" not in header:
            return (
                "Module header references parameters that are not declared. "
                "Make sure DDR_ADDR_W and DDR_BANK_W appear in the `#(...)` "
                "block before being used in the port list."
            )
        return None

    # ================================================================
    # Testbench generation (independent LLM call)
    # ================================================================
    def _build_tb_prompt(self) -> str:
        """Prompt for the testbench LLM call. Independent from RTL prompt
        so the testbench can validate observable behavior without copying
        from the RTL implementation.

        CRITICAL: we explicitly prescribe the sampling model to prevent
        off-by-one sampling bugs. The LLM, left to its own devices, tends
        to write counters that either double-count or miss-count a single
        cycle at phase boundaries. We force a specific, correct pattern.
        """
        p = self.p
        return f"""You are writing a self-checking SystemVerilog testbench for a
DDR3-1600 memory controller initialization FSM. The testbench will be run
in Cadence Xcelium (xrun -sysv) and grades the DUT pass/fail.

You are NOT being shown the DUT implementation — you are writing tests
against the SPEC'd behavior. This independence is intentional.

DUT MODULE INTERFACE (the testbench instantiates this):

  module init_fsm #(
      parameter int DDR_ADDR_W = {p['DDR_ADDR_W']},
      parameter int DDR_BANK_W = {p['DDR_BANK_W']}
  ) (
      input  logic                    clk,            // 200 MHz
      input  logic                    rst_n,          // active-low async
      input  logic                    enable,         // pulse to start init
      output logic                    init_done,      // high in S_DONE only
      output logic                    init_fail,
      output logic                    init_cmd_valid, // 1 cycle per cmd
      output logic [3:0]              init_cmd,       // {{cs_n,ras_n,cas_n,we_n}}
      output logic [DDR_ADDR_W-1:0]   init_addr,
      output logic [DDR_BANK_W-1:0]   init_bank,
      output logic                    init_cke,
      output logic                    init_reset_n,
      output logic [3:0]              init_state      // FSM state, debug only
  );

EXPECTED BEHAVIOR (per JEDEC JESD79-3F section 4.6 + spec):

  1. After reset, FSM stays IDLE until `enable` pulses high.
  2. Drive RESET# (init_reset_n) low for >= {p['WAIT_RESET']} cycles ({p['RESET_HOLD_US']} us).
  3. Release RESET#, hold CKE low for >= {p['WAIT_CKE']} cycles ({p['CKE_DELAY_US']} us).
  4. Release CKE, wait >= {p['WAIT_TXPR']} cycles (tXPR = {p['tXPR_ns']} ns).
  5. Issue MRS commands in order: bank=2 (MR2), bank=3 (MR3), bank=1 (MR1), bank=0 (MR0).
     Each MRS is one cycle of init_cmd_valid=1 with init_cmd=4'b0000.
  6. Issue ZQCL: init_cmd=4'b0110, init_addr[10]=1 (long calibration), bank=0.
  7. Wait >= {p['WAIT_ZQCL']} cycles (tZQinit = {p['tZQinit_ns']} ns).
  8. Assert init_done high, hold high (ONLY in S_DONE state, init_state=4'd14).

EXPECTED MR ADDRESS VALUES (the testbench checks these on the wire):
  MR0 = 15'h{p['MR0_HEX']}    MR1 = 15'h{p['MR1_HEX']}
  MR2 = 15'h{p['MR2_HEX']}    MR3 = 15'h{p['MR3_HEX']}

═══════════════════════════════════════════════════════════════════
MANDATORY SAMPLING MODEL (READ CAREFULLY — off-by-one bugs here fail
legitimate RTL):
═══════════════════════════════════════════════════════════════════

The RTL uses counters of the form `counter == WAIT_N - 1` to spend
exactly WAIT_N cycles in each phase (cycles 0..WAIT_N-1). Your
testbench MUST count those cycles correctly or you will undercount.

RULE 1 -- Sample output signals on the posedge BEFORE incrementing any
          cycle counter. The signal is what the RTL drove during the
          cycle that just ended. If you increment first and then sample,
          you will miss the cycle where the signal first went low.

RULE 2 -- When counting "cycles where signal X was at value V", use
          this EXACT pattern:

            always @(posedge clk) begin
              if (rst_n) begin
                if (signal_X == V) count_X <= count_X + 1;
              end
            end

          Do NOT gate on sentinels like "release_cycle != -1" or
          "have_seen_transition" — those introduce a one-cycle blind
          spot at the phase boundary. Just count every cycle the
          signal is at the target value for as long as the simulation
          runs. If the RTL is correct the count will be exact.

RULE 3 -- Thresholds for pass checks MUST use the spec values exactly:
            RESET# low cycles >= {p['WAIT_RESET']}
            CKE low cycles during the CKE-delay phase >= {p['WAIT_CKE']}
          If your measured count comes out as {p['WAIT_RESET']-1} or {p['WAIT_CKE']-1},
          your counter logic is wrong — the RTL holds exactly
          {p['WAIT_RESET']} / {p['WAIT_CKE']} cycles. Fix the TB, not the
          threshold.

RULE 4 -- For the "CKE stayed low during reset/CKE-wait phases" check,
          count the NUMBER OF CYCLES where an illegal CKE=1 was
          observed while init_reset_n was low. The check passes iff
          that count is zero. Do NOT try to detect the legitimate
          low->high transition and skip it — just observe that while
          RESET# is low, CKE must never be 1. The CKE-delay phase
          (RESET# high, CKE low) is self-terminating: as soon as CKE
          goes high you are by definition out of that phase, so "was
          CKE high before the legitimate transition" is a nonsense
          question.

          Use this simple pattern:

            always @(posedge clk) begin
              if (rst_n && !init_reset_n && init_cke) begin
                cke_violations <= cke_violations + 1;
              end
            end

          Then the check is just `cke_violations == 0`. Any other
          framing (flags, sentinels, first-transition skipping) will
          introduce off-by-one bugs.

═══════════════════════════════════════════════════════════════════

REQUIREMENTS FOR THE TESTBENCH:
  - Module name: init_fsm_tb
  - Drive 200 MHz clock (5.0 ns period): always #2.5 clk = ~clk;
  - Apply async reset (rst_n=0 for 10 cycles), then deassert, then pulse enable.
  - Use a TIMEOUT of about {p['WAIT_RESET'] + p['WAIT_CKE'] + p['WAIT_TXPR'] + p['WAIT_ZQCL'] + 5000} cycles
  - At minimum, check ALL of these as separate self-checking tests with [PASS]/[FAIL] prints:
      * init_done eventually asserts
      * init_fail never asserts
      * init_state reaches 4'd14 (S_DONE)
      * RESET# low for >= {p['WAIT_RESET']} cycles (see RULE 2, RULE 3)
      * CKE low for >= {p['WAIT_CKE']} cycles during CKE-delay phase (see RULE 2)
      * Exactly 4 MRS commands issued
      * MR program order is bank 2 -> 3 -> 1 -> 0
      * MR address values match (MR2=0x{p['MR2_HEX']}, MR3=0x{p['MR3_HEX']}, MR1=0x{p['MR1_HEX']}, MR0=0x{p['MR0_HEX']})
      * ZQCL command (4'b0110) is issued at least once
      * ZQCL has init_addr[10] === 1'b1
      * CKE-during-reset violation count == 0 (see RULE 4)
  - Print "[PASS] N: <name>" or "[FAIL] N: <name>" per check, with the
    actual measured value included when it failed.
  - Print a final summary line "ALL N TESTS PASSED" or "M of N TESTS FAILED"
  - Call $finish at the end
  - $dumpfile("init_fsm_tb.vcd"); $dumpvars(0, init_fsm_tb); for waveform debug

DO NOT couple to the DUT's internal state numbering beyond the values
listed above (init_state=4'd14 for done). Don't assume specific state
numbers for intermediate states — observe behavior on the output ports
instead.

OUTPUT FORMAT:
Return ONLY the SystemVerilog file inside a ```systemverilog code fence.
No prose before or after. Must compile cleanly with xrun -sysv."""

    @staticmethod
    def _tb_sanity_check(tb: str) -> str | None:
        """Catch obvious testbench problems before writing to disk."""
        if "module init_fsm_tb" not in tb:
            return "Testbench is missing `module init_fsm_tb` declaration."
        if "init_fsm" not in tb or "dut" not in tb.lower():
            return "Testbench does not appear to instantiate the init_fsm DUT."
        if "$finish" not in tb:
            return "Testbench is missing $finish — simulation would hang."
        if "[PASS]" not in tb and "[FAIL]" not in tb:
            return (
                "Testbench does not print [PASS]/[FAIL] markers — "
                "sim parser will see 0 tests."
            )
        # Catch the two most common off-by-one patterns. If either of
        # these appears, the LLM has regressed to the pattern we keep
        # seeing fail. Force a regenerate.
        if re.search(r"release_cycle\s*!=\s*-1\s*&&.*init_cke", tb):
            return (
                "TB uses a `release_cycle != -1` sentinel to gate the CKE "
                "check. This pattern has a one-cycle blind spot at the "
                "phase boundary and produces spurious failures. Use the "
                "simple pattern from RULE 4 instead: count cycles where "
                "(!init_reset_n && init_cke) unconditionally."
            )
        return None

    def generate_testbench(self) -> tuple[str, int]:
        """Run the LLM testbench-generation pipeline. Returns (tb_text, lines)."""
        prompt = self._build_tb_prompt()
        tb = ""
        for local_try in range(1, self.max_attempts + 1):
            tb_text = self._call_llm(prompt)
            tb = self._extract_sv(tb_text)
            err = self._tb_sanity_check(tb)
            if err is None:
                break
            print(f"  ! TB sanity check failed (try {local_try}/{self.max_attempts}): {err}")
            prompt = (
                self._build_tb_prompt()
                + "\n\nYOUR LAST OUTPUT FAILED A LOCAL SANITY CHECK:\n"
                + f"  {err}\n"
                + "Regenerate the testbench fixing this specific issue."
            )
        else:
            print(f"  ! WARNING: TB sanity still failing after {self.max_attempts} tries.")
        return tb, len(tb.splitlines())

    # ================================================================
    # Manifest
    # ================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "init_fsm",
            "file": "init_fsm.sv",
            "phase": 1,
            "agent": "init_fsm_agent_llm",
            "spec_version": self.spec.get("schema_version"),
            "design_id": self.spec.get("design_id"),
            "generator": {
                "model": self.model,
                "temperature": self.temperature,
                "deterministic": False,
            },
            "parameters": {
                "DDR_ADDR_W":    p["DDR_ADDR_W"],
                "DDR_BANK_W":    p["DDR_BANK_W"],
                "CTR_WIDTH":     p["CTR_WIDTH"],
                "WAIT_RESET":    p["WAIT_RESET"],
                "WAIT_CKE":      p["WAIT_CKE"],
                "WAIT_TXPR":     p["WAIT_TXPR"],
                "WAIT_ZQCL":     p["WAIT_ZQCL"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk",   "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "control": [{"name": "enable", "width": 1, "dir": "input"}],
                "status_out": [
                    {"name": "init_done", "width": 1, "dir": "output"},
                    {"name": "init_fail", "width": 1, "dir": "output"},
                ],
                "ddr_cmd_out": [
                    {"name": "init_cmd_valid", "width": 1, "dir": "output"},
                    {"name": "init_cmd",       "width": 4, "dir": "output"},
                    {"name": "init_addr",      "width": p["DDR_ADDR_W"], "dir": "output"},
                    {"name": "init_bank",      "width": p["DDR_BANK_W"], "dir": "output"},
                ],
                "ddr_ctrl_out": [
                    {"name": "init_cke",     "width": 1, "dir": "output"},
                    {"name": "init_reset_n", "width": 1, "dir": "output"},
                ],
                "debug": [{"name": "init_state", "width": 4, "dir": "output"}],
            },
            "assertions": [
                {"name": "p_cke_low_during_reset", "check": "IN-002"},
                {"name": "p_done_only_in_done",    "check": "IN-005"},
                {"name": "p_zqcl_a10",             "check": "IN-010"},
            ],
            "coverage_points": ["cp_state", "cp_mr_cmd", "cp_zq_cmd", "cp_done"],
        }

    # ================================================================
    # Main entry point
    # ================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  INIT / RESET FSM AGENT  (LLM: {self.model}, T={self.temperature})")
        print(f"  Spec: {self.spec_path}")
        if self.retry_instructions:
            n = len(self.retry_instructions.get("failed_checks", []))
            print(f"  Retry mode: {n} prior failures fed back to the model")
        print(hdr)

        print("\n[1/3] Generating RTL via LLM ...")
        prompt = self._build_prompt()
        rtl = ""
        local_attempts = 3  # local sanity-fix retries before giving up
        for local_try in range(1, local_attempts + 1):
            rtl_text = self._call_llm(prompt)
            rtl = self._extract_sv(rtl_text)
            err = self._sv_sanity_check(rtl)
            if err is None:
                break
            print(f"  ! Local sanity check failed (try {local_try}/{local_attempts}): {err}")
            # Append the error to the prompt and retry — the LLM will
            # see exactly what it did wrong without us going through
            # validation -> sim -> retry-loop overhead.
            prompt = (
                self._build_prompt()
                + "\n\nYOUR LAST OUTPUT FAILED A LOCAL SYNTAX SANITY CHECK:\n"
                + f"  {err}\n"
                + "Regenerate the file fixing this specific issue."
            )
        else:
            print(f"  ! WARNING: sanity check still failing after {local_attempts} tries. "
                  f"Writing anyway; xrun will likely fail.")
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines of SystemVerilog")

        print("\n[2/3] Building manifest ...")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  OK: {port_cnt} ports | {len(manifest['assertions'])} assertions")

        print("\n[3/3] Writing files ...")
        rtl_path  = self.output_dir / "init_fsm.sv"
        tb_path   = self.output_dir / "init_fsm_tb.sv"
        mfst_path = self.output_dir / "init_fsm_manifest.json"
        rtl_path.write_text(rtl)
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  -> {rtl_path}\n  -> {mfst_path}")

        # Testbench: generate-once semantics. The TB is independent
        # verification — once it exists, we keep using it across runs
        # (and across RTL regenerations) so failing tests reflect real
        # RTL bugs, not testbench drift. Delete the file to force a
        # fresh generation on the next pipeline run.
        if tb_path.is_file():
            tb_lines = sum(1 for _ in open(tb_path))
            print(f"  -> {tb_path}  (existing testbench kept, {tb_lines} lines)")
        else:
            print(f"\n  Generating testbench via LLM (first run, none on disk) ...")
            tb_text, tb_lines = self.generate_testbench()
            tb_path.write_text(tb_text)
            print(f"  -> {tb_path}  (newly generated, {tb_lines} lines)")

        print(f"\n{hdr}\n  DONE -- init_fsm.sv ready for validation\n{hdr}")
        return {
            "status": "success",
            "module": "init_fsm",
            "phase": 1,
            "rtl_path": str(rtl_path),
            "tb_path": str(tb_path),
            "manifest_path": str(mfst_path),
            "manifest": manifest,
            "rtl_lines": rtl_lines,
            "tb_lines": tb_lines,
            "ports": port_cnt,
        }


# --- Interactive entry point ---
if __name__ == "__main__":
    import sys
    print("+=============================================+")
    print("|     INIT / RESET FSM AGENT  (Phase 1, LLM)  |")
    print("+=============================================+")
    spec = input("Spec JSON path: ").strip() or "ddr3_microarchitecture_spec.json"
    out  = input("Output dir (Enter for ./output): ").strip() or "./output"
    if not os.path.isfile(spec):
        print(f"Not found: {spec}"); sys.exit(1)
    agent = InitFsmAgent(spec, out)
    agent.run()