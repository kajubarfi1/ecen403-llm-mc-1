#!/usr/bin/env python3
"""
+======================================================================+
|                 BANK TRACKER AGENT  (LLM-driven)                     |
|  Phase 2 -- Depends on: Config Registers (config_regs)               |
|  Generates: bank_tracker.sv + bank_tracker_manifest.json             |
|                                                                      |
|  8 independent bank state machines (IDLE/ACTIVE/PRECHARGING).        |
|  Tracks open row per bank, 14 timing counters.                       |
|  Outputs per-bank permission bits (act/rd/wr/pre_allowed).           |
|                                                                      |
|  HYBRID DETERMINISM PATTERN:                                         |
|    - RTL generation:   LLM-driven (Claude API)                       |
|    - Manifest:         DETERMINISTIC (Python)                        |
+======================================================================+
"""

import json, sys, os, math, re, time
from pathlib import Path
from datetime import datetime

try:
    import anthropic
    _HAS_ANTHROPIC = True
except ImportError:
    _HAS_ANTHROPIC = False


class BankTrackerAgent:

    def __init__(
        self,
        spec_path: str,
        output_dir: str = "./output",
        retry_instructions: dict = None,
        model: str = None,
        temperature: float = 0.7,
        max_attempts: int = 3,
    ):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geo = self.spec["memory_geometry"]
        self.ca  = self.spec["controller_architecture"]
        self.tm  = self.spec["timing_model"]
        self.dc  = self.tm["$derived_cycles"]
        self.p   = self._derive()

        # LLM config
        self.retry_instructions = retry_instructions
        self.model = model or os.environ.get("CLAUDE_MODEL", "claude-sonnet-4-5")
        self.temperature = 0.3 if retry_instructions else temperature
        self.max_attempts = max_attempts

    # ==================================================================
    # DETERMINISTIC: parameter derivation
    # ==================================================================
    def _derive(self) -> dict:
        p = {}
        p["ROW_BITS"]  = self.geo["row_bits"]
        p["BANK_BITS"] = self.geo["bank_bits"]
        p["NUM_BANKS"] = 2 ** p["BANK_BITS"]

        timing_params = [
            "tRCD_nCK", "tRP_nCK", "tRAS_nCK", "tRC_nCK",
            "tRRD_nCK", "tFAW_nCK", "tWTR_nCK", "tWR_nCK",
            "tRTP_nCK", "tCCD_nCK", "tRFC_nCK",
        ]
        for tp in timing_params:
            p[tp] = self.dc[tp]

        max_val = max(p[tp] for tp in timing_params)
        p["CTR_WIDTH"] = max(1, max_val.bit_length())

        p["FAW_DEPTH"] = 4
        p["TREFI_nCK"] = self.dc["tREFI_nCK"]

        return p

    # ==================================================================
    # DETERMINISTIC: validation
    # ==================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["NUM_BANKS"] != 8:
            errors.append(f"Expected 8 banks for DDR3, got {p['NUM_BANKS']}")
        if p["tRCD_nCK"] < 1:
            errors.append(f"tRCD must be >= 1, got {p['tRCD_nCK']}")
        return errors

    # ==================================================================
    # LLM: contract (LARGE -- this is the most structural module)
    # ==================================================================
    def _validator_contract(self) -> str:
        p = self.p
        return f"""\
============================================================
HARD NAMING CONTRACT -- VIOLATING ANY RULE REJECTS THE OUTPUT
============================================================

Module declaration MUST be exactly:
    module bank_tracker #(
        parameter NUM_BANKS  = {p['NUM_BANKS']},
        parameter BANK_BITS  = {p['BANK_BITS']},
        parameter ROW_BITS   = {p['ROW_BITS']},
        parameter CTR_WIDTH  = {p['CTR_WIDTH']}
    ) (

Port list (exact names -- the testbench uses `dut(.*)`, so names MUST match):

  input  logic                       clk
  input  logic                       rst_n

  input  logic                       cmd_act_valid
  input  logic [BANK_BITS-1:0]       cmd_act_bank
  input  logic [ROW_BITS-1:0]        cmd_act_row
  input  logic                       cmd_pre_valid
  input  logic [BANK_BITS-1:0]       cmd_pre_bank
  input  logic                       cmd_pre_all
  input  logic                       cmd_rd_valid
  input  logic [BANK_BITS-1:0]       cmd_rd_bank
  input  logic                       cmd_wr_valid
  input  logic [BANK_BITS-1:0]       cmd_wr_bank
  input  logic                       cmd_ref_valid

  input  logic [7:0]                 cfg_tRCD_nCK
  input  logic [7:0]                 cfg_tRP_nCK
  input  logic [7:0]                 cfg_tRAS_nCK
  input  logic [7:0]                 cfg_tRC_nCK
  input  logic [7:0]                 cfg_tRRD_nCK
  input  logic [7:0]                 cfg_tFAW_nCK
  input  logic [7:0]                 cfg_tWTR_nCK
  input  logic [7:0]                 cfg_tWR_nCK
  input  logic [7:0]                 cfg_tRTP_nCK
  input  logic [7:0]                 cfg_tCCD_nCK
  input  logic [7:0]                 cfg_tRFC_nCK

  output logic [NUM_BANKS-1:0]       bank_is_active
  output logic [ROW_BITS-1:0]        bank_open_row [NUM_BANKS]
  output logic [NUM_BANKS-1:0]       bank_act_allowed
  output logic [NUM_BANKS-1:0]       bank_rd_allowed
  output logic [NUM_BANKS-1:0]       bank_wr_allowed
  output logic [NUM_BANKS-1:0]       bank_pre_allowed
  output logic                       all_banks_idle
  output logic                       faw_allows_act

RULES:
  1. Parameter names: NUM_BANKS, BANK_BITS, ROW_BITS, CTR_WIDTH --
     use these exact identifiers, with literal values:
       NUM_BANKS  = {p['NUM_BANKS']}
       BANK_BITS  = {p['BANK_BITS']}
       ROW_BITS   = {p['ROW_BITS']}
       CTR_WIDTH  = {p['CTR_WIDTH']}
  2. Define a 3-state enum with at least these two members:
       BANK_IDLE, BANK_ACTIVE
     (a third state like BANK_PRECHAR is allowed but not required by TB)
  3. Per-bank counter array names (one element per bank, REQUIRED NAMES):
       ctr_rcd, ctr_rp, ctr_ras, ctr_rc, ctr_wtr, ctr_wr, ctr_rtp
  4. Global counter names (shared across banks, REQUIRED NAMES):
       ctr_rrd, ctr_ccd, ctr_rfc
  5. The word "faw" MUST appear in the RTL (FAW tracking).
  6. Include at least one `always_ff @(posedge clk ...)` block and at
     least one `always_comb` block.
  7. End with `endmodule`.

BEHAVIORAL REQUIREMENTS (the testbench relies on these EXACT semantics):

  RESET BEHAVIOR:
    * All banks start in BANK_IDLE with row=0 and all counters=0.
    * bank_is_active   == 8'h00       (no bank active)
    * bank_act_allowed == 8'hFF       (all 8 banks ready to ACT)
    * all_banks_idle   == 1
    * faw_allows_act   == 1

  ACT COMMAND (cmd_act_valid pulse, 1 cycle):
    * Next cycle: bk_state[cmd_act_bank] <= BANK_ACTIVE
    *             bk_row[cmd_act_bank]   <= cmd_act_row
    *             ctr_rcd[cmd_act_bank]  <= cfg_tRCD_nCK
    *             ctr_ras[cmd_act_bank]  <= cfg_tRAS_nCK
    *             ctr_rc[cmd_act_bank]   <= cfg_tRC_nCK
    *             ctr_rrd (global)       <= cfg_tRRD_nCK
    *             FAW window gets a new entry with cfg_tFAW_nCK
    * tRCD must elapse before RD/WR to that bank is allowed.

  PRE COMMAND:
    * cmd_pre_all=1: all banks with state==BANK_ACTIVE go to IDLE.
    * cmd_pre_all=0: just bk_state[cmd_pre_bank] goes to IDLE.
    * ctr_rp[bank] loads cfg_tRP_nCK. Bank cannot re-ACT until rp==0.

  RD COMMAND:
    * ctr_ccd (global) loads cfg_tCCD_nCK.
    * ctr_rtp[cmd_rd_bank] loads cfg_tRTP_nCK.
    * After RD, bank_rd_allowed[b] goes to 0 for tCCD, then returns to 1.

  WR COMMAND:
    * ctr_ccd (global) loads cfg_tCCD_nCK.
    * ctr_wtr[cmd_wr_bank] loads cfg_tWTR_nCK.
    * ctr_wr[cmd_wr_bank]  loads cfg_tWR_nCK.

  REF COMMAND (auto refresh):
    * ctr_rfc (global) loads cfg_tRFC_nCK.
    * All banks forced to BANK_IDLE.
    * During tRFC, bank_act_allowed == 8'h00 for every bank.

  PERMISSION OUTPUTS (always_comb, per bank):
    bank_is_active[i]   = (bk_state[i] == BANK_ACTIVE)
    bank_open_row[i]    = bk_row[i]
    bank_act_allowed[i] = (bk_state[i] == BANK_IDLE)
                        && (ctr_rc[i]  == 0)
                        && (ctr_rp[i]  == 0)
                        && (ctr_rrd    == 0)
                        && (ctr_rfc    == 0)
                        && faw_allows_act
    bank_rd_allowed[i]  = (bk_state[i] == BANK_ACTIVE)
                        && (ctr_rcd[i] == 0)
                        && (ctr_ccd    == 0)
                        && (ctr_rfc    == 0)
    bank_wr_allowed[i]  = (bk_state[i] == BANK_ACTIVE)
                        && (ctr_rcd[i] == 0)
                        && (ctr_ccd    == 0)
                        && (ctr_rfc    == 0)
    bank_pre_allowed[i] = (bk_state[i] == BANK_ACTIVE)
                        && (ctr_ras[i] == 0)
                        && (ctr_rtp[i] == 0)
                        && (ctr_wr[i]  == 0)
                        && (ctr_wtr[i] == 0)
                        && (ctr_rfc    == 0)

  FAW (4 ACTs within tFAW window):
    * Maintain a circular buffer `faw_pipe` of {p['FAW_DEPTH']} slots.
    * Each slot holds a CTR_WIDTH-wide countdown timer.
    * On cmd_act_valid, place cfg_tFAW_nCK into the next slot (round robin).
    * Every cycle, decrement any non-zero slot.
    * faw_allows_act = 1 iff AT LEAST ONE slot is currently 0.
      In other words: faw_allows_act = (faw_pipe[0]==0) || (faw_pipe[1]==0)
                                    || (faw_pipe[2]==0) || (faw_pipe[3]==0)

  COUNTER DECREMENT:
    Every cycle, each non-zero counter (per-bank and global) decrements by 1.
    When a command loads a counter, it overrides the decrement on that cycle.

IMPLEMENTATION GUIDANCE (you choose the implementation):

  STATE ENCODING:
    Define an enum type for bank state with at least BANK_IDLE and
    BANK_ACTIVE members. You may add additional states (e.g. precharge
    in-progress). Choose your own encoding values.

  INTERNAL SIGNALS:
    You need per-bank state, per-bank open row tracking, per-bank timing
    counters for tRCD/tRP/tRAS/tRC/tWTR/tWR/tRTP, and global timing
    counters for tRRD/tCCD/tRFC. Name them as you see fit, but the
    required counter names listed in RULES above (ctr_rcd, ctr_rp, etc.)
    must still be used so the validator can check them.

  FAW IMPLEMENTATION:
    Implement tFAW tracking using any approach you prefer -- circular
    buffer, shift register, or timestamp window. Whatever you choose,
    expose the result as faw_allows_act. The signal name faw_pipe is
    not required -- use whatever internal structure makes sense.

  all_banks_idle:
    Drive all_banks_idle high when no bank has an active row. Implement
    this however you prefer -- reduction, for loop, explicit per-bank
    check, etc.

  faw_allows_act:
    Drive faw_allows_act high when an ACT is permitted by the tFAW
    window constraint. The semantics: no more than 4 ACTs may occur
    within any tFAW-cycle window.

You may add SVA and covergroups inside translate_off guards.
============================================================
"""

    # ==================================================================
    # LLM: prompt
    # ==================================================================
    def _build_prompt(self) -> str:
        p = self.p

        base = f"""\
You are generating SystemVerilog RTL for a DDR3 memory controller bank
tracker module. This is the most structurally complex Phase 2 block --
it maintains 8 per-bank state machines and a large set of DDR3 timing
counters.

SPEC PARAMETERS (all from $derived_cycles at 400 MHz DDR clock):
  NUM_BANKS   = {p['NUM_BANKS']}
  BANK_BITS   = {p['BANK_BITS']}
  ROW_BITS    = {p['ROW_BITS']}
  CTR_WIDTH   = {p['CTR_WIDTH']}
  FAW_DEPTH   = {p['FAW_DEPTH']}

  Timing (nCK at the controller clock):
    tRCD = {p['tRCD_nCK']}   tRP  = {p['tRP_nCK']}   tRAS = {p['tRAS_nCK']}
    tRC  = {p['tRC_nCK']}   tRRD = {p['tRRD_nCK']}   tFAW = {p['tFAW_nCK']}
    tWTR = {p['tWTR_nCK']}   tWR  = {p['tWR_nCK']}   tRTP = {p['tRTP_nCK']}
    tCCD = {p['tCCD_nCK']}   tRFC = {p['tRFC_nCK']}

DESCRIPTION:
  bank_tracker models all DDR3 bank-level timing constraints. It receives
  single-cycle command-valid pulses from the scheduler (cmd_act_valid,
  cmd_pre_valid, cmd_rd_valid, cmd_wr_valid, cmd_ref_valid) and tells
  the scheduler, via combinational permission vectors, which operations
  are legal on which banks THIS cycle.

  Each bank has its own state (IDLE or ACTIVE), its own open row, and
  its own set of bank-local timing counters. Shared timing counters
  (tRRD, tCCD, tRFC) apply across banks.

  tFAW is implemented as a {p['FAW_DEPTH']}-slot circular window of
  countdown timers. Each ACT loads one slot with cfg_tFAW_nCK. An ACT is
  only allowed if at least one slot is currently at 0.

{self._validator_contract()}

Generate the complete `bank_tracker.sv` file. Include a header comment
block, the module declaration with parameters, port list, the state enum,
all required internal declarations, the always_ff block that maintains
state/counters/FAW, the always_comb block that drives the permission
outputs, and the two assign statements for `faw_allows_act` and
`all_banks_idle`, and `endmodule`. Do not include a testbench.

Return the SystemVerilog code inside a single ```systemverilog code block.
"""

        if self.retry_instructions:
            failed = self.retry_instructions.get("failed_checks", [])
            msg = self.retry_instructions.get("message", "Previous attempt failed")
            fb = f"\n\n============================================================\n"
            fb += f"RETRY FEEDBACK ({msg}):\n"
            fb += f"============================================================\n"
            fb += "Validation failures from previous attempt:\n\n"
            for chk in failed[:15]:
                fb += f"  [{chk.get('id','?')}] {chk.get('name','?')}\n"
                fb += f"    expected: {chk.get('expected','?')}\n"
                fb += f"    actual:   {chk.get('actual','?')}\n"
            fb += "\nRe-read the HARD NAMING CONTRACT and fix these failures.\n"
            base += fb

        return base

    # ==================================================================
    # LLM: call
    # ==================================================================
    def _call_llm(self, prompt: str) -> str:
        if not _HAS_ANTHROPIC:
            raise RuntimeError("anthropic package not installed.")
        api_key = os.environ.get("ANTHROPIC_API_KEY")
        if not api_key:
            raise RuntimeError("ANTHROPIC_API_KEY not set.")
        client = anthropic.Anthropic(api_key=api_key)
        resp = client.messages.create(
            model=self.model,
            max_tokens=8192,  # bank_tracker is large
            temperature=self.temperature,
            messages=[{"role": "user", "content": prompt}],
        )
        return "".join(b.text for b in resp.content if hasattr(b, "text"))

    # ==================================================================
    # LLM: extract
    # ==================================================================
    def _extract_sv(self, out: str) -> str:
        for pat in [
            r"```systemverilog\s*\n(.*?)```",
            r"```sv\s*\n(.*?)```",
            r"```verilog\s*\n(.*?)```",
            r"```\s*\n(.*?)```",
        ]:
            m = re.search(pat, out, re.DOTALL)
            if m:
                return m.group(1).strip()
        m = re.search(r"(module\s+bank_tracker\b.*?endmodule)", out, re.DOTALL)
        if m:
            return m.group(1).strip()
        raise ValueError("No SystemVerilog code block found.")

    # ==================================================================
    # LLM: sanity checks
    # ==================================================================
    def _sv_sanity_check(self, rtl: str) -> list:
        p = self.p
        problems = []
        rtl_no_sva = re.sub(
            r"//\s*(?:synopsys|synthesis)\s+translate_off.*?//\s*(?:synopsys|synthesis)\s+translate_on",
            "", rtl, flags=re.DOTALL,
        )

        # Guard 1: module / endmodule
        if "module bank_tracker" not in rtl:
            problems.append("module bank_tracker not found")
        if "endmodule" not in rtl:
            problems.append("endmodule missing")

        # Guard 2: parameter literals
        for pname, pval in [
            ("NUM_BANKS", p["NUM_BANKS"]),
            ("BANK_BITS", p["BANK_BITS"]),
            ("ROW_BITS",  p["ROW_BITS"]),
            ("CTR_WIDTH", p["CTR_WIDTH"]),
        ]:
            if not re.search(rf"parameter\s+{pname}\s*=\s*{pval}\b", rtl):
                problems.append(f"parameter {pname} = {pval} not found")

        # Guard 3: required cmd_* input ports (TB uses dut(.*))
        required_cmd = [
            "cmd_act_valid", "cmd_act_bank", "cmd_act_row",
            "cmd_pre_valid", "cmd_pre_bank", "cmd_pre_all",
            "cmd_rd_valid",  "cmd_rd_bank",
            "cmd_wr_valid",  "cmd_wr_bank",
            "cmd_ref_valid",
        ]
        for s in required_cmd:
            if s not in rtl:
                problems.append(f"cmd port `{s}` missing")

        # Guard 4: required cfg_* ports
        required_cfg = [
            "cfg_tRCD_nCK", "cfg_tRP_nCK", "cfg_tRAS_nCK", "cfg_tRC_nCK",
            "cfg_tRRD_nCK", "cfg_tFAW_nCK", "cfg_tWTR_nCK", "cfg_tWR_nCK",
            "cfg_tRTP_nCK", "cfg_tCCD_nCK", "cfg_tRFC_nCK",
        ]
        for s in required_cfg:
            if s not in rtl:
                problems.append(f"cfg port `{s}` missing")

        # Guard 5: required output signals
        required_out = [
            "bank_is_active", "bank_open_row",
            "bank_act_allowed", "bank_rd_allowed",
            "bank_wr_allowed", "bank_pre_allowed",
            "all_banks_idle", "faw_allows_act",
        ]
        for s in required_out:
            if s not in rtl:
                problems.append(f"output port `{s}` missing")

        # Guard 6: state enum members
        for s in ["BANK_IDLE", "BANK_ACTIVE"]:
            if s not in rtl:
                problems.append(f"enum member `{s}` missing")

        # Guard 7: per-bank counter names
        for s in ["ctr_rcd", "ctr_rp", "ctr_ras", "ctr_rc",
                  "ctr_wtr", "ctr_wr", "ctr_rtp"]:
            if s not in rtl:
                problems.append(f"per-bank counter `{s}` missing")

        # Guard 8: global counter names
        for s in ["ctr_rrd", "ctr_ccd", "ctr_rfc"]:
            if s not in rtl:
                problems.append(f"global counter `{s}` missing")

        # Guard 9: FAW mentioned
        if "faw" not in rtl.lower():
            problems.append("FAW logic missing ('faw' not found in RTL)")

        # Guard 10: faw tracking present (any implementation)
        if "faw" not in rtl.lower():
            problems.append("FAW tracking logic missing ('faw' not found in RTL)")

        # Guard 11: always_ff and always_comb both present
        if not re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk", rtl):
            problems.append("always_ff @(posedge clk ...) block missing")
        if "always_comb" not in rtl:
            problems.append("always_comb block missing (permission outputs)")

        # Guard 12: faw_allows_act must be driven (any implementation)
        if not re.search(r"faw_allows_act", rtl_no_sva):
            problems.append("faw_allows_act signal missing")

        # Guard 13: all_banks_idle must be driven (any implementation)
        if not re.search(r"all_banks_idle", rtl_no_sva):
            problems.append("all_banks_idle signal missing")

        # Guard 14: no NBA on combinational output vectors
        # (may be indexed: `bank_is_active[j] <= ...` in a for loop)
        for comb_out in ["bank_is_active", "bank_act_allowed",
                         "bank_rd_allowed", "bank_wr_allowed",
                         "bank_pre_allowed"]:
            if re.search(rf"\b{comb_out}(\s*\[[^\]]*\])?\s*<=", rtl_no_sva):
                problems.append(
                    f"{comb_out} must be combinational (assign or always_comb, not NBA)"
                )

        return problems

    # ==================================================================
    # DETERMINISTIC: manifest
    # ==================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "bank_tracker", "file": "bank_tracker.sv",
            "phase": 2, "agent": "bank_tracker_agent",
            "dependencies": ["config_regs"],
            "parameters": {
                "NUM_BANKS": p["NUM_BANKS"], "BANK_BITS": p["BANK_BITS"],
                "ROW_BITS":  p["ROW_BITS"],  "CTR_WIDTH": p["CTR_WIDTH"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "cmd_feedback": [
                    {"name": "cmd_act_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_act_bank", "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_act_row",  "width": p["ROW_BITS"],  "dir": "input"},
                    {"name": "cmd_pre_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_pre_bank", "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_pre_all",  "width": 1, "dir": "input"},
                    {"name": "cmd_rd_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_rd_bank",  "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_wr_valid", "width": 1, "dir": "input"},
                    {"name": "cmd_wr_bank",  "width": p["BANK_BITS"], "dir": "input"},
                    {"name": "cmd_ref_valid", "width": 1, "dir": "input"},
                ],
                "config_in": [
                    {"name": f"cfg_{n}_nCK", "width": 8, "dir": "input",
                     "source": f"config_regs.cfg_{n}_nCK"}
                    for n in ["tRCD", "tRP", "tRAS", "tRC", "tRRD", "tFAW",
                             "tWTR", "tWR", "tRTP", "tCCD", "tRFC"]
                ],
                "status_out": [
                    {"name": "bank_is_active",   "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_open_row",    "width": f"{p['NUM_BANKS']}x{p['ROW_BITS']}", "dir": "output"},
                    {"name": "bank_act_allowed", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_rd_allowed",  "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_wr_allowed",  "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "bank_pre_allowed", "width": p["NUM_BANKS"], "dir": "output"},
                    {"name": "all_banks_idle",   "width": 1, "dir": "output"},
                    {"name": "faw_allows_act",   "width": 1, "dir": "output"},
                ],
            },
        }

    # ==================================================================
    # MAIN
    # ==================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        mode = "LLM (retry)" if self.retry_instructions else "LLM (cold)"
        print(f"{hdr}\n  BANK TRACKER AGENT -- {mode}")
        print(f"  Model:   {self.model}")
        print(f"  Temp:    {self.temperature}")
        print(f"  Spec:    {self.spec_path}\n{hdr}")

        print("\n[1/4] Validating spec ...")
        errs = self.validate()
        if errs:
            for e in errs:
                print(f"  x {e}")
            return {"status": "error", "errors": errs}
        print("  + Valid")
        for k, v in self.p.items():
            print(f"    {k:12s} = {v}")

        print("\n[2/4] Generating RTL via LLM ...")
        rtl = None
        last_problems = []
        prompt = self._build_prompt()

        for attempt in range(1, self.max_attempts + 1):
            print(f"  -> Attempt {attempt}/{self.max_attempts} "
                  f"(temp={self.temperature})...")
            try:
                llm_out = self._call_llm(prompt)
                candidate = self._extract_sv(llm_out)
            except Exception as e:
                print(f"  x LLM call failed: {e}")
                if attempt == self.max_attempts:
                    return {"status": "error",
                            "errors": [f"LLM call failed: {e}"]}
                time.sleep(2)
                continue

            problems = self._sv_sanity_check(candidate)
            if not problems:
                rtl = candidate
                print(f"  + RTL passed sanity check ({len(rtl.splitlines())} lines)")
                break

            print(f"  x sanity check failed ({len(problems)} issue(s)):")
            for pr in problems[:8]:
                print(f"    - {pr}")
            last_problems = problems

            feedback = (
                "\n\nYour previous output failed local sanity checks:\n"
                + "\n".join(f"  - {x}" for x in problems[:15])
                + "\n\nFix these issues. Follow the HARD NAMING CONTRACT exactly."
            )
            prompt = self._build_prompt() + feedback
            self.temperature = max(0.2, self.temperature - 0.2)

        if rtl is None:
            return {"status": "error",
                    "errors": [f"RTL generation failed after {self.max_attempts} attempts"],
                    "last_problems": last_problems}

        print("\n[3/4] Manifest ...")
        manifest = self.generate_manifest()
        n_ports = sum(len(v) for v in manifest["ports"].values())
        print(f"  + {n_ports} ports")

        print("\n[4/4] Writing files ...")
        sv_path = self.output_dir / "bank_tracker.sv"
        mf_path = self.output_dir / "bank_tracker_manifest.json"
        sv_path.write_text(rtl)
        mf_path.write_text(json.dumps(manifest, indent=2))
        print(f"  + {sv_path}")
        print(f"  + {mf_path}")

        print(f"\n{hdr}\n  DONE -- bank_tracker.sv\n{hdr}")
        return {
            "status": "success",
            "module": "bank_tracker",
            "phase": 2,
            "lines": len(rtl.splitlines()),
            "manifest": manifest,
            "rtl_path": str(sv_path),
        }


if __name__ == "__main__":
    print("+==============================================+")
    print("|   BANK TRACKER AGENT  (LLM, Phase 2)         |")
    print("+==============================================+\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'"); sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = BankTrackerAgent(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)