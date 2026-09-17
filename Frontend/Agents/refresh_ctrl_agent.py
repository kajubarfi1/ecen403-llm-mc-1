#!/usr/bin/env python3
"""
+======================================================================+
|                 REFRESH CONTROLLER AGENT  (LLM-driven)               |
|  Phase 2 -- Depends on: Config Registers (config_regs)               |
|  Generates: refresh_ctrl.sv + refresh_ctrl_manifest.json             |
|                                                                      |
|  tREFI interval counter, postpone tracking (max 8),                  |
|  urgent threshold, refresh starvation detection.                     |
|                                                                      |
|  HYBRID DETERMINISM PATTERN:                                         |
|    - RTL generation:   LLM-driven (Claude API)                       |
|    - Manifest:         DETERMINISTIC (Python)                        |
|    - Validation/Derive:DETERMINISTIC (Python)                        |
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


class RefreshCtrlAgent:

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

        self.ca = self.spec["controller_architecture"]
        self.dc = self.spec["timing_model"]["$derived_cycles"]
        self.rp = self.ca["refresh_policy"]
        self.p  = self._derive()

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
        p["tREFI_nCK"]        = self.dc["tREFI_nCK"]           # 6240
        p["tRFC_nCK"]         = self.dc["tRFC_nCK"]            # 128
        p["MAX_POSTPONE"]     = self.rp["max_postpone_count"]  # 8
        p["URGENT_THRESH"]    = self.rp["urgent_threshold"]    # 6
        p["REFRESH_PRIORITY"] = self.rp["refresh_priority"]    # urgent_preempt

        p["REFI_CTR_W"] = max(1, p["tREFI_nCK"].bit_length())       # 13 bits
        p["POST_CTR_W"] = max(1, p["MAX_POSTPONE"].bit_length())    # 4 bits

        return p

    # ==================================================================
    # DETERMINISTIC: validation
    # ==================================================================
    def validate(self) -> list:
        errors = []
        p = self.p
        if p["tREFI_nCK"] < 1:
            errors.append(f"tREFI must be > 0, got {p['tREFI_nCK']}")
        if p["URGENT_THRESH"] > p["MAX_POSTPONE"]:
            errors.append(f"urgent_threshold ({p['URGENT_THRESH']}) > max_postpone ({p['MAX_POSTPONE']})")
        return errors

    # ==================================================================
    # LLM: contract
    # ==================================================================
    def _validator_contract(self) -> str:
        p = self.p
        return f"""\
============================================================
HARD NAMING CONTRACT -- VIOLATING ANY RULE REJECTS THE OUTPUT
============================================================

Module declaration MUST be exactly:
    module refresh_ctrl #(
        parameter REFI_CTR_W = {p['REFI_CTR_W']},
        parameter POST_CTR_W = {p['POST_CTR_W']}
    ) (

Port list (exact names, exact directions, exact widths):
    input  logic                    clk
    input  logic                    rst_n
    input  logic                    init_done
    input  logic                    cfg_force_refresh
    input  logic [23:0]             cfg_tREFI_nCK
    input  logic [3:0]              cfg_max_postpone
    input  logic [3:0]              cfg_urgent_threshold
    input  logic                    cfg_ref_priority
    output logic                    ref_required
    output logic                    ref_urgent
    input  logic                    ref_ack
    output logic [2:0]              ref_pending_cnt
    output logic                    ref_starve_flag

RULES:
  1. Parameter names are EXACTLY: REFI_CTR_W, POST_CTR_W.
  2. Parameter literal values MUST be {p['REFI_CTR_W']} and {p['POST_CTR_W']}.
  3. Internal signal NAMES (used by validator regex):
       * `refi_ctr`      -- tREFI interval counter
       * `refi_tick`     -- pulse when refi_ctr reaches 0
       * `postpone_cnt`  -- running count of un-acked refreshes (pending)
       * `starve_detect` or similar containing the word "starve"
  4. `init_done` MUST gate all counter activity. While init_done == 0:
       * refi_ctr is held at 0
       * postpone_cnt is held at 0
       * ref_required, ref_urgent, ref_starve_flag are all 0
  5. refi_ctr counts DOWN from cfg_tREFI_nCK. When it reaches 0, it
     reloads with cfg_tREFI_nCK and raises refi_tick for 1 cycle.
  6. postpone_cnt increments on (refi_tick OR cfg_force_refresh),
     decrements on ref_ack. Simultaneous increment+ack must cancel out
     (no change).
  7. postpone_cnt MUST saturate at cfg_max_postpone (never exceed it).
  8. ref_required = high when postpone_cnt > 0 AND init_done == 1.
  9. ref_urgent = high when ref_required AND
                       (postpone_cnt >= cfg_urgent_threshold) AND
                       cfg_ref_priority == 1.
 10. ref_pending_cnt exposes the low 3 bits of postpone_cnt to the CSR.
 11. ref_starve_flag is a registered 1-cycle pulse that fires when refi_tick
     arrives while postpone_cnt is already at cfg_max_postpone (saturated).
 12. Include at least one `always_ff @(posedge clk or negedge rst_n)` block.
 13. Use both the words "urgent" and "threshold" in your code/comments.
 14. End with `endmodule`.

REQUIRED REFI COUNTER STRUCTURE (copy this block verbatim):

    logic [REFI_CTR_W-1:0] refi_ctr;
    logic                  refi_tick;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            refi_ctr  <= '0;
            refi_tick <= 1'b0;
        end else if (!init_done) begin
            refi_ctr  <= '0;
            refi_tick <= 1'b0;
        end else begin
            refi_tick <= 1'b0;
            if (refi_ctr == '0) begin
                refi_ctr  <= cfg_tREFI_nCK[REFI_CTR_W-1:0];
                refi_tick <= 1'b1;
            end else begin
                refi_ctr <= refi_ctr - 1'b1;
            end
        end
    end

REQUIRED POSTPONE COUNTER STRUCTURE (copy this block verbatim):

    logic [POST_CTR_W-1:0] postpone_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            postpone_cnt <= '0;
        end else if (!init_done) begin
            postpone_cnt <= '0;
        end else begin
            case ({{(refi_tick | cfg_force_refresh), ref_ack}})
                2'b10: if (postpone_cnt < cfg_max_postpone)
                           postpone_cnt <= postpone_cnt + 1'b1;
                2'b01: if (|postpone_cnt)
                           postpone_cnt <= postpone_cnt - 1'b1;
                default: ; // 2'b00 idle, 2'b11 cancel
            endcase
        end
    end

REQUIRED OUTPUT ASSIGNMENTS (copy verbatim):

    assign ref_required    = (|postpone_cnt) & init_done;
    assign ref_urgent      = ref_required
                           & (postpone_cnt >= cfg_urgent_threshold)
                           & cfg_ref_priority;
    assign ref_pending_cnt = postpone_cnt[2:0];

REQUIRED STARVATION DETECT (copy verbatim):

    logic starve_detect;
    assign starve_detect = refi_tick
                         & (postpone_cnt >= cfg_max_postpone)
                         & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

You may add SVA or coverage inside translate_off guards, but the blocks
above must appear as written.
============================================================
"""

    # ==================================================================
    # LLM: prompt
    # ==================================================================
    def _build_prompt(self) -> str:
        p = self.p

        base = f"""\
You are generating SystemVerilog RTL for a DDR3 memory controller refresh
controller module.

SPEC PARAMETERS:
  tREFI_nCK         = {p['tREFI_nCK']}     (refresh interval, DRAM clocks)
  tRFC_nCK          = {p['tRFC_nCK']}      (refresh command duration)
  MAX_POSTPONE      = {p['MAX_POSTPONE']}        (max pending refreshes)
  URGENT_THRESH     = {p['URGENT_THRESH']}        (pending >= this -> urgent)
  REFRESH_PRIORITY  = {p['REFRESH_PRIORITY']}
  REFI_CTR_W        = {p['REFI_CTR_W']}    (counter width for tREFI)
  POST_CTR_W        = {p['POST_CTR_W']}     (postpone counter width)

BEHAVIOR:
  - Once init_done is high, a free-running counter ticks every tREFI cycles.
  - Each tick means a refresh is owed. The controller tracks how many
    refreshes are owed in `postpone_cnt`.
  - The scheduler pulses `ref_ack` when it issues an AUTO REFRESH; each ack
    decrements postpone_cnt.
  - `ref_required` is high whenever postpone_cnt > 0.
  - `ref_urgent` asks the scheduler to preempt other traffic when we fall
    behind (postpone_cnt >= urgent_threshold, and priority mode enabled).
  - CSRs may force an extra refresh via cfg_force_refresh (1-cycle pulse
    treated like an implicit refi_tick).
  - If a new tick lands while already saturated at cfg_max_postpone, raise
    ref_starve_flag for 1 cycle as a diagnostic.
  - Before init_done, the whole module is quiescent.

{self._validator_contract()}

Generate the complete `refresh_ctrl.sv` file. Include a header comment,
the module declaration with parameters, port list, all the required
always_ff / assign blocks, and `endmodule`. Do not include a testbench.

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
            max_tokens=6144,
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
        m = re.search(r"(module\s+refresh_ctrl\b.*?endmodule)", out, re.DOTALL)
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
        if "module refresh_ctrl" not in rtl:
            problems.append("module refresh_ctrl not found")
        if "endmodule" not in rtl:
            problems.append("endmodule missing")

        # Guard 2: required ports
        required_ports = [
            "clk", "rst_n", "init_done", "cfg_force_refresh",
            "cfg_tREFI_nCK", "cfg_max_postpone", "cfg_urgent_threshold",
            "cfg_ref_priority",
            "ref_required", "ref_urgent", "ref_ack",
            "ref_pending_cnt", "ref_starve_flag",
        ]
        for port in required_ports:
            if port not in rtl:
                problems.append(f"port `{port}` missing")

        # Guard 3: parameter literals
        m = re.search(r"parameter\s+REFI_CTR_W\s*=\s*(\d+)", rtl)
        if not m or int(m.group(1)) < p["REFI_CTR_W"]:
            got = m.group(1) if m else "none"
            problems.append(f"REFI_CTR_W must be >= {p['REFI_CTR_W']}, got {got}")
        m = re.search(r"parameter\s+POST_CTR_W\s*=\s*(\d+)", rtl)
        if not m or int(m.group(1)) < p["POST_CTR_W"]:
            got = m.group(1) if m else "none"
            problems.append(f"POST_CTR_W must be >= {p['POST_CTR_W']}, got {got}")

        # Guard 4: internal signal names required by contract
        for sig in ["refi_ctr", "refi_tick", "postpone_cnt"]:
            if sig not in rtl:
                problems.append(f"internal signal `{sig}` missing")

        # Guard 5: starvation logic present (validator checks for 'starve')
        if "starve" not in rtl.lower():
            problems.append("starvation logic (containing 'starve') missing")

        # Guard 6: urgent + threshold words both present (validator V-RF-11)
        if "urgent" not in rtl.lower():
            problems.append("'urgent' keyword missing in code/comments")
        if "threshold" not in rtl.lower():
            problems.append("'threshold' keyword missing in code/comments")

        # Guard 7: always_ff present
        if not re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk", rtl):
            problems.append("no `always_ff @(posedge clk ...)` block found")

        # Guard 8: init_done gating -- must see !init_done as a reset-like guard somewhere
        if not re.search(r"!\s*init_done", rtl):
            problems.append("init_done gating (`!init_done` guard) missing")

        # Guard 9: ref_required assign gated by init_done
        if not re.search(
            r"assign\s+ref_required\s*=\s*[^;]*init_done", rtl_no_sva
        ):
            problems.append("ref_required must be gated by init_done in an assign")

        # Guard 10: ref_urgent logic checks cfg_urgent_threshold and cfg_ref_priority
        m = re.search(r"assign\s+ref_urgent\s*=\s*([^;]+);", rtl_no_sva, re.DOTALL)
        if not m:
            problems.append("assign for ref_urgent missing")
        else:
            body = m.group(1)
            if "cfg_urgent_threshold" not in body:
                problems.append("ref_urgent must compare against cfg_urgent_threshold")
            if "cfg_ref_priority" not in body:
                problems.append("ref_urgent must be gated by cfg_ref_priority")

        # Guard 11: ref_pending_cnt = postpone_cnt[2:0]
        if not re.search(
            r"assign\s+ref_pending_cnt\s*=\s*postpone_cnt\s*\[\s*2\s*:\s*0\s*\]",
            rtl_no_sva,
        ):
            problems.append("ref_pending_cnt must be `postpone_cnt[2:0]`")

        # Guard 12: no NBA on ref_required / ref_urgent / ref_pending_cnt
        # (may be indexed: `ref_pending_cnt[0] <= ...`)
        for comb_out in ["ref_required", "ref_urgent", "ref_pending_cnt"]:
            if re.search(rf"\b{comb_out}(\s*\[[^\]]*\])?\s*<=", rtl_no_sva):
                problems.append(f"{comb_out} must be combinational (use assign, not NBA)")

        return problems

    # ==================================================================
    # DETERMINISTIC: manifest
    # ==================================================================
    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "refresh_ctrl", "file": "refresh_ctrl.sv",
            "phase": 2, "agent": "refresh_ctrl_agent",
            "dependencies": ["config_regs"],
            "parameters": {
                "REFI_CTR_W": p["REFI_CTR_W"], "POST_CTR_W": p["POST_CTR_W"],
                "tREFI_nCK": p["tREFI_nCK"], "tRFC_nCK": p["tRFC_nCK"],
                "MAX_POSTPONE": p["MAX_POSTPONE"], "URGENT_THRESH": p["URGENT_THRESH"],
            },
            "ports": {
                "clock_reset": [
                    {"name": "clk", "width": 1, "dir": "input"},
                    {"name": "rst_n", "width": 1, "dir": "input"},
                ],
                "control": [
                    {"name": "init_done", "width": 1, "dir": "input",
                     "source": "init_fsm.init_done"},
                    {"name": "cfg_force_refresh", "width": 1, "dir": "input",
                     "source": "config_regs.cfg_force_refresh"},
                ],
                "config_in": [
                    {"name": "cfg_tREFI_nCK", "width": 24, "dir": "input",
                     "source": "config_regs.cfg_tREFI_nCK"},
                    {"name": "cfg_max_postpone", "width": 4, "dir": "input",
                     "source": "config_regs.cfg_max_postpone"},
                    {"name": "cfg_urgent_threshold", "width": 4, "dir": "input",
                     "source": "config_regs.cfg_urgent_threshold"},
                    {"name": "cfg_ref_priority", "width": 1, "dir": "input",
                     "source": "config_regs.cfg_ref_priority"},
                ],
                "scheduler_if": [
                    {"name": "ref_required", "width": 1, "dir": "output"},
                    {"name": "ref_urgent", "width": 1, "dir": "output"},
                    {"name": "ref_ack", "width": 1, "dir": "input"},
                ],
                "status_out": [
                    {"name": "ref_pending_cnt", "width": 3, "dir": "output"},
                    {"name": "ref_starve_flag", "width": 1, "dir": "output"},
                ],
            },
        }

    # ==================================================================
    # MAIN
    # ==================================================================
    def run(self) -> dict:
        hdr = "=" * 62
        mode = "LLM (retry)" if self.retry_instructions else "LLM (cold)"
        print(f"{hdr}\n  REFRESH CONTROLLER AGENT -- {mode}")
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
            print(f"    {k:17s} = {v}")

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
        sv_path = self.output_dir / "refresh_ctrl.sv"
        mf_path = self.output_dir / "refresh_ctrl_manifest.json"
        sv_path.write_text(rtl)
        mf_path.write_text(json.dumps(manifest, indent=2))
        print(f"  + {sv_path}")
        print(f"  + {mf_path}")

        print(f"\n{hdr}\n  DONE -- refresh_ctrl.sv\n{hdr}")
        return {
            "status": "success",
            "module": "refresh_ctrl",
            "phase": 2,
            "lines": len(rtl.splitlines()),
            "manifest": manifest,
            "rtl_path": str(sv_path),
        }


if __name__ == "__main__":
    print("+==============================================+")
    print("|   REFRESH CONTROLLER AGENT  (LLM, Phase 2)   |")
    print("+==============================================+\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'"); sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = RefreshCtrlAgent(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)