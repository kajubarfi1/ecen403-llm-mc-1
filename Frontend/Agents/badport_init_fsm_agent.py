#!/usr/bin/env python3
"""
+======================================================================+
|        BADPORT INIT FSM AGENT  (one-shot bug injector)               |
|                                                                      |
|  Subclasses InitFsmAgent. Identical except _build_prompt()           |
|  injects 2-3 random sabotages so the LLM's first-pass RTL is        |
|  likely buggy. This agent does NOT self-correct — the pipeline       |
|  orchestrator hands failures to the GOOD agent for retries.          |
+======================================================================+
"""

from __future__ import annotations
import random, re, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
for _rel in [".", "..", "../Phase_1_Agents", "Phase_1_Agents",
             "../Agents/Phase_1_Agents", "Agents/Phase_1_Agents"]:
    _p = os.path.normpath(os.path.join(HERE, _rel))
    if os.path.isdir(_p) and _p not in sys.path:
        sys.path.insert(0, _p)

from Frontend.Agents.init_fsm_agent import InitFsmAgent


# ── Sabotage functions: (prompt, params) -> modified prompt ──

def _sab_wrong_ddr_addr_w(prompt, p):
    """DDR_ADDR_W off by one → fails V-JED-04."""
    w = p["DDR_ADDR_W"] - 1
    return prompt.replace(
        f"parameter DDR_ADDR_W = {p['DDR_ADDR_W']}",
        f"parameter DDR_ADDR_W = {w}"
    ).replace(
        f"parameter int DDR_ADDR_W = {p['DDR_ADDR_W']}",
        f"parameter int DDR_ADDR_W = {w}"
    )

def _sab_wrong_wait_reset(prompt, p):
    """Shorten WAIT_RESET by 50 cycles → fails V-TIM-01."""
    return prompt.replace(
        f"localparam WAIT_RESET   = {p['WAIT_RESET']};",
        f"localparam WAIT_RESET   = {p['WAIT_RESET'] - 50};"
    )

def _sab_wrong_wait_cke(prompt, p):
    """Shorten WAIT_CKE by 50 cycles → fails V-TIM-02."""
    return prompt.replace(
        f"localparam WAIT_CKE     = {p['WAIT_CKE']};",
        f"localparam WAIT_CKE     = {max(1, p['WAIT_CKE'] - 50)};"
    )

def _sab_wrong_mr_order(prompt, p):
    """Swap MR0/MR1 order → fails V-JED-01."""
    return prompt.replace(
        "issue MR2, MR3, MR1, MR0 (in that order",
        "issue MR2, MR3, MR0, MR1 (in that order"
    ).replace(
        "S_MR1        = 4'd6,\n        S_MR0        = 4'd7,",
        "S_MR0        = 4'd6,\n        S_MR1        = 4'd7,"
    )

def _sab_wrong_zqcl_cmd(prompt, p):
    """Wrong ZQCL encoding 4'b0100 instead of 4'b0110."""
    return prompt.replace("ZQCL = 4'b0110", "ZQCL = 4'b0100")

def _sab_zqcl_no_a10(prompt, p):
    """ZQCL address all zeros instead of A10=1."""
    zeros = '0' * ((p['DDR_ADDR_W'] + 3) // 4)
    return prompt.replace(
        f"{p['DDR_ADDR_W']}'h{p['ZQCL_ADDR_HEX']}",
        f"{p['DDR_ADDR_W']}'h{zeros}"
    ).replace("with A10=1", "with all address bits zero"
    ).replace("init_addr[10]=1 (long calibration)",
              "init_addr = 0 (standard calibration)")

def _sab_cke_during_reset(prompt, p):
    """CKE HIGH during reset → fails CKE violation check."""
    return prompt.replace(
        "init_cke MUST be low whenever state IN {S_IDLE, S_RESET_LOW, S_RESET_HIGH}",
        "init_cke MUST be high whenever state IN {S_IDLE, S_RESET_LOW, S_RESET_HIGH}"
    ).replace(
        "S_IDLE       = 4'd0,   // before enable; init_reset_n=0, init_cke=0",
        "S_IDLE       = 4'd0,   // before enable; init_reset_n=0, init_cke=1"
    )

def _sab_wrong_sdone_encoding(prompt, p):
    """S_DONE = 4'd15 instead of 4'd14 → fails state check."""
    return prompt.replace("S_DONE       = 4'd14", "S_DONE       = 4'd15"
    ).replace("init_state=4'd14", "init_state=4'd15")

def _sab_cmd_valid_registered(prompt, p):
    """Register init_cmd_valid → one-cycle bleed into wait states."""
    return prompt.replace(
        "init_cmd_valid MUST be COMBINATIONAL (driven from `always_comb`, not\n    registered)",
        "init_cmd_valid MUST be REGISTERED (driven from `always_ff`, not combinational)"
    ).replace(
        "Drive it from the combinational state-decode case\n    block; do NOT register it",
        "Drive it from a registered always_ff block; do NOT use always_comb for this"
    )

def _sab_wrong_mr_value(prompt, p):
    """Corrupt one MR register hex value → fails MR encoding check."""
    mk = random.choice(["MR0_HEX", "MR1_HEX", "MR2_HEX", "MR3_HEX"])
    good = p[mk]
    bad = f"{(int(good, 16) ^ 0xF):0{len(good)}X}"
    return prompt.replace(f"'h{good}", f"'h{bad}")

def _sab_drop_init_done_constraint(prompt, p):
    """Loosen init_done timing → may assert in wrong state."""
    return prompt.replace(
        "init_done MUST be asserted ONLY in S_DONE (state == 4'd14) and held high\n    there. It must be 0 in every other state, including S_IDLE.",
        "init_done should be asserted once initialization completes. The exact timing is flexible."
    )


SABOTAGE_POOL = [
    _sab_wrong_ddr_addr_w, _sab_wrong_wait_reset, _sab_wrong_wait_cke,
    _sab_wrong_mr_order, _sab_wrong_zqcl_cmd, _sab_zqcl_no_a10,
    _sab_cke_during_reset, _sab_wrong_sdone_encoding,
    _sab_cmd_valid_registered, _sab_wrong_mr_value,
    _sab_drop_init_done_constraint,
]


class BadportInitFsmAgent(InitFsmAgent):
    """One-shot bug injector. Overrides only _build_prompt()."""

    def _build_prompt(self) -> str:
        prompt = super()._build_prompt()
        num = random.randint(2, 3)
        chosen = random.sample(SABOTAGE_POOL, min(num, len(SABOTAGE_POOL)))
        applied = []
        for fn in chosen:
            new = fn(prompt, self.p)
            if new != prompt:
                prompt = new
                applied.append(fn.__name__)
        if applied:
            print(f"  [BADPORT] sabotages: {', '.join(applied)}")
        return prompt


if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output (Enter=./output): ").strip() or "./output"
    r = BadportInitFsmAgent(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)