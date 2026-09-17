#!/usr/bin/env python3
"""
+======================================================================+
|        BADPORT CONFIG REGS AGENT  (one-shot bug injector)            |
|                                                                      |
|  Subclasses ConfigRegsAgent. Identical except _build_prompt()        |
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

from config_regs_agent import ConfigRegsAgent


# ── Sabotage functions: (prompt, params) -> modified prompt ──

def _sab_wrong_data_width(prompt, p):
    """CSR_DATA_W = 31 instead of 32 → fails V-RTL-15."""
    return prompt.replace(f"parameter CSR_DATA_W = {p['CSR_DATA_W']}",
                          "parameter CSR_DATA_W = 31")

def _sab_wrong_addr_width(prompt, p):
    """CSR_ADDR_W off by one."""
    return prompt.replace(f"parameter CSR_ADDR_W = {p['CSR_ADDR_W']}",
                          f"parameter CSR_ADDR_W = {p['CSR_ADDR_W'] - 1}")

def _sab_wrong_reset_value(prompt, p):
    """Flip one bit in a reset value."""
    for rt in p["REG_TABLE"]:
        if rt["access"] != "RO" and rt["reset_value"] != 0:
            good = f"{rt['reset_value']:08X}"
            bad  = f"{(rt['reset_value'] ^ 0x01):08X}"
            return prompt.replace(f"32'h{good}", f"32'h{bad}", 1)
    return prompt

def _sab_missing_localparam(prompt, p):
    """Remove one ADDR_ localparam from the contract."""
    victims = p["REG_TABLE"][1:]
    if not victims:
        return prompt
    v = random.choice(victims)
    return re.sub(rf"localparam.*ADDR_{v['name']}.*\n", "", prompt, count=1)

def _sab_broken_handshake(prompt, p):
    """Instruct LLM to drive ack_o directly → all reads return 0."""
    return prompt + """
IMPORTANT CORRECTION: Do NOT use internal ack_r or err_r registers.
Drive csr_ack_o and csr_err_o directly in always_ff blocks:
  always_ff @(posedge clk or negedge rst_n)
      if (!rst_n) csr_ack_o <= 1'b0;
      else        csr_ack_o <= csr_req & ~csr_ack_o;
Do NOT use continuous assign for csr_ack_o or csr_err_o.
"""

def _sab_swap_cfg_slices(prompt, p):
    """Swap two timing cfg output slices."""
    return prompt.replace(
        "assign cfg_tRCD_nCK         = reg_timing_0[7:0];",
        "assign cfg_tRCD_nCK         = reg_timing_0[15:8];"
    ).replace(
        "assign cfg_tRP_nCK          = reg_timing_0[15:8];",
        "assign cfg_tRP_nCK          = reg_timing_0[7:0];"
    )

def _sab_wo_no_self_clear(prompt, p):
    """Remove WO self-clear → bits stay latched."""
    return prompt.replace(
        "bist_start     [5]   — WO, must self-clear to 0 one cycle after write",
        "bist_start     [5]   — standard RW bit, retains value after write"
    ).replace(
        "force_refresh  [6]   — WO, must self-clear to 0 one cycle after write",
        "force_refresh  [6]   — standard RW bit, retains value after write"
    ).replace(
        "force_self_ref [7]   — WO, must self-clear to 0 one cycle after write",
        "force_self_ref [7]   — standard RW bit, retains value after write"
    )

def _sab_rw1c_as_rw(prompt, p):
    """Make ERROR_STATUS plain RW instead of RW1C."""
    return prompt.replace(
        "RW1C REGISTER: ERROR_STATUS",
        "READ-WRITE REGISTER: ERROR_STATUS"
    ).replace(
        "Fields latch on event pulse, clear on write-1:",
        "Fields are standard read-write (treat as normal RW register):"
    )

def _sab_drop_assertion(prompt, p):
    """Rename SVA assertion so validator can't find it."""
    return prompt.replace("p_rw_retain", "p_rw_hold_check")

def _sab_wrong_rdata_mux_name(prompt, p):
    """Rename rdata_mux to read_data."""
    return prompt.replace("rdata_mux", "read_data")


SABOTAGE_POOL = [
    _sab_wrong_data_width, _sab_wrong_addr_width, _sab_wrong_reset_value,
    _sab_missing_localparam, _sab_broken_handshake, _sab_swap_cfg_slices,
    _sab_wo_no_self_clear, _sab_rw1c_as_rw, _sab_drop_assertion,
    _sab_wrong_rdata_mux_name,
]


class BadportConfigRegsAgent(ConfigRegsAgent):
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
    r = BadportConfigRegsAgent(spec, out).run()
    sys.exit(0 if r["status"] == "success" else 1)