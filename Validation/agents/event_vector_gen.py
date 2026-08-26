"""
Event Vector Generator (Stage 4)
==================================
Takes an event_spec.json and produces a <path_id>_vectors.hex file containing
the actual test sequence. This is the one LLM-driven step in the event-mode
flow — the spec defines WHAT can be checked, the vector file defines WHAT IS
checked.

Reads:
  - event_spec.json (signal definitions, timing, start expression)
  - Optionally the RTL of the path's first block, to ground timing constants

Writes:
  - <output-dir>/<path_id>_vectors.hex

Validation (pre-write):
  1. Every sig_id referenced in any vector must exist in event_spec.signals
  2. Every check_order references two signals that were both waited-for earlier
     in the file (otherwise arrival_cycle is -1 at runtime → MISSING error)
  3. The first non-reset opcode must be 09 (event_start) for event-mode specs
  4. wait_for timeouts must not exceed sim_timeout_cycles

On validation failure, the agent retries with the error list appended to the
prompt (same pattern as event_spec_agent).

Author: Validation Subsystem — Event Vector Gen (Stage 4)
"""

import argparse
import json
import os
import re
import sys
from typing import Dict, List, Optional, Set, Tuple

from llm_client import call_llm, strip_fences


# =============================================================================
# Hex Vector Parsing
# =============================================================================

# Opcodes that count as vectors (not comments / blanks)
OPCODE_NAMES = {
    0x00: "reset",
    0x03: "step",
    0x04: "wait_for",
    0x05: "check_at",
    0x06: "check_not_yet",
    0x07: "expect_handshake",
    0x08: "check_order",
    0x09: "event_start",
    0x0A: "csr_read",
    0x0B: "csr_write",
}


class ParsedVector:
    __slots__ = ("line_num", "raw", "op", "p", "d", "e")

    def __init__(self, line_num: int, raw: str, op: int, p: int, d: int, e: int):
        self.line_num = line_num
        self.raw = raw
        self.op = op
        self.p = p
        self.d = d
        self.e = e

    def __repr__(self):
        return f"L{self.line_num}:{OPCODE_NAMES.get(self.op, hex(self.op))}({self.p:08x},{self.d:08x},{self.e:08x})"


_VECTOR_RE = re.compile(
    r"^\s*([0-9a-fA-F]{1,2})\s+"
    r"([0-9a-fA-F]{1,8})\s+"
    r"([0-9a-fA-F]{1,8})\s+"
    r"([0-9a-fA-F]{1,8})\s*(?://.*)?$"
)


def parse_vector_file(text: str) -> List[ParsedVector]:
    """Parse a hex vector file into a list of ParsedVector.

    Comment lines (`// ...`) and blank lines are skipped but counted for
    line_num so error messages match the physical file position.
    """
    vectors = []
    for i, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("//"):
            continue
        m = _VECTOR_RE.match(line)
        if not m:
            # Not a vector and not a comment — treat as a parse error by
            # recording it as a sentinel. The validator will flag it.
            raise ValueError(f"line {i}: not a valid vector or comment: {line!r}")
        op = int(m.group(1), 16)
        p = int(m.group(2), 16)
        d = int(m.group(3), 16)
        e = int(m.group(4), 16)
        vectors.append(ParsedVector(i, stripped, op, p, d, e))
    return vectors


# =============================================================================
# Static Validation
# =============================================================================

class VectorValidationError(Exception):
    pass


def validate_vectors(vectors: List[ParsedVector], event_spec: dict) -> List[str]:
    """Apply constraints 1-4 from the Stage 4 design.

    Returns a list of error strings. Empty list means valid.
    """
    errors = []

    valid_sig_ids = {sig["id"] for sig in event_spec.get("signals", [])}
    sim_timeout = event_spec.get("sim_timeout_cycles", 200000)
    mode = event_spec.get("mode", "event")

    # Rule 3: first non-reset opcode must be 09 for event-mode specs
    if mode == "event":
        seen_start = False
        for v in vectors:
            if v.op == 0x00:
                continue  # reset allowed anywhere, doesn't count as "first"
            if v.op == 0x09:
                seen_start = True
                break
            # Found a non-reset, non-start opcode first
            errors.append(
                f"rule 3: first non-reset opcode at line {v.line_num} is "
                f"0x{v.op:02X} ({OPCODE_NAMES.get(v.op, '?')}); "
                f"expected 0x09 (event_start) before any check/wait ops"
            )
            break
        if not seen_start and any(v.op not in (0x00,) for v in vectors):
            # Didn't encounter event_start at all among non-reset vectors
            has_checks = any(v.op in (0x04, 0x05, 0x06, 0x07, 0x08) for v in vectors)
            if has_checks:
                errors.append(
                    "rule 3: mode='event' vector file contains check/wait ops "
                    "but no event_start (opcode 09)"
                )

    # Rule 2: track which sig_ids have been waited-for as we scan forward.
    # expect_handshake counts as waiting on valid_id (matches the library's
    # arrival_cycle[valid_id] = sim_cycle behavior).
    waited_sigs: Set[int] = set()

    for v in vectors:
        if v.op == 0x00 or v.op == 0x09:
            # reset / event_start — no sig refs
            continue

        if v.op == 0x03:
            # step — no sig refs
            continue

        if v.op in (0x04, 0x05, 0x06):
            # wait_for / check_at / check_not_yet — single sig in p[7:0]
            sig_id = v.p & 0xFF
            if sig_id not in valid_sig_ids:
                errors.append(
                    f"rule 1: line {v.line_num} ({OPCODE_NAMES[v.op]}) "
                    f"references unknown sig_id {sig_id} "
                    f"(valid: {sorted(valid_sig_ids)})"
                )
                continue
            # Rule 4: wait_for timeouts must not exceed sim_timeout_cycles
            if v.op == 0x04:
                if v.e > sim_timeout:
                    errors.append(
                        f"rule 4: line {v.line_num} wait_for timeout {v.e} "
                        f"exceeds sim_timeout_cycles {sim_timeout}"
                    )
                waited_sigs.add(sig_id)

        elif v.op == 0x07:
            # expect_handshake — valid_id in p[7:0], ready_id in p[15:8]
            valid_id = v.p & 0xFF
            ready_id = (v.p >> 8) & 0xFF
            if valid_id not in valid_sig_ids:
                errors.append(
                    f"rule 1: line {v.line_num} expect_handshake "
                    f"valid_id {valid_id} not in spec"
                )
            if ready_id not in valid_sig_ids:
                errors.append(
                    f"rule 1: line {v.line_num} expect_handshake "
                    f"ready_id {ready_id} not in spec"
                )
            if v.e > sim_timeout:
                errors.append(
                    f"rule 4: line {v.line_num} expect_handshake timeout {v.e} "
                    f"exceeds sim_timeout_cycles {sim_timeout}"
                )
            waited_sigs.add(valid_id)

        elif v.op == 0x08:
            # check_order — first_id in p[7:0], second_id in p[15:8]
            first_id = v.p & 0xFF
            second_id = (v.p >> 8) & 0xFF
            if first_id not in valid_sig_ids:
                errors.append(
                    f"rule 1: line {v.line_num} check_order "
                    f"first_id {first_id} not in spec"
                )
            if second_id not in valid_sig_ids:
                errors.append(
                    f"rule 1: line {v.line_num} check_order "
                    f"second_id {second_id} not in spec"
                )
            # Rule 2: both sigs must have been waited for earlier
            if first_id in valid_sig_ids and first_id not in waited_sigs:
                errors.append(
                    f"rule 2: line {v.line_num} check_order first_id {first_id} "
                    f"was never waited for (no prior wait_for/expect_handshake)"
                )
            if second_id in valid_sig_ids and second_id not in waited_sigs:
                errors.append(
                    f"rule 2: line {v.line_num} check_order second_id {second_id} "
                    f"was never waited for (no prior wait_for/expect_handshake)"
                )

        elif v.op in (0x0A, 0x0B):
            # csr_read / csr_write — address in p[7:0], no sig refs.
            # Timeout in E must not exceed sim_timeout_cycles.
            if v.e > sim_timeout:
                op_name = "csr_read" if v.op == 0x0A else "csr_write"
                errors.append(
                    f"rule 4: line {v.line_num} {op_name} timeout {v.e} "
                    f"exceeds sim_timeout_cycles {sim_timeout}"
                )

        else:
            errors.append(
                f"line {v.line_num}: unknown opcode 0x{v.op:02X}"
            )

    # Rule 5: mixed-mode paths (csr_interface.present) must contain at least
    # one csr_read op. Otherwise the CSR infrastructure is pointless.
    csr_present = bool(event_spec.get("csr_interface", {}).get("present", False))
    if csr_present:
        has_csr_read = any(v.op == 0x0A for v in vectors)
        if not has_csr_read:
            errors.append(
                "rule 5: csr_interface.present=true but no csr_read (opcode 0A) "
                "found in vectors. Mixed-mode paths must exercise the CSR interface."
            )

    return errors


# =============================================================================
# Prompt Construction
# =============================================================================

SYSTEM_PROMPT = """You are a hardware verification engineer writing event-mode test vectors for a DDR3 memory controller integration path.

You output ONLY the contents of a hex vector file — no JSON, no markdown fences, no prose. Each line is either:
  - A comment starting with //
  - A vector: OO PPPPPPPP DDDDDDDD EEEEEEEE (four hex fields separated by spaces)

Do not wrap your output in code fences. Your first output character must be either '/' (for a comment) or a hex digit."""


def build_prompt(event_spec: dict, rtl_hint: Optional[str] = None) -> str:
    path_id = event_spec["path_id"]
    sim_timeout = event_spec.get("sim_timeout_cycles", 200000)
    mode = event_spec.get("mode", "event")

    # Signal catalog
    sig_lines = []
    for sig in event_spec["signals"]:
        sid = sig["id"]
        name = sig["name"]
        kind = sig["kind"]
        if kind == "raw":
            width = sig.get("width", "?")
            path = sig.get("path", "?")
            sig_lines.append(f"  {sid:3d}  {name:30s}  raw[{width}]  {path}")
        else:
            expr = sig.get("expression", "")
            sig_lines.append(f"  {sid:3d}  {name:30s}  predicate   {expr}")
    sig_catalog = "\n".join(sig_lines)

    # CSR section — built only when csr_interface.present=true
    csr_iface = event_spec.get("csr_interface", {})
    csr_present = bool(csr_iface.get("present", False))
    csr_opcode_lines = ""
    csr_section = ""
    if csr_present:
        csr_opcode_lines = (
            "  0A csr_read       — P[7:0]=csr_addr, D=expected_data, E=ack_timeout\n"
            "  0B csr_write      — P[7:0]=csr_addr, D=write_data,    E=ack_timeout\n"
        )

        # Determine in-path blocks by scanning signal paths (u_<block>.<port>).
        # This gives us the definitive list of blocks whose outputs are driving
        # the DUT, which maps directly to which sts_* bits can be nonzero.
        in_path_blocks = set()
        for sig in event_spec.get("signals", []):
            path = sig.get("path", "") or sig.get("expression", "")
            for match in re.findall(r"u_([a-zA-Z0-9_]+)", path):
                in_path_blocks.add(match)
        # config_regs is always in path when csr_interface.present=true, even
        # if nothing references it directly in a signal
        in_path_blocks.add("config_regs")

        # Hardcoded map: CTRL_STATUS bit name -> block whose output drives the
        # corresponding sts_* input of config_regs. If the block is not in the
        # path, event_tb_codegen's auto-tieoff forces that sts_* input to 0,
        # meaning the bit will ALWAYS be 0 in the CSR read result.
        # Source: config_regs.sv rdata_mux case ADDR_CTRL_STATUS + the
        # conn_{17,18,19} definitions mapping block outputs -> sts_* ports.
        BIT_DRIVERS = {
            "init_done":            "init_fsm",
            "init_fail":            "init_fsm",  # sts_init_fail_event
            "cal_done":             "calibration",
            "cal_fail":             "calibration",
            "bist_done":            None,         # no block in 11-block design drives
            "bist_fail":            None,
            "ref_pending_cnt":      "refresh_ctrl",
            "ref_starve_event":     "refresh_ctrl",
            "self_refresh_active":  None,         # tied low by tb
            "ecc_ce_count":         None,
            "ecc_ue_event":         None,
        }

        # Format the register map for the LLM, with per-bit driver analysis.
        reg_lines = []
        computed_value_lines = []
        for r in csr_iface.get("registers", []):
            name = r.get("name", "?")
            addr = r.get("address", "?")
            bits = r.get("bits", {})
            coerced = []
            for nm, pos in bits.items():
                try:
                    coerced.append((nm, int(pos)))
                except (TypeError, ValueError):
                    continue
            bit_pairs = sorted(coerced, key=lambda kv: kv[1])

            # Compact register line for the catalog
            bits_str = ", ".join(f"bit[{pos}]={nm}" for nm, pos in bit_pairs)
            reg_lines.append(f"  {name}  address={addr}  {bits_str}")

            # Per-bit driver analysis
            computed_value_lines.append(f"\n  {name} @ {addr}:")
            computed_value = 0
            for bit_name, bit_pos in bit_pairs:
                driver = BIT_DRIVERS.get(bit_name, "?")
                if driver is None:
                    note = f"tied LOW by tb (no driver block)"
                    value = 0
                elif driver == "?":
                    note = f"UNKNOWN — check config_regs.sv rdata_mux"
                    value = 0
                elif driver in in_path_blocks:
                    # This bit CAN be set, depending on what the block does
                    if bit_name in ("init_fail", "cal_fail", "bist_fail",
                                    "ecc_ue_event", "ref_starve_event",
                                    "init_fail_event"):
                        note = f"driven by {driver} (in path) → expected 0 (no failure)"
                        value = 0
                    elif bit_name in ("ecc_ce_count", "ref_pending_cnt"):
                        note = f"driven by {driver} (in path) → expected 0 (steady state)"
                        value = 0
                    else:
                        note = f"driven by {driver} (in path) → expected 1 (asserted after event)"
                        value = 1
                else:
                    note = f"tied LOW ({driver} NOT in path → sts_* forced to 0)"
                    value = 0

                if value:
                    computed_value |= (1 << bit_pos)
                computed_value_lines.append(
                    f"    bit[{bit_pos}] {bit_name}: {note}"
                )
            computed_value_lines.append(
                f"    → EXPECTED VALUE = 0x{computed_value:08X}"
            )

        reg_catalog = "\n".join(reg_lines) if reg_lines else "  (none)"
        bit_analysis = "\n".join(computed_value_lines)
        in_path_str = ", ".join(sorted(in_path_blocks))

        csr_section = f"""
=== CSR INTERFACE (MIXED MODE) ===

This path includes config_regs. After the autonomous block(s) complete,
the vector file MUST perform at least one csr_read (opcode 0A) to verify
the status registers reflect the expected post-boot state.

Register map (from csr_interface.registers):
{reg_catalog}

CSR opcode encoding:
  0A csr_read   OO=0A, P[7:0]=CSR address, D=expected value, E=ack timeout
  0B csr_write  OO=0B, P[7:0]=CSR address, D=data to write,  E=ack timeout

=== COMPUTED EXPECTED VALUES (USE THESE) ===

The testbench auto-generator ties sts_* inputs of config_regs to 0 when
the block that would normally drive them is NOT in this path. That means
only bits corresponding to in-path blocks can be nonzero — everything else
is forced low by the tie-off logic.

In-path blocks for this path: {in_path_str}

Per-bit analysis:
{bit_analysis}

CRITICAL: use the EXPECTED VALUE computed above verbatim in your csr_read
vectors. Do NOT reason independently about "what the bit should mean" —
the auto-tieoff logic overrides your intuition for any block not in the
in-path list. If you're uncertain whether a bit will be set, look at
whether its driver block is in the in-path list above.

WORKED EXAMPLE — csr_read CTRL_STATUS, timeout 100:
  0A 00000000 <EXPECTED> 00000064
  where <EXPECTED> is the 8-digit hex value from the analysis above.

RULES for CSR ops:
- Place csr_read AFTER the wait_for for the event that produces the bit
  (e.g. after wait_for(cal_done=1), then csr_read to verify cal_done bit
  is reflected in CTRL_STATUS).
- csr_read ack timeout (E field) should be small (100 is plenty) because
  the Wishbone slave always acks within 1-2 cycles.
- csr_read ack timeout must NOT exceed sim_timeout_cycles.
- The expected data D is compared with === (strict match). Partial masks
  are NOT supported — you must supply the EXACT expected 32-bit value
  computed above.
- Reserved bits in the register are 0 by default — already accounted for
  in the computed expected values above.
- Do not use csr_write in status-read paths (14/15/17). Writing to
  status registers has no effect (they are RO) and may fail the ack.
"""

    rtl_section = ""
    if rtl_hint:
        rtl_section = f"\n=== RTL REFERENCE (first block of path) ===\n```systemverilog\n{rtl_hint}\n```\n"

    return f"""Generate an event-mode vector file for path {path_id}.

=== VECTOR FORMAT ===
Each vector line: OO PPPPPPPP DDDDDDDD EEEEEEEE (four hex fields, lowercase or uppercase)

Opcodes:
  00 reset          — no fields; calls handle_reset()
  09 event_start    — no fields; pulses DUT enable and zeroes sim_cycle
  04 wait_for       — P[7:0]=sig_id, D=expected_value, E=timeout_cycles
  05 check_at       — P[7:0]=sig_id, D=expected_value, E=target_cycle
  06 check_not_yet  — P[7:0]=sig_id, D=expected_value, E=until_cycle
  07 expect_handshake — P[7:0]=valid_sig_id, P[15:8]=ready_sig_id, E=timeout
  08 check_order    — P[7:0]=first_sig_id, P[15:8]=second_sig_id, E=min_gap_cycles
  03 step           — P=cycles_to_advance (rarely needed in pure event mode)
{csr_opcode_lines}
Comments use // and are stripped by the parser.

=== SIGNAL CATALOG ===
(id, name, kind, details)
{sig_catalog}
{csr_section}
=== CONSTRAINTS ===
- sim_timeout_cycles = {sim_timeout}. wait_for/expect_handshake timeouts MUST NOT exceed this.
- Mode is {mode!r}. The first non-reset opcode MUST be 09 (event_start), otherwise
  sim_cycle is never zeroed and every timing check is meaningless.
- check_order(A, B, gap) REQUIRES that both signal A and signal B were previously
  waited for via wait_for or expect_handshake earlier in the file. Otherwise the
  runtime will emit "CHECK_ORDER MISSING" and fail.
- sig_id fields go in the LOW bits of P: bits [7:0] for first sig, bits [15:8] for
  second sig (in expect_handshake/check_order). Example: first=5, second=8 → P=0x00000805.
- All numeric fields are HEX. Writing "100" means 0x100 = 256 decimal. If you want
  decimal 100 write "00000064".

=== CRITICAL: HEX ENCODING DISCIPLINE ===

Every sig_id you write in a hex field must match the sig_id you describe in the
adjacent comment. This is the single most common mistake. Before writing any
vector, compute the hex value and double-check it.

WORKED EXAMPLES:
  wait_for sig_id=21 (mrs_mr2_issued), value=1, timeout=4096:
    -> hex: 04 00000015 00000001 00001000
    -> P[7:0] = 0x15 = 21 (correct)

  check_order first=21 (mrs_mr2), second=22 (mrs_mr3), min_gap=1:
    -> hex: 08 00001615 00000000 00000001
    -> P[7:0]  = 0x15 = 21 (correct)
    -> P[15:8] = 0x16 = 22 (correct)

  check_order first=24 (mrs_mr0), second=25 (zqcl), min_gap=3:
    -> hex: 08 00001918 00000000 00000003
    -> P[7:0]  = 0x18 = 24 (correct)
    -> P[15:8] = 0x19 = 25 (correct)

Notice: in check_order, the two sig IDs are placed "backwards" in hex - the
SECOND sig goes in the UPPER byte. Reading "00001918" left to right: "0019"
is the upper half (second_id=25), "18" is the lower half (first_id=24).
This is the MOST common source of swapped-order bugs. Verify by decomposing:
  for check_order(A, B, gap): P = (B << 8) | A, written as 0x0000{{B:02X}}{{A:02X}}

=== CRITICAL: TIMELINE RULES ===

sim_cycle is a MONOTONIC counter inside the testbench. It only advances; it
never rewinds.

Ops that advance sim_cycle:
  - wait_for: advances until the signal is observed, up to `timeout` cycles.
  - check_at: advances directly to `target_cycle` if not already past it.
  - check_not_yet: advances all the way to `until_cycle`, sampling as it goes.
  - step: advances exactly `P` cycles.

Ops that do NOT advance sim_cycle:
  - reset (opcode 00): resets the DUT but does NOT touch sim_cycle.
  - event_start (opcode 09): ZEROES sim_cycle.

THE CARDINAL RULE: wait_for catches an event even if it already happened.
The runtime library has a parallel latch that records the first cycle each
signal went nonzero. wait_for(sig, 1, ...) consults this latch and returns
the actual fire cycle - NOT the cycle wait_for was called. This means you
can wait for events in any order. Waiting for state_done first (which
advances sim_cycle to ~140000) and then waiting for mrs_mr2_issued (which
fired at ~140040) still works - the latch has it recorded.

HOWEVER: the latch only works for value=1. wait_for(sig, 0, ...) still
samples live. Prefer waiting for nonzero values.

=== CRITICAL: min_gap VALUES IN check_order ===

check_order with min_gap > 0 is FRAGILE - you must know the actual RTL
timing. When in doubt, USE min_gap=0. Wrong large values are the second
most common bug class.

RULES:
- For two events in the SAME block separated by a named RTL localparam
  (tMRD, tMOD, tZQinit), use that exact localparam value as min_gap.
- For two events in DIFFERENT blocks (e.g. init_done in init_fsm
  triggering ref_required in refresh_ctrl), you usually do NOT know the
  exact inter-block latency. Use min_gap=0 or min_gap=1. Do not guess
  "a big number like 128" - you will false-positive on a valid RTL.
- Signals that may fire on the SAME cycle (init_done -> cal_done via a
  1-cycle flop) REQUIRE min_gap=0.
- check_order does NOT enforce an UPPER bound. You cannot write
  "within 100 cycles" with check_order. Use wait_for with a timeout instead.

IF YOU ARE UNSURE OF A NUMBER: use min_gap=0. A looser check that passes
is better than a tighter check that false-positives.

=== TEST COVERAGE GOALS ===
1. Reset the DUT (opcode 00) - always first.
2. Start the autonomous sequence (opcode 09) - always second.
3. Use check_not_yet at most ONCE, only to guard a single well-defined
   "must not happen before cycle X" constraint.
4. wait_for EVERY event you will later reference in a check_order.
5. wait_for the completion signal(s) - these are the most important.
6. check_order ops go LAST, after all their prerequisite waits.
   Use min_gap=0 unless you have an RTL localparam telling you otherwise.
7. check_at for error-flag sanity (init_fail=0, cal_fail=0) at a cycle
   you know has been reached.
8. DO NOT use step (opcode 03) in pure event-mode specs.

=== STATE-REGISTER PREFERENCE ===

When the spec exposes a raw state register with a single terminal state
(e.g. u_init_fsm.init_state == 14 for S_DONE), prefer one wait_for on that
state register over chains of waits on intermediate events you do not care
about individually. Only declare and wait for intermediate predicates if
you plan to reference them in check_order.

=== RECOMMENDED SEQUENCE PATTERN (init/cal/refresh paths) ===
  00  reset
  09  event_start
  04  wait_for <primary completion signal> timeout=<large>
  04  wait_for <secondary completion signal> timeout=<large>
  08  check_order first=<primary> second=<secondary> min_gap=0
  05  check_at <error flag>=0 at <cycle already reached>
{rtl_section}
=== OUTPUT ===

Return ONLY the vector file content. First character must be '/' (comment) or a hex digit.
Do not include ```, do not include JSON, do not explain.
Aim for 8-20 vectors covering the full sequence. Fewer vectors with correct
min_gap values is better than many vectors with guessed gaps.
"""


# =============================================================================
# Agent
# =============================================================================

class EventVectorAgent:
    def __init__(self, event_spec_path: str, output_dir: str,
                 rtl_hint_path: Optional[str] = None):
        self.event_spec_path = event_spec_path
        self.output_dir = output_dir
        self.rtl_hint_path = rtl_hint_path

        with open(event_spec_path) as f:
            self.event_spec = json.load(f)

    def _load_rtl_hint(self) -> Optional[str]:
        if not self.rtl_hint_path or not os.path.exists(self.rtl_hint_path):
            return None
        with open(self.rtl_hint_path) as f:
            lines = f.readlines()
        # Cap at 400 lines to bound prompt size
        if len(lines) > 400:
            lines = lines[:400] + [f"// ... ({len(lines) - 400} more lines truncated)\n"]
        return "".join(lines)

    def generate(self, max_retries: int = 2) -> List[ParsedVector]:
        rtl_hint = self._load_rtl_hint()
        prompt = build_prompt(self.event_spec, rtl_hint=rtl_hint)

        last_errors = []
        for attempt in range(max_retries + 1):
            messages = [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
            ]
            if last_errors:
                messages.append({
                    "role": "user",
                    "content": (
                        "Your previous vector file failed validation:\n"
                        + "\n".join(f"  - {e}" for e in last_errors)
                        + "\n\nFix all errors and return the corrected vector file. "
                        "Return ONLY the hex file content, no fences, no prose."
                    ),
                })

            print(f"[EventVectorAgent] Attempt {attempt + 1}/{max_retries + 1} — calling LLM")
            raw = call_llm(messages, max_tokens=8000)
            text = strip_fences(raw).strip()

            try:
                vectors = parse_vector_file(text)
            except ValueError as e:
                last_errors = [f"parse error: {e}"]
                print(f"[EventVectorAgent] Parse error: {e}")
                self._last_text = text
                continue

            errors = validate_vectors(vectors, self.event_spec)
            if not errors:
                print(f"[EventVectorAgent] Vectors validated ({len(vectors)} vectors)")
                self._last_text = text
                return vectors

            last_errors = errors
            print(f"[EventVectorAgent] Validation failed with {len(errors)} errors:")
            for err in errors[:10]:
                print(f"  - {err}")
            if len(errors) > 10:
                print(f"  ... and {len(errors) - 10} more")
            self._last_text = text

        raise VectorValidationError(
            f"Failed to generate valid vector file for "
            f"{self.event_spec['path_id']} after {max_retries + 1} attempts. "
            f"Last errors: {last_errors}"
        )

    def write(self, vectors: List[ParsedVector]) -> str:
        os.makedirs(self.output_dir, exist_ok=True)
        path_id = self.event_spec["path_id"]
        out_path = os.path.join(self.output_dir, f"{path_id}_vectors.hex")
        # We write the raw LLM text (preserves comments). The parsed
        # vectors were only used for validation.
        with open(out_path, "w") as f:
            f.write(self._last_text)
            if not self._last_text.endswith("\n"):
                f.write("\n")
        print(f"[EventVectorAgent] Wrote {out_path}")
        return out_path


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Generate event-mode vector file from event_spec.json"
    )
    parser.add_argument("--event-spec", required=True,
                        help="Path to event_spec.json")
    parser.add_argument("--output-dir", required=True,
                        help="Directory to write <path_id>_vectors.hex into")
    parser.add_argument("--rtl-hint", default=None,
                        help="Optional RTL file to include as context (timing constants, etc.)")
    parser.add_argument("--max-retries", type=int, default=2)
    args = parser.parse_args()

    agent = EventVectorAgent(args.event_spec, args.output_dir, args.rtl_hint)
    vectors = agent.generate(max_retries=args.max_retries)
    agent.write(vectors)
    return 0


if __name__ == "__main__":
    sys.exit(main())