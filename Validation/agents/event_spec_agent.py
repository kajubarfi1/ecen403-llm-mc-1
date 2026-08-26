"""
Event Spec Agent (Stage 3)
============================
Generates event_spec.json for autonomous-FSM and handshake-driven paths
(paths 08, 09, 14, 15, 17 in the DDR3 controller validation suite).

Reads:
  - path_definitions.json entry for the target path
  - Frontend manifests for each block in the path (port catalog)
  - The wiring template (instance names: u_<block_id>)
  - Raw RTL files (for localparam constants and state encodings)

Writes:
  - scopes/<path_id>/generated/event_spec.json

The spec format is documented in Stage 2. Briefly:
  - signals[]: list of {id, name, kind, ...} where kind is "raw" or "predicate"
  - start: how event_start() pulses the DUT to begin its sequence
  - vector_format: opcode-to-task mapping for Stage 4's dispatch loop

Architecture note: this agent does NOT generate the vector hex file itself.
That's a separate downstream step (event_vector_gen, runs after this).
The split mirrors the existing path_scope_generator -> vector_gen_agent split.

Author: Validation Subsystem — Event Spec Agent
"""

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List, Optional, Tuple

from llm_client import call_llm, strip_fences


# =============================================================================
# Schema validation rules (the 9 from Stage 2 §2.4)
# =============================================================================

# Forbidden tokens in predicate expressions — block SV injection out of expr context
PREDICATE_FORBIDDEN_TOKENS = [
    ";", "module", "endmodule", "always", "initial",
    "task", "endtask", "function", "endfunction",
    "$display", "$finish", "$write", "$fopen", "$system",
    # SVA sampled-value functions require a clocking context ($past, $rose,
    # $fell, $stable, $changed, $sampled). They cannot appear in a plain
    # combinational expression pasted into a ternary, which is where predicate
    # expressions end up. These must be rewritten as pure level-sensitive
    # Boolean logic over the signals in the catalog.
    "$past", "$rose", "$fell", "$stable", "$changed", "$sampled",
]

VALID_MODES = {"event", "cycle", "mixed"}


class SpecValidationError(Exception):
    pass


def validate_event_spec(spec: dict, allowed_blocks: List[str]) -> List[str]:
    """Validate an event_spec.json against the Stage 2 schema rules.

    Returns a list of error strings. Empty list means valid.
    `allowed_blocks` is the path's block list — predicates may only reference
    instances of blocks in this list (rule 6).
    """
    errors = []

    # Rule: required top-level fields
    for field in ("path_id", "mode", "max_sig_id", "sim_timeout_cycles", "start", "signals", "vector_format"):
        if field not in spec:
            errors.append(f"missing required top-level field: {field}")
    if errors:
        return errors  # bail early — downstream checks assume these exist

    # Rule 1: mode is valid
    if spec["mode"] not in VALID_MODES:
        errors.append(f"rule 1: mode must be one of {sorted(VALID_MODES)}, got {spec['mode']!r}")

    # Rule 2: max_sig_id <= library MAX_SIG_ID (32)
    if not isinstance(spec["max_sig_id"], int) or spec["max_sig_id"] > 32 or spec["max_sig_id"] < 1:
        errors.append(f"rule 2: max_sig_id must be int in [1, 32], got {spec['max_sig_id']!r}")

    # Signal-level checks (rules 3, 4, 5, 6)
    seen_ids = set()
    allowed_instances = {f"u_{b}" for b in allowed_blocks}
    for i, sig in enumerate(spec.get("signals", [])):
        loc = f"signals[{i}]"
        if "id" not in sig or "name" not in sig or "kind" not in sig:
            errors.append(f"{loc}: missing id/name/kind")
            continue

        # Rule 3: unique sig ids
        if sig["id"] in seen_ids:
            errors.append(f"rule 3: {loc} duplicate id={sig['id']}")
        seen_ids.add(sig["id"])

        # Rule 2 (cont): id must be within max_sig_id
        if sig["id"] >= spec["max_sig_id"] or sig["id"] < 0:
            errors.append(f"rule 2: {loc} id={sig['id']} out of range [0, {spec['max_sig_id']})")

        if sig["kind"] == "raw":
            # Rule 4: raw needs path + width
            if "path" not in sig or "width" not in sig:
                errors.append(f"rule 4: {loc} kind=raw requires 'path' and 'width'")
                continue
            # Rule 6: instance must be in allowed_blocks
            inst_match = re.match(r"^([a-zA-Z_][a-zA-Z0-9_]*)\.", sig["path"])
            if not inst_match:
                errors.append(f"rule 6: {loc} path {sig['path']!r} does not start with an instance name")
            elif inst_match.group(1) not in allowed_instances:
                errors.append(
                    f"rule 6: {loc} references instance {inst_match.group(1)!r} "
                    f"not in path blocks {sorted(allowed_instances)}"
                )

        elif sig["kind"] == "predicate":
            if "expression" not in sig:
                errors.append(f"rule 4: {loc} kind=predicate requires 'expression'")
                continue
            expr = sig["expression"]
            # Rule 5: forbidden tokens
            for tok in PREDICATE_FORBIDDEN_TOKENS:
                if tok in expr:
                    errors.append(f"rule 5: {loc} expression contains forbidden token {tok!r}")
            # Rule 6: every u_<block> reference must be in allowed instances
            for inst in re.findall(r"\b(u_[a-zA-Z0-9_]+)\b", expr):
                if inst not in allowed_instances:
                    errors.append(
                        f"rule 6: {loc} expression references {inst!r} "
                        f"not in path blocks {sorted(allowed_instances)}"
                    )
        else:
            errors.append(f"{loc}: unknown kind {sig['kind']!r} (must be 'raw' or 'predicate')")

    # Rule 7: pulse start needs non-empty expression
    start = spec.get("start", {})
    if start.get("kind") == "pulse" and not start.get("expression", "").strip():
        errors.append("rule 7: start.kind='pulse' requires a non-empty expression")

    # Rule 8: opcode 00 (reset) required
    opcodes = spec.get("vector_format", {}).get("opcodes", {})
    if "00" not in opcodes:
        errors.append("rule 8: vector_format.opcodes must include '00' (reset)")

    # Rule 9: event mode requires opcode 09 (event_start)
    if spec.get("mode") == "event" and "09" not in opcodes:
        errors.append("rule 9: mode='event' requires vector_format.opcodes to include '09' (event_start)")

    # Rule 10: csr_interface presence must match config_regs in the path
    has_config_regs = "config_regs" in allowed_blocks
    csr_iface = spec.get("csr_interface", {})
    csr_present = bool(csr_iface.get("present", False))
    if has_config_regs and not csr_present:
        errors.append(
            "rule 10: path includes config_regs but csr_interface.present is not true. "
            "Mixed-mode paths must declare csr_interface with present=true and a register map."
        )
    if csr_present and not has_config_regs:
        errors.append(
            "rule 10: csr_interface.present=true but config_regs is not in path blocks. "
            "CSR operations require config_regs to be in the path."
        )
    if csr_present:
        regs = csr_iface.get("registers", [])
        if not isinstance(regs, list) or len(regs) == 0:
            errors.append(
                "rule 10: csr_interface.registers must be a non-empty list when present=true"
            )
        else:
            for j, r in enumerate(regs):
                if not isinstance(r, dict):
                    errors.append(f"rule 10: csr_interface.registers[{j}] must be an object")
                    continue
                for f in ("name", "address", "bits"):
                    if f not in r:
                        errors.append(f"rule 10: csr_interface.registers[{j}] missing {f!r}")

    return errors


# =============================================================================
# Context Assembly
# =============================================================================

BLOCK_TO_MANIFEST = {
    "wb_port": "wb_port_manifest.json", "addr_decoder": "addr_decoder_manifest.json",
    "cmd_queue": "cmd_queue_manifest.json", "bank_tracker": "bank_tracker_manifest.json",
    "scheduler": "scheduler_manifest.json", "refresh_ctrl": "refresh_ctrl_manifest.json",
    "cmd_gen": "cmd_gen_manifest.json", "data_path": "data_path_manifest.json",
    "init_fsm": "init_fsm_manifest.json", "config_regs": "config_regs_manifest.json",
    "calibration": "calibration_manifest.json",
}
BLOCK_TO_RTL = {k: k + ".sv" for k in BLOCK_TO_MANIFEST}


def discover_file(frontend_root: str, filename: str) -> Optional[str]:
    for dirpath, _, filenames in os.walk(frontend_root):
        if filename in filenames:
            return os.path.join(dirpath, filename)
    return None


def load_path_def(path_defs_path: str, path_id: str) -> Tuple[dict, list]:
    """Return (path_def, all_connections) for the requested path."""
    with open(path_defs_path) as f:
        d = json.load(f)
    for p in d["paths"]:
        if p["id"] == path_id:
            return p, d.get("direct_connections", [])
    raise ValueError(f"path_id {path_id!r} not found in {path_defs_path}")


def load_manifest_ports(manifest_path: str) -> Dict[str, dict]:
    """Return {port_name: {width, dir, group}} for a block manifest."""
    with open(manifest_path) as f:
        m = json.load(f)
    ports = {}
    for group, plist in m.get("ports", {}).items():
        for p in plist:
            ports[p["name"]] = {"width": p["width"], "dir": p["dir"], "group": group}
    return ports


def load_rtl_text(rtl_path: str, max_lines: int = 500) -> str:
    """Read RTL file, capped at max_lines to bound prompt size."""
    with open(rtl_path) as f:
        lines = f.readlines()
    if len(lines) > max_lines:
        return "".join(lines[:max_lines]) + f"\n// ... ({len(lines) - max_lines} more lines truncated)\n"
    return "".join(lines)


def assemble_context(path_id: str, path_defs_path: str, frontend_root: str) -> dict:
    """Gather path def, manifests, RTL, and connections for the LLM prompt."""
    path_def, all_connections = load_path_def(path_defs_path, path_id)
    blocks = path_def["blocks"]

    used_conn_ids = set(path_def.get("connections_used", []))
    used_connections = [c for c in all_connections if c["id"] in used_conn_ids]

    block_data = {}
    for bid in blocks:
        manifest_path = discover_file(frontend_root, BLOCK_TO_MANIFEST.get(bid, ""))
        rtl_path = discover_file(frontend_root, BLOCK_TO_RTL.get(bid, ""))
        block_data[bid] = {
            "manifest_path": manifest_path,
            "rtl_path": rtl_path,
            "ports": load_manifest_ports(manifest_path) if manifest_path else {},
            "rtl_text": load_rtl_text(rtl_path) if rtl_path else "",
            "instance_name": f"u_{bid}",
        }

    return {
        "path_def": path_def,
        "blocks": blocks,
        "connections": used_connections,
        "block_data": block_data,
    }


# =============================================================================
# Prompt Construction
# =============================================================================

SYSTEM_PROMPT = """You are a hardware verification engineer designing event-mode test specs for DDR3 memory controller integration paths.

You output ONLY a single JSON object — no prose, no markdown fences, no commentary. The JSON conforms to the event_spec schema documented in the user message."""


_CSR_PROMPT_SECTION = """
=== CSR INTERFACE (MIXED MODE ONLY) ===

This path includes config_regs, so the generated spec must include a
"csr_interface" top-level section AND mode="mixed". The testbench will be
able to perform Wishbone-style CSR reads and writes via new opcodes
0A (csr_read) and 0B (csr_write).

Extract the register map from config_regs.sv. Look for:
  - localparam declarations: ADDR_CTRL_STATUS = 8'h00, ADDR_CTRL_CONFIG = 8'h04, etc.
  - The rdata_mux case statement: each ADDR_X case contains bit-field
    assignments like rdata_mux[0] = sts_init_done.

Emit the csr_interface section in this exact shape:

  "csr_interface": {
    "present": true,
    "address_width": 8,
    "data_width": 32,
    "registers": [
      {
        "name": "CTRL_STATUS",
        "address": "0x00",
        "bits": {
          "init_done": 0,
          "cal_done":  1,
          "cal_fail":  2,
          "bist_done": 3,
          "bist_fail": 4
        }
      }
    ]
  }

RULES:
- Only include registers RELEVANT to the path. For path_14 (init -> status),
  you only need CTRL_STATUS (for init_done bit). For path_15, only
  CTRL_STATUS (for cal_done bit). For path_17, only CTRL_STATUS.
- The "address" field must be a hex string like "0x00".
- The "bits" field maps bit-field names to their bit positions (integers).
  These correspond to the rdata_mux[N] = sts_foo assignments in the RTL.
- Do NOT include every register in config_regs. Fewer is better — only what
  this path actually reads.
- The agent will automatically inject CSR signals (csr_cyc_i, csr_stb_i,
  csr_we_i, csr_adr_i, csr_dat_i, csr_sel_i, csr_ack_o, csr_dat_o) into
  the testbench. You do NOT need to declare them as signals in the
  "signals" array — csr_read/csr_write are handled as dedicated opcodes.
- You DO still need normal signals for the autonomous blocks (init_fsm,
  calibration) since vector_gen needs them for wait_for/check_order.

"""


def build_prompt(ctx: dict) -> str:
    path_def = ctx["path_def"]
    blocks = ctx["blocks"]
    has_config_regs = "config_regs" in blocks
    csr_section = _CSR_PROMPT_SECTION if has_config_regs else ""
    mode_hint = (
        "mixed" if has_config_regs else "event"
    )
    csr_opcode_hint = (
        '    "0A": {{ "name": "csr_read", "fields": {{ "PPPPPPPP[7:0]": "csr_addr", "DDDDDDDD": "expected", "EEEEEEEE": "timeout" }}, "task_call": "csr_read(addr, expected, timeout, vec_num, pc, fc, tt)" }},\n'
        '    "0B": {{ "name": "csr_write", "fields": {{ "PPPPPPPP[7:0]": "csr_addr", "DDDDDDDD": "data", "EEEEEEEE": "timeout" }}, "task_call": "csr_write(addr, data, timeout, vec_num, pc, fc, tt)" }}'
        if has_config_regs else ""
    )

    # Block port catalogs (compact form)
    block_sections = []
    for bid in blocks:
        bd = ctx["block_data"][bid]
        port_lines = []
        for pname, pinfo in sorted(bd["ports"].items()):
            if pname in ("clk", "rst_n"):
                continue
            w = pinfo["width"]
            d = pinfo["dir"]
            port_lines.append(f"    {pname}  [{w}]  {d}")
        ports_str = "\n".join(port_lines) if port_lines else "    (no manifest available)"
        block_sections.append(
            f"=== Block: {bid} (instance: u_{bid}) ===\n"
            f"  Ports:\n{ports_str}\n\n"
            f"  RTL ({bd['rtl_path'] or '(missing)'}):\n"
            f"```systemverilog\n{bd['rtl_text']}\n```\n"
        )

    conn_lines = []
    for c in ctx["connections"]:
        sigs = ", ".join(f"{s['source_port']}->{s['sink_port']} [{s['width']}]" for s in c["signals"])
        conn_lines.append(f"  {c['id']}: {c['from']} -> {c['to']}: {sigs} ({c.get('desc', '')})")
    conn_text = "\n".join(conn_lines) if conn_lines else "  (none)"

    return f"""Generate an event_spec.json for the following DDR3 controller integration path.

PATH ID: {path_def['id']}
PATH NAME: {path_def['name']}
BLOCKS: {' -> '.join(blocks)}
MODE HINT: {mode_hint}  (use this for the top-level "mode" field)

CONNECTIONS USED:
{conn_text}

BLOCK DETAILS:
{''.join(block_sections)}
{csr_section}
=== EVENT_SPEC SCHEMA ===

You output a single JSON object with these top-level fields:

  path_id            (string) — must equal "{path_def['id']}"
  mode               (string) — "event" for fully autonomous paths, "mixed" if the path
                                also needs cycle-mode CSR reads at the tail
  max_sig_id         (int)    — leave as 32 unless you need more than 32 signals
  sim_timeout_cycles (int)    — overall watchdog. Use 800000 for init paths,
                                200000 for short paths
  start              (object) — describes how to begin the autonomous sequence:
    {{
      "kind": "pulse",
      "expression": "u_<block>.<input_port> = 1'b1;"
    }}
    Use kind="pulse" for paths with a single enable input. The expression is a
    raw SV statement that will be pasted verbatim into the testbench.
  signals            (array)  — see below
  vector_format      (object) — copy verbatim from the section at the bottom

=== SIGNALS ===

Each signal entry has an integer id (unique, 0..max_sig_id-1), a human-readable
name, and a kind. Two kinds are supported:

  RAW signal (sample a port directly):
    {{
      "id": 0,
      "name": "init_state",
      "kind": "raw",
      "path": "u_init_fsm.init_state",
      "width": 4
    }}

  PREDICATE signal (composite boolean expression):
    {{
      "id": 5,
      "name": "mrs_mr2_issued",
      "kind": "predicate",
      "expression": "u_init_fsm.init_cmd_valid && u_init_fsm.init_cmd == 4'b0000 && u_init_fsm.init_bank == 3'd2"
    }}

RULES FOR SIGNALS:
1. Every signal id must be unique and < max_sig_id.
2. Raw signals MUST use the instance name u_<block> as the path prefix, where
   <block> is one of: {', '.join(blocks)}. No other instances exist.
3. Predicate expressions MUST only reference u_<block>.<port> for blocks in
   the path. They MUST NOT contain any of: ; module endmodule always initial
   task endtask function endfunction $display $finish (these would break
   the SV elaboration when pasted into a function body).
4. Predicate expressions are pasted into a "(<expression>) ? 32'h1 : 32'h0"
   ternary — keep them PURE COMBINATIONAL BOOLEAN. They must evaluate to a
   single bit based on the CURRENT VALUES of signals. They MUST NOT use SVA
   sampled-value functions: $past, $rose, $fell, $stable, $changed, $sampled.
   Those require a clocking context and will fail to compile in a function.
   To express "rising edge of X," use a raw signal that samples X directly
   and let the runtime latch track first occurrence. Do not attempt to detect
   edges inside a predicate.
5. Prefer raw signals over predicates when a single port suffices. State
   register samples (e.g. u_init_fsm.init_state) are clearer than chains of
   command predicates.
6. Cover the full set of events the path must check: state transitions,
   handshakes, completion signals, error/fail signals, and any composite
   events the spec requires (e.g. JEDEC MRS sequence).

=== START EXPRESSION ===

For paths beginning with init_fsm: the start expression is "u_init_fsm.enable = 1'b1;".
For paths beginning with calibration alone: typically also a single-port enable.
For CSR-only paths (no autonomous block): use {{"kind": "none"}} and omit "expression".

Examine the RTL of the FIRST block in the path to find the input port that
triggers its autonomous sequence. It will typically be named "enable", "start",
or similar.

=== VECTOR_FORMAT (copy verbatim) ===

{{
  "format_string": "OO PPPPPPPP DDDDDDDD EEEEEEEE",
  "opcodes": {{
    "00": {{ "name": "reset", "fields": {{}}, "task_call": "handle_reset()" }},
    "09": {{ "name": "event_start", "fields": {{}}, "task_call": "event_start()" }},
    "04": {{ "name": "wait_for", "fields": {{ "PPPPPPPP[7:0]": "sig_id", "DDDDDDDD": "value", "EEEEEEEE": "timeout" }}, "task_call": "wait_for(sig_id, value, timeout, vec_num, pc, fc, tt)" }},
    "05": {{ "name": "check_at", "fields": {{ "PPPPPPPP[7:0]": "sig_id", "DDDDDDDD": "value", "EEEEEEEE": "target_cycle" }}, "task_call": "check_at(sig_id, value, target_cycle, vec_num, pc, fc, tt)" }},
    "06": {{ "name": "check_not_yet", "fields": {{ "PPPPPPPP[7:0]": "sig_id", "DDDDDDDD": "value", "EEEEEEEE": "until_cycle" }}, "task_call": "check_not_yet(sig_id, value, until_cycle, vec_num, pc, fc, tt)" }},
    "07": {{ "name": "expect_handshake", "fields": {{ "PPPPPPPP[7:0]": "valid_id", "PPPPPPPP[15:8]": "ready_id", "EEEEEEEE": "timeout" }}, "task_call": "expect_handshake(valid_id, ready_id, timeout, vec_num, pc, fc, tt)" }},
    "08": {{ "name": "check_order", "fields": {{ "PPPPPPPP[7:0]": "first_id", "PPPPPPPP[15:8]": "second_id", "EEEEEEEE": "min_gap" }}, "task_call": "check_order(first_id, second_id, min_gap, vec_num, pc, fc, tt)" }}{',' if csr_opcode_hint else ''}
{csr_opcode_hint}
  }}
}}

=== OUTPUT ===

Return ONLY the JSON object. No markdown fences. No prose before or after.
The first character of your response must be '{{' and the last must be '}}'.
"""


# =============================================================================
# Agent
# =============================================================================

class EventSpecAgent:
    def __init__(self, path_id: str, path_defs_path: str, frontend_root: str, output_dir: str):
        self.path_id = path_id
        self.path_defs_path = path_defs_path
        self.frontend_root = os.path.abspath(frontend_root)
        self.output_dir = output_dir

    def generate(self, max_retries: int = 2) -> dict:
        """Generate, validate, and return the event_spec dict.

        On validation failure, retries with the error list appended to the
        prompt — same pattern the existing agents use.
        """
        ctx = assemble_context(self.path_id, self.path_defs_path, self.frontend_root)
        blocks = ctx["blocks"]
        prompt = build_prompt(ctx)

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
                        "Your previous response failed validation with these errors:\n"
                        + "\n".join(f"  - {e}" for e in last_errors)
                        + "\n\nFix all errors and regenerate the JSON. Return ONLY the JSON object."
                    ),
                })

            print(f"[EventSpecAgent] Attempt {attempt + 1}/{max_retries + 1} — calling LLM")
            raw = call_llm(messages, max_tokens=8000)
            text = strip_fences(raw).strip()

            try:
                spec = json.loads(text)
            except json.JSONDecodeError as e:
                last_errors = [f"response is not valid JSON: {e}"]
                print(f"[EventSpecAgent] JSON parse error: {e}")
                continue

            errors = validate_event_spec(spec, allowed_blocks=blocks)
            if not errors:
                print(f"[EventSpecAgent] Spec validated ({len(spec.get('signals', []))} signals)")
                return spec

            last_errors = errors
            print(f"[EventSpecAgent] Validation failed with {len(errors)} errors:")
            for e in errors:
                print(f"  - {e}")

        raise SpecValidationError(
            f"Failed to generate valid event_spec for {self.path_id} after "
            f"{max_retries + 1} attempts. Last errors: {last_errors}"
        )

    def write(self, spec: dict) -> str:
        os.makedirs(self.output_dir, exist_ok=True)
        out_path = os.path.join(self.output_dir, "event_spec.json")
        with open(out_path, "w") as f:
            json.dump(spec, f, indent=2)
        print(f"[EventSpecAgent] Wrote {out_path}")
        return out_path


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Generate event_spec.json for an event-mode integration path"
    )
    parser.add_argument("--path-id", required=True,
                        help="Path ID from path_definitions.json (e.g. path_08_init_to_cal)")
    parser.add_argument("--path-defs", required=True, help="Path to path_definitions.json")
    parser.add_argument("--frontend-root", required=True, help="Path to Frontend output root")
    parser.add_argument("--output-dir", required=True,
                        help="Directory to write event_spec.json into")
    parser.add_argument("--max-retries", type=int, default=2,
                        help="LLM retry budget on validation failure (default: 2)")
    args = parser.parse_args()

    agent = EventSpecAgent(args.path_id, args.path_defs, args.frontend_root, args.output_dir)
    spec = agent.generate(max_retries=args.max_retries)
    agent.write(spec)
    return 0


if __name__ == "__main__":
    sys.exit(main())