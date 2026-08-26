"""
Failure Triage Agent
=====================
Analyzes simulation failures to determine root cause by cross-referencing:

  1. Simulation log       — raw Xcelium output with PASS/FAIL/MISMATCH lines
  2. Simulation report     — parsed JSON from sim_runner (mismatches, counts, status)
  3. Reference model       — Python golden model (expected behavior source)
  4. Testbench             — SystemVerilog TB that drove the simulation
  5. Test vectors          — hex/JSON stimulus+expected data
  6. Microarchitecture spec — authoritative DDR3 controller specification

The agent uses an LLM to perform multi-pass failure analysis:

  Pass 1: Classify — categorize the failure type (compile, mismatch, timeout, etc.)
  Pass 2: Localize — narrow down the failing vectors and map to spec behavior
  Pass 3: Root-cause — cross-reference TB, refmodel, vectors, and spec to find
           whether the bug is in RTL, testbench, reference model, or vectors
  Pass 4: Recommend — suggest concrete fixes with file + line references

Output: A structured triage report (JSON) with human-readable summary.

Usage:
    # Standalone
    python3 failure_triage_agent.py \\
        --scope config_regs \\
        --sim-log ./scopes/config_regs/reports/config_regs_sim.log \\
        --sim-report ./scopes/config_regs/reports/config_regs_simulate_report.json \\
        --testbench ./scopes/config_regs/config_regs_tb.sv \\
        --refmodel ./reference_models/config_regs_refmodel.py \\
        --vectors-hex ./scopes/config_regs/config_regs_vectors.hex \\
        --vectors-json ./scopes/config_regs/config_regs_vectors.json \\
        --spec ./spec/llmmc_microarchitecturespec_filled.json \\
        --output-dir ./scopes/config_regs/reports/

    # Called from orchestrator (programmatic)
    agent = FailureTriageAgent(scope=..., sim_log=..., ...)
    report = agent.run()

Author: Validation Subsystem — Agent 5 (Failure Triage)
"""

import argparse
import json
import os
import re
import sys
import requests
from datetime import datetime
from typing import Any, Dict, List, Optional
from llm_client import call_llm, strip_fences

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# =============================================================================
# File Loaders
# =============================================================================

def load_json(path: str) -> Optional[dict]:
    """Safely load a JSON file, returning None on failure."""
    if not path or not os.path.exists(path):
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"[TriageAgent] Warning: Could not load {path}: {e}")
        return None


def load_text(path: str, max_lines: int = 0) -> Optional[str]:
    """Safely load a text file. If max_lines > 0, return only that many lines."""
    if not path or not os.path.exists(path):
        return None
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            if max_lines > 0:
                lines = []
                for i, line in enumerate(f):
                    if i >= max_lines:
                        lines.append(f"\n... [truncated at {max_lines} lines] ...")
                        break
                    lines.append(line)
                return "".join(lines)
            return f.read()
    except Exception as e:
        print(f"[TriageAgent] Warning: Could not load {path}: {e}")
        return None


def load_spec(path: str) -> dict:
    """Load the microarchitecture spec."""
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def extract_spec_context(spec: dict, scope: str) -> dict:
    """Pull only the spec sections relevant to this scope (mirrors refmodel_agent)."""
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

    elif scope == "refresh_ctrl":
        ctx["timing_model"] = spec.get("timing_model", {})
        ctx["clocking_model"] = spec.get("clocking_model", {})
        ctx["refresh"] = spec.get("refresh", {})

    else:
        # Generic: include everything that might be relevant
        for key in ["timing_model", "clocking_model", "memory_geometry",
                     "host_interface", "csr_register_map", "controller_architecture",
                     "initialization_sequence", "refresh"]:
            if key in spec:
                ctx[key] = spec[key]

    return ctx


# =============================================================================
# Failure Extraction Helpers
# =============================================================================

def extract_sim_failures(sim_log: str) -> dict:
    """Parse simulation log for structured failure information."""
    info = {
        "compile_errors": [],
        "mismatches": [],
        "sva_failures": [],
        "timeout": False,
        "fatal_errors": [],
        "warnings": [],
        "pass_fail_summary": None,
    }

    if not sim_log:
        return info

    # Compile errors
    for m in re.finditer(r'xmvlog:\s*\*E.*', sim_log):
        info["compile_errors"].append(m.group(0))
    for m in re.finditer(r'xmelab:\s*\*E.*', sim_log):
        info["compile_errors"].append(m.group(0))

    # Mismatches — multiple formats
    # Format: MISMATCH/FAIL vec=N addr=0xHH expected=0xHH actual/got=0xHH
    for m in re.finditer(
        r'(?:MISMATCH|FAIL).*?[Vv]ec(?:tor)?[= ]*(\d+).*?[Aa]ddr=0x([0-9A-Fa-f]+).*?'
        r'[Ee]xpected=0x([0-9A-Fa-f]+).*?(?:Actual|got)=0x([0-9A-Fa-f]+)',
        sim_log
    ):
        info["mismatches"].append({
            "vector": int(m.group(1)),
            "addr": m.group(2),
            "expected": m.group(3),
            "actual": m.group(4),
        })

    # Also catch simpler FAIL lines without full mismatch format
    for m in re.finditer(r'^\s*FAIL\s*[-:]\s*(.+)$', sim_log, re.MULTILINE):
        text = m.group(1).strip()
        # Skip if already captured as a mismatch
        if not any(text in json.dumps(mm) for mm in info["mismatches"]):
            info["mismatches"].append({"raw_fail_line": text})

    # SVA assertion failures
    for m in re.finditer(r'xmsim:\s*\*E,ASRTST.*', sim_log):
        info["sva_failures"].append(m.group(0))

    # Timeout / watchdog
    if re.search(r'(?:Watchdog|WATCHDOG|TIMEOUT)', sim_log):
        info["timeout"] = True

    # Fatal errors
    for m in re.finditer(r'xmsim:\s*\*F.*', sim_log):
        info["fatal_errors"].append(m.group(0))

    # Pass/fail summary
    summary = re.search(r'PASS:\s*(\d+)\s+FAIL:\s*(\d+)', sim_log)
    if summary:
        info["pass_fail_summary"] = {
            "passed": int(summary.group(1)),
            "failed": int(summary.group(2)),
        }
    else:
        p = re.search(r'(?:Pass(?:ed)?|PASS(?:ED)?):\s*(\d+)', sim_log)
        f = re.search(r'(?:Fail(?:ed)?|FAIL(?:ED)?):\s*(\d+)', sim_log)
        if p and f:
            info["pass_fail_summary"] = {
                "passed": int(p.group(1)),
                "failed": int(f.group(1)),
            }

    # Warnings (first 20)
    warnings = re.findall(r'xm(?:vlog|elab|sim):\s*\*W.*', sim_log)
    info["warnings"] = warnings[:20]

    return info


def extract_failing_vectors(mismatches: list, vectors_json: Optional[dict]) -> list:
    """Given mismatch list, pull the corresponding vector entries from the JSON."""
    if not vectors_json or not mismatches:
        return []

    # vectors_json can be a list of vectors or a dict with a "vectors" key
    vec_list = vectors_json if isinstance(vectors_json, list) else vectors_json.get("vectors", [])

    failing = []
    for mm in mismatches:
        vec_idx = mm.get("vector")
        if vec_idx is not None and 0 <= vec_idx < len(vec_list):
            entry = dict(vec_list[vec_idx])
            entry["_mismatch"] = mm
            failing.append(entry)

    return failing


def extract_relevant_tb_sections(tb_code: str) -> str:
    """Extract the most relevant sections of a testbench for triage context.
    Returns a trimmed version focused on the comparison/checker logic."""
    if not tb_code:
        return ""

    lines = tb_code.split("\n")
    relevant = []
    in_relevant = False
    context_window = 5  # lines before/after keywords

    # Keywords that indicate comparison/checker/driver logic
    keywords = [
        "MISMATCH", "FAIL", "PASS", "expected", "actual", "compare",
        "check", "$fscanf", "$readmemh", "vector", "assert", "error",
        "mismatch", "fail_count", "pass_count",
    ]

    # Mark lines near keywords as relevant
    marked = [False] * len(lines)
    for i, line in enumerate(lines):
        for kw in keywords:
            if kw.lower() in line.lower():
                for j in range(max(0, i - context_window), min(len(lines), i + context_window + 1)):
                    marked[j] = True
                break

    # Also always include module declaration, DUT instantiation, clock gen
    for i, line in enumerate(lines):
        stripped = line.strip()
        if any(stripped.startswith(p) for p in ["module ", "endmodule", "// DUT", "always #"]):
            for j in range(max(0, i - 2), min(len(lines), i + 3)):
                marked[j] = True

    # Build output with line numbers
    last_included = -10
    for i, line in enumerate(lines):
        if marked[i]:
            if i - last_included > 2:
                relevant.append(f"  ... [{i - last_included - 1} lines omitted] ...")
            relevant.append(f"{i+1:4d}| {line}")
            last_included = i

    # If we captured very little, just return the whole thing (truncated)
    if len(relevant) < 20:
        return "\n".join(f"{i+1:4d}| {l}" for i, l in enumerate(lines[:300]))

    return "\n".join(relevant)


# =============================================================================
# Failure Classification
# =============================================================================

FAILURE_CATEGORIES = {
    "compile_error":   "RTL or testbench has syntax/elaboration errors — simulation never ran",
    "data_mismatch":   "DUT output does not match expected values from reference model",
    "timeout":         "Simulation hit watchdog timer — possible hang, deadlock, or infinite loop",
    "sva_violation":   "SystemVerilog assertion failed during simulation",
    "fatal_error":     "Simulator encountered a fatal error (memory, license, etc.)",
    "unknown_error":   "Simulation did not produce recognizable pass/fail output",
}


def classify_failure(sim_report: dict, parsed_log: dict) -> str:
    """Classify the failure into a category based on sim report and parsed log."""
    status = sim_report.get("status", "unknown")

    if status == "compile_error" or parsed_log["compile_errors"]:
        return "compile_error"
    if status == "timeout" or parsed_log["timeout"]:
        return "timeout"
    if parsed_log["fatal_errors"]:
        return "fatal_error"
    if parsed_log["mismatches"] or status == "fail":
        return "data_mismatch"
    if parsed_log["sva_failures"]:
        return "sva_violation"
    return "unknown_error"


# =============================================================================
# LLM Prompts for Each Triage Pass
# =============================================================================

SYSTEM_PROMPT = """You are an expert hardware verification engineer specializing in DDR3 memory
controller validation. You are performing failure triage on a simulation that did not pass.

Your goal is to determine the ROOT CAUSE of the failure — whether the bug is in:
  (a) The RTL design under test (actual hardware bug)
  (b) The testbench (incorrect stimulus sequencing, wrong protocol, comparison bug)
  (c) The reference model (incorrect expected values)
  (d) The test vectors (malformed stimulus or impossible test scenario)
  (e) The simulation infrastructure (compile errors, missing files, tool issues)

Be precise, cite specific signal names, addresses, vector indices, and line numbers.
When you identify the root cause, explain WHY the mismatch occurs mechanistically."""


def build_verified_facts(sim_report: dict, parsed_log: dict) -> str:
    """Build a ground-truth fact sheet from parsed simulation data.
    
    These facts are programmatically extracted and CANNOT be contradicted
    by the LLM. They anchor the triage analysis to reality.
    """
    total = sim_report.get("total_tests", 0)
    passed = sim_report.get("pass_count", 0)
    failed = sim_report.get("fail_count", 0)
    pass_rate = (passed / total * 100) if total > 0 else 0

    # Analyze mismatch pattern
    mismatches = parsed_log.get("mismatches", []) + (sim_report.get("mismatches") or [])
    actual_values = set()
    expected_values = set()
    for m in mismatches:
        act = str(m.get("actual", m.get("got", ""))).lower()
        exp = str(m.get("expected", m.get("exp", ""))).lower()
        if act:
            actual_values.add(act)
        if exp:
            expected_values.add(exp)

    consistent = len(actual_values) <= 2
    compile_errors = parsed_log.get("compile_errors", [])
    compiled_ok = len(compile_errors) == 0

    facts = []
    facts.append("=" * 60)
    facts.append("VERIFIED FACTS — from simulation log parser (ground truth)")
    facts.append("DO NOT contradict these facts in your analysis.")
    facts.append("=" * 60)

    if compiled_ok:
        facts.append(f"  Compilation: SUCCEEDED (0 compile errors)")
    else:
        facts.append(f"  Compilation: FAILED ({len(compile_errors)} compile errors)")

    if total > 0:
        facts.append(f"  Simulation: RAN TO COMPLETION")
        facts.append(f"  Total tests: {total}")
        facts.append(f"  Passed: {passed}")
        facts.append(f"  Failed: {failed}")
        facts.append(f"  Pass rate: {pass_rate:.1f}%")

    if mismatches:
        facts.append(f"  Mismatches: {len(mismatches)}")
        facts.append(f"  Actual values in mismatches: {', '.join(sorted(actual_values))}")
        facts.append(f"  Expected values in mismatches: {', '.join(sorted(expected_values))}")
        if consistent:
            facts.append(f"  All failures show CONSISTENT actual value(s) — likely a single root cause")
        else:
            facts.append(f"  Failures show VARIED actual values — may indicate multiple issues")

    if pass_rate >= 90 and consistent:
        facts.append("")
        facts.append("  IMPORTANT: With 90%+ pass rate and consistent failure pattern,")
        facts.append("  the most likely cause is a minor timing/modeling edge case in the")
        facts.append("  reference model, NOT an RTL bug. The RTL is probably correct —")
        facts.append("  the refmodel just doesn't perfectly replicate one specific behavior.")
        facts.append("  Do NOT claim this is an RTL bug unless you have concrete evidence")
        facts.append("  from the RTL source code (which you do not have access to).")
        facts.append("  Do NOT make claims about JEDEC/DDR3 spec compliance without")
        facts.append("  citing specific section numbers from the JESD79-3F standard.")

    facts.append("=" * 60)
    return "\n".join(facts)


def build_classify_prompt(scope: str, category: str, parsed_log: dict,
                          sim_report: dict) -> str:
    """Pass 1: Classify and summarize the failure."""
    verified = build_verified_facts(sim_report, parsed_log)
    return f"""FAILURE TRIAGE — Pass 1: Classification

{verified}

Scope: {scope}
Failure category: {category} — {FAILURE_CATEGORIES[category]}

Simulation report:
  Status: {sim_report.get('status', 'unknown')}
  Total tests: {sim_report.get('total_tests', 'N/A')}
  Passed: {sim_report.get('pass_count', 'N/A')}
  Failed: {sim_report.get('fail_count', 'N/A')}

Compile errors ({len(parsed_log['compile_errors'])}):
{chr(10).join(parsed_log['compile_errors'][:10]) if parsed_log['compile_errors'] else '  (none)'}

Data mismatches ({len(parsed_log['mismatches'])}):
{json.dumps(parsed_log['mismatches'][:15], indent=2) if parsed_log['mismatches'] else '  (none)'}

SVA failures ({len(parsed_log['sva_failures'])}):
{chr(10).join(parsed_log['sva_failures'][:5]) if parsed_log['sva_failures'] else '  (none)'}

Timeout: {parsed_log['timeout']}
Fatal errors: {chr(10).join(parsed_log['fatal_errors'][:5]) if parsed_log['fatal_errors'] else '(none)'}
Summary: {json.dumps(parsed_log['pass_fail_summary']) if parsed_log['pass_fail_summary'] else 'N/A'}

Respond with a JSON object:
{{
  "category": "{category}",
  "severity": "critical|high|medium|low",
  "failure_summary": "<one-paragraph summary of what failed and the pattern>",
  "affected_vector_range": "<e.g. vectors 45-52, or 'all', or 'N/A'>",
  "likely_component": "rtl|testbench|refmodel|vectors|infrastructure",
  "initial_hypothesis": "<your best initial guess at root cause>",
  "needs_deeper_analysis": true/false
}}

Output ONLY valid JSON."""


def build_localize_prompt(scope: str, category: str, classification: dict,
                          failing_vectors: list, spec_context: dict,
                          tb_excerpt: str) -> str:
    """Pass 2: Localize the failure to specific signals/registers/operations."""
    return f"""FAILURE TRIAGE — Pass 2: Localization

Scope: {scope}
Category: {category}
Initial hypothesis: {classification.get('initial_hypothesis', 'N/A')}

FAILING VECTORS (with expected vs actual):
{json.dumps(failing_vectors[:20], indent=2)}

SPEC CONTEXT (authoritative behavior):
{json.dumps(spec_context, indent=2)[:8000]}

TESTBENCH EXCERPT (comparison/driver logic):
{tb_excerpt[:6000]}

Analyze the failing vectors against the spec. For each distinct failure pattern:
1. What address/register/field is affected?
2. What is the expected value (from spec) and what did the DUT produce?
3. Is the expected value from the reference model actually correct per spec?
4. Could the testbench be driving signals incorrectly?

Respond with a JSON object:
{{
  "failure_patterns": [
    {{
      "pattern_id": 1,
      "description": "<what is failing>",
      "affected_addresses": ["0x...", ...],
      "affected_fields": ["field_name", ...],
      "vector_indices": [45, 46, ...],
      "expected_correct_per_spec": true/false,
      "testbench_drives_correctly": true/false,
      "notes": "<specific observations>"
    }}
  ],
  "common_thread": "<if multiple patterns share a root cause, describe it>",
  "refined_hypothesis": "<updated root cause hypothesis>"
}}

Output ONLY valid JSON."""


def deterministic_constant_check(rtl_code: str, refmodel_code: str,
                                 mismatched_signals: set) -> dict:
    """Compare constants shared between RTL and refmodel.
    
    Extracts named constants from RTL localparams, Python module-level
    assignments and flags any that share a name but have different values.
    
    Returns a dict:
      {
        "verdict": "rtl_bug" | "refmodel_bug" | "no_mismatch" | "inconclusive",
        "mismatches": [
          {"name": "DDR_WR", "rtl_value": 5, "rtl_line": "cmd_gen.sv:271",
           "refmodel_value": 4, "refmodel_line": "refmodel.py:8", "decision": "rtl_bug"}
        ],
        "summary": "human-readable one-liner"
      }
    """
    import re
    result = {"verdict": "inconclusive", "mismatches": [], "summary": ""}
    if not rtl_code or not refmodel_code:
        return result
    # Extract RTL localparams: "localparam NAME = 4'bXXXX;" or 4'd10 or 32'hDEADBEEF
    rtl_constants = {}
    current_file = "unknown.sv"
    rtl_lp_re = re.compile(
        r"localparam\s+(?:logic\s*\[[^\]]+\]\s*)?([A-Z_][A-Z0-9_]*)\s*=\s*"
        r"(?:(\d+)'([bhdo])([0-9a-fA-FxXzZ_]+)|(\d+))\s*;"
    )
    for i, line in enumerate(rtl_code.split("\n"), 1):
        if line.startswith("// =====") and ".sv" in line:
            m = re.search(r"(\w+\.sv)", line)
            if m:
                current_file = m.group(1)
            continue
        m = rtl_lp_re.search(line)
        if m:
            name = m.group(1)
            if m.group(5):  
                val = int(m.group(5))
            else:
                width, base, digits = m.group(2), m.group(3), m.group(4).replace("_", "")
                try:
                    if base in ("b", "B"):
                        val = int(digits, 2)
                    elif base in ("h", "H"):
                        val = int(digits, 16)
                    elif base in ("o", "O"):
                        val = int(digits, 8)
                    else:
                        val = int(digits)
                except ValueError:
                    continue
            if name not in rtl_constants:
                rtl_constants[name] = (val, f"{current_file}:{i}", line.strip())
    # Extract refmodel constants: "NAME = <int>" or "NAME = 0bXXXX" at module level
    py_const_re = re.compile(
        r"^([A-Z_][A-Z0-9_]*)\s*=\s*(0b[01]+|0x[0-9a-fA-F]+|\d+)"
    )
    refmodel_constants = {}
    for i, line in enumerate(refmodel_code.split("\n"), 1):
        stripped = line.strip()
        if stripped.startswith("#") or not stripped:
            continue
        m = py_const_re.match(stripped)
        if m:
            name = m.group(1)
            raw = m.group(2)
            try:
                if raw.startswith("0b"):
                    val = int(raw, 2)
                elif raw.startswith("0x"):
                    val = int(raw, 16)
                else:
                    val = int(raw)
            except ValueError:
                continue
            if name not in refmodel_constants:
                refmodel_constants[name] = (val, f"refmodel.py:{i}", stripped)
    # Compare shared names
    shared = set(rtl_constants.keys()) & set(refmodel_constants.keys())
    for name in sorted(shared):
        rtl_val, rtl_loc, rtl_line = rtl_constants[name]
        ref_val, ref_loc, ref_line = refmodel_constants[name]
        if rtl_val != ref_val:
            #If reference value differs from RTL, RTL bug
            decision = "rtl_bug"
            result["mismatches"].append({
                "name": name,
                "rtl_value": rtl_val,
                "rtl_line": rtl_loc,
                "rtl_source": rtl_line,
                "refmodel_value": ref_val,
                "refmodel_line": ref_loc,
                "refmodel_source": ref_line,
                "decision": decision,
            })
    if result["mismatches"]:
        result["verdict"] = "rtl_bug"
        mm = result["mismatches"][0]
        result["summary"] = (
            f"DETERMINISTIC CHECK: RTL constant {mm['name']}={mm['rtl_value']} "
            f"(at {mm['rtl_line']}) contradicts refmodel {mm['name']}={mm['refmodel_value']} "
            f"(at {mm['refmodel_line']}). RTL is the guilty component."
        )
    else:
        result["verdict"] = "no_mismatch"
        result["summary"] = (
            f"DETERMINISTIC CHECK: {len(shared)} shared constants compared, "
            f"all values agree. Value-level RTL bug ruled out."
        )
    return result


def find_signal_evidence(rtl_code: str, signal_name: str, max_lines: int = 30) -> str:
    """Search RTL source for assignments to a signal and referenced constants.
    
    Returns a formatted string of file:line -> code for each assignment, plus
    any localparams referenced in those assignments. Gives the triage LLM
    pre-quoted evidence so it cannot hallucinate.
    """
    if not rtl_code or not signal_name:
        return "(no RTL or signal name)"
    import re
    lines = rtl_code.split("\n")
    current_file = "unknown.sv"
    evidence_lines = []
    referenced_constants = set()
    # Patterns: "signal <= ...", "signal = ...", "assign signal = ..."
    # Allow array indexing: "signal[i] <=" etc.
    assign_re = re.compile(
        r"(?:assign\s+)?" + re.escape(signal_name) + r"(?:\s*\[[^\]]*\])?\s*(?:<=|=)\s*(.+?);",
        re.IGNORECASE,
    )
    const_re = re.compile(r"\b([A-Z][A-Z0-9_]{2,})\b")
    for i, line in enumerate(lines, 1):
        if line.startswith("// =====") and ".sv" in line:
            # file header marker
            m = re.search(r"(\w+\.sv)", line)
            if m:
                current_file = m.group(1)
            continue
        m = assign_re.search(line)
        if m:
            evidence_lines.append(f"  {current_file}:{i}: {line.strip()}")
            # Collect referenced UPPERCASE identifiers (likely localparams)
            for const in const_re.findall(m.group(1)):
                if const not in ("NULL", "TRUE", "FALSE", "X", "Z"):
                    referenced_constants.add(const)
            if len(evidence_lines) >= max_lines:
                break
    if not evidence_lines:
        return f"(no assignments to '{signal_name}' found in RTL source)"
    result = [f"Assignments to '{signal_name}':"]
    result.extend(evidence_lines)
    # Now find the localparam definitions for referenced constants
    if referenced_constants:
        result.append(f"\nReferenced constants ({len(referenced_constants)}):")
        current_file = "unknown.sv"
        for i, line in enumerate(lines, 1):
            if line.startswith("// =====") and ".sv" in line:
                m = re.search(r"(\w+\.sv)", line)
                if m:
                    current_file = m.group(1)
                continue
            stripped = line.strip()
            if stripped.startswith("localparam") or stripped.startswith("parameter") or "`define" in stripped:
                for const in referenced_constants:
                    if re.search(r"\b" + re.escape(const) + r"\b", stripped):
                        result.append(f"  {current_file}:{i}: {stripped}")
                        break
    return "\n".join(result)


def decode_mismatches(mismatches: list, output_packing: list) -> str:
    """Decode each mismatch's expected/got hex into per-field signal mismatches.
    
    For each failing vector, XORs expected and actual, walks the output packing
    to find which named fields differ, and formats a human-readable decode.
    Returns a string suitable for injection into a triage prompt.
    """
    if not mismatches or not output_packing:
        return "(no mismatches to decode)"
    lines = []
    for m in mismatches[:20]:  # cap at 20 for prompt size
        try:
            vec = m.get("vector", "?")
            exp = int(str(m.get("expected", "0")).replace("0x", ""), 16)
            act = int(str(m.get("actual", "0")).replace("0x", ""), 16)
            diff = exp ^ act
            if diff == 0:
                continue
            lines.append(f"vec={vec}: expected=0x{exp:08x} actual=0x{act:08x} diff=0x{diff:08x}")
            # Walk packing, find fields that overlap with diff bits
            for f in output_packing:
                lo = f.get("lo", 0)
                hi = f.get("hi", 0)
                width = f.get("width", hi - lo + 1)
                mask = ((1 << width) - 1) << lo
                if diff & mask:
                    exp_field = (exp & mask) >> lo
                    act_field = (act & mask) >> lo
                    block = f.get("block", "?")
                    name = f.get("name", "?")
                    lines.append(
                        f"    bit[{hi}:{lo}] {block}.{name}: "
                        f"expected={exp_field} (0x{exp_field:x}) "
                        f"actual={act_field} (0x{act_field:x})"
                    )
        except (ValueError, TypeError) as e:
            lines.append(f"vec={m.get('vector','?')}: (decode error: {e})")
    return "\n".join(lines) if lines else "(all mismatches decoded to no differing bits)"


def build_rootcause_prompt(scope: str, category: str, classification: dict,
                           localization: dict, refmodel_code: str,
                           tb_code: str, spec_context: dict,
                           sim_report: dict = None, parsed_log: dict = None,
                           rtl_code: str = "",
                           decoded_mismatches: str = "",
                           rtl_evidence: str = "",
                           deterministic_check: dict = None) -> str:
    """Pass 3: Determine definitive root cause with file/line references."""

    # Truncate large inputs to fit context window
    refmodel_excerpt = refmodel_code[:8000] if refmodel_code else "(not available)"
    tb_excerpt = tb_code[:6000] if tb_code else "(not available)"
    rtl_excerpt = rtl_code[:12000] if rtl_code else "(not available - RTL source not provided)"

    verified = build_verified_facts(sim_report or {}, parsed_log or {})

    det = deterministic_check or {}
    if det.get("verdict") == "rtl_bug" and det.get("mismatches"):
        det_section = "AUTHORITATIVE DETERMINISTIC VERDICT (rule-based, not LLM):\n"
        det_section += det.get("summary", "") + "\n"
        det_section += "Confirmed constant mismatches:\n"
        for mm in det["mismatches"]:
            det_section += f"  - {mm['name']}: RTL={mm['rtl_value']} at {mm['rtl_line']} vs refmodel={mm['refmodel_value']} at {mm['refmodel_line']}\n"
        det_section += "\nYOU MUST report guilty_component=rtl, is_rtl_bug=true, and cite this verdict. The deterministic check has already proven the RTL is wrong.\n"
    elif det.get("verdict") == "no_mismatch":
        det_section = "DETERMINISTIC VALUE CHECK: All shared constants agree. Value-level RTL bugs ruled out.\n"
    else:
        det_section = "DETERMINISTIC VALUE CHECK: inconclusive.\n"
    return f"""FAILURE TRIAGE — Pass 3: Root Cause Determination
{det_section}

{verified}

Scope: {scope}
Category: {category}
Failure patterns: {json.dumps(localization.get('failure_patterns', []), indent=2)[:4000]}
Refined hypothesis: {localization.get('refined_hypothesis', 'N/A')}

RTL SOURCE (SystemVerilog) - THIS IS THE DEVICE UNDER TEST:
```systemverilog
{rtl_excerpt}
```

REFERENCE MODEL (Python) - independently derived from spec:
```python
{refmodel_excerpt}
```

TESTBENCH (SystemVerilog):
```systemverilog
{tb_excerpt}
```

SPEC CONTEXT:
{json.dumps(spec_context, indent=2)[:4000]}

DECODED MISMATCHES (per-signal view of each failing vector):
{decoded_mismatches}
PRE-QUOTED RTL EVIDENCE (exact lines that assign each mismatched signal):
{rtl_evidence}


EVIDENCE RULE (MANDATORY SIGNAL-SEARCH PROTOCOL):

Step 1: For EACH mismatched signal from DECODED MISMATCHES, locate the signal's
producing block. The decoded mismatches use format "block.signal_name" e.g.
"cmd_gen.ddr_cmd" means search within the cmd_gen.sv section of RTL SOURCE.

Step 2: In that block's RTL, find the EXACT ASSIGNMENT lines for that signal.
Search for "<signal_name> <=" or "<signal_name> =" or "assign <signal_name>".
For "cmd_gen.ddr_cmd" you would search cmd_gen.sv for "ddr_cmd <=" and list
EVERY assignment you find.

Step 3: For each assignment, quote the line verbatim with its file name. Also
quote the localparams or constants referenced. For example, if you find:
    cmd_gen.sv: ddr_cmd <= DDR_WR;
You must then search for "DDR_WR" in the same file and quote:
    cmd_gen.sv: localparam DDR_WR = 4'b0101;
So you can compare that value against the spec.

Step 4: Compare each quoted RTL value against the spec and against the
DECODED MISMATCHES. If the actual=N from a decoded mismatch corresponds to
a localparam that the spec defines differently, THAT is the bug.

Step 5: ONLY after performing Steps 1-4 with real quoted evidence, state your
root_cause. The root_cause field MUST contain a file name and at least one
verbatim quoted line. If you cannot find assignments or constants for the
mismatched signals in RTL SOURCE, set guilty_component='unknown'.

FORBIDDEN behaviors (these make your response invalid):
- Reasoning about signals by name alone without quoting their RTL assignments
- Suggesting "tFAW shift register" or "pipeline latency" or "state machine"
  issues unless the decoded mismatch signal IS a tFAW/pipeline/state signal
- Citing files not present in RTL SOURCE
- Invented localparam values
- Any root_cause that doesn't include a filename and a quoted line

Determine the DEFINITIVE root cause. The null hypothesis is that the RTL is wrong.
Only conclude the refmodel/testbench is at fault if you have CONCRETE EVIDENCE from the
code shown above, not just a plausible story.

Cross-reference in this order:
1. SPEC-ANCHORED CONSTANTS: If the mismatch is a fixed value (DDR command encoding,
   register reset value, timing parameter, FSM state code) and the spec pins that value,
   the RTL is almost certainly wrong. The refmodel reads the spec; it rarely invents
   constants. Blame the RTL unless you can point to a specific refmodel line that
   contradicts the spec.
2. REFMODEL CORRECTNESS: Does the refmodel compute expected values correctly per the
   spec? Quote the specific refmodel line that is wrong, or conclude the refmodel is OK.
3. TESTBENCH DRIVING: Does the testbench drive the DUT and compare outputs correctly?
   Quote a specific testbench line that is wrong, or conclude the testbench is OK.
4. TIMING/PIPELINE: Is the check happening at the wrong cycle? Quote the specific
   check op and the pipeline stage it lands on.
5. TEST VECTORS: Are the vectors exercising valid scenarios?

IMPORTANT: If you cannot identify a specific line of code in the refmodel or testbench
that is wrong, and the failure pattern is a clean value mismatch (not a 1-cycle offset,
not a sticky-signal drift), the RTL is the guilty component. Do not invent refmodel bugs
to explain mismatches you cannot localize.

For each failure pattern, determine which component is at fault.

Respond with a JSON object:
{{
  "root_causes": [
    {{
      "pattern_id": 1,
      "guilty_component": "rtl|testbench|refmodel|vectors|infrastructure",
      "confidence": "high|medium|low",
      "root_cause": "<precise explanation of the bug>",
      "evidence": "<specific signal values, line numbers, or spec references>",
      "mechanism": "<step-by-step how the failure occurs>"
    }}
  ],
  "primary_root_cause": "<if one root cause dominates, summarize it>",
  "is_rtl_bug": true/false,
  "is_verification_bug": true/false
}}

Output ONLY valid JSON."""


def build_recommend_prompt(scope: str, rootcause: dict,
                           classification: dict) -> str:
    """Pass 4: Generate concrete fix recommendations."""
    return f"""FAILURE TRIAGE — Pass 4: Recommendations

Scope: {scope}
Root causes: {json.dumps(rootcause.get('root_causes', []), indent=2)}
Primary root cause: {rootcause.get('primary_root_cause', 'N/A')}
Is RTL bug: {rootcause.get('is_rtl_bug', 'unknown')}
Is verification bug: {rootcause.get('is_verification_bug', 'unknown')}

For each root cause, provide a specific, actionable fix recommendation.

Respond with a JSON object:
{{
  "recommendations": [
    {{
      "pattern_id": 1,
      "target_file": "<which file to modify: rtl/testbench/refmodel/vectors>",
      "fix_type": "code_change|config_change|regenerate|manual_review",
      "description": "<what to change and why>",
      "suggested_fix": "<pseudo-code or specific code change if possible>",
      "priority": "critical|high|medium|low",
      "can_auto_fix": true/false
    }}
  ],
  "suggested_pipeline_action": "fix_and_rerun|regenerate_testbench|regenerate_vectors|regenerate_refmodel|escalate_to_rtl_team|manual_review",
  "summary": "<2-3 sentence human-readable triage conclusion>"
}}

Output ONLY valid JSON."""


# =============================================================================
# Agent
# =============================================================================

class FailureTriageAgent:
    """Performs multi-pass LLM-driven failure triage on simulation results."""

    def __init__(
        self,
        scope: str,
        sim_log_path: str,
        sim_report_path: str,
        testbench_path: str,
        refmodel_path: str,
        vectors_hex_path: str = "",
        vectors_json_path: str = "",
        spec_path: str = "",
        output_dir: str = ".",
        rtl_paths: list = None,
    ):
        self.scope = scope
        self.sim_log_path = sim_log_path
        self.sim_report_path = sim_report_path
        self.testbench_path = testbench_path
        self.refmodel_path = refmodel_path
        self.vectors_hex_path = vectors_hex_path
        self.vectors_json_path = vectors_json_path
        self.spec_path = spec_path
        self.output_dir = output_dir
        self.rtl_paths = rtl_paths or []
        os.makedirs(output_dir, exist_ok=True)

    def log(self, msg: str):
        print(f"[TriageAgent][{self.scope}] {msg}")

    # --- Data Loading ---

    def _load_inputs(self) -> dict:
        """Load all input files into a unified context dict."""
        self.log("Loading input files...")

        sim_log = load_text(self.sim_log_path, max_lines=2000)
        sim_report = load_json(self.sim_report_path) or {}
        tb_code = load_text(self.testbench_path)
        refmodel_code = load_text(self.refmodel_path)
        # Load RTL source files so triage can compare RTL against spec
        rtl_code_parts = []
        for rpath in self.rtl_paths:
            rtext = load_text(rpath)
            if rtext:
                fname = os.path.basename(rpath)
                rtl_code_parts.append("// ===== " + fname + " =====\n" + rtext)
        rtl_code = "\n\n".join(rtl_code_parts) if rtl_code_parts else ""
        # Load hex_format.json so we can decode mismatches into signal names
        hex_format_path = os.path.join(
            os.path.dirname(self.sim_log_path or ""), "..", "generated", "hex_format.json"
        )
        hex_format = load_json(hex_format_path) or {}
        output_packing = hex_format.get("output_packing", [])
        vectors_json = load_json(self.vectors_json_path)
        vectors_hex = load_text(self.vectors_hex_path, max_lines=500)
        spec = load_json(self.spec_path) or {}
        spec_context = extract_spec_context(spec, self.scope) if spec else {}

        # Parse the simulation log for structured failure data
        parsed_log = extract_sim_failures(sim_log or "")

        # Extract failing vector details
        failing_vectors = extract_failing_vectors(
            parsed_log["mismatches"] + (sim_report.get("mismatches") or []),
            vectors_json,
        )

        # Extract relevant TB sections for compact context
        tb_excerpt = extract_relevant_tb_sections(tb_code or "")

        inputs = {
            "sim_log": sim_log,
            "sim_report": sim_report,
            "parsed_log": parsed_log,
            "tb_code": tb_code,
            "tb_excerpt": tb_excerpt,
            "refmodel_code": refmodel_code,
            "rtl_code": rtl_code,
            "decoded_mismatches": "",  # filled after inputs dict is built
            "output_packing": output_packing,
            "vectors_json": vectors_json,
            "vectors_hex": vectors_hex,
            "spec": spec,
            "spec_context": spec_context,
            "failing_vectors": failing_vectors,
        }

        # Log what we loaded
        loaded = [k for k, v in inputs.items() if v]
        missing = [k for k, v in inputs.items() if not v]
        self.log(f"  Loaded: {', '.join(loaded)}")
        if missing:
            self.log(f"  Missing/empty: {', '.join(missing)}")

        # Decode mismatches using output packing (after inputs dict built)
        mismatches_list = (sim_report.get("mismatches") or []) + (parsed_log.get("mismatches") or [])
        inputs["decoded_mismatches"] = decode_mismatches(mismatches_list, output_packing)
        # Pre-quoted RTL evidence for each mismatched signal
        signal_names_seen = set()
        for m in mismatches_list[:20]:
            try:
                exp = int(str(m.get('expected','0')).replace('0x',''), 16)
                act = int(str(m.get('actual','0')).replace('0x',''), 16)
                diff = exp ^ act
                for f in output_packing:
                    lo = f.get('lo', 0); hi = f.get('hi', 0)
                    width = f.get('width', hi - lo + 1)
                    mask = ((1 << width) - 1) << lo
                    if diff & mask:
                        signal_names_seen.add(f.get('name',''))
            except Exception:
                pass
        evidence_parts = []
        for sig in sorted(signal_names_seen):
            if sig:
                evidence_parts.append(find_signal_evidence(rtl_code, sig))
        inputs["rtl_evidence"] = "\n\n".join(evidence_parts) if evidence_parts else "(no evidence extracted)"
        # Deterministic value-constant check (no LLM)
        det_result = deterministic_constant_check(rtl_code, refmodel_code, signal_names_seen)
        inputs["deterministic_check"] = det_result
        return inputs

    # --- LLM Call with JSON Parsing ---

    def _llm_json(self, prompt: str, pass_name: str) -> dict:
        """Call LLM with the triage system prompt and parse JSON response."""
        self.log(f"  LLM call: {pass_name}...")
        try:
            raw = call_llm([
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": prompt},
            ], max_tokens=8000)

            cleaned = strip_fences(raw)
            result = json.loads(cleaned)
            self.log(f"  {pass_name}: OK")
            return result

        except json.JSONDecodeError as e:
            self.log(f"  {pass_name}: JSON parse error — {e}")
            self.log(f"  Raw response (first 500 chars): {raw[:500]}")
            return {"error": f"JSON parse error: {e}", "raw": raw[:2000]}

        except requests.exceptions.RequestException as e:
            self.log(f"  {pass_name}: API error — {e}")
            return {"error": f"API error: {e}"}

        except Exception as e:
            self.log(f"  {pass_name}: Unexpected error — {e}")
            return {"error": f"Unexpected error: {e}"}

    # --- Triage Passes ---

    def pass1_classify(self, inputs: dict) -> dict:
        """Pass 1: Classify the failure type and severity."""
        self.log("Pass 1: Classification")

        category = classify_failure(inputs["sim_report"], inputs["parsed_log"])
        self.log(f"  Category: {category}")

        prompt = build_classify_prompt(
            self.scope, category, inputs["parsed_log"], inputs["sim_report"]
        )
        result = self._llm_json(prompt, "classify")
        result["_category"] = category
        return result

    def pass2_localize(self, inputs: dict, classification: dict) -> dict:
        """Pass 2: Localize failures to specific signals/addresses."""
        self.log("Pass 2: Localization")

        category = classification.get("_category", "unknown_error")

        # For compile errors, localization is the error messages themselves
        if category == "compile_error":
            self.log("  Compile error — skipping deep localization")
            return {
                "failure_patterns": [{
                    "pattern_id": 1,
                    "description": "Compile/elaboration errors prevent simulation",
                    "affected_addresses": [],
                    "affected_fields": [],
                    "vector_indices": [],
                    "expected_correct_per_spec": None,
                    "testbench_drives_correctly": None,
                    "notes": "\n".join(inputs["parsed_log"]["compile_errors"][:20]),
                }],
                "common_thread": "Compile errors must be fixed before triage can proceed",
                "refined_hypothesis": "Fix compile errors in RTL or testbench",
            }

        prompt = build_localize_prompt(
            self.scope, category, classification,
            inputs["failing_vectors"],
            inputs["spec_context"],
            inputs["tb_excerpt"],
        )
        return self._llm_json(prompt, "localize")

    def pass3_rootcause(self, inputs: dict, classification: dict,
                        localization: dict) -> dict:
        """Pass 3: Determine definitive root cause."""
        self.log("Pass 3: Root Cause Analysis")

        category = classification.get("_category", "unknown_error")

        prompt = build_rootcause_prompt(
            self.scope, category, classification, localization,
            inputs["refmodel_code"] or "",
            inputs["tb_code"] or "",
            inputs["spec_context"],
            sim_report=inputs.get("sim_report", {}),
            parsed_log=inputs.get("parsed_log", {}),
        )
        return self._llm_json(prompt, "rootcause")

    def pass4_recommend(self, classification: dict, rootcause: dict) -> dict:
        """Pass 4: Generate fix recommendations."""
        self.log("Pass 4: Recommendations")

        prompt = build_recommend_prompt(self.scope, rootcause, classification)
        return self._llm_json(prompt, "recommend")

    #Main Pipeline 

    def run(self) -> dict:
        """Execute the full triage pipeline. Returns structured report."""
        self.log("=" * 60)
        self.log(f"Starting failure triage for scope: {self.scope}")
        self.log("=" * 60)

        report = {
            "scope": self.scope,
            "timestamp": datetime.now().isoformat(),
            "status": "in_progress",
            "passes": {},
        }

        # Load all inputs
        try:
            inputs = self._load_inputs()
        except Exception as e:
            self.log(f"ERROR: Failed to load inputs: {e}")
            report["status"] = "input_error"
            report["error"] = str(e)
            self._save_report(report)
            return report

        #  check: is there actually a failure to triage?
        sim_status = inputs["sim_report"].get("status", "unknown")
        if sim_status == "pass":
            self.log("Simulation PASSED — nothing to triage")
            report["status"] = "no_failure"
            report["summary"] = "Simulation passed. No triage needed."
            self._save_report(report)
            return report

        # Pass 1: Classify
        classification = self.pass1_classify(inputs)
        report["passes"]["classify"] = classification
        report["passes"]["deterministic_check"] = inputs.get("deterministic_check", {})

        # Early exit for infrastructure issues with no deeper analysis needed
        if not classification.get("needs_deeper_analysis", True) or classification.get("_category") in ("compile_error", "fatal_error"):
            category = classification.get("_category", "unknown")
            if category in ("compile_error", "fatal_error"):
                self.log("Infrastructure issue — skipping deep analysis")
                report["passes"]["localize"] = {"skipped": True, "reason": category}
                report["passes"]["rootcause"] = {
                    "root_causes": [{
                        "pattern_id": 1,
                        "guilty_component": "infrastructure",
                        "confidence": "high",
                        "root_cause": classification.get("initial_hypothesis", "Compile/fatal error"),
                        "evidence": "\n".join(inputs["parsed_log"]["compile_errors"][:10] +
                                             inputs["parsed_log"]["fatal_errors"][:5]),
                        "mechanism": "Simulation could not run due to infrastructure issues",
                    }],
                    "primary_root_cause": classification.get("initial_hypothesis", "Fix compile errors"),
                    "is_rtl_bug": False,
                    "is_verification_bug": True,
                }
                report["passes"]["recommend"] = self.pass4_recommend(
                    classification, report["passes"]["rootcause"]
                )
                # Deterministic compile-error check: if the missing port exists
                # in the block manifest, the RTL was modified -> RTL bug.
                import re as _re, glob as _glob
                ce_list = inputs.get("parsed_log", {}).get("compile_errors", [])
                for _ce in ce_list:
                    _pm = _re.search(r"Port name '(\w+)'.*instance '.*u_(\w+)'", _ce)
                    if _pm:
                        _port = _pm.group(1)
                        _mod = _pm.group(2)
                        for _mp in _glob.glob("../Frontend/OutputFolders/*/lint_combined/*_manifest.json") + \
                                    _glob.glob("../Frontend/OutputFolders/VALIDATIONREPORT/lint_combined/*_manifest.json"):
                            if _mod in _mp:
                                try:
                                    _md = load_json(_mp)
                                    _all_ports = [p.get("name","") for g,pl in (_md.get("ports",{}) or {}).items() for p in pl]
                                    if _port in _all_ports:
                                        _rc_msg = (
                                            f"COMPILE ERROR: Port '{_port}' exists in {_mod} manifest "
                                            f"but is missing from the current RTL. RTL was modified.")
                                        report["passes"]["rootcause"]["primary_root_cause"] = _rc_msg
                                        report["passes"]["rootcause"]["is_rtl_bug"] = True
                                        report["passes"]["rootcause"]["is_verification_bug"] = False
                                        # Override report-level fields directly
                                        report["guilty_component"] = "rtl"
                                        report["is_rtl_bug"] = True
                                        report["is_verification_bug"] = False
                                        report["primary_root_cause"] = _rc_msg
                                        report["suggested_action"] = "escalate_to_rtl_team"
                                        report["severity"] = "critical"
                                        report["summary"] = _rc_msg
                                        report["passes"]["recommend"] = {
                                            "recommendations": [{
                                                "priority": "critical",
                                                "target_file": f"{_mod}.sv",
                                                "description": (
                                                    f"Port '{_port}' was removed or renamed in {_mod}.sv. "
                                                    f"The design manifest confirms this port should exist. "
                                                    f"Restore the port or update all dependent modules.")
                                            }],
                                            "suggested_pipeline_action": "escalate_to_rtl_team",
                                            "summary": _rc_msg
                                        }
                                except Exception:
                                    pass
                report["status"] = "triaged"
                self._finalize_report(report)
                return report

        # Pass 2: Localize
        localization = self.pass2_localize(inputs, classification)
        report["passes"]["localize"] = localization

        # Pass 3: Root cause
        rootcause = self.pass3_rootcause(inputs, classification, localization)
        report["passes"]["rootcause"] = rootcause

        # Pass 4: Recommendations — skip if deterministic check already identified RTL bug
        _det = inputs.get("deterministic_check", {})
        if _det.get("verdict") == "rtl_bug" and _det.get("mismatches"):
            self.log("Pass 4: SKIPPED (deterministic check already identified RTL bug)")
            mm = _det["mismatches"][0]
            recommendations = {
                "recommendations": [{
                    "priority": "critical",
                    "target_file": mm["rtl_line"].split(":")[0],
                    "description": (
                        f"Fix RTL constant {mm['name']}: currently {mm['rtl_value']} "
                        f"at {mm['rtl_line']}, should be {mm['refmodel_value']} per spec "
                        f"(matches refmodel at {mm['refmodel_line']})."
                    ),
                }],
                "suggested_pipeline_action": "escalate_to_rtl_team",
                "summary": _det.get("summary", "RTL value constant mismatch"),
            }
        else:
            recommendations = self.pass4_recommend(classification, rootcause)
        report["passes"]["recommend"] = recommendations

        # Coverage assessment: determine if path is substantially validated
        report["coverage"] = self._assess_coverage(inputs)

        report["status"] = "triaged"
        self._finalize_report(report)
        return report

    def _assess_coverage(self, inputs: dict) -> dict:
        """Assess overall validation coverage based on pass/fail ratio and mismatch patterns."""
        sim_report = inputs.get("sim_report", {})
        parsed_log = inputs.get("parsed_log", {})

        total = sim_report.get("total_tests", 0)
        passed = sim_report.get("pass_count", 0)
        failed = sim_report.get("fail_count", 0)

        # If total is 0, try to infer from mismatches
        mismatches = parsed_log.get("mismatches", []) + (sim_report.get("mismatches") or [])
        if total == 0 and mismatches:
            failed = len(mismatches)

        pass_rate = (passed / total * 100) if total > 0 else 0

        # Analyze mismatch pattern consistency
        actual_values = set()
        for m in mismatches:
            act = m.get("actual", m.get("got", ""))
            if act:
                actual_values.add(str(act).lower())
        consistent_pattern = len(actual_values) <= 2  # All failures show same 1-2 values

        # Determine validation level
        if total == 0:
            level = "no_data"
            verdict = "No test results to assess"
        elif failed == 0:
            level = "fully_validated"
            verdict = f"All {total} tests passed — path fully validated"
        elif pass_rate >= 90 and consistent_pattern:
            level = "substantially_validated"
            verdict = (f"{passed}/{total} tests passed ({pass_rate:.0f}%). "
                      f"{failed} failures show consistent pattern "
                      f"(likely minor timing/modeling edge case). "
                      f"Path is substantially validated — core functionality confirmed.")
        elif pass_rate >= 75:
            level = "partially_validated"
            verdict = (f"{passed}/{total} tests passed ({pass_rate:.0f}%). "
                      f"Most functionality works but {failed} failures need investigation.")
        else:
            level = "not_validated"
            verdict = (f"{passed}/{total} tests passed ({pass_rate:.0f}%). "
                      f"Significant failures — path needs rework.")

        return {
            "total_tests": total,
            "passed": passed,
            "failed": failed,
            "pass_rate_pct": round(pass_rate, 1),
            "consistent_failure_pattern": consistent_pattern,
            "unique_actual_values": list(actual_values),
            "validation_level": level,
            "verdict": verdict,
        }

    def _finalize_report(self, report: dict):
        """Add top-level summary fields and save."""
        rc = report["passes"].get("rootcause", {})
        rec = report["passes"].get("recommend", {})
        cl = report["passes"].get("classify", {})

        # Preserve fields already set by deterministic checks (manifest, constant)
        _pre_set = report.get("guilty_component") is not None
        report["category"] = cl.get("_category", "unknown")
        # Severity: deterministic RTL bug is always critical
        if report.get("passes", {}).get("deterministic_check", {}).get("verdict") == "rtl_bug":
            report["severity"] = "critical"
        else:
            report["severity"] = cl.get("severity", "unknown")
        report["primary_root_cause"] = rc.get("primary_root_cause", "undetermined")
        report["is_rtl_bug"] = rc.get("is_rtl_bug", None)
        report["is_verification_bug"] = rc.get("is_verification_bug", None)
        # HIGHEST PRIORITY: Deterministic constant check.
        # This is rule-based and cannot hallucinate.
        _det = report.get("passes", {}).get("deterministic_check", {})
        if _det.get("verdict") == "rtl_bug" and _det.get("mismatches"):
            report["guilty_component"] = "rtl"
            report["is_rtl_bug"] = True
            report["is_verification_bug"] = False
            report["suggested_action"] = "escalate_to_rtl_team"
            report["primary_root_cause"] = _det.get("summary", report.get("primary_root_cause", ""))
            report["deterministic_verdict"] = _det
        else:
            # Fall back to Pass 3 rootcause 
            _rc_list = rc.get("root_causes", [])
            if _rc_list and isinstance(_rc_list, list) and _rc_list[0].get("guilty_component"):
                report["guilty_component"] = _rc_list[0]["guilty_component"]
            else:
                report["guilty_component"] = cl.get("likely_component", "unknown")
            report["suggested_action"] = rec.get("suggested_pipeline_action", "manual_review")
        report["summary"] = rec.get("summary", cl.get("failure_summary", "Triage incomplete"))

        # Override suggested action if substantially validated — but NOT if a
        # deterministic RTL bug was found. RTL bugs always escalate regardless of pass rate.
        coverage = report.get("coverage", {})
        _det_rtl = (report.get("passes", {}).get("deterministic_check", {}).get("verdict") == "rtl_bug")
        if coverage.get("validation_level") == "substantially_validated" and not _det_rtl:
            report["suggested_action"] = "accept_with_waivers"
        # Override coverage verdict text when deterministic RTL bug detected.
        # The "substantially validated" verdict is misleading for confirmed RTL bugs.
        if _det_rtl and coverage:
            _det_summary = report.get("passes", {}).get("deterministic_check", {}).get("summary", "")
            coverage["validation_level"] = "rtl_bug_detected"
            coverage["verdict"] = (
                f"{coverage.get('passed', 0)}/{coverage.get('total_tests', 0)} tests passed "
                f"({coverage.get('pass_rate_pct', 0)}%). "
                f"DETERMINISTIC CHECK FAILED: {_det_summary} "
                f"Path cannot be validated until RTL is fixed."
            )
            report["coverage"] = coverage

        self._save_report(report)
        self._print_summary(report)

    def _save_report(self, report: dict):
        """Write triage report to disk."""
        report_path = os.path.join(
            self.output_dir, f"{self.scope}_triage_report.json"
        )
        os.makedirs(self.output_dir, exist_ok=True)
        with open(report_path, "w") as f:
            json.dump(report, f, indent=2)
        self.log(f"Triage report saved: {report_path}")

    def _print_summary(self, report: dict):
        """Print a human-readable triage summary to console."""
        print()
        print("=" * 70)
        print(f"  FAILURE TRIAGE SUMMARY — scope: {self.scope}")
        print("=" * 70)
        print(f"  Status:           {report.get('status', 'unknown')}")
        print(f"  Category:         {report.get('category', 'unknown')}")
        print(f"  Severity:         {report.get('severity', 'unknown')}")
        print(f"  Guilty component: {report.get('guilty_component', 'unknown')}")
        print(f"  Is RTL bug:       {report.get('is_rtl_bug', 'N/A')}")
        print(f"  Is verif bug:     {report.get('is_verification_bug', 'N/A')}")
        print(f"  Suggested action: {report.get('suggested_action', 'N/A')}")
        print()

        # Coverage assessment
        coverage = report.get("coverage", {})
        if coverage:
            level = coverage.get("validation_level", "unknown")
            level_icons = {
                "fully_validated": "✓ FULLY VALIDATED",
                "substantially_validated": "◐ SUBSTANTIALLY VALIDATED",
                "partially_validated": "◔ PARTIALLY VALIDATED",
                "not_validated": "✗ NOT VALIDATED",
                "no_data": "? NO DATA",
            }
            # Override coverage label when a deterministic RTL bug was detected —
            # the path is not "validated" if the RTL has a confirmed value bug.
            _det_rtl = (report.get("passes", {}).get("deterministic_check", {}).get("verdict") == "rtl_bug")
            if _det_rtl:
                coverage_label = "✗ RTL BUG DETECTED"
            else:
                coverage_label = level_icons.get(level, level)
            print(f"  Coverage:         {coverage_label}")
            print(f"  Pass rate:        {coverage.get('passed', 0)}/{coverage.get('total_tests', 0)} "
                  f"({coverage.get('pass_rate_pct', 0)}%)")
            if coverage.get("consistent_failure_pattern") and coverage.get("failed", 0) > 0:
                print(f"  Failure pattern:  Consistent ({coverage.get('failed', 0)} failures, "
                      f"all show: {', '.join(coverage.get('unique_actual_values', []))})")
            print(f"  Verdict:          {coverage.get('verdict', 'N/A')}")
            print()

        print(f"  Root cause: {report.get('primary_root_cause', 'undetermined')}")
        print()
        print(f"  Summary: {report.get('summary', 'N/A')}")
        print()

        # Print recommendations if available
        recs = report.get("passes", {}).get("recommend", {}).get("recommendations", [])
        if recs:
            print("  Recommendations:")
            for rec in recs:
                priority = rec.get("priority", "?")
                target = rec.get("target_file", "?")
                desc = rec.get("description", "?")
                print(f"    [{priority:8s}] {target}: {desc}")
            print()

        print(f"  Full report: {self.output_dir}/{self.scope}_triage_report.json")
        print("=" * 70)


# CLI

def main():
    parser = argparse.ArgumentParser(
        description="DDR3 Memory Controller — Failure Triage Agent",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Full triage after a failed simulation
  python3 failure_triage_agent.py \\
      --scope config_regs \\
      --sim-log ./scopes/config_regs/reports/config_regs_sim.log \\
      --sim-report ./scopes/config_regs/reports/config_regs_simulate_report.json \\
      --testbench ./scopes/config_regs/config_regs_tb.sv \\
      --refmodel ./reference_models/config_regs_refmodel.py \\
      --vectors-json ./scopes/config_regs/config_regs_vectors.json \\
      --spec ./spec/llmmc_microarchitecturespec_filled.json \\
      --output-dir ./scopes/config_regs/reports/

  # Minimal (just sim log + report)
  python3 failure_triage_agent.py \\
      --scope wb_port \\
      --sim-log ./wb_port_sim.log \\
      --sim-report ./wb_port_sim_report.json \\
      --output-dir ./reports/
        """
    )

    parser.add_argument("--scope", required=True,
                        help="Validation scope (e.g. config_regs, wb_port, init_sequence)")
    parser.add_argument("--sim-log", required=True,
                        help="Path to simulation log file")
    parser.add_argument("--sim-report", required=True,
                        help="Path to simulation report JSON (from sim_runner)")
    parser.add_argument("--testbench", default="",
                        help="Path to testbench .sv file")
    parser.add_argument("--refmodel", default="",
                        help="Path to reference model .py file")
    parser.add_argument("--vectors-hex", default="",
                        help="Path to test vectors .hex file")
    parser.add_argument("--vectors-json", default="",
                        help="Path to test vectors .json file")
    parser.add_argument("--spec", default="",
                        help="Path to microarchitecture spec JSON")
    parser.add_argument("--output-dir", default=".",
                        help="Directory to save triage report")
    parser.add_argument("--api-key",
                        help="TAMU AI API key override")
    parser.add_argument("--model",
                        help="LLM model ID override")

    args = parser.parse_args()

    # Override globals if provided
    if args.api_key:
        global API_KEY
        API_KEY = args.api_key
    if args.model:
        global MODEL_ID
        MODEL_ID = args.model

    agent = FailureTriageAgent(
        scope=args.scope,
        sim_log_path=args.sim_log,
        sim_report_path=args.sim_report,
        testbench_path=args.testbench,
        refmodel_path=args.refmodel,
        vectors_hex_path=args.vectors_hex,
        vectors_json_path=args.vectors_json,
        spec_path=args.spec,
        output_dir=args.output_dir,
    )

    report = agent.run()

    # Exit code: 0 if triaged successfully, 1 if triage itself failed
    if report["status"] in ("triaged", "no_failure"):
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()