#!/usr/bin/env python3
"""
intake_agent.py (Claude-powered)

What it does:
1) Loads .env (no external deps) and reads:
   - ANTHROPIC_API_KEY
   - MODEL
   - ORFS_DIR
   - OUT_ROOT
   - PLATFORM (optional default)
   - MAKE_TARGET (optional default)
   - MAKE_JOBS (optional default)

2) Deterministically validates a frontend bundle containing:
   - a manifest JSON (e.g., *_manifest.json or manifest.json)
   - the RTL file referenced by manifest["file"]

3) Produces:
   - intake_report.json (machine-readable)
   - intake_summary.md  (Claude-generated human-readable fix plan)
   under out_dir (defaults to OUT_ROOT/intake/<bundle_name>/ if OUT_ROOT is set).

Exit codes:
  0 -> PASS
  1 -> PASS_WITH_WARNINGS
  2 -> FAIL

Usage:
  python intake_agent.py --bundle_dir /path/to/bundle
  python intake_agent.py --bundle_dir /path/to/bundle --out_dir /path/to/out
  python intake_agent.py --bundle_dir /path/to/bundle --env_file /path/to/.env
"""

from __future__ import annotations

import argparse
import json
import os
import re
import textwrap
import urllib.request
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


# ----------------------------
# .env loader (no dependencies)
# ----------------------------

def load_env_file(env_path: Path) -> None:
    """
    Minimal .env loader:
    - supports KEY=VALUE lines
    - ignores blank lines and lines starting with '#'
    - does not overwrite existing environment variables
    """
    if not env_path.exists():
        return

    for raw_line in env_path.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        k = k.strip()
        v = v.strip().strip('"').strip("'")

        # Handle cases like: KEY= [REDACTED] (leading spaces)
        v = v.strip()

        os.environ.setdefault(k, v)


# ----------------------------
# Findings / report structures
# ----------------------------

@dataclass
class Finding:
    severity: str  # "ERROR" | "WARNING"
    code: str
    message: str
    fix: str


def add_finding(lst: List[Finding], severity: str, code: str, message: str, fix: str) -> None:
    lst.append(Finding(severity=severity, code=code, message=message, fix=fix))


def status_from_findings(errors: List[Finding], warnings: List[Finding]) -> str:
    if errors:
        return "FAIL"
    if warnings:
        return "PASS_WITH_WARNINGS"
    return "PASS"


# ----------------------------
# Lightweight SystemVerilog parsing
#   - module header extraction
#   - port list parsing (name + direction + simple packed range)
# Notes:
#   This intentionally avoids full SV parsing; it’s enough for intake validation.
# ----------------------------

MODULE_HEADER_RE = re.compile(
    r"\bmodule\s+(?P<name>\w+)\s*(?:#\s*\(.*?\))?\s*\((?P<ports>.*?)\)\s*;",
    re.S,
)


def strip_comments(s: str) -> str:
    s = re.sub(r"//.*", "", s)
    s = re.sub(r"/\*.*?\*/", "", s, flags=re.S)
    return s


def extract_module_header(rtl_text: str, module_name: str) -> Optional[str]:
    txt = strip_comments(rtl_text)
    for m in MODULE_HEADER_RE.finditer(txt):
        if m.group("name") == module_name:
            # Return the entire "module ... (...);" header
            return m.group(0)
    return None


def extract_ports_blob(rtl_text: str, module_name: str) -> Optional[str]:
    txt = strip_comments(rtl_text)
    for m in MODULE_HEADER_RE.finditer(txt):
        if m.group("name") == module_name:
            return m.group("ports")
    return None


def parse_ports_from_blob(ports_blob: str) -> Dict[str, Dict[str, Any]]:
    """
    Parses simple ANSI-style port declarations split by commas.
    Returns: port_name -> {dir, range, raw}
    Handles unpacked array dimensions after the port name, e.g.:
      "input logic [ROW_BITS-1:0] q_row [DEPTH]"
    """
    parts = [p.strip() for p in ports_blob.split(",") if p.strip()]
    port_map: Dict[str, Dict[str, Any]] = {}
    for p in parts:
        toks = p.split()
        if not toks:
            continue
        if toks[0] not in ("input", "output", "inout"):
            continue

        # Find the port name: last token that is a plain identifier (not [something])
        name = None
        for tok in reversed(toks):
            if re.match(r"^\w+$", tok):
                name = tok
                break
        if name is None:
            continue

        # Packed range is the first [...] in the declaration
        rng_m = re.search(r"\[[^\]]+\]", p)
        rng = rng_m.group(0) if rng_m else None

        port_map[name] = {"dir": toks[0], "range": rng, "raw": p}
    return port_map


# ----------------------------
# Bundle/manifest discovery
# ----------------------------

def find_manifest_json(bundle_dir: Path) -> Optional[Path]:
    """
    Finds the manifest in the bundle directory.
    Prefers:
      1) manifest.json
      2) *_manifest.json
      3) any *manifest*.json
    """
    direct = bundle_dir / "manifest.json"
    if direct.exists():
        return direct

    exact = list(bundle_dir.glob("*_manifest.json"))
    if exact:
        return sorted(exact, key=lambda p: len(p.name))[0]

    broad = list(bundle_dir.glob("*manifest*.json"))
    if broad:
        return sorted(broad, key=lambda p: len(p.name))[0]

    return None


# ----------------------------
# OpenROAD-flow-scripts checks (path presence only)
# ----------------------------

def check_orfs_dir(orfs_dir: Optional[str], errors: List[Finding], warnings: List[Finding]) -> Dict[str, Any]:
    """
    Check that ORFS_DIR exists and looks like OpenROAD-flow-scripts.
    We only validate path existence and presence of a Makefile as a sanity check.
    """
    info: Dict[str, Any] = {"orfs_dir": orfs_dir, "exists": False, "looks_valid": False}

    if not orfs_dir:
        add_finding(
            warnings, "WARNING", "ORFS-001",
            "ORFS_DIR not set. Runner/packager may not know where OpenROAD-flow-scripts is installed.",
            "Set ORFS_DIR in .env to your OpenROAD-flow-scripts path."
        )
        return info

    p = Path(orfs_dir)
    info["exists"] = p.exists()
    if not p.exists():
        add_finding(
            errors, "ERROR", "ORFS-002",
            f"ORFS_DIR points to a non-existent path: {orfs_dir}",
            "Fix ORFS_DIR in .env so it points to the OpenROAD-flow-scripts directory."
        )
        return info

    mk = p / "flow" / "Makefile"
    info["looks_valid"] = mk.exists()
    if not mk.exists():
        add_finding(
            warnings, "WARNING", "ORFS-003",
            f"ORFS_DIR exists but does not contain a Makefile: {orfs_dir}",
            "Double-check ORFS_DIR is set to the root of OpenROAD-flow-scripts."
        )

    return info


# ----------------------------
# Deterministic validation
# ----------------------------

def deterministic_validate(bundle_dir: Path) -> Dict[str, Any]:
    errors: List[Finding] = []
    warnings: List[Finding] = []
    facts: Dict[str, Any] = {"bundle_dir": str(bundle_dir)}

    # Env-derived defaults (these are allowed to satisfy OpenROAD needs)
    env = {
        "MODEL": os.environ.get("MODEL", "").strip(),
        "PLATFORM": os.environ.get("PLATFORM", "").strip(),
        "MAKE_TARGET": os.environ.get("MAKE_TARGET", "").strip(),
        "MAKE_JOBS": os.environ.get("MAKE_JOBS", "").strip(),
        "ORFS_DIR": os.environ.get("ORFS_DIR", "").strip(),
        "OUT_ROOT": os.environ.get("OUT_ROOT", "").strip(),
        "HAS_API_KEY": bool(os.environ.get("ANTHROPIC_API_KEY", "").strip()),
    }
    facts["env"] = {k: (v if k != "HAS_API_KEY" else env["HAS_API_KEY"]) for k, v in env.items()}

    # Bundle dir existence
    if not bundle_dir.exists():
        add_finding(
            errors, "ERROR", "IO-001",
            f"Bundle directory does not exist: {bundle_dir}",
            "Ensure the frontend uploaded the bundle and the backend path is correct."
        )
        return _finalize_validation(errors, warnings, facts, manifest=None)

    # ORFS sanity check (path presence)
    facts["orfs_check"] = check_orfs_dir(env["ORFS_DIR"] or None, errors, warnings)

    # Find manifest
    manifest_path = find_manifest_json(bundle_dir)
    if not manifest_path:
        add_finding(
            errors, "ERROR", "MAN-001",
            f"No manifest JSON found in {bundle_dir}",
            "Include manifest.json or *_manifest.json in the bundle."
        )
        return _finalize_validation(errors, warnings, facts, manifest=None)

    facts["manifest_path"] = str(manifest_path)

    # Load manifest
    try:
        manifest = json.loads(manifest_path.read_text())
    except Exception as e:
        add_finding(
            errors, "ERROR", "MAN-002",
            f"Manifest is not valid JSON: {e}",
            "Fix JSON formatting and re-export from frontend."
        )
        return _finalize_validation(errors, warnings, facts, manifest=None)

    # Required keys
    for key, code, fix in [
        ("module_name", "MAN-010", "Add module_name (top module) to the manifest."),
        ("file", "MAN-011", "Add file (RTL filename) to the manifest."),
        ("ports", "MAN-012", "Add ports (grouped port lists) to the manifest."),
        ("parameters", "MAN-013", "Add parameters (dict; can be empty {}) to the manifest."),
    ]:
        if key not in manifest:
            add_finding(errors, "ERROR", code, f"Missing manifest key '{key}'.", fix)

    if errors:
        return _finalize_validation(errors, warnings, facts, manifest=manifest)

    # Basic type checks
    if not isinstance(manifest["module_name"], str) or not manifest["module_name"].strip():
        add_finding(errors, "ERROR", "MAN-020", "manifest.module_name must be a non-empty string.", "Set module_name to the RTL top module name.")
    rtl_files_raw = manifest["file"] if isinstance(manifest["file"], list) else [manifest["file"]]
    if not rtl_files_raw or not all(isinstance(f, str) and f.strip() for f in rtl_files_raw):
        add_finding(errors, "ERROR", "MAN-021",
                    "manifest.file must be a non-empty string, or a list of non-empty strings for a "
                    "design that spans several sources.",
                    "Set file to the RTL filename, or to a list of filenames.")
    if not isinstance(manifest["ports"], dict):
        add_finding(errors, "ERROR", "MAN-022", "manifest.ports must be a dict of groups -> port lists.", "Fix ports to be an object with arrays per group.")
    if not isinstance(manifest["parameters"], dict):
        add_finding(errors, "ERROR", "MAN-023", "manifest.parameters must be a dict (can be empty {}).", "Fix parameters to be an object/dict.")

    if errors:
        return _finalize_validation(errors, warnings, facts, manifest=manifest)

    module_name = manifest["module_name"].strip()
    rtl_files = [f.strip() for f in rtl_files_raw]
    rtl_paths = [bundle_dir / f for f in rtl_files]

    facts.update({"module_name": module_name, "rtl_files": rtl_files,
                  "rtl_paths": [str(p) for p in rtl_paths]})

    # RTL file existence
    missing = [f for f, p in zip(rtl_files, rtl_paths) if not p.exists()]
    if missing:
        add_finding(
            errors, "ERROR", "IO-010",
            f"RTL file(s) referenced by manifest do not exist: {missing}",
            "Include the listed file(s) in the bundle, or fix manifest.file."
        )
        return _finalize_validation(errors, warnings, facts, manifest=manifest)

    # The top module may be defined in any of the listed sources
    sources = [(f, p.read_text(errors="ignore")) for f, p in zip(rtl_files, rtl_paths)]
    defining = [(f, t) for f, t in sources if extract_module_header(t, module_name)]
    if len(defining) > 1:
        add_finding(
            warnings, "WARNING", "RTL-002",
            f"Top module '{module_name}' is defined in more than one listed file: {[f for f, _ in defining]}",
            "Keep a single definition of the top module in the bundle."
        )
    rtl_filename, rtl_text = defining[0] if defining else (rtl_files[0], sources[0][1])
    facts.update({"rtl_filename": rtl_filename, "rtl_path": str(bundle_dir / rtl_filename)})

    # Top module present
    header = extract_module_header(rtl_text, module_name)
    ports_blob = extract_ports_blob(rtl_text, module_name)
    if not header or not ports_blob:
        add_finding(
            errors, "ERROR", "RTL-001",
            f"Top module '{module_name}' not found (or not in ANSI header form) in '{rtl_filename}'.",
            "Fix manifest.module_name or ensure the RTL defines that module with an ANSI-style port list."
        )
        return _finalize_validation(errors, warnings, facts, manifest=manifest)

    facts["rtl_module_header_excerpt"] = header[:1400]

    rtl_ports = parse_ports_from_blob(ports_blob)
    facts["rtl_ports_found"] = sorted(rtl_ports.keys())

    # Flatten manifest ports
    manifest_ports: List[Dict[str, Any]] = []
    for group, plist in manifest["ports"].items():
        if not isinstance(plist, list):
            add_finding(
                errors, "ERROR", "MAN-030",
                f"ports['{group}'] must be a list.",
                f"Fix ports['{group}'] to be a list of port objects."
            )
            continue
        for p in plist:
            if not isinstance(p, dict):
                add_finding(
                    errors, "ERROR", "MAN-031",
                    f"A port entry in group '{group}' is not an object: {p!r}",
                    "Each port must be an object like {name, width, dir}."
                )
                continue
            manifest_ports.append({"group": group, **p})

    if errors:
        return _finalize_validation(errors, warnings, facts, manifest=manifest)

    # Check port fields and cross-check with RTL for existence + direction
    missing_ports: List[str] = []
    dir_mismatches: List[Tuple[str, str, str]] = []
    bad_port_entries = 0

    for p in manifest_ports:
        name = p.get("name")
        direction = p.get("dir")
        width = p.get("width")

        if not isinstance(name, str) or not name.strip():
            bad_port_entries += 1
            add_finding(errors, "ERROR", "MAN-032", f"Port missing/invalid name: {p}", "Ensure every port has a non-empty string 'name'.")
            continue
        if direction not in ("input", "output", "inout"):
            bad_port_entries += 1
            add_finding(errors, "ERROR", "MAN-033", f"Port '{name}' has invalid dir: {direction!r}", "Set dir to 'input', 'output', or 'inout'.")
            continue
        resolved_width = _resolve_width(width)
        if resolved_width is None:
            bad_port_entries += 1
            add_finding(errors, "ERROR", "MAN-034", f"Port '{name}' has invalid width: {width!r}", "Set width to a positive integer, or use 'NxM' for unpacked arrays (e.g. '16x15').")
            continue

        if name not in rtl_ports:
            missing_ports.append(name)
        else:
            rdir = rtl_ports[name]["dir"]
            if rdir != direction:
                dir_mismatches.append((name, direction, rdir))

    if missing_ports:
        add_finding(
            errors, "ERROR", "RTL-010",
            f"Manifest lists ports not present in RTL: {sorted(set(missing_ports))}",
            "Update RTL module port list or regenerate the manifest from the RTL."
        )

    if dir_mismatches:
        add_finding(
            errors, "ERROR", "RTL-011",
            f"Port direction mismatches (name, manifest, rtl): {dir_mismatches}",
            "Fix manifest port directions or correct RTL port directions."
        )

    # Warn if RTL has ports not in manifest (usually frontend manifest generation bug)
    manifest_port_names = {p.get("name") for p in manifest_ports if isinstance(p.get("name"), str)}
    extra_rtl_ports = [n for n in rtl_ports.keys() if n not in manifest_port_names]
    if extra_rtl_ports:
        add_finding(
            warnings, "WARNING", "MAN-040",
            f"RTL includes ports not listed in manifest: {sorted(extra_rtl_ports)}",
            "Regenerate the manifest so it includes all module ports (or update it manually)."
        )

    # OpenROAD readiness (what the Runner/Packager will need)
    # Some can be satisfied by backend defaults in .env
    readiness: Dict[str, Any] = {
        "platform": manifest.get("platform") or (os.environ.get("PLATFORM") or None),
        "make_target": manifest.get("make_target") or (os.environ.get("MAKE_TARGET") or None),
        "make_jobs": manifest.get("make_jobs") or (os.environ.get("MAKE_JOBS") or None),
        "clock_port": None,
        "reset_port": None,
        "clock_period_ns": manifest.get("clock_period_ns") or None,
        "has_orfs_dir": bool((os.environ.get("ORFS_DIR") or "").strip()),
    }

    # Try to infer clock/reset from manifest groups if present
    clock_reset = manifest["ports"].get("clock_reset", [])
    if isinstance(clock_reset, list):
        for p in clock_reset:
            if not isinstance(p, dict):
                continue
            n = p.get("name")
            d = p.get("dir")
            if not isinstance(n, str) or d != "input":
                continue
            ln = n.lower()
            if readiness["clock_port"] is None and "clk" in ln:
                readiness["clock_port"] = n
            if readiness["reset_port"] is None and ("rst" in ln or "reset" in ln):
                readiness["reset_port"] = n

    facts["openroad_readiness"] = readiness

    # Readiness warnings/errors policy:
    # - PLATFORM required, but can come from .env
    if not readiness["platform"]:
        add_finding(
            errors, "ERROR", "OR-001",
            "No target PLATFORM specified (needed by OpenROAD-flow-scripts).",
            "Set PLATFORM in .env (e.g., sky130hd) or add manifest.platform."
        )

    # - clock port is *strongly* recommended; if missing, warn (you can upgrade to ERROR later)
    if not readiness["clock_port"]:
        add_finding(
            warnings, "WARNING", "OR-002",
            "Clock port not identified from manifest (ports.clock_reset).",
            "Add the clock under ports.clock_reset (dir=input, width=1) or add an explicit manifest.clock_port."
        )

    # - clock period not present: warn (or make ERROR if you require it now)
    if readiness["clock_period_ns"] is None:
        add_finding(
            warnings, "WARNING", "OR-003",
            "Clock period not provided (needed to generate SDC create_clock).",
            "Add manifest.clock_period_ns OR have backend policy default it (and record that default in the packager manifest)."
        )

    return _finalize_validation(errors, warnings, facts, manifest=manifest)


def _resolve_width(width: Any) -> Optional[int]:
    """
    Resolve a port width value to a positive integer.
    Accepts:
      - int:        e.g. 16
      - str int:    e.g. "16"
      - NxM string: e.g. "16x15" (unpacked array — total bits = N*M)
    Returns None if the value cannot be resolved to a positive integer.
    """
    if isinstance(width, int):
        return width if width > 0 else None
    if isinstance(width, str):
        width = width.strip()
        # NxM format (e.g. "16x15" for a [15:0] port unpacked over 16 entries)
        nx_match = re.match(r"^(\d+)[xX](\d+)$", width)
        if nx_match:
            total = int(nx_match.group(1)) * int(nx_match.group(2))
            return total if total > 0 else None
        # Plain integer string
        if width.isdigit():
            v = int(width)
            return v if v > 0 else None
    return None


def _finalize_validation(errors: List[Finding], warnings: List[Finding], facts: Dict[str, Any], manifest: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    status = status_from_findings(errors, warnings)
    return {
        "status": status,
        "errors": [asdict(e) for e in errors],
        "warnings": [asdict(w) for w in warnings],
        "facts": facts,
        "manifest": manifest,  # included for Claude context; omitted from saved JSON report by default
    }


# ----------------------------
# Claude call (Anthropic Messages API via urllib)
# ----------------------------

def call_claude_messages(api_key: str, model: str, system: str, user: str, max_tokens: int = 900) -> str:
    """
    Minimal Anthropic Messages API call. Uses urllib (no extra deps).
    NOTE: If your environment uses a proxy/gateway, adjust URL/headers accordingly.
    """
    url = "https://api.anthropic.com/v1/messages"
    payload = {
        "model": model,
        "max_tokens": max_tokens,
        "system": system,
        "messages": [{"role": "user", "content": user}],
    }

    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("Content-Type", "application/json")
    req.add_header("x-api-key", api_key)
    req.add_header("anthropic-version", "2023-06-01")

    with urllib.request.urlopen(req, timeout=60) as resp:
        raw = resp.read().decode("utf-8")

    obj = json.loads(raw)
    # Extract text blocks
    chunks: List[str] = []
    for block in obj.get("content", []):
        if block.get("type") == "text":
            chunks.append(block.get("text", ""))
    return "\n".join(chunks).strip()


def build_claude_prompts(validation: Dict[str, Any]) -> Tuple[str, str]:
    """
    Create Claude (system, user) prompts using deterministic findings as "trusted facts".
    Keeps the prompt bounded: includes full manifest, but only RTL header excerpt, not full RTL.
    """
    status = validation["status"]
    errors = validation.get("errors", [])
    warnings = validation.get("warnings", [])
    facts = validation.get("facts", {})
    manifest = validation.get("manifest") or {}

    rtl_header = facts.get("rtl_module_header_excerpt", "")

    system = (
        "You are an ASIC backend intake agent in a capstone project. "
        "Your job is to interpret deterministic validation results for a block bundle "
        "(RTL + frontend manifest) and produce a precise, actionable fix plan so the design "
        "can be packaged and run with OpenROAD-flow-scripts. "
        "Do NOT invent file contents. Only propose changes grounded in the provided data."
    )

    # Don’t dump secrets; env includes HAS_API_KEY only.
    user = f"""
Deterministic intake validation produced:

STATUS: {status}

FACTS (trusted):
{json.dumps(facts, indent=2)}

ERRORS (trusted):
{json.dumps(errors, indent=2)}

WARNINGS (trusted):
{json.dumps(warnings, indent=2)}

MANIFEST (trusted):
{json.dumps(manifest, indent=2)}

RTL MODULE HEADER EXCERPT (trusted):
{rtl_header}

Please output a markdown report with these sections:

1) Executive summary (2-4 bullets)
2) Blocking issues (if any): for each, explain WHY it blocks OpenROAD and the exact fix
3) Non-blocking warnings: impact + recommended fix
4) Suggested manifest changes (show minimal JSON snippets)
5) Suggested RTL changes (ONLY if necessary; show minimal diff-like snippets)
6) OpenROAD readiness checklist:
   - platform/PDK, clock port, clock period, ORFS_DIR sanity, and anything else inferred
   - state whether each is satisfied by manifest vs backend .env defaults

Keep it concise but highly actionable.
""".strip()

    return system, user


# ----------------------------
# Output helpers
# ----------------------------

def write_json(path: Path, obj: Any) -> None:
    path.write_text(json.dumps(obj, indent=2))


def write_text(path: Path, s: str) -> None:
    path.write_text(s if s.endswith("\n") else (s + "\n"), encoding="utf-8")


# ----------------------------
# Main
# ----------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle_dir", required=True, type=Path, help="Directory containing manifest JSON + referenced RTL")
    ap.add_argument("--out_dir", type=Path, default=None, help="Output directory (defaults to OUT_ROOT/intake/<bundle_name>/ if OUT_ROOT is set)")
    ap.add_argument("--env_file", type=Path, default=Path(".env"), help="Path to .env file (default: ./.env)")
    ap.add_argument("--max_tokens", type=int, default=900, help="Claude max_tokens for summary")
    args = ap.parse_args()

    # Load .env first
    load_env_file(args.env_file)

    # Resolve out_dir default
    if args.out_dir is None:
        out_root = (os.environ.get("OUT_ROOT") or "").strip()
        if out_root:
            args.out_dir = Path(out_root) / "intake" / args.bundle_dir.name
        else:
            args.out_dir = Path("./intake_out") / args.bundle_dir.name

    args.out_dir.mkdir(parents=True, exist_ok=True)

    # Deterministic validation
    validation = deterministic_validate(args.bundle_dir)

    # Save machine-readable report (omit full manifest to keep it lighter)
    report = {
        "status": validation["status"],
        "errors": validation["errors"],
        "warnings": validation["warnings"],
        "facts": validation["facts"],
    }
    write_json(args.out_dir / "intake_report.json", report)

    # Claude-generated summary
    api_key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    model = (os.environ.get("MODEL") or "claude-opus-4-6").strip()

    if not api_key:
        summary = textwrap.dedent(f"""\
        # Intake Summary (Claude skipped)

        Claude summary was skipped because `ANTHROPIC_API_KEY` is not set.

        **Deterministic status:** {validation["status"]}
        - Errors: {len(validation.get("errors", []))}
        - Warnings: {len(validation.get("warnings", []))}

        See `intake_report.json` for details.
        """)
        write_text(args.out_dir / "intake_summary.md", summary)
    else:
        system, user = build_claude_prompts(validation)
        try:
            summary_md = call_claude_messages(
                api_key=api_key,
                model=model,
                system=system,
                user=user,
                max_tokens=args.max_tokens,
            )
        except Exception as e:
            summary_md = textwrap.dedent(f"""\
            # Intake Summary (Claude call failed)

            Claude call failed with:
            `{e}`

            Falling back to deterministic findings.
            **Deterministic status:** {validation["status"]}

            See `intake_report.json` for details.
            """)
        write_text(args.out_dir / "intake_summary.md", summary_md)

    # Exit code
    if validation["status"] == "PASS":
        return 0
    if validation["status"] == "PASS_WITH_WARNINGS":
        return 1
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
