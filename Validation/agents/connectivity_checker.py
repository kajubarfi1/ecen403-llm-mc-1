"""
Connectivity Checker Agent
============================
Static pre-flight verification that all inter-block connections defined in
path_definitions.json actually exist in the frontend-generated RTL manifests.

Checks performed per connection:
  1. Source manifest exists and contains the source port
  2. Sink manifest exists and contains the sink port
  3. Port widths match between source and sink (and match path_definitions)
  4. Port directions are correct (source is output, sink is input)

Checks performed per path:
  5. All blocks in the path have manifests available
  6. All connections_used in the path pass checks 1-4
  7. Entry/exit boundary ports exist on the first/last block
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple


# =============================================================================
# Manifest Discovery
# =============================================================================

# Map block IDs (from path_definitions.json) to the manifest filename pattern
# the frontend generates. The frontend names manifests as {block}_manifest.json.
BLOCK_TO_MANIFEST = {
    "wb_port":      "wb_port_manifest.json",
    "addr_decoder": "addr_decoder_manifest.json",
    "cmd_queue":    "cmd_queue_manifest.json",
    "bank_tracker": "bank_tracker_manifest.json",
    "scheduler":    "scheduler_manifest.json",
    "refresh_ctrl": "refresh_ctrl_manifest.json",
    "cmd_gen":      "cmd_gen_manifest.json",
    "data_path":    "data_path_manifest.json",
    "init_fsm":     "init_fsm_manifest.json",
    "config_regs":  "config_regs_manifest.json",
    "calibration":  "calibration_manifest.json",
}

# Map block IDs to their RTL filenames (for fallback parsing)
BLOCK_TO_RTL = {
    "wb_port":      "wb_port.sv",
    "addr_decoder": "addr_decoder.sv",
    "cmd_queue":    "cmd_queue.sv",
    "bank_tracker": "bank_tracker.sv",
    "scheduler":    "scheduler.sv",
    "refresh_ctrl": "refresh_ctrl.sv",
    "cmd_gen":      "cmd_gen.sv",
    "data_path":    "data_path.sv",
    "init_fsm":     "init_fsm.sv",
    "config_regs":  "config_regs.sv",
    "calibration":  "calibration.sv",
}


def discover_manifests(frontend_root: str) -> Dict[str, str]:
    """
    Walk the frontend output directory tree to find all manifest JSON files.
    Returns a map of { block_id: absolute_path_to_manifest }.
    
    Searches across Phase1Output, Phase2Output, Phase3Output, etc.
    """
    found = {}
    
    # Build a reverse lookup: filename -> block_id
    filename_to_block = {v: k for k, v in BLOCK_TO_MANIFEST.items()}
    
    for dirpath, dirnames, filenames in os.walk(frontend_root):
        for fname in filenames:
            if fname in filename_to_block:
                block_id = filename_to_block[fname]
                if block_id not in found:  # first match wins (earlier phase)
                    found[block_id] = os.path.join(dirpath, fname)
    
    return found


def discover_rtl_files(frontend_root: str) -> Dict[str, str]:
    """
    Walk the frontend output directory tree to find all RTL (.sv) files.
    Returns a map of { block_id: absolute_path_to_sv }.
    Used as fallback when manifests are missing.
    """
    found = {}
    filename_to_block = {v: k for k, v in BLOCK_TO_RTL.items()}
    
    for dirpath, dirnames, filenames in os.walk(frontend_root):
        for fname in filenames:
            # Skip testbench files
            if fname.endswith("_tb.sv"):
                continue
            if fname in filename_to_block:
                block_id = filename_to_block[fname]
                if block_id not in found:
                    found[block_id] = os.path.join(dirpath, fname)
    
    return found


# =============================================================================
# Manifest Parsing
# =============================================================================

def load_manifest(path: str) -> dict:
    """Load a frontend manifest JSON file."""
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def extract_ports_from_manifest(manifest: dict) -> Dict[str, dict]:
    """
    Extract a flat port map from a manifest.
    
    Returns: { port_name: { "width": int, "dir": "input"|"output", "group": str } }
    """
    ports = {}
    for group_name, port_list in manifest.get("ports", {}).items():
        for p in port_list:
            ports[p["name"]] = {
                "width": p["width"],
                "dir": p["dir"],
                "group": group_name,
            }
    return ports


# =============================================================================
# RTL Fallback Parsing (when manifest is missing)
# =============================================================================

def parse_rtl_ports(rtl_path: str) -> Dict[str, dict]:
    """
    Best-effort parse of SystemVerilog module port declarations.
    
    Handles patterns like:
        input  wire [31:0] wb_dat_i,
        output logic       wb_ack_o,
        input              clk,
    
    Returns: { port_name: { "width": int, "dir": "input"|"output", "group": "rtl_parsed" } }
    """
    with open(rtl_path, "r", encoding="utf-8") as f:
        content = f.read()
    
    ports = {}
    
    # Find the module port declaration block (between first '(' and matching ')')
    # Then parse individual port lines
    port_pattern = re.compile(
        r'(input|output|inout)\s+'
        r'(?:wire|logic|reg)?\s*'
        r'(?:\[(\d+):(\d+)\])?\s*'
        r'(\w+)',
        re.MULTILINE
    )
    
    for match in port_pattern.finditer(content):
        direction = match.group(1)
        msb = match.group(2)
        lsb = match.group(3)
        name = match.group(4)
        
        if msb is not None and lsb is not None:
            width = abs(int(msb) - int(lsb)) + 1
        else:
            width = 1
        
        # Normalize inout → output for checking purposes
        if direction == "inout":
            direction = "output"
        
        ports[name] = {
            "width": width,
            "dir": direction,
            "group": "rtl_parsed",
        }
    
    return ports


# =============================================================================
# Connection Checking Logic
# =============================================================================

class CheckResult:
    """Result of a single check."""
    
    def __init__(self, check_id: str, target: str, status: str,
                 message: str, details: Optional[dict] = None):
        self.check_id = check_id
        self.target = target          # connection ID or path ID
        self.status = status          # "pass" | "fail" | "warn" | "skip"
        self.message = message
        self.details = details or {}
    
    def to_dict(self) -> dict:
        return {
            "check_id": self.check_id,
            "target": self.target,
            "status": self.status,
            "message": self.message,
            "details": self.details,
        }


def check_connection(
    conn: dict,
    block_ports: Dict[str, Dict[str, dict]],
    path_defs_blocks: dict,
) -> List[CheckResult]:
    """
    Verify a single direct_connection from path_definitions.json.
    
    Args:
        conn: A connection dict from path_definitions.json
        block_ports: { block_id: { port_name: {width, dir, group} } }
        path_defs_blocks: The "blocks" dict from path_definitions for fallback info
    
    Returns: List of CheckResults for this connection.
    """
    results = []
    conn_id = conn["id"]
    src_block = conn["from"]
    dst_block = conn["to"]
    
    # Check 1: Source block ports available
    if src_block not in block_ports:
        results.append(CheckResult(
            f"{conn_id}_src_avail", conn_id, "skip",
            f"Source block '{src_block}' has no manifest or RTL available. Cannot verify.",
            {"block": src_block}
        ))
        return results
    
    # Check 2: Sink block ports available
    if dst_block not in block_ports:
        results.append(CheckResult(
            f"{conn_id}_dst_avail", conn_id, "skip",
            f"Sink block '{dst_block}' has no manifest or RTL available. Cannot verify.",
            {"block": dst_block}
        ))
        return results
    
    src_ports = block_ports[src_block]
    dst_ports = block_ports[dst_block]
    
    # Check each signal in the connection
    for sig in conn.get("signals", []):
        src_name = sig["source_port"]
        dst_name = sig["sink_port"]
        expected_width = sig["width"]
        sig_label = f"{src_block}.{src_name} → {dst_block}.{dst_name}"
        
        # --- Source port exists? ---
        if src_name not in src_ports:
            results.append(CheckResult(
                f"{conn_id}_{src_name}_src_exists", conn_id, "fail",
                f"Source port '{src_name}' not found in {src_block} manifest.",
                {"signal": sig_label, "available_ports": sorted(src_ports.keys())}
            ))
            continue
        
        # --- Sink port exists? ---
        # Handle indexed ports like "error_flags[2]" — strip the index
        dst_name_base = re.sub(r'\[\d+\]$', '', dst_name)
        if dst_name_base not in dst_ports:
            results.append(CheckResult(
                f"{conn_id}_{dst_name}_dst_exists", conn_id, "fail",
                f"Sink port '{dst_name}' not found in {dst_block} manifest.",
                {"signal": sig_label, "available_ports": sorted(dst_ports.keys())}
            ))
            continue
        
        src_info = src_ports[src_name]
        dst_info = dst_ports[dst_name_base]
        
        # --- Source direction check (should be output) ---
        if src_info["dir"] not in ("output", "inout"):
            results.append(CheckResult(
                f"{conn_id}_{src_name}_src_dir", conn_id, "fail",
                f"Source port '{src_block}.{src_name}' is '{src_info['dir']}', expected 'output'.",
                {"signal": sig_label, "actual_dir": src_info["dir"]}
            ))
        
        # --- Sink direction check (should be input) ---
        if dst_info["dir"] not in ("input", "inout"):
            results.append(CheckResult(
                f"{conn_id}_{dst_name}_dst_dir", conn_id, "fail",
                f"Sink port '{dst_block}.{dst_name}' is '{dst_info['dir']}', expected 'input'.",
                {"signal": sig_label, "actual_dir": dst_info["dir"]}
            ))
        
        # --- Width match between source and sink ---
        if isinstance(expected_width, int):
            if isinstance(src_info["width"], int) and src_info["width"] != expected_width:
                results.append(CheckResult(
                    f"{conn_id}_{src_name}_src_width", conn_id, "fail",
                    f"Source port '{src_block}.{src_name}' width mismatch: "
                    f"manifest={src_info['width']}, path_defs={expected_width}.",
                    {"signal": sig_label, "manifest_width": src_info["width"],
                     "expected_width": expected_width}
                ))
            
            if isinstance(dst_info["width"], int) and dst_info["width"] != expected_width:
                # Allow sink to be wider (e.g., error_flags is 3 bits, connection is 1 bit slice)
                if "[" in dst_name:
                    pass  # Indexed — width mismatch expected
                else:
                    results.append(CheckResult(
                        f"{conn_id}_{dst_name}_dst_width", conn_id, "fail",
                        f"Sink port '{dst_block}.{dst_name}' width mismatch: "
                        f"manifest={dst_info['width']}, path_defs={expected_width}.",
                        {"signal": sig_label, "manifest_width": dst_info["width"],
                         "expected_width": expected_width}
                    ))
        else:
            # Non-integer width (like "timing_t", "16×entry_t") — can only check existence
            results.append(CheckResult(
                f"{conn_id}_{src_name}_struct", conn_id, "warn",
                f"Signal '{sig_label}' has structured width '{expected_width}' — "
                f"existence verified, width check skipped.",
                {"signal": sig_label, "structured_width": str(expected_width)}
            ))
            continue
        
        # --- All checks passed for this signal ---
        if not any(r.check_id.startswith(f"{conn_id}_{src_name}") and r.status == "fail"
                   for r in results):
            if not any(r.check_id.startswith(f"{conn_id}_{dst_name}") and r.status == "fail"
                       for r in results):
                results.append(CheckResult(
                    f"{conn_id}_{src_name}_ok", conn_id, "pass",
                    f"Signal '{sig_label}' verified: width={expected_width}, directions correct.",
                    {"signal": sig_label, "width": expected_width}
                ))
    
    return results


def check_path(
    path: dict,
    connection_results: Dict[str, str],
    block_ports: Dict[str, Dict[str, dict]],
) -> List[CheckResult]:
    """
    Verify a multi-hop path from path_definitions.json.
    
    Args:
        path: A path dict from path_definitions.json
        connection_results: { conn_id: "pass"|"fail"|"warn"|"skip" } aggregate per connection
        block_ports: { block_id: { port_name: {...} } }
    
    Returns: List of CheckResults for this path.
    """
    results = []
    path_id = path["id"]
    
    # Check: All blocks in path have port data available
    missing_blocks = [b for b in path["blocks"] if b not in block_ports]
    if missing_blocks:
        results.append(CheckResult(
            f"{path_id}_blocks", path_id, "warn",
            f"Path '{path_id}' has {len(missing_blocks)} blocks without manifests: {missing_blocks}.",
            {"missing_blocks": missing_blocks}
        ))
    
    # Check: All connections_used have passed
    failed_conns = []
    skipped_conns = []
    for conn_id in path.get("connections_used", []):
        status = connection_results.get(conn_id, "skip")
        if status == "fail":
            failed_conns.append(conn_id)
        elif status == "skip":
            skipped_conns.append(conn_id)
    
    if failed_conns:
        results.append(CheckResult(
            f"{path_id}_conns", path_id, "fail",
            f"Path '{path_id}' has {len(failed_conns)} failing connections: {failed_conns}.",
            {"failed_connections": failed_conns}
        ))
    elif skipped_conns:
        results.append(CheckResult(
            f"{path_id}_conns", path_id, "warn",
            f"Path '{path_id}' has {len(skipped_conns)} unverifiable connections (missing manifests): {skipped_conns}.",
            {"skipped_connections": skipped_conns}
        ))
    else:
        results.append(CheckResult(
            f"{path_id}_conns", path_id, "pass",
            f"Path '{path_id}': all {len(path.get('connections_used', []))} connections verified.",
        ))
    
    # Check: Entry boundary ports exist on the first block
    entry = path.get("entry_boundary", {})
    if entry.get("type") == "external" or entry.get("type") == "ddr":
        first_block = path["blocks"][0]
        if first_block in block_ports:
            for sig_name in entry.get("signals", []):
                if sig_name not in block_ports[first_block]:
                    results.append(CheckResult(
                        f"{path_id}_entry_{sig_name}", path_id, "fail",
                        f"Entry boundary signal '{sig_name}' not found on block '{first_block}'.",
                        {"block": first_block, "signal": sig_name}
                    ))
    
    # Check: Exit boundary ports exist on the last block
    exit_b = path.get("exit_boundary", {})
    if exit_b.get("type") == "external" or exit_b.get("type") == "ddr":
        last_block = path["blocks"][-1]
        if last_block in block_ports:
            for sig_name in exit_b.get("signals", []):
                if sig_name not in block_ports[last_block]:
                    results.append(CheckResult(
                        f"{path_id}_exit_{sig_name}", path_id, "fail",
                        f"Exit boundary signal '{sig_name}' not found on block '{last_block}'.",
                        {"block": last_block, "signal": sig_name}
                    ))
    
    return results


# =============================================================================
# Main Checker Class
# =============================================================================

class ConnectivityChecker:
    """
    Static connectivity verifier for the DDR3 memory controller.
    
    Reads path_definitions.json and frontend manifests, cross-references
    all connections and paths, and produces a structured report.
    """
    
    def __init__(
        self,
        path_defs_path: str,
        frontend_root: str,
        output_dir: str = ".",
        spec_path: Optional[str] = None,
    ):
        self.path_defs_path = path_defs_path
        self.frontend_root = os.path.abspath(frontend_root)
        self.output_dir = output_dir
        self.spec_path = spec_path
    
    def run(self) -> dict:
        """
        Execute all connectivity checks.
        
        Returns a report dict with structure:
        {
            "status": "pass" | "fail" | "warn",
            "timestamp": "...",
            "summary": { "total_checks": N, "pass": N, "fail": N, "warn": N, "skip": N },
            "manifests_found": { block_id: path, ... },
            "manifests_missing": [ block_id, ... ],
            "connection_results": [ { check_id, target, status, message, details }, ... ],
            "path_results": [ ... ],
            "connection_summary": { conn_id: "pass"|"fail"|"warn"|"skip", ... },
            "path_summary": { path_id: "pass"|"fail"|"warn", ... },
        }
        """
        print("[ConnectivityChecker] Starting static connectivity verification...")
        
        # Load path definitions
        with open(self.path_defs_path, "r", encoding="utf-8") as f:
            path_defs = json.load(f)
        
        print(f"[ConnectivityChecker] Loaded path_definitions: "
              f"{len(path_defs['direct_connections'])} connections, "
              f"{len(path_defs['paths'])} paths")
        
        # Discover manifests across all frontend phases
        manifest_paths = discover_manifests(self.frontend_root)
        rtl_paths = discover_rtl_files(self.frontend_root)
        
        all_block_ids = list(path_defs["blocks"].keys())
        found_blocks = list(manifest_paths.keys())
        missing_blocks = [b for b in all_block_ids if b not in manifest_paths]
        
        print(f"[ConnectivityChecker] Manifests found: {len(found_blocks)}/{len(all_block_ids)}")
        for block_id, mpath in sorted(manifest_paths.items()):
            # Show relative path for readability
            rel = os.path.relpath(mpath, self.frontend_root)
            print(f"  {block_id:16s} → {rel}")
        
        if missing_blocks:
            # Try RTL fallback for missing manifests
            rtl_fallbacks = []
            for block_id in missing_blocks:
                if block_id in rtl_paths:
                    rtl_fallbacks.append(block_id)
            
            still_missing = [b for b in missing_blocks if b not in rtl_paths]
            
            if rtl_fallbacks:
                print(f"[ConnectivityChecker] RTL fallback for: {rtl_fallbacks}")
            if still_missing:
                print(f"[ConnectivityChecker] WARNING: No manifest or RTL for: {still_missing}")
        
        # Load port data from manifests (primary) and RTL (fallback)
        block_ports: Dict[str, Dict[str, dict]] = {}
        port_sources: Dict[str, str] = {}  # block_id → "manifest" | "rtl_parsed"
        
        for block_id in all_block_ids:
            if block_id in manifest_paths:
                try:
                    manifest = load_manifest(manifest_paths[block_id])
                    block_ports[block_id] = extract_ports_from_manifest(manifest)
                    port_sources[block_id] = "manifest"
                except Exception as e:
                    print(f"[ConnectivityChecker] WARNING: Failed to load manifest "
                          f"for {block_id}: {e}")
            
            if block_id not in block_ports and block_id in rtl_paths:
                try:
                    block_ports[block_id] = parse_rtl_ports(rtl_paths[block_id])
                    port_sources[block_id] = "rtl_parsed"
                    print(f"[ConnectivityChecker] Parsed RTL for '{block_id}': "
                          f"{len(block_ports[block_id])} ports")
                except Exception as e:
                    print(f"[ConnectivityChecker] WARNING: Failed to parse RTL "
                          f"for {block_id}: {e}")
        
        print(f"[ConnectivityChecker] Port data loaded for "
              f"{len(block_ports)}/{len(all_block_ids)} blocks")
        
        # Run connection checks
        all_conn_results: List[CheckResult] = []
        for conn in path_defs["direct_connections"]:
            results = check_connection(conn, block_ports, path_defs["blocks"])
            all_conn_results.extend(results)
        
        # Aggregate connection-level status
        conn_summary: Dict[str, str] = {}
        for conn in path_defs["direct_connections"]:
            conn_id = conn["id"]
            conn_checks = [r for r in all_conn_results if r.target == conn_id]
            if any(r.status == "fail" for r in conn_checks):
                conn_summary[conn_id] = "fail"
            elif any(r.status == "skip" for r in conn_checks):
                conn_summary[conn_id] = "skip"
            elif any(r.status == "warn" for r in conn_checks):
                conn_summary[conn_id] = "warn"
            elif conn_checks:
                conn_summary[conn_id] = "pass"
            else:
                conn_summary[conn_id] = "skip"
        
        # Run path checks
        all_path_results: List[CheckResult] = []
        for path in path_defs["paths"]:
            results = check_path(path, conn_summary, block_ports)
            all_path_results.extend(results)
        
        # Aggregate path-level status
        path_summary: Dict[str, str] = {}
        for path in path_defs["paths"]:
            path_id = path["id"]
            path_checks = [r for r in all_path_results if r.target == path_id]
            if any(r.status == "fail" for r in path_checks):
                path_summary[path_id] = "fail"
            elif any(r.status == "warn" for r in path_checks):
                path_summary[path_id] = "warn"
            elif path_checks:
                path_summary[path_id] = "pass"
            else:
                path_summary[path_id] = "skip"
        
        # Overall summary
        all_results = all_conn_results + all_path_results
        summary = {
            "total_checks": len(all_results),
            "pass": sum(1 for r in all_results if r.status == "pass"),
            "fail": sum(1 for r in all_results if r.status == "fail"),
            "warn": sum(1 for r in all_results if r.status == "warn"),
            "skip": sum(1 for r in all_results if r.status == "skip"),
        }
        
        if summary["fail"] > 0:
            overall_status = "fail"
        elif summary["warn"] > 0:
            overall_status = "warn"
        else:
            overall_status = "pass"
        
        # Print summary
        self._print_summary(conn_summary, path_summary, summary, overall_status,
                            port_sources, missing_blocks)
        
        # Build report
        report = {
            "status": overall_status,
            "timestamp": datetime.now().isoformat(),
            "frontend_root": self.frontend_root,
            "path_defs_path": self.path_defs_path,
            "summary": summary,
            "manifests_found": {
                bid: os.path.relpath(p, self.frontend_root)
                for bid, p in manifest_paths.items()
            },
            "manifests_missing": [b for b in all_block_ids if b not in manifest_paths],
            "rtl_fallbacks": [b for b in all_block_ids
                              if port_sources.get(b) == "rtl_parsed"],
            "port_sources": port_sources,
            "connection_summary": conn_summary,
            "path_summary": path_summary,
            "connection_results": [r.to_dict() for r in all_conn_results],
            "path_results": [r.to_dict() for r in all_path_results],
        }
        
        # Save report
        if self.output_dir:
            os.makedirs(self.output_dir, exist_ok=True)
            report_path = os.path.join(self.output_dir, "connectivity_report.json")
            with open(report_path, "w", encoding="utf-8") as f:
                json.dump(report, f, indent=2)
            print(f"\n[ConnectivityChecker] Report saved: {report_path}")
        
        return report
    
    def _print_summary(
        self,
        conn_summary: Dict[str, str],
        path_summary: Dict[str, str],
        summary: dict,
        overall_status: str,
        port_sources: Dict[str, str],
        missing_blocks: List[str],
    ):
        """Print a formatted summary to console."""
        STATUS_ICONS = {"pass": "✓", "fail": "✗", "warn": "⚠", "skip": "–"}
        
        print()
        print("=" * 70)
        print("  CONNECTIVITY CHECK RESULTS")
        print("=" * 70)
        
        # Connection results
        print("\n  Direct Connections:")
        for conn_id, status in sorted(conn_summary.items()):
            icon = STATUS_ICONS.get(status, "?")
            print(f"    [{icon}] {conn_id:16s}  {status}")
        
        # Path results
        print("\n  Paths:")
        for path_id, status in sorted(path_summary.items()):
            icon = STATUS_ICONS.get(status, "?")
            print(f"    [{icon}] {path_id:40s}  {status}")
        
        # Totals
        print(f"\n  Summary:")
        print(f"    Total checks:  {summary['total_checks']}")
        print(f"    Passed:        {summary['pass']}")
        print(f"    Failed:        {summary['fail']}")
        print(f"    Warnings:      {summary['warn']}")
        print(f"    Skipped:       {summary['skip']}")
        
        conn_pass = sum(1 for s in conn_summary.values() if s == "pass")
        conn_total = len(conn_summary)
        path_pass = sum(1 for s in path_summary.values() if s == "pass")
        path_total = len(path_summary)
        
        print(f"\n    Connections:    {conn_pass}/{conn_total} fully verified")
        print(f"    Paths:         {path_pass}/{path_total} fully verified")
        
        if missing_blocks:
            print(f"\n    Missing data:  {missing_blocks}")
        
        print(f"\n  Overall: {overall_status.upper()}")
        print("=" * 70)


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="DDR3 Memory Controller — Static Connectivity Checker",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic check
  python3 connectivity_checker.py \\
      --path-defs ./path_definitions.json \\
      --frontend-root ~/Capstone/ecen403-llm-mc-1/Frontend/OutputFolders

  # With explicit output directory
  python3 connectivity_checker.py \\
      --path-defs ./path_definitions.json \\
      --frontend-root ~/Capstone/ecen403-llm-mc-1/Frontend/OutputFolders \\
      --output-dir ./reports
        """
    )
    
    parser.add_argument("--path-defs", required=True,
                        help="Path to path_definitions.json")
    parser.add_argument("--frontend-root", required=True,
                        help="Path to Frontend/OutputFolders directory")
    parser.add_argument("--output-dir", default=".",
                        help="Directory for connectivity_report.json (default: cwd)")
    
    args = parser.parse_args()
    
    checker = ConnectivityChecker(
        path_defs_path=args.path_defs,
        frontend_root=args.frontend_root,
        output_dir=args.output_dir,
    )
    
    report = checker.run()
    
    # Exit code: 0 for pass/warn, 1 for fail
    if report["status"] == "fail":
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()