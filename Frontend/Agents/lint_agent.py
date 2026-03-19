#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                      LINT AGENT                                      ║
║                                                                      ║
║  Inter-phase port consistency checker                                ║
║  Runs between RTL generation phases as a gate.                       ║
║                                                                      ║
║  Input:  Directory of *_manifest.json files (from all agents)        ║
║  Output: lint_report.json + console pass/fail                        ║
║                                                                      ║
║  Checks performed:                                                   ║
║    L-001  Source→Sink width match (via source annotations)           ║
║    L-002  Source port exists in producer manifest                     ║
║    L-003  Parameter consistency (ROW_BITS, ADDR_WIDTH, etc.)         ║
║    L-004  Clock/reset port uniformity (clk, rst_n on every module)  ║
║    L-005  Dependency graph acyclicity                                ║
║    L-006  Dangling outputs (produced but never consumed)             ║
║    L-007  Missing dependencies (source module not in deps list)      ║
║    L-008  Phase ordering (consumer phase > producer phase)           ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json
import sys
import os
import glob
from pathlib import Path
from datetime import datetime
from collections import defaultdict


class LintAgent:

    def __init__(self, manifest_dir: str, output_dir: str = "./output"):
        self.manifest_dir = Path(manifest_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Load all manifests
        self.modules = {}
        pattern = str(self.manifest_dir / "*_manifest.json")
        for mf_path in sorted(glob.glob(pattern)):
            with open(mf_path) as f:
                m = json.load(f)
            self.modules[m["module_name"]] = m

        # Build port index: module_name -> {port_name: {width, dir, group}}
        self.port_index = {}
        for mod_name, mod in self.modules.items():
            ports = {}
            for grp_name, grp_ports in mod["ports"].items():
                for p in grp_ports:
                    ports[p["name"]] = {
                        "width": p["width"],
                        "dir": p["dir"],
                        "group": grp_name,
                        "source": p.get("source"),
                    }
            self.port_index[mod_name] = ports

        # Build source→sink connections
        self.connections = []  # list of (consumer_mod, consumer_port, producer_mod, producer_port)
        for mod_name, ports in self.port_index.items():
            for port_name, info in ports.items():
                if info["source"]:
                    # source format: "module_name.port_name"
                    parts = info["source"].split(".", 1)
                    if len(parts) == 2:
                        self.connections.append((mod_name, port_name, parts[0], parts[1]))

        self.errors = []
        self.warnings = []
        self.info = []

    # ──────────────────────────────────────────────────────
    # Individual checks
    # ──────────────────────────────────────────────────────

    def check_L001_width_match(self):
        """L-001: Source→Sink width match."""
        for consumer_mod, consumer_port, producer_mod, producer_port in self.connections:
            if producer_mod not in self.port_index:
                continue  # L-002 catches this

            producer_ports = self.port_index[producer_mod]
            if producer_port not in producer_ports:
                continue  # L-002 catches this

            consumer_w = self.port_index[consumer_mod][consumer_port]["width"]
            producer_w = producer_ports[producer_port]["width"]

            if consumer_w != producer_w:
                self.errors.append({
                    "check": "L-001",
                    "severity": "ERROR",
                    "message": f"Width mismatch: {consumer_mod}.{consumer_port} "
                               f"(w={consumer_w}) <- {producer_mod}.{producer_port} "
                               f"(w={producer_w})",
                })
            else:
                self.info.append(
                    f"L-001 OK: {consumer_mod}.{consumer_port} <- "
                    f"{producer_mod}.{producer_port} (w={consumer_w})"
                )

    def check_L002_source_exists(self):
        """L-002: Source port exists in producer manifest."""
        for consumer_mod, consumer_port, producer_mod, producer_port in self.connections:
            if producer_mod not in self.port_index:
                self.errors.append({
                    "check": "L-002",
                    "severity": "ERROR",
                    "message": f"{consumer_mod}.{consumer_port} references "
                               f"unknown module '{producer_mod}'",
                })
                continue

            if producer_port not in self.port_index[producer_mod]:
                self.errors.append({
                    "check": "L-002",
                    "severity": "ERROR",
                    "message": f"{consumer_mod}.{consumer_port} references "
                               f"unknown port '{producer_mod}.{producer_port}'",
                })

    def check_L003_parameter_consistency(self):
        """L-003: Key parameters consistent across all modules."""
        # Parameters that must be identical everywhere they appear
        global_params = ["ROW_BITS", "ADDR_WIDTH", "BANK_BITS", "COL_BITS",
                         "DATA_WIDTH", "SEL_WIDTH", "AUX_WIDTH", "DDR_ADDR_W",
                         "DDR_BANK_W"]

        param_values = defaultdict(dict)  # param_name -> {module: value}

        for mod_name, mod in self.modules.items():
            params = mod.get("parameters", {})
            for gp in global_params:
                if gp in params:
                    param_values[gp][mod_name] = params[gp]

        for param_name, mod_vals in param_values.items():
            values = set(mod_vals.values())
            if len(values) > 1:
                detail = ", ".join(f"{m}={v}" for m, v in mod_vals.items())
                self.errors.append({
                    "check": "L-003",
                    "severity": "ERROR",
                    "message": f"Parameter '{param_name}' inconsistent: {detail}",
                })
            else:
                mods = list(mod_vals.keys())
                val = list(values)[0]
                self.info.append(
                    f"L-003 OK: {param_name}={val} consistent across {mods}"
                )

    def check_L004_clock_reset(self):
        """L-004: Every sequential module must have clk and rst_n ports."""
        # addr_decoder is combinational — exclude
        combinational = {"addr_decoder"}

        for mod_name, ports in self.port_index.items():
            if mod_name in combinational:
                continue

            has_clk = "clk" in ports
            has_rst = "rst_n" in ports

            if not has_clk:
                self.errors.append({
                    "check": "L-004",
                    "severity": "ERROR",
                    "message": f"Module '{mod_name}' missing 'clk' port",
                })
            if not has_rst:
                self.errors.append({
                    "check": "L-004",
                    "severity": "ERROR",
                    "message": f"Module '{mod_name}' missing 'rst_n' port",
                })

            # Check width = 1 and direction = input
            if has_clk and ports["clk"]["width"] != 1:
                self.errors.append({
                    "check": "L-004",
                    "severity": "ERROR",
                    "message": f"{mod_name}.clk width={ports['clk']['width']}, expected 1",
                })
            if has_rst and ports["rst_n"]["width"] != 1:
                self.errors.append({
                    "check": "L-004",
                    "severity": "ERROR",
                    "message": f"{mod_name}.rst_n width={ports['rst_n']['width']}, expected 1",
                })

    def check_L005_dependency_acyclic(self):
        """L-005: Dependency graph has no cycles."""
        dep_graph = {}
        for mod_name, mod in self.modules.items():
            dep_graph[mod_name] = mod.get("dependencies", [])

        # Simple DFS cycle detection
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {m: WHITE for m in dep_graph}
        cycle_path = []

        def dfs(node):
            color[node] = GRAY
            for dep in dep_graph.get(node, []):
                if dep not in color:
                    continue  # external dependency
                if color[dep] == GRAY:
                    cycle_path.append(f"{node} -> {dep}")
                    return True
                if color[dep] == WHITE:
                    if dfs(dep):
                        cycle_path.append(f"{node} -> {dep}")
                        return True
            color[node] = BLACK
            return False

        has_cycle = False
        for mod in dep_graph:
            if color[mod] == WHITE:
                if dfs(mod):
                    has_cycle = True
                    break

        if has_cycle:
            self.errors.append({
                "check": "L-005",
                "severity": "ERROR",
                "message": f"Dependency cycle detected: {' -> '.join(reversed(cycle_path))}",
            })
        else:
            self.info.append("L-005 OK: No dependency cycles")

    def check_L006_dangling_outputs(self):
        """L-006: Outputs that are never referenced as a source."""
        # Build set of all consumed ports
        consumed = set()
        for _, _, producer_mod, producer_port in self.connections:
            consumed.add((producer_mod, producer_port))

        # Check every output port
        for mod_name, ports in self.port_index.items():
            for port_name, info in ports.items():
                if info["dir"] == "output" and port_name not in ("clk", "rst_n"):
                    if (mod_name, port_name) not in consumed:
                        self.warnings.append({
                            "check": "L-006",
                            "severity": "WARNING",
                            "message": f"Dangling output: {mod_name}.{port_name} "
                                       f"(w={info['width']}) — not consumed by any module",
                        })

    def check_L007_missing_dependencies(self):
        """L-007: Source annotations reference modules not in deps list."""
        for consumer_mod, consumer_port, producer_mod, producer_port in self.connections:
            mod = self.modules[consumer_mod]
            declared_deps = mod.get("dependencies", [])
            if producer_mod not in declared_deps:
                self.warnings.append({
                    "check": "L-007",
                    "severity": "WARNING",
                    "message": f"{consumer_mod} uses {producer_mod}.{producer_port} "
                               f"but '{producer_mod}' not in its dependencies list",
                })

    def check_L008_phase_ordering(self):
        """L-008: Consumer phase must be >= producer phase."""
        for consumer_mod, consumer_port, producer_mod, producer_port in self.connections:
            if producer_mod not in self.modules:
                continue
            consumer_phase = self.modules[consumer_mod].get("phase", 0)
            producer_phase = self.modules[producer_mod].get("phase", 0)
            if consumer_phase < producer_phase:
                self.errors.append({
                    "check": "L-008",
                    "severity": "ERROR",
                    "message": f"{consumer_mod} (phase {consumer_phase}) depends on "
                               f"{producer_mod} (phase {producer_phase}) — "
                               f"consumer must be >= producer phase",
                })

    # ──────────────────────────────────────────────────────
    # Run all checks
    # ──────────────────────────────────────────────────────

    def run(self) -> dict:
        hdr = "=" * 66
        print(f"{hdr}")
        print(f"  LINT AGENT — Port Consistency Checker")
        print(f"  Manifests: {self.manifest_dir}")
        print(f"  Modules:   {len(self.modules)}")
        print(f"{hdr}")

        if not self.modules:
            print("\n  ✗ No manifest files found!")
            return {"status": "error", "errors": ["No manifest files found"]}

        print(f"\n  Loaded modules:")
        for name, mod in sorted(self.modules.items()):
            phase = mod.get("phase", "?")
            deps = mod.get("dependencies", [])
            n_ports = sum(len(v) for v in mod["ports"].values())
            print(f"    Phase {phase}  {name:20s}  {n_ports:2d} ports  deps={deps}")

        print(f"\n  Found {len(self.connections)} source→sink connections\n")

        # Run all checks
        checks = [
            ("L-001", "Width match",             self.check_L001_width_match),
            ("L-002", "Source exists",            self.check_L002_source_exists),
            ("L-003", "Parameter consistency",    self.check_L003_parameter_consistency),
            ("L-004", "Clock/reset uniformity",   self.check_L004_clock_reset),
            ("L-005", "Dependency acyclicity",    self.check_L005_dependency_acyclic),
            ("L-006", "Dangling outputs",         self.check_L006_dangling_outputs),
            ("L-007", "Missing dependencies",     self.check_L007_missing_dependencies),
            ("L-008", "Phase ordering",           self.check_L008_phase_ordering),
        ]

        for check_id, check_name, check_fn in checks:
            print(f"  Running {check_id}: {check_name} …")
            check_fn()

        # Report
        print(f"\n{'─' * 66}")
        print(f"  RESULTS")
        print(f"{'─' * 66}")

        n_err = len(self.errors)
        n_warn = len(self.warnings)
        n_info = len(self.info)

        if self.errors:
            print(f"\n  ✗ ERRORS ({n_err}):")
            for e in self.errors:
                print(f"    [{e['check']}] {e['message']}")

        if self.warnings:
            print(f"\n  ⚠ WARNINGS ({n_warn}):")
            for w in self.warnings:
                print(f"    [{w['check']}] {w['message']}")

        if self.info:
            print(f"\n  ✓ PASSED ({n_info}):")
            for i in self.info:
                print(f"    {i}")

        # Summary
        status = "PASS" if n_err == 0 else "FAIL"
        print(f"\n{'─' * 66}")
        print(f"  {status}  |  {n_err} errors  |  {n_warn} warnings  |  {n_info} passed")
        print(f"{'─' * 66}")

        # Write report
        report = {
            "timestamp": datetime.now().isoformat(),
            "manifest_dir": str(self.manifest_dir),
            "modules_checked": list(self.modules.keys()),
            "connections_checked": len(self.connections),
            "status": status,
            "errors": self.errors,
            "warnings": self.warnings,
            "info": self.info,
            "summary": {
                "errors": n_err,
                "warnings": n_warn,
                "passed": n_info,
            },
        }

        report_path = self.output_dir / "lint_report.json"
        report_path.write_text(json.dumps(report, indent=2))
        print(f"\n  Report: {report_path}")

        return report


# ─── Interactive entry point ───
if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║         LINT AGENT — Port Checker            ║")
    print("╚══════════════════════════════════════════════╝")
    print()

    manifest_dir = input("Enter directory containing *_manifest.json files: ").strip()

    if not manifest_dir:
        print("Error: No path provided.")
        sys.exit(1)

    if not os.path.isdir(manifest_dir):
        print(f"Error: Not a directory: {manifest_dir}")
        sys.exit(1)

    output_dir = input("Output directory for lint_report.json (Enter for same dir): ").strip()
    if not output_dir:
        output_dir = manifest_dir

    print()
    agent = LintAgent(manifest_dir, output_dir)
    result = agent.run()
    sys.exit(0 if result["status"] == "PASS" else 1)
