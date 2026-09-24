#!/usr/bin/env python3
"""
Verilator Lint Script -- real static analysis (deterministic, no LLM)
========================================================================
Runs `verilator --lint-only` against generated RTL, one module at a time.

Verilator isn't installed locally or on Olympus's head node -- it's only
on the Slurm compute nodes (confirmed: `which verilator` -> nothing on the
head node, `/usr/bin/verilator` via `srun`). So this reuses the same
SSH/Slurm transport as simulator.py rather than shelling out locally.

Per-module, not combined: a syntax error in one module should point at
that module immediately, not surface as an error somewhere in an 11-module
combined lint pass that has to be bisected by hand.

Policy: Verilator errors (%Error) fail the gate. Warnings (%Warning-*) are
reported but don't block -- same "informational, not blocking" treatment
the sim gate already gives SVA assertion failures.
"""

import os
import re
import tempfile
from pathlib import Path
from datetime import datetime

from simulator import XceliumSimulator

# The Verilator on Olympus (4.028, 2020) doesn't honor `synopsys/synthesis
# translate_off` pragmas the way Xcelium does, and doesn't support
# SystemVerilog `covergroup`/`coverpoint` at all (a long-standing Verilator
# limitation, not a flag). Both constructs are explicitly marked
# simulation-only via that exact pragma in every generator's output, so we
# enforce it ourselves before linting -- Verilator should check the
# synthesizable design, not fail on code the pragma already says to skip.
_TRANSLATE_OFF_RE = re.compile(
    r"//\s*(?:synopsys|synthesis)\s+translate_off.*?//\s*(?:synopsys|synthesis)\s+translate_on",
    re.DOTALL,
)


def _strip_sim_only_blocks(rtl_text: str) -> str:
    return _TRANSLATE_OFF_RE.sub("", rtl_text)


_EXIT_SUMMARY_RE = re.compile(r"^%Error:\s*Exiting due to \d+ (error|warning)\(s\)")


def _parse_verilator_output(stdout: str) -> dict:
    # Verilator's own default: by design, ANY warning (not just a real
    # %Error) makes it exit non-zero and print "%Error: Exiting due to N
    # warning(s)". That summary line isn't a distinct finding -- the real
    # findings are the specific %Error:/%Warning-* lines above it -- so it's
    # excluded here rather than double-counted as its own error.
    errors, warnings = [], []
    for line in stdout.split("\n"):
        stripped = line.strip()
        if _EXIT_SUMMARY_RE.match(stripped):
            continue
        if stripped.startswith("%Error"):
            errors.append(stripped)
        elif stripped.startswith("%Warning"):
            warnings.append(stripped)
    return {"errors": errors, "warnings": warnings}


class VerilatorLint:

    def __init__(self, ssh_config: dict):
        self.ssh_config = ssh_config

    def run(self, rtl_dir: str, modules: list) -> dict:
        rtl_dir = Path(rtl_dir)
        sim = XceliumSimulator(ssh_config=self.ssh_config)
        results = {}
        all_clean = True

        try:
            sim.connect()
        except Exception as e:
            return {"status": "SKIPPED", "reason": f"SSH failed: {e}", "modules": {}}

        try:
            for mod in modules:
                sv_path = rtl_dir / f"{mod}.sv"
                if not sv_path.exists():
                    results[mod] = {"status": "SKIPPED", "reason": "file missing"}
                    all_clean = False
                    continue

                # Written into a fresh temp dir under the module's real
                # filename (not a random tmp name) so Verilator's own
                # DECLFILENAME check (filename must match module name)
                # doesn't fire spuriously on our wrapper's plumbing.
                stripped_text = _strip_sim_only_blocks(sv_path.read_text())
                tmp_dir = tempfile.mkdtemp()
                tmp_path = os.path.join(tmp_dir, f"{mod}.sv")
                Path(tmp_path).write_text(stripped_text)
                sim.upload_files([tmp_path])
                cmd = f"cd {sim.work_dir} && verilator --lint-only -Wall -sv {mod}.sv 2>&1"
                result = sim.srun(cmd, timeout=60)
                os.remove(tmp_path)
                os.rmdir(tmp_dir)
                stdout = result["stdout"]
                parsed = _parse_verilator_output(stdout)

                clean = len(parsed["errors"]) == 0
                if not clean:
                    all_clean = False

                results[mod] = {
                    "status": "PASS" if clean else "FAIL",
                    "errors": parsed["errors"],
                    "warnings": parsed["warnings"],
                    "raw_output": stdout,
                }
        finally:
            sim.disconnect()

        return {
            "status": "PASS" if all_clean else "FAIL",
            "modules": results,
            "timestamp": datetime.now().isoformat(),
        }


if __name__ == "__main__":
    import sys
    import json

    rtl_dir = input("RTL directory: ").strip()
    modules = input("Module names (comma-separated): ").strip().split(",")
    modules = [m.strip() for m in modules if m.strip()]

    cfg = {
        "hostname": os.environ.get("OLYMPUS_HOST", "olympus.ece.tamu.edu"),
        "port": 22,
        "username": os.environ.get("OLYMPUS_USER", ""),
        "key_path": os.environ.get("OLYMPUS_KEY", None),
    }

    result = VerilatorLint(cfg).run(rtl_dir, modules)
    print(json.dumps({k: v for k, v in result.items() if k != "modules"}, indent=2))
    for mod, r in result["modules"].items():
        sym = "OK" if r["status"] == "PASS" else "FAIL"
        print(f"  {sym} {mod}: {len(r.get('errors', []))} errors, {len(r.get('warnings', []))} warnings")
    sys.exit(0 if result["status"] == "PASS" else 1)
