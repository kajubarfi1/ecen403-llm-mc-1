#!/usr/bin/env python3
"""
dummy_validation_agent.py -- STUB pipeline stage, spec synthesis -> Phase 1.

full_pipeline.py calls this right after microarch_cli.py/microarch_compiler.py
produce a spec and before that spec is handed to Phase 1. It is explicitly a
placeholder: Jacob's Validation subsystem will eventually own this stage (a
real JEDEC/architectural review of the synthesized spec, in the same spirit
as Validation/structural/integration_map_gen.py's checks on the RTL side).
Until that hookup exists, validate_spec() below does one honest, if shallow,
check of its own -- confirms the spec actually has every top-level section
Spec/llmmc_microarchitecture.schema.json requires -- and surfaces (rather
than re-derives) microarch_compiler.compile_spec()'s own 27 consistency
checks if that result is passed in. It deliberately does NOT re-run JEDEC
timing derivation or cross-block architectural checks; compile_spec() already
did the real work, and duplicating it here would just be two places that can
disagree.

Contract to preserve when this is replaced: validate_spec(spec, compile_result=None)
-> {"status": "PASS"|"FAIL", "findings": [str, ...], "validator": str}.
full_pipeline.py only depends on that shape.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

SPEC_ROOT = Path(__file__).resolve().parents[3] / "Spec"
SCHEMA_PATH = SPEC_ROOT / "llmmc_microarchitecture.schema.json"

# Fallback if the schema file can't be read for some reason -- kept in sync
# with its top-level `required` list as of the 2026-09-24 drop.
_FALLBACK_REQUIRED_SECTIONS = [
    "memory_geometry", "clocking_model", "timing_model",
    "controller_architecture", "initialization_sequence", "calibration",
    "host_interface", "data_path_mapping", "phy_interface",
    "csr_register_map", "latency_model", "observability",
    "failure_taxonomy", "implementation_targets",
]


def _schema_required_sections() -> list[str]:
    try:
        schema = json.loads(SCHEMA_PATH.read_text())
        req = schema.get("required")
        if req:
            return req
    except Exception:
        pass
    return _FALLBACK_REQUIRED_SECTIONS


def validate_spec(spec: dict, compile_result: dict | None = None) -> dict:
    findings = []

    required = _schema_required_sections()
    missing = [s for s in required if s not in spec]
    if missing:
        findings.append(f"missing required top-level section(s): {', '.join(missing)}")

    if compile_result is not None and not compile_result.get("consistency_ok", True):
        failed = [c["name"] for c in compile_result.get("consistency_checks", [])
                  if not c.get("pass")]
        findings.append(
            f"microarch_compiler consistency check(s) failed: {', '.join(failed)}")

    return {
        "status": "FAIL" if findings else "PASS",
        "findings": findings,
        "validator": "dummy_validation_agent (stub -- pending Jacob's Validation subsystem)",
    }


if __name__ == "__main__":
    spec_path = input("Spec JSON path: ").strip()
    spec = json.loads(Path(spec_path).read_text())
    result = validate_spec(spec)
    print(json.dumps(result, indent=2))
    sys.exit(0 if result["status"] == "PASS" else 1)
