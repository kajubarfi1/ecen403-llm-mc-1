#!/usr/bin/env python3
"""
+======================================================================+
|        BADPORT WB_PORT AGENT  (DEMO)                                 |
|                                                                      |
|  Wraps the real WishbonePortAgent. Injects a MISSING PORT bug        |
|  on attempt 1: wb_stall_o is omitted from the port list.             |
|  Self-corrects on attempt 2.                                         |
|                                                                      |
|  Profile: FAST  (1 retry, clean on attempt 2)                        |
+======================================================================+
"""
import json, sys, os, re
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
for _rel in [".", "..", "../Phase_1_Agents", "Phase_1_Agents",
             "../Agents/Phase_1_Agents", "Agents/Phase_1_Agents"]:
    _p = os.path.normpath(os.path.join(HERE, _rel))
    if os.path.isdir(_p) and _p not in sys.path:
        sys.path.insert(0, _p)

from wb_port_agent import WishbonePortAgent

BUG_CLEARS_ON_ATTEMPT = 2  # bug active on attempt 1 only


class BadportWbPortAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output", attempt: int = 1):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.attempt = attempt
        self._real = WishbonePortAgent(spec_path, output_dir)
        self.p = self._real.p
        self.spec = self._real.spec

    def validate(self):
        return self._real.validate()

    def generate_rtl(self) -> str:
        rtl = self._real.generate_rtl()
        if self.attempt < BUG_CLEARS_ON_ATTEMPT:
            # BUG: rename wb_stall_o -> wb_halt_o everywhere. The signal is
            # still driven internally, but the validation agent's text search
            # for "wb_stall_o" fails (V-RTL-20, V-RTL-23).
            buggy = rtl.replace("wb_stall_o", "wb_halt_o")
            if buggy != rtl:
                print(f"  [BADPORT] attempt {self.attempt}: injected renamed-port bug (wb_stall_o -> wb_halt_o)")
            return buggy
        print(f"  [BADPORT] attempt {self.attempt}: bug cleared, generating clean RTL")
        return rtl

    def generate_testbench(self) -> str:
        return self._real.generate_testbench()

    def generate_manifest(self) -> dict:
        return self._real.generate_manifest()

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  BADPORT WB_PORT AGENT  [attempt {self.attempt}]\n  Spec: {self.spec_path}\n{hdr}")
        print("\n[1/5] Validating parameters ...")
        errs = self.validate()
        if errs:
            for e in errs: print(f"  ERROR: {e}")
            return {"status": "error", "errors": errs}
        print("  OK")
        print("\n[2/5] Generating RTL ...")
        rtl = self.generate_rtl()
        rtl_lines = len(rtl.splitlines())
        print(f"  OK: {rtl_lines} lines")
        print("\n[3/5] Generating testbench ...")
        tb = self.generate_testbench()
        tb_lines = len(tb.splitlines())
        print(f"  OK: {tb_lines} lines")
        print("\n[4/5] Generating port manifest ...")
        manifest = self.generate_manifest()
        port_cnt = sum(len(v) for v in manifest["ports"].values())
        print(f"  OK: {port_cnt} ports")
        print("\n[5/5] Writing files ...")
        rtl_path = self.output_dir / "wb_port.sv"
        rtl_path.write_text(rtl)
        tb_path = self.output_dir / "wb_port_tb.sv"
        tb_path.write_text(tb)
        mfst_path = self.output_dir / "wb_port_manifest.json"
        mfst_path.write_text(json.dumps(manifest, indent=2))
        print(f"  -> {rtl_path}")
        print(f"  -> {tb_path}")
        print(f"  -> {mfst_path}")
        print(f"\n{hdr}\n  DONE -- wb_port.sv (attempt {self.attempt})\n{hdr}")
        return {
            "status": "success", "module": "wb_port", "phase": 1,
            "rtl_path": str(rtl_path), "tb_path": str(tb_path),
            "manifest_path": str(mfst_path), "manifest": manifest,
            "rtl_lines": rtl_lines, "tb_lines": tb_lines, "ports": port_cnt,
        }


if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    out = input("Output (Enter=./output): ").strip() or "./output"
    att = int(input("Attempt [1]: ").strip() or "1")
    r = BadportWbPortAgent(spec, out, attempt=att).run()
    sys.exit(0 if r["status"] == "success" else 1)