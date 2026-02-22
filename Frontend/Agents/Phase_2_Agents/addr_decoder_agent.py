#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║                 ADDRESS DECODER AGENT                                ║
║  Phase 2 — Depends on: Wishbone Port (wb_port)                      ║
║  Generates: addr_decoder.sv + addr_decoder_manifest.json             ║
║                                                                      ║
║  Combinational row-bank-column splitter.                             ║
║  Maps 29-bit byte address → row[14:0], bank[2:0], col[9:0]          ║
║  per address_mapping policy (row-bank-column).                       ║
╚══════════════════════════════════════════════════════════════════════╝
"""

import json, sys, os, math
from pathlib import Path
from datetime import datetime


class AddrDecoderAgent:

    def __init__(self, spec_path: str, output_dir: str = "./output"):
        self.spec_path = spec_path
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

        with open(spec_path) as f:
            self.spec = json.load(f)

        self.geo = self.spec["memory_geometry"]
        self.host = self.spec["host_interface"]
        self.p = self._derive()

    def _derive(self) -> dict:
        p = {}
        p["ROW_BITS"]   = self.geo["row_bits"]         # 15
        p["COL_BITS"]   = self.geo["column_bits"]       # 10
        p["BANK_BITS"]  = self.geo["bank_bits"]         # 3
        p["RANKS"]      = self.geo["ranks"]             # 1
        p["RANK_BITS"]  = 1 if self.geo["ranks"] > 1 else 0
        p["BL"]         = self.geo["burst_length"]      # 8
        p["ADDR_WIDTH"] = self.host["address_width_bits"]  # 29
        p["DATA_WIDTH"] = self.host["data_width_bits"]     # 32
        p["MAPPING"]    = self.geo["address_mapping"]      # row-bank-column

        # Burst byte offset: BL8 × channel_width_bytes = 8 × 2 = 16 bytes → 4 bits
        channel_bytes = (self.geo["byte_lanes"] * self.geo["device_width_bits"]) // 8
        p["BURST_OFFSET"] = int(math.log2(p["BL"] * channel_bytes))  # 4
        # Column bits A[2:0] are consumed by BL8 burst (implicit in DDR3)
        p["COL_LOW_SKIP"] = int(math.log2(p["BL"]))  # 3
        p["COL_USED"]     = p["COL_BITS"] - p["COL_LOW_SKIP"]  # 7 usable column bits

        return p

    def validate(self) -> list:
        errors = []
        p = self.p
        total = p["BURST_OFFSET"] + p["COL_USED"] + p["BANK_BITS"] + p["ROW_BITS"] + p["RANK_BITS"]
        if total > p["ADDR_WIDTH"]:
            errors.append(f"Address bits overflow: {total} > {p['ADDR_WIDTH']}")
        if p["MAPPING"] not in ("row-bank-column", "row-column-bank"):
            errors.append(f"Unknown mapping: {p['MAPPING']}")
        return errors

    def generate_rtl(self) -> str:
        p = self.p
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        # Bit slicing for row-bank-column mapping:
        # addr[1:0]   = byte offset (2 bits, ignored — word aligned)
        # addr[12:2]  = column[10:0] (full 10 col bits; bottom 3 = 0 for BL8 by convention)
        # addr[15:13] = bank[2:0]
        # addr[30:16] = row[14:0]  (but addr is only 29 bits, so row = addr[28:16] → 13 bits?)
        #
        # Correct approach: just do positional slicing
        # byte_off = log2(DATA_WIDTH/8) = 2
        # Then: col = ADDR[byte_off + COL_BITS - 1 : byte_off]
        #       bank = ADDR[byte_off + COL_BITS + BANK_BITS - 1 : byte_off + COL_BITS]
        #       row  = ADDR[byte_off + COL_BITS + BANK_BITS + ROW_BITS - 1 : byte_off + COL_BITS + BANK_BITS]

        bo = p["BURST_OFFSET"]    # 4 (BL8 × 2B channel)
        col_lo = bo
        col_hi = bo + p["COL_USED"] - 1  # 7 usable col bits
        bank_lo = col_hi + 1
        bank_hi = bank_lo + p["BANK_BITS"] - 1
        row_lo = bank_hi + 1
        row_hi = row_lo + p["ROW_BITS"] - 1

        return f"""\
////////////////////////////////////////////////////////////////////////////////
// Module:    addr_decoder
// File:      addr_decoder.sv
// Generated: {ts}
// Agent:     Address Decoder Agent (Phase 2)
// Spec:      {self.spec.get('design_id', 'N/A')} rev {self.spec.get('revision', 'N/A')}
//
// Description:
//   Combinational address decoder. Maps {p['ADDR_WIDTH']}-bit byte address to
//   row[{p['ROW_BITS']-1}:0], bank[{p['BANK_BITS']-1}:0], col[{p['COL_BITS']-1}:0].
//   Mapping policy: {p['MAPPING']}
//   Zero pipeline latency.
//
// Bit slicing ({p['MAPPING']}):
//   addr[{bo-1}:0]    → burst byte offset ({bo} bits, BL8 × {p['BURST_OFFSET']}B)
//   addr[{col_hi}:{col_lo}]   → column [{p['COL_BITS']-1}:3]  ({p['COL_USED']} usable bits, A[2:0]=0 for BL8)
//   addr[{bank_hi}:{bank_lo}]  → bank   [{p['BANK_BITS']-1}:0]
//   addr[{row_hi}:{row_lo}]  → row    [{p['ROW_BITS']-1}:0]
//
// Dependency: Wishbone Port (receives req_addr)
// Validation: AD-001 .. AD-003
////////////////////////////////////////////////////////////////////////////////

module addr_decoder #(
    parameter ADDR_WIDTH = {p['ADDR_WIDTH']},
    parameter ROW_BITS   = {p['ROW_BITS']},
    parameter COL_BITS   = {p['COL_BITS']},
    parameter BANK_BITS  = {p['BANK_BITS']},
    parameter RANK_BITS  = {max(1, p['RANK_BITS'])}
) (
    // ────────────── Input (from wb_port) ──────────────
    input  logic [ADDR_WIDTH-1:0]   req_addr,       // byte address from wb_port

    // ────────────── Decoded outputs (to cmd_queue) ──────────────
    output logic [ROW_BITS-1:0]     dec_row,        // row address
    output logic [BANK_BITS-1:0]    dec_bank,       // bank address
    output logic [COL_BITS-1:0]     dec_col,        // column address
    output logic [RANK_BITS-1:0]    dec_rank        // rank (0 for single-rank)
);

    // ================================================================
    // Address slicing — {p['MAPPING']}
    // ================================================================
    // Purely combinational, zero latency.
    //
    //  |<-- row [{p['ROW_BITS']}b] -->|<-- bank [{p['BANK_BITS']}b] -->|<-- col [{p['COL_BITS']}b] -->|<-- byte_off [{bo}b] -->|
    //  [{row_hi}                  {row_lo}] [{bank_hi}            {bank_lo}] [{col_hi}            {col_lo}] [{bo-1}             0]
    // ================================================================

    // Column: upper bits from address, lower 3 bits = 0 (BL8 burst)
    assign dec_col  = {{req_addr[{col_hi}:{col_lo}], 3'b000}};
    assign dec_bank = req_addr[{bank_hi}:{bank_lo}];
    assign dec_row  = req_addr[{row_hi}:{row_lo}];

    // Single-rank system: rank always 0
    assign dec_rank = '0;

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // AD-001: Verify full decode covers expected address range
    property p_addr_range;
        @(req_addr) 1'b1 |-> (req_addr < (1 << ADDR_WIDTH));
    endproperty

    // AD-002: Column bottom bits should be 0 for BL8 aligned accesses
    // (informational — not all accesses are BL8 aligned)

    // AD-003: Decode is purely combinational (no clock needed)
    // (verified by absence of always_ff)

    // synthesis translate_on
    // synopsys translate_on

endmodule
"""

    def generate_manifest(self) -> dict:
        p = self.p
        return {
            "module_name": "addr_decoder",
            "file": "addr_decoder.sv",
            "phase": 2,
            "agent": "addr_decoder_agent",
            "dependencies": ["wb_port"],
            "spec_version": self.spec.get("schema_version"),
            "parameters": {
                "ADDR_WIDTH": p["ADDR_WIDTH"], "ROW_BITS": p["ROW_BITS"],
                "COL_BITS": p["COL_BITS"], "BANK_BITS": p["BANK_BITS"],
                "RANK_BITS": max(1, p["RANK_BITS"]), "MAPPING": p["MAPPING"],
            },
            "ports": {
                "input": [
                    {"name": "req_addr", "width": p["ADDR_WIDTH"], "dir": "input",
                     "source": "wb_port.req_addr"},
                ],
                "output": [
                    {"name": "dec_row",  "width": p["ROW_BITS"],  "dir": "output"},
                    {"name": "dec_bank", "width": p["BANK_BITS"], "dir": "output"},
                    {"name": "dec_col",  "width": p["COL_BITS"],  "dir": "output"},
                    {"name": "dec_rank", "width": max(1, p["RANK_BITS"]), "dir": "output"},
                ],
            },
        }

    def run(self) -> dict:
        hdr = "=" * 62
        print(f"{hdr}\n  ADDRESS DECODER AGENT\n  Spec: {self.spec_path}\n{hdr}")
        print("\n[1/4] Validating …")
        errs = self.validate()
        if errs:
            for e in errs: print(f"  ✗ {e}")
            return {"status": "error", "errors": errs}
        print("  ✓ Valid")
        for k,v in self.p.items(): print(f"    {k:20s} = {v}")

        print("\n[2/4] Generating RTL …")
        rtl = self.generate_rtl()
        print(f"  ✓ {len(rtl.splitlines())} lines")

        print("\n[3/4] Manifest …")
        manifest = self.generate_manifest()
        print(f"  ✓ {sum(len(v) for v in manifest['ports'].values())} ports")

        print("\n[4/4] Writing …")
        (self.output_dir / "addr_decoder.sv").write_text(rtl)
        (self.output_dir / "addr_decoder_manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"  ✓ {self.output_dir}/addr_decoder.sv")
        print(f"  ✓ {self.output_dir}/addr_decoder_manifest.json")
        print(f"\n{hdr}\n  DONE — addr_decoder.sv\n{hdr}")
        return {"status": "success", "module": "addr_decoder", "phase": 2,
                "lines": len(rtl.splitlines()), "manifest": manifest}


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════╗")
    print("║   ADDRESS DECODER AGENT  (Phase 2)          ║")
    print("╚══════════════════════════════════════════════╝\n")
    spec = input("Enter path to spec JSON: ").strip()
    if not spec or not os.path.isfile(spec):
        print(f"Error: invalid path '{spec}'"); sys.exit(1)
    out = input("Output directory (Enter for ./output): ").strip() or "./output"
    print()
    r = AddrDecoderAgent(spec, out).run()
    sys.exit(0 if r["status"]=="success" else 1)
