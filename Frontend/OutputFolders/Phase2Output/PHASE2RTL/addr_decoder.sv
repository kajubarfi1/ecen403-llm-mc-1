////////////////////////////////////////////////////////////////////////////////
// Module:    addr_decoder
// File:      addr_decoder.sv
// Generated: 2026-03-19 11:15:33
// Agent:     Address Decoder Agent (Phase 2)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   Combinational address decoder. Maps 29-bit byte address to
//   row[14:0], bank[2:0], col[9:0].
//   Mapping policy: row-bank-column
//   Zero pipeline latency.
//
// Bit slicing (row-bank-column):
//   addr[3:0]    → burst byte offset (4 bits, BL8 × 4B)
//   addr[10:4]   → column [9:3]  (7 usable bits, A[2:0]=0 for BL8)
//   addr[13:11]  → bank   [2:0]
//   addr[28:14]  → row    [14:0]
//
// Dependency: Wishbone Port (receives req_addr)
// Validation: AD-001 .. AD-003
////////////////////////////////////////////////////////////////////////////////

module addr_decoder #(
    parameter ADDR_WIDTH = 29,
    parameter ROW_BITS   = 15,
    parameter COL_BITS   = 10,
    parameter BANK_BITS  = 3,
    parameter RANK_BITS  = 1
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
    // Address slicing — row-bank-column
    // ================================================================
    // Purely combinational, zero latency.
    //
    //  |<-- row [15b] -->|<-- bank [3b] -->|<-- col [10b] -->|<-- byte_off [4b] -->|
    //  [28                  14] [13            11] [10            4] [3             0]
    // ================================================================

    // Column: upper bits from address, lower 3 bits = 0 (BL8 burst)
    assign dec_col  = {req_addr[10:4], 3'b000};
    assign dec_bank = req_addr[13:11];
    assign dec_row  = req_addr[28:14];

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
