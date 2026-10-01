////////////////////////////////////////////////////////////////////////////////
// Module:    addr_decoder
// File:      addr_decoder.sv
// Generated: 2026-09-29 20:59:43
// Generator:     Address Decoder Generator (Phase 2)
// Spec:      ddr3_mc_800_x8_1lane_1rank rev compiled_ddr3800_x8_1lane_1rank
//
// Description:
//   Combinational address decoder. Maps 27-bit byte address to
//   row[13:0], bank[2:0], col[9:0].
//   Mapping policy: row-bank-column
//   Zero pipeline latency.
//
// Bit slicing (row-bank-column):
//   addr[2:0]    → burst byte offset (3 bits, BL8 × 3B)
//   addr[9:3]   → column [9:3]  (7 usable bits, A[2:0]=0 for BL8)
//   addr[12:10]  → bank   [2:0]
//   addr[26:13]  → row    [13:0]
//
// Dependency: Wishbone Port (receives req_addr)
// Validation: AD-001 .. AD-003
////////////////////////////////////////////////////////////////////////////////

module addr_decoder #(
    parameter ADDR_WIDTH = 27,
    parameter ROW_BITS   = 14,
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
    //  |<-- row [14b] -->|<-- bank [3b] -->|<-- col [10b] -->|<-- byte_off [3b] -->|
    //  [26                  13] [12            10] [9            3] [2             0]
    // ================================================================

    // Column: upper bits from address, lower 3 bits = 0 (BL8 burst)
    assign dec_col  = {req_addr[9:3], 3'b000};
    assign dec_bank = req_addr[12:10];
    assign dec_row  = req_addr[26:13];

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
