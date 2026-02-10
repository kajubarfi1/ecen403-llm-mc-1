// ============================================================================
// 8-Bit Ripple Carry Adder - Complete Implementation
// ============================================================================
// This file contains the complete implementation of an 8-bit ripple carry adder.
// The design uses 8 full adder cells connected in series with sequential
// carry propagation from LSB to MSB.
//
// Design: 8-bit Ripple Carry Adder
// Architecture: Ripple Carry (Sequential carry propagation)
// Date: 2026-02-10
// ============================================================================

// ============================================================================
// Module: full_adder
// Description: Single-bit full adder implementing sum and carry logic
// ============================================================================
module full_adder (
    input  logic a,      // First input bit
    input  logic b,      // Second input bit
    input  logic cin,    // Carry input
    output logic sum,    // Sum output
    output logic cout    // Carry output
);

    // ------------------------------------------------------------------------
    // Combinational Logic Implementation
    // ------------------------------------------------------------------------
    // Sum: XOR of all three inputs
    // This represents the odd parity of the inputs
    // ------------------------------------------------------------------------
    always_comb begin
        sum = a ^ b ^ cin;
    end

    // ------------------------------------------------------------------------
    // Carry Output Logic
    // ------------------------------------------------------------------------
    // Carry is generated when:
    // 1. Both a AND b are 1 (generate condition)
    // 2. Either a OR b is 1, AND cin is 1 (propagate condition)
    //
    // Implementation: cout = (a & b) | (cin & (a ^ b))
    // This is equivalent to: cout = (a & b) | (a & cin) | (b & cin)
    // ------------------------------------------------------------------------
    always_comb begin
        cout = (a & b) | (cin & (a ^ b));
    end

endmodule : full_adder


// ============================================================================
// Module: ripple_carry_adder
// Description: 8-bit ripple carry adder using 8 full adder instances
// ============================================================================
module ripple_carry_adder (
    input  logic [7:0] A,      // First 8-bit operand
    input  logic [7:0] B,      // Second 8-bit operand
    input  logic       Cin,    // Carry input
    output logic [7:0] S,      // 8-bit sum output
    output logic       Cout    // Carry output
);

    // ------------------------------------------------------------------------
    // Parameters
    // ------------------------------------------------------------------------
    localparam int WIDTH = 8;  // Bit width of the adder

    // ------------------------------------------------------------------------
    // Internal Signals - Carry Chain
    // ------------------------------------------------------------------------
    // carry[0] connects to Cin (input carry)
    // carry[1] to carry[7] are intermediate carries between full adders
    // carry[i+1] receives the cout from full adder at bit position i
    // Cout connects to the carry output of FA7 (MSB full adder)
    // ------------------------------------------------------------------------
    logic [WIDTH:0] carry;  // 9 bits: carry[0] through carry[8]

    // ------------------------------------------------------------------------
    // Carry Chain Initialization
    // ------------------------------------------------------------------------
    // Connect the external carry input to the internal carry chain
    assign carry[0] = Cin;

    // ------------------------------------------------------------------------
    // Full Adder Instantiation using Generate Block
    // ------------------------------------------------------------------------
    // This generate block instantiates WIDTH (8) full adders
    // Each full adder:
    // - Takes bit i from A and B
    // - Takes carry[i] as carry input
    // - Produces sum bit S[i]
    // - Produces carry[i+1] as carry output to the next stage
    // ------------------------------------------------------------------------
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_full_adders
            full_adder FA_inst (
                .a    (A[i]),       // Bit i of first operand
                .b    (B[i]),       // Bit i of second operand
                .cin  (carry[i]),   // Carry from previous stage (or Cin for i=0)
                .sum  (S[i]),       // Sum output bit i
                .cout (carry[i+1])  // Carry to next stage (or Cout for i=7)
            );
        end
    endgenerate

    // ------------------------------------------------------------------------
    // Final Carry Output Assignment
    // ------------------------------------------------------------------------
    // The carry output from the MSB full adder (FA7) becomes the final Cout
    // This indicates overflow for unsigned arithmetic
    assign Cout = carry[WIDTH];

endmodule : ripple_carry_adder


// ============================================================================
// End of File
// ============================================================================
