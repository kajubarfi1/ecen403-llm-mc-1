// =============================================================================
// 8-Bit Ripple Carry Adder - SystemVerilog Skeleton
// =============================================================================
// This file contains the skeleton structure for an 8-bit ripple carry adder.
// Module interfaces and internal signals are defined, but implementation logic
// is marked with TODO comments.
//
// Design Specifications:
//   - Bit Width: 8 bits (parameterized as WIDTH=8)
//   - Carry-In: Yes (external Cin port)
//   - Carry-Out: Yes (external Cout port)
//   - Overflow Detection: No
//   - Arithmetic: Unsigned addition with carry support
//
// Date: 2026-02-10
// =============================================================================

// =============================================================================
// Module: full_adder
// =============================================================================
// Description: Single-bit full adder
// Computes the sum and carry-out of three single-bit inputs
//
// Logic Equations:
//   sum  = a ⊕ b ⊕ cin
//   cout = (a · b) + (cin · (a ⊕ b))
//   or
//   cout = (a · b) + (a · cin) + (b · cin)  [majority function]
// =============================================================================
module full_adder (
    input  logic a,      // First operand bit
    input  logic b,      // Second operand bit
    input  logic cin,    // Carry input from previous stage
    output logic sum,    // Sum output bit
    output logic cout    // Carry output to next stage
);

    // =========================================================================
    // TODO: Implement full adder logic
    // =========================================================================
    // Hint: sum  = a ^ b ^ cin
    //       cout = (a & b) | (cin & (a ^ b))
    //       or cout = (a & b) | (a & cin) | (b & cin)

    // Placeholder assignments to avoid compilation errors
    assign sum  = 1'b0;
    assign cout = 1'b0;

endmodule


// =============================================================================
// Module: ripple_carry_adder
// =============================================================================
// Description: 8-bit ripple carry adder with carry-in and carry-out
// Uses eight full_adder modules connected in series to perform 8-bit addition.
// The carry propagates sequentially from LSB (bit 0) to MSB (bit 7).
//
// Architecture:
//   FA[0]: A[0] + B[0] + carry[0] (=Cin) → S[0], carry[1]
//   FA[1]: A[1] + B[1] + carry[1]        → S[1], carry[2]
//   FA[2]: A[2] + B[2] + carry[2]        → S[2], carry[3]
//   FA[3]: A[3] + B[3] + carry[3]        → S[3], carry[4]
//   FA[4]: A[4] + B[4] + carry[4]        → S[4], carry[5]
//   FA[5]: A[5] + B[5] + carry[5]        → S[5], carry[6]
//   FA[6]: A[6] + B[6] + carry[6]        → S[6], carry[7]
//   FA[7]: A[7] + B[7] + carry[7]        → S[7], Cout
//
// Computation:
//   {Cout, S[7:0]} = A[7:0] + B[7:0] + Cin
// =============================================================================
module ripple_carry_adder #(
    parameter int WIDTH = 8  // Bit width of the adder
) (
    input  logic [WIDTH-1:0] A,      // First 8-bit operand
    input  logic [WIDTH-1:0] B,      // Second 8-bit operand
    input  logic             Cin,    // Carry input (for multi-precision arithmetic)
    output logic [WIDTH-1:0] S,      // 8-bit sum output
    output logic             Cout    // Carry output (bit 8 of result)
);

    // =========================================================================
    // Internal Signal Declarations
    // =========================================================================

    // Carry chain: carry[0] through carry[WIDTH-1]
    // carry[0] is connected to external Cin
    // carry[1] through carry[WIDTH-1] are intermediate carries between FAs
    // Cout is connected to the final full adder's cout
    logic [WIDTH-1:0] carry;

    // Carry signal mapping for WIDTH=8:
    // carry[0]: Connected to external Cin
    // carry[1]: Carry from FA[0] to FA[1]
    // carry[2]: Carry from FA[1] to FA[2]
    // carry[3]: Carry from FA[2] to FA[3]
    // carry[4]: Carry from FA[3] to FA[4]
    // carry[5]: Carry from FA[4] to FA[5]
    // carry[6]: Carry from FA[5] to FA[6]
    // carry[7]: Carry from FA[6] to FA[7]
    // Cout:     Carry out from FA[7] (external output)

    // =========================================================================
    // Carry-In Connection
    // =========================================================================

    // Connect external carry input to the first stage
    assign carry[0] = Cin;

    // =========================================================================
    // Full Adder Instantiations
    // =========================================================================
    // TODO: Instantiate WIDTH (8) full_adder modules
    // Connect them in a ripple carry chain:
    //   - Each FA takes A[i], B[i], and carry[i] as inputs
    //   - Each FA produces S[i] and carry[i+1] as outputs
    //   - The last FA (bit 7) produces Cout instead of carry[8]
    //
    // Example for bit 0:
    //   full_adder fa_bit0 (
    //       .a    (A[0]),
    //       .b    (B[0]),
    //       .cin  (carry[0]),
    //       .sum  (S[0]),
    //       .cout (carry[1])
    //   );

    // Full Adder for bit 0 (LSB)
    full_adder fa_bit0 (
        .a    (A[0]),
        .b    (B[0]),
        .cin  (carry[0]),
        .sum  (S[0]),
        .cout (carry[1])
    );

    // Full Adder for bit 1
    full_adder fa_bit1 (
        .a    (A[1]),
        .b    (B[1]),
        .cin  (carry[1]),
        .sum  (S[1]),
        .cout (carry[2])
    );

    // Full Adder for bit 2
    full_adder fa_bit2 (
        .a    (A[2]),
        .b    (B[2]),
        .cin  (carry[2]),
        .sum  (S[2]),
        .cout (carry[3])
    );

    // Full Adder for bit 3
    full_adder fa_bit3 (
        .a    (A[3]),
        .b    (B[3]),
        .cin  (carry[3]),
        .sum  (S[3]),
        .cout (carry[4])
    );

    // Full Adder for bit 4
    full_adder fa_bit4 (
        .a    (A[4]),
        .b    (B[4]),
        .cin  (carry[4]),
        .sum  (S[4]),
        .cout (carry[5])
    );

    // Full Adder for bit 5
    full_adder fa_bit5 (
        .a    (A[5]),
        .b    (B[5]),
        .cin  (carry[5]),
        .sum  (S[5]),
        .cout (carry[6])
    );

    // Full Adder for bit 6
    full_adder fa_bit6 (
        .a    (A[6]),
        .b    (B[6]),
        .cin  (carry[6]),
        .sum  (S[6]),
        .cout (carry[7])
    );

    // Full Adder for bit 7 (MSB)
    full_adder fa_bit7 (
        .a    (A[7]),
        .b    (B[7]),
        .cin  (carry[7]),
        .sum  (S[7]),
        .cout (Cout)    // Final carry out to external Cout port
    );

    // =========================================================================
    // Implementation Notes
    // =========================================================================
    // 1. All 8 full adders are instantiated and connected
    // 2. The carry chain is established: Cin → carry[0] → ... → carry[7] → Cout
    // 3. Only the full_adder module logic needs to be implemented
    // 4. This skeleton compiles without errors (all outputs have placeholder values)
    // 5. For a working adder, implement the logic in the full_adder module

endmodule


// =============================================================================
// Notes for Implementation
// =============================================================================
// 1. The full_adder module needs the sum and carry-out logic implemented:
//    - sum  = a ^ b ^ cin
//    - cout = (a & b) | (cin & (a ^ b))  or  (a & b) | (a & cin) | (b & cin)
//
// 2. The ripple_carry_adder module has all instantiations complete
//    - All 8 full adders are connected in the carry chain
//    - No additional logic needed in this module
//
// 3. This skeleton compiles without errors (placeholder assignments prevent warnings)
//
// 4. Testing Strategy:
//    - Test full_adder with all 8 input combinations (000 to 111)
//    - Test ripple_carry_adder with edge cases:
//      * A=8'h00, B=8'h00, Cin=0 → S=8'h00, Cout=0
//      * A=8'hFF, B=8'h01, Cin=0 → S=8'h00, Cout=1 (carry out)
//      * A=8'hFF, B=8'hFF, Cin=1 → S=8'hFF, Cout=1 (max carry)
//      * A=8'h42, B=8'h1F, Cin=0 → S=8'h61, Cout=0 (basic addition)
//      * Random test vectors for comprehensive coverage
//
// 5. Multi-precision arithmetic:
//    - Chain multiple adders by connecting Cout of one to Cin of the next
//    - Example for 16-bit: {Cout_high, S_high} = adder(A_high, B_high, Cout_low)
//
// 6. Critical path timing:
//    - Worst case: Cin → carry[0] → ... → carry[7] → Cout
//    - Delay ≈ 8 × 2 gate delays = 16 gate delays
//    - This limits maximum operating frequency for 8-bit addition
// =============================================================================
