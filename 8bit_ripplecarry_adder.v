// 1-bit Full Adder (Reusable building block)
// Implements: {cout, sum} = a + b + cin
module full_adder_1bit (
    input  logic a,
    input  logic b,
    input  logic cin,
    output logic sum,
    output logic cout
);
    // Pure combinational logic
    always_comb begin
        sum  = a ^ b ^ cin;
        cout = (a & b) | (a & cin) | (b & cin);
    end
endmodule


// 8-bit Ripple Carry Adder built from 1-bit Full Adders
module ripple_adder_8bit (
    input  logic [7:0] A,
    input  logic [7:0] B,
    input  logic       Cin,
    output logic [7:0] Sum,
    output logic       Cout
);

    // Internal carry chain:
    // C[0] is carry out of bit0, C[7] is carry out of bit7 (final carry)
    logic [7:0] C;

    // Bit 0 (uses external Cin)
    full_adder_1bit FA0 (
        .a   (A[0]),
        .b   (B[0]),
        .cin (Cin),
        .sum (Sum[0]),
        .cout(C[0])
    );

    // Bits 1 through 7 (carry ripples)
    genvar i;
    generate
        for (i = 1; i < 8; i++) begin : GEN_FA
            full_adder_1bit FA (
                .a   (A[i]),
                .b   (B[i]),
                .cin (C[i-1]),
                .sum (Sum[i]),
                .cout(C[i])
            );
        end
    endgenerate

    // Final carry-out
    assign Cout = C[7];

endmodule

