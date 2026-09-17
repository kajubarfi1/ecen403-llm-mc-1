// bad_block.sv — Intentionally invalid RTL for pipeline error testing
// Errors introduced:
//   1. Module name is "bad_block" but manifest says "good_block" (name mismatch)
//   2. Port "missing_port" is in the manifest but not declared here
//   3. "data_out" direction is "output" here but manifest says "input"
//   4. Syntax error: missing semicolon on wire declaration
//   5. Undefined signal used in always block

module bad_block (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out,   // manifest says this is "input" — direction mismatch
    output logic        valid_out
    // "missing_port" is listed in manifest but not declared here
);

    // Syntax error: missing semicolon
    logic [7:0] internal_reg

    // Undefined signal
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 8'h00;
            data_out     <= 8'h00;
            valid_out    <= 1'b0;
        end else begin
            internal_reg <= data_in & undefined_signal;  // undefined_signal not declared
            data_out     <= internal_reg;
            valid_out    <= |internal_reg;
        end
    end

endmodule
