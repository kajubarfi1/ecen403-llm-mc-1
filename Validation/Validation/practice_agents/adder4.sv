module adder4 (
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       cin,
    output logic [3:0] sum,
    output logic       cout
);
    logic [4:0] full_sum;

    always_comb begin
        full_sum = a + b + cin;
        sum      = full_sum[3:0];
        cout     = full_sum[4];
    end
endmodule
