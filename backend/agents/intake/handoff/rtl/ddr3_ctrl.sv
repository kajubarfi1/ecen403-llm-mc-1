module ddr3_ctrl (
 input logic clk,
 input logic rst_n,
 input logic req,
 output logic gnt
);
 always_ff @(posedge clk) begin
  if (!rst_n) gnt <= 1'b0;
  else gnt <= req;
 end
endmodule
