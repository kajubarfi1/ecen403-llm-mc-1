`timescale 1ps/1ps
// uberddr3_wb_monitor.sv — passive monitor on UberDDR3's Wishbone host port.
//
// Emits one TXN line per accepted request (cyc & stb & !stall) and one per
// response (ack), sampled on the controller clock in the same convention as
// this subsystem's generated monitors: values present at the rising edge,
// i.e. what the DUT itself sampled. Responses pair with requests in order
// (Wishbone pipelined). Also stamps the moment UberDDR3 reports calibration
// complete, so the offline checker can separate the controller's own
// calibration traffic from host traffic.
//
// Consumed by check_data_integrity.py together with the pin trace from
// uberddr3_pin_sva.sv.
module uberddr3_wb_monitor #(
    parameter int ADDR_W = 26,
    parameter int DATA_W = 128,
    parameter int SEL_W  = 16
) (
    input  logic              clk,
    input  logic              cyc,
    input  logic              stb,
    input  logic              we,
    input  logic [ADDR_W-1:0] addr,
    input  logic [DATA_W-1:0] wdata,
    input  logic [SEL_W-1:0]  sel,
    input  logic              stall,
    input  logic              ack,
    input  logic [DATA_W-1:0] rdata,
    input  logic              calib_complete
);
    always @(posedge clk) begin
        if (cyc && stb && !stall)
            $display("TXN wb request t=%0t addr=%0h we=%0d data=%0h sel=%0h", $time, addr, we, wdata, sel);
        if (ack)
            $display("TXN wb response t=%0t data=%0h", $time, rdata);
    end
    always @(posedge calib_complete)
        $display("TXN wb calib_complete t=%0t", $time);
endmodule

bind ddr3_dimm_micron_sim uberddr3_wb_monitor #(.ADDR_W(WB_ADDR_BITS), .DATA_W(WB_DATA_BITS), .SEL_W(WB_SEL_BITS)) u_wb_mon (
    .clk            (i_controller_clk),
    .cyc            (i_wb_cyc),
    .stb            (i_wb_stb),
    .we             (i_wb_we),
    .addr           (i_wb_addr),
    .wdata          (i_wb_data),
    .sel            (i_wb_sel),
    .stall          (o_wb_stall),
    .ack            (o_wb_ack),
    .rdata          (o_wb_data),
    .calib_complete (ddr3_top.o_calib_complete)
);
