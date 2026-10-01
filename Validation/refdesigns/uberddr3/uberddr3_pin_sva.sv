`timescale 1ps/1ps
// uberddr3_pin_sva.sv — attach the spec-derived timing/protocol assertions to
// UberDDR3's DRAM pins.
//
// UberDDR3 (AngeloJacobo/UberDDR3) is the known-good reference for the
// validation subsystem: a controller that runs a real Micron DDR3 model to a
// self-checking finish. The question this file answers is the false-positive
// rate of OUR assertions, which were generated from OUR spec of UberDDR3's
// configuration (builds/uberddr3_ddr3-667_x16_2lane_1rank/microarch_spec.json)
// with no knowledge of UberDDR3's internals.
//
// Observation point: the DDR3 pins between ddr3_top and the Micron model,
// sampled on the DDR clock — one command per tCK, exactly what the DRAM
// sees and exactly what the Micron model's own timing checks see. That makes
// the Micron model an independent cross-check on every assertion here.
//
// Encoding: our ddr_cmd is {CS#, RAS#, CAS#, WE#} (interface_catalog.json ->
// ddr_cmd.command_encoding, identical to the JESD79-3 truth table). With CS#
// high the other three pins are don't-care, so they are normalised to the
// DESELECT code rather than passed through as a random pattern.
module uberddr3_pin_sva #(
    parameter int ROW_BITS = 16,
    parameter int BA_BITS  = 3
) (
    input  logic                 ck,        // DDR clock at the pins (ck of the Micron model)
    input  logic                 rst_n,     // testbench reset (active low)
    input  logic                 cs_n,
    input  logic                 ras_n,
    input  logic                 cas_n,
    input  logic                 we_n,
    input  logic [BA_BITS-1:0]   ba,
    input  logic [ROW_BITS-1:0]  addr
);
    logic [3:0] ddr_cmd;
    assign ddr_cmd = cs_n ? 4'b1111 : {1'b0, ras_n, cas_n, we_n};

    // Generated from the UberDDR3 spec with:
    //   sva_gen.py --spec builds/uberddr3_.../microarch_spec.json --clock ddr --suffix _pins
    cmd_gen_sva_pins #(.BANK_W(BA_BITS), .ADDR_W(ROW_BITS)) u_sva (
        .clk      (ck),
        .rst_n    (rst_n),
        .ddr_cmd  (ddr_cmd),
        .ddr_bank (ba),
        .ddr_addr (addr)
    );

    // A command trace in the same TXN format our monitors emit, so the pin
    // stream can be scoreboarded later without a second adapter.
    always @(posedge ck) begin
        #1;
        if (rst_n && ddr_cmd != 4'b0111 && ddr_cmd != 4'b1111)
            $display("TXN ddr_cmd command t=%0t addr=%0h bank=%0h cmd=%0h", $time, addr, ba, ddr_cmd);
    end
endmodule

// Bind into UberDDR3's own testbench, on the wires that feed the Micron model.
bind ddr3_dimm_micron_sim uberddr3_pin_sva #(.ROW_BITS(16), .BA_BITS(3)) u_pin_sva (
    .ck    (o_ddr3_clk_p[0]),
    .rst_n (reset_n),
    .cs_n  (cs_n[0]),
    .ras_n (ras_n),
    .cas_n (cas_n),
    .we_n  (we_n),
    .ba    (ba_addr),
    .addr  (addr)
);
