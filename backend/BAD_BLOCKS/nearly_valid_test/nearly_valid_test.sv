// nearly_valid_test.sv
// PURPOSE: Passes intake_agent.py validation (syntactically correct, module
//          header parseable, ports match manifest) but contains issues that
//          only surface inside OpenROAD-flow-scripts:
//
//   1. Combinational loop       → place/route congestion or synthesis warning/error
//   2. CDC violation            → timing analysis failure (clk → clk2 uncrossed)
//   3. Undriven output bits     → synthesis warning, possible DRC downstream
//   4. Latch inference          → synthesis warning (incomplete always_comb)
//   5. Aggressive clock period  → guaranteed timing violation (WNS < 0) in reporter
//
// Ports are intentionally clean and match the companion manifest.json exactly
// so that intake passes without errors.

`timescale 1ns / 1ps

module nearly_valid_test (
    input  logic        clk,
    input  logic        clk2,
    input  logic        rst_n,
    input  logic [7:0]  data_in,
    input  logic [3:0]  addr,
    input  logic        wr_en,
    output logic [7:0]  data_out,
    output logic        valid,
    output logic [3:0]  status
);

    // ----------------------------------------------------------------
    // Internal signals
    // ----------------------------------------------------------------
    logic [7:0] pipe_stage1, pipe_stage2;
    logic [7:0] feedback;
    logic [3:0] state, next_state;
    logic       cdc_flag;

    // ----------------------------------------------------------------
    // ISSUE 1: Combinational loop
    // feedback depends on data_out, data_out depends on feedback.
    // Synthesis tools may break the loop or error out; place/route will
    // see oscillating logic that degrades timing closure.
    // ----------------------------------------------------------------
    assign feedback  = data_out ^ 8'hA5;
    assign data_out  = pipe_stage2 | feedback;   // loop: data_out → feedback → data_out

    // ----------------------------------------------------------------
    // ISSUE 2: Clock Domain Crossing (CDC) — no synchronizer
    // cdc_flag is written on clk, read directly on clk2.
    // OpenROAD's timing analysis will flag a multi-cycle path violation.
    // ----------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            pipe_stage1 <= 8'h00;
        else
            pipe_stage1 <= data_in + 8'h01;
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            cdc_flag <= 1'b0;
        else
            cdc_flag <= pipe_stage1[7];   // written on clk
    end

    always_ff @(posedge clk2 or negedge rst_n) begin
        if (!rst_n)
            pipe_stage2 <= 8'h00;
        else if (cdc_flag)                // read on clk2 — CDC violation
            pipe_stage2 <= pipe_stage1;
        else
            pipe_stage2 <= pipe_stage2 >> 1;
    end

    // ----------------------------------------------------------------
    // ISSUE 3: Latch inference
    // 'valid' is not assigned in all branches of the always_comb block.
    // Synthesis infers a latch for 'valid', which is flagged by ORFS
    // and causes issues in the static timing analysis step.
    // ----------------------------------------------------------------
    always_comb begin
        if (wr_en) begin
            valid = 1'b1;
            // 'valid' has no else assignment → latch inferred
        end
    end

    // ----------------------------------------------------------------
    // ISSUE 4: Partially undriven output
    // status[3:2] are never assigned — they will be tied to X/Z in
    // simulation and cause synthesis warnings about undriven bits.
    // ----------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= 4'h0;
        else
            state <= next_state;
    end

    always_comb begin
        case (state)
            4'h0: next_state = wr_en  ? 4'h1 : 4'h0;
            4'h1: next_state = valid  ? 4'h2 : 4'h1;
            4'h2: next_state = 4'h0;
            default: next_state = 4'h0;
        endcase
    end

    // status[1:0] driven, status[3:2] left undriven
    assign status[1:0] = state[1:0];
    // status[3:2] intentionally not assigned

endmodule
