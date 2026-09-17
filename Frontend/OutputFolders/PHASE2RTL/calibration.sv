////////////////////////////////////////////////////////////////////////////////
// Module:    calibration
// File:      calibration.sv
// Generated: 2026-09-17 12:58:39
// Agent:     Calibration Agent (Phase 2)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   Minimal calibration block for abstract PHY boundary.
//   - Waits for init_done from init_fsm
//   - Latches cal_done permanently high on first init_done high (sticky)
//   - Issues periodic ZQCS request every 512000 nCK
//     (128000 controller cycles)
//   - Write/read leveling disabled (PHY not modeled)
//
// Dependency: Init/Reset FSM (init_done)
// Validation: CL-001 .. CL-003
////////////////////////////////////////////////////////////////////////////////

module calibration #(
    parameter ZQCS_CTR_W = 17,
    parameter ZQCS_WAIT  = 128000,
    parameter TZQCS_CYC  = 16
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    init_done,
    output logic                    cal_done,
    output logic                    cal_fail,
    output logic                    zqcs_req,
    input  logic                    zqcs_ack
);

    // ================================================================
    // cal_done — sticky latch: goes high on first init_done high and stays
    // high until reset. No edge detection.
    // ================================================================
    logic cal_done_r;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)            cal_done_r <= 1'b0;
        else if (init_done)    cal_done_r <= 1'b1;
    end

    assign cal_done = cal_done_r;
    assign cal_fail = 1'b0;

    // ================================================================
    // Periodic ZQCS counter
    // ================================================================
    logic [ZQCS_CTR_W-1:0] zqcs_ctr;
    logic                  zqcs_pending;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            zqcs_ctr     <= '0;
            zqcs_pending <= 1'b0;
        end else if (!cal_done_r) begin
            zqcs_ctr     <= '0;
            zqcs_pending <= 1'b0;
        end else begin
            if (zqcs_ctr == '0) begin
                zqcs_ctr     <= ZQCS_WAIT[ZQCS_CTR_W-1:0];
                zqcs_pending <= 1'b1;
            end else begin
                zqcs_ctr <= zqcs_ctr - 1'b1;
            end

            if (zqcs_ack)
                zqcs_pending <= 1'b0;
        end
    end

    assign zqcs_req = zqcs_pending & cal_done_r;

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // CL-001: cal_done high implies either init_done was high last cycle
    // (legitimate first rise) OR cal_done was already high (sticky hold).
    // This avoids the $rose() race: at the edge where init_done first goes
    // high, $past(init_done) would sample the PRIOR edge (when it was still 0).
    property p_cal_after_init;
        @(posedge clk) disable iff (!rst_n)
        cal_done |-> ($past(init_done) || $past(cal_done));
    endproperty
    assert property (p_cal_after_init)
        else $error("[CL-001] cal_done high without prior init_done or sticky hold");

    // CL-002: cal_fail always 0 (abstract PHY)
    property p_no_fail;
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (!cal_fail);
    endproperty
    assert property (p_no_fail)
        else $error("[CL-002] cal_fail asserted in abstract PHY mode");

    // CL-003: ZQCS only after cal_done
    property p_zqcs_after_cal;
        @(posedge clk) disable iff (!rst_n)
        zqcs_req |-> cal_done;
    endproperty
    assert property (p_zqcs_after_cal)
        else $error("[CL-003] ZQCS requested before cal_done");

    covergroup cg_cal @(posedge clk);
        option.per_instance = 1;
        cp_cal_done  : coverpoint cal_done;
        cp_zqcs_req  : coverpoint zqcs_req;
        cp_zqcs_ack  : coverpoint zqcs_ack;
    endgroup
    cg_cal cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
