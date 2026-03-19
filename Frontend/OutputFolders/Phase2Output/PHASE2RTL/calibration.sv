////////////////////////////////////////////////////////////////////////////////
// Module:    calibration
// File:      calibration.sv
// Generated: 2026-03-19 11:15:33
// Agent:     Calibration Agent (Phase 2)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   Minimal calibration block for abstract PHY boundary.
//   - Waits for init_done from init_fsm
//   - Asserts cal_done one cycle after init_done (no actual leveling)
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
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,
    input  logic                    rst_n,

    // ────────────── From init_fsm ──────────────
    input  logic                    init_done,

    // ────────────── Status outputs ──────────────
    output logic                    cal_done,       // calibration complete
    output logic                    cal_fail,       // always 0 (abstract PHY)

    // ────────────── ZQCS request (to cmd_gen / scheduler) ──────────────
    output logic                    zqcs_req,       // request periodic ZQCS
    input  logic                    zqcs_ack        // scheduler completed ZQCS
);

    // ================================================================
    // cal_done — one cycle after init_done
    // ================================================================
    logic init_done_d;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) init_done_d <= 1'b0;
        else        init_done_d <= init_done;

    // cal_done latches high once init completes
    logic cal_done_r;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)                          cal_done_r <= 1'b0;
        else if (init_done && !init_done_d)  cal_done_r <= 1'b1;  // rising edge of init_done

    assign cal_done = cal_done_r;
    assign cal_fail = 1'b0;  // abstract PHY — calibration never fails

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
            // Count down
            if (zqcs_ctr == '0) begin
                zqcs_ctr     <= ZQCS_WAIT[ZQCS_CTR_W-1:0];
                zqcs_pending <= 1'b1;
            end else begin
                zqcs_ctr <= zqcs_ctr - 1'b1;
            end

            // Clear pending on ack
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

    // CL-001: cal_done only after init_done
    property p_cal_after_init;
        @(posedge clk) disable iff (!rst_n)
        cal_done |-> init_done;
    endproperty
    assert property (p_cal_after_init)
        else $error("[CL-001] cal_done before init_done");

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

    // Coverage
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
