//==============================================================================
// refresh_ctrl.sv
//
// DDR3 Memory Controller Refresh Controller Module
//
// This module manages the periodic refresh requirements for DDR3 SDRAM.
// It tracks refresh intervals (tREFI), counts pending refreshes, and signals
// urgency when the controller falls behind the refresh schedule.
//
// Key Features:
//   - Free-running tREFI interval counter
//   - Postpone counter tracking pending refreshes
//   - Urgent refresh signaling when pending count exceeds threshold
//   - Starvation detection when refresh requests are maximally postponed
//   - CSR-driven forced refresh capability
//   - Configurable parameters via CSR interface
//
//==============================================================================

module refresh_ctrl #(
    parameter REFI_CTR_W = 13,
    parameter POST_CTR_W = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    init_done,
    input  logic                    cfg_force_refresh,
    input  logic [23:0]             cfg_tREFI_nCK,
    input  logic [3:0]              cfg_max_postpone,
    input  logic [3:0]              cfg_urgent_threshold,
    input  logic                    cfg_ref_priority,
    output logic                    ref_required,
    output logic                    ref_urgent,
    input  logic                    ref_ack,
    output logic [2:0]              ref_pending_cnt,
    output logic                    ref_starve_flag
);

    //==========================================================================
    // REFI Interval Counter
    //
    // Counts down from cfg_tREFI_nCK to 0, generating a refi_tick pulse
    // every tREFI cycles. This free-running counter operates only after
    // init_done is asserted.
    //==========================================================================

    logic [REFI_CTR_W-1:0] refi_ctr;
    logic                  refi_tick;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            refi_ctr  <= '0;
            refi_tick <= 1'b0;
        end else if (!init_done) begin
            refi_ctr  <= '0;
            refi_tick <= 1'b0;
        end else begin
            refi_tick <= 1'b0;
            if (refi_ctr == '0) begin
                refi_ctr  <= cfg_tREFI_nCK[REFI_CTR_W-1:0];
                refi_tick <= 1'b1;
            end else begin
                refi_ctr <= refi_ctr - 1'b1;
            end
        end
    end

    //==========================================================================
    // Postpone Counter
    //
    // Tracks the number of pending (un-acknowledged) refresh requests.
    // Increments on refi_tick or cfg_force_refresh, decrements on ref_ack.
    // Saturates at cfg_max_postpone to prevent overflow.
    //==========================================================================

    logic [POST_CTR_W-1:0] postpone_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            postpone_cnt <= '0;
        end else if (!init_done) begin
            postpone_cnt <= '0;
        end else begin
            case ({(refi_tick | cfg_force_refresh), ref_ack})
                2'b10: if (postpone_cnt < cfg_max_postpone)
                           postpone_cnt <= postpone_cnt + 1'b1;
                2'b01: if (|postpone_cnt)
                           postpone_cnt <= postpone_cnt - 1'b1;
                default: ; // 2'b00 idle, 2'b11 cancel
            endcase
        end
    end

    //==========================================================================
    // Output Assignments
    //
    // ref_required: Indicates at least one refresh is pending
    // ref_urgent:   Indicates scheduler should preempt other traffic when
    //               pending count reaches or exceeds the urgent threshold
    //               and priority mode is enabled
    // ref_pending_cnt: Exposes lower 3 bits of postpone count to CSR
    //==========================================================================

    assign ref_required    = (|postpone_cnt) & init_done;
    assign ref_urgent      = ref_required
                           & (postpone_cnt >= cfg_urgent_threshold)
                           & cfg_ref_priority;
    assign ref_pending_cnt = postpone_cnt[2:0];

    //==========================================================================
    // Starvation Detection
    //
    // Detects when a new refresh interval tick arrives while the postpone
    // counter is already saturated at cfg_max_postpone. This indicates the
    // memory controller is unable to service refresh requests fast enough.
    // The starve_detect signal is registered to produce a 1-cycle pulse
    // on ref_starve_flag for diagnostic purposes.
    //==========================================================================

    logic starve_detect;
    assign starve_detect = refi_tick
                         & (postpone_cnt >= cfg_max_postpone)
                         & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

endmodule