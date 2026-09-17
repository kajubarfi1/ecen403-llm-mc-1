//============================================================================
// Module: refresh_ctrl
//
// Description:
//   DDR3 Memory Controller Refresh Controller
//
//   Manages periodic AUTO REFRESH commands per JEDEC spec. Tracks refresh
//   interval (tREFI) and allows postponement up to a configurable limit.
//   Asserts ref_urgent when the number of pending refreshes exceeds the
//   urgent threshold, allowing the scheduler to preempt normal traffic.
//
// Parameters:
//   REFI_CTR_W       - Width of the tREFI interval counter (13 bits)
//   POST_CTR_W       - Width of the postpone counter (4 bits)
//
// Key Behavior:
//   - After init_done, refi_ctr counts down every cycle from cfg_tREFI_nCK
//   - Each refi_tick increments postpone_cnt (a refresh is owed)
//   - ref_ack from scheduler decrements postpone_cnt (refresh issued)
//   - ref_required signals when any refresh is pending
//   - ref_urgent signals when pending count >= urgent threshold
//   - Saturates at cfg_max_postpone; raises ref_starve_flag if overflow
//
//============================================================================

module refresh_ctrl #(
    parameter REFI_CTR_W = 13,
    parameter POST_CTR_W = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    
    // Initialization
    input  logic                    init_done,
    
    // Configuration registers
    input  logic                    cfg_force_refresh,
    input  logic [23:0]             cfg_tREFI_nCK,
    input  logic [3:0]              cfg_max_postpone,
    input  logic [3:0]              cfg_urgent_threshold,
    input  logic                    cfg_ref_priority,
    
    // Refresh request interface
    output logic                    ref_required,
    output logic                    ref_urgent,
    input  logic                    ref_ack,
    
    // Status
    output logic [2:0]              ref_pending_cnt,
    output logic                    ref_starve_flag
);

    //========================================================================
    // REFI Interval Counter
    //
    // Free-running down-counter that generates a refi_tick pulse every
    // cfg_tREFI_nCK cycles when init_done is high.
    //========================================================================

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

    //========================================================================
    // Postpone Counter
    //
    // Tracks the number of pending (un-issued) refresh commands.
    // - Increments on refi_tick or cfg_force_refresh
    // - Decrements on ref_ack
    // - Simultaneous inc+dec cancel out (no change)
    // - Saturates at cfg_max_postpone
    //========================================================================

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

    //========================================================================
    // Output Assignments
    //
    // ref_required: asserted when any refresh is pending
    // ref_urgent:   asserted when pending count exceeds the urgent threshold
    //               and priority mode is enabled (allows preemption)
    // ref_pending_cnt: exposes lower 3 bits of postpone_cnt to CSR
    //========================================================================

    assign ref_required    = (|postpone_cnt) & init_done;
    assign ref_urgent      = ref_required
                           & (postpone_cnt >= cfg_urgent_threshold)
                           & cfg_ref_priority;
    assign ref_pending_cnt = postpone_cnt[2:0];

    //========================================================================
    // Starvation Detection
    //
    // Raises a 1-cycle diagnostic flag when a refi_tick arrives but
    // postpone_cnt is already saturated at cfg_max_postpone (cannot
    // increment further, indicating refresh starvation).
    //========================================================================

    logic starve_detect;
    assign starve_detect = refi_tick
                         & (postpone_cnt >= cfg_max_postpone)
                         & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

endmodule