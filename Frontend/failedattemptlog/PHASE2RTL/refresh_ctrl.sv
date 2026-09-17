//============================================================
// Module: refresh_ctrl
//
// Description:
//   DDR3 Memory Controller Refresh Scheduler
//
//   Tracks refresh intervals (tREFI) and maintains a count of
//   pending (postponed) refreshes. Asserts ref_required when
//   at least one refresh is owed, and ref_urgent when the
//   pending count exceeds the urgent threshold and priority
//   mode is enabled.
//
//   The scheduler acknowledges each issued refresh via ref_ack,
//   which decrements the postpone counter. If refreshes cannot
//   be serviced and the counter saturates at cfg_max_postpone,
//   the starve flag is raised as a diagnostic.
//
// Parameters:
//   REFI_CTR_W  - Width of the tREFI interval counter (13 bits)
//   POST_CTR_W  - Width of the postpone counter (4 bits)
//
// Behavior:
//   - refi_ctr counts down from cfg_tREFI_nCK and pulses refi_tick
//   - postpone_cnt tracks pending refreshes (increments on tick/force)
//   - ref_urgent signals when postpone_cnt >= urgent threshold
//   - All activity gated by init_done
//============================================================

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

    //========================================
    // tREFI Interval Counter
    //========================================
    // Counts down from cfg_tREFI_nCK to 0, then reloads.
    // Pulses refi_tick for one cycle when reaching 0.
    // Gated by init_done.

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

    //========================================
    // Postpone Counter
    //========================================
    // Tracks the number of pending (owed) refreshes.
    // Increments on refi_tick or cfg_force_refresh.
    // Decrements on ref_ack (scheduler issued a refresh).
    // Saturates at cfg_max_postpone.
    // Simultaneous increment and ack cancel out.

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

    //========================================
    // Output Assignments
    //========================================
    // ref_required: high when any refresh is pending
    // ref_urgent:   high when pending count >= urgent threshold
    //               and priority mode is enabled
    // ref_pending_cnt: exposes low 3 bits for CSR readback

    assign ref_required    = (|postpone_cnt) & init_done;
    assign ref_urgent      = ref_required
                           & (postpone_cnt >= cfg_urgent_threshold)
                           & cfg_ref_priority;
    assign ref_pending_cnt = postpone_cnt[2:0];

    //========================================
    // Starvation Detection
    //========================================
    // If a new refresh tick arrives while postpone_cnt is already
    // saturated at cfg_max_postpone, raise ref_starve_flag for
    // one cycle as a diagnostic warning.

    logic starve_detect;
    assign starve_detect = refi_tick
                         & (postpone_cnt >= cfg_max_postpone)
                         & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

endmodule