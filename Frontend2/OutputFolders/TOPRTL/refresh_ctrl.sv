// refresh_ctrl.sv -- tREFI interval counter, postpone tracking,
// urgent-threshold escalation, refresh starvation detection.
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

    // tREFI interval counter -- counts down from cfg_tREFI_nCK; init_done
    // gates all activity (held quiescent before init completes).
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

    // Postpone counter -- running count of un-acked (owed) refreshes.
    // Saturates at cfg_max_postpone; simultaneous tick+ack cancels out.
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

    // ref_required/ref_urgent/ref_pending_cnt are combinational functions
    // of postpone_cnt -- urgent escalation compares against
    // cfg_urgent_threshold when the controller is in priority-preempt mode.
    assign ref_required    = (|postpone_cnt) & init_done;
    assign ref_urgent      = ref_required
                           & (postpone_cnt >= cfg_urgent_threshold)
                           & cfg_ref_priority;
    assign ref_pending_cnt = postpone_cnt[2:0];

    // Starvation detect -- registered 1-cycle pulse when a tick arrives
    // while already saturated at cfg_max_postpone.
    logic starve_detect;
    assign starve_detect = refi_tick
                         & (postpone_cnt >= cfg_max_postpone)
                         & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

endmodule
