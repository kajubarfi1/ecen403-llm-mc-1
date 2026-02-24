////////////////////////////////////////////////////////////////////////////////
// Module:    refresh_ctrl
// File:      refresh_ctrl.sv
// Generated: 2026-02-24 16:09:52
// Agent:     Refresh Controller Agent (Phase 2)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   tREFI interval counter (6240 nCK = 7.8µs).
//   Tracks postponed refresh count (max 8).
//   Asserts ref_urgent when postponed >= 6.
//   Signals ref_starve when postponed > 8.
//   Supports CSR force_refresh.
//
// Dependency: Config Registers (cfg_tREFI_nCK, cfg_max_postpone, etc.)
// Validation: RF-001 .. RF-006
////////////////////////////////////////////////////////////////////////////////

module refresh_ctrl #(
    parameter REFI_CTR_W = 13,
    parameter POST_CTR_W = 4
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,
    input  logic                    rst_n,

    // ────────────── Control ──────────────
    input  logic                    init_done,          // don't refresh until init complete
    input  logic                    cfg_force_refresh,  // CSR force refresh (pulse)

    // ────────────── Config inputs (from config_regs) ──────────────
    input  logic [23:0]             cfg_tREFI_nCK,
    input  logic [3:0]              cfg_max_postpone,
    input  logic [3:0]              cfg_urgent_threshold,
    input  logic                    cfg_ref_priority,   // 1 = urgent_preempt

    // ────────────── Scheduler interface ──────────────
    output logic                    ref_required,       // refresh needed (normal)
    output logic                    ref_urgent,         // urgent — preempt scheduler
    input  logic                    ref_ack,            // scheduler completed refresh

    // ────────────── Status ──────────────
    output logic [2:0]              ref_pending_cnt,    // current postpone count (to CSR)
    output logic                    ref_starve_flag     // starvation event pulse
);

    // ================================================================
    // tREFI interval counter
    // ================================================================
    logic [REFI_CTR_W-1:0] refi_ctr;
    logic                  refi_tick;  // fires every tREFI

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

    // ================================================================
    // Postpone counter
    // ================================================================
    // Increments on refi_tick (refresh due but not yet issued)
    // Decrements on ref_ack (refresh completed)
    // Force refresh acts as an additional refi_tick
    // ================================================================
    logic [POST_CTR_W-1:0] postpone_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            postpone_cnt <= '0;
        end else if (!init_done) begin
            postpone_cnt <= '0;
        end else begin
            case ({(refi_tick | cfg_force_refresh), ref_ack})
                2'b10: begin   // refresh due, not acked
                    if (postpone_cnt < cfg_max_postpone)
                        postpone_cnt <= postpone_cnt + 1'b1;
                end
                2'b01: begin   // acked, no new refresh due
                    if (|postpone_cnt)
                        postpone_cnt <= postpone_cnt - 1'b1;
                end
                2'b11: begin   // simultaneous — net zero
                    // no change
                end
                default: ;     // 2'b00 — idle
            endcase
        end
    end

    // ================================================================
    // Outputs
    // ================================================================

    // Refresh required when postpone count > 0
    assign ref_required   = (|postpone_cnt) & init_done;

    // Urgent when count >= threshold AND priority mode is urgent_preempt
    assign ref_urgent     = ref_required
                          & (postpone_cnt >= cfg_urgent_threshold)
                          & cfg_ref_priority;

    // Pending count for CTRL_STATUS CSR (3-bit view)
    assign ref_pending_cnt = postpone_cnt[2:0];

    // Starvation: postpone count hit max and another tick arrived
    logic starve_detect;
    assign starve_detect = refi_tick & (postpone_cnt >= cfg_max_postpone) & init_done;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag <= 1'b0;
        else        ref_starve_flag <= starve_detect;

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // RF-001: postpone never exceeds max_postpone
    property p_no_overflow;
        @(posedge clk) disable iff (!rst_n || !init_done)
        1'b1 |-> (postpone_cnt <= cfg_max_postpone);
    endproperty
    assert property (p_no_overflow)
        else $error("[RF-001] postpone count exceeded max");

    // RF-002: ref_urgent only when count >= threshold
    property p_urgent_thresh;
        @(posedge clk) disable iff (!rst_n)
        ref_urgent |-> (postpone_cnt >= cfg_urgent_threshold);
    endproperty
    assert property (p_urgent_thresh)
        else $error("[RF-002] ref_urgent with count below threshold");

    // RF-004: no refresh before init_done
    property p_no_early_ref;
        @(posedge clk) disable iff (!rst_n)
        (!init_done) |-> (!ref_required);
    endproperty
    assert property (p_no_early_ref)
        else $error("[RF-004] refresh requested before init_done");

    // Coverage
    covergroup cg_ref @(posedge clk);
        option.per_instance = 1;
        cp_tick    : coverpoint refi_tick;
        cp_ack     : coverpoint ref_ack;
        cp_urgent  : coverpoint ref_urgent;
        cp_starve  : coverpoint ref_starve_flag;
        cp_force   : coverpoint cfg_force_refresh;
        cp_pending : coverpoint postpone_cnt { bins low = {[0:3]}; bins high = {[4:8]}; }
    endgroup
    cg_ref cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
