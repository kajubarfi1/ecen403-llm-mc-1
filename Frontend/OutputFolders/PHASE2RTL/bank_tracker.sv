////////////////////////////////////////////////////////////////////////////////
// Module:    bank_tracker
// File:      bank_tracker.sv
// Generated: 2026-03-23 14:57:17
// Agent:     Bank Tracker Agent (Phase 2)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   8 independent bank state machines tracking IDLE/ACTIVE/PRECHARGING.
//   Maintains open row per bank (15-bit), 14 timing counters.
//   Outputs per-bank permission bits for the scheduler.
//   All timing loaded from cfg_* buses (runtime-programmable via CSRs).
//
// Dependency: Config Registers (cfg_tRCD_nCK, cfg_tRP_nCK, etc.)
// Validation: BT-001 .. BT-006
////////////////////////////////////////////////////////////////////////////////

module bank_tracker #(
    parameter NUM_BANKS  = 8,
    parameter BANK_BITS  = 3,
    parameter ROW_BITS   = 15,
    parameter CTR_WIDTH  = 8
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                       clk,
    input  logic                       rst_n,

    // ────────────── Command feedback (from cmd_gen) ──────────────
    input  logic                       cmd_act_valid,    // ACT issued this cycle
    input  logic [BANK_BITS-1:0]       cmd_act_bank,     // which bank was activated
    input  logic [ROW_BITS-1:0]        cmd_act_row,      // which row was activated
    input  logic                       cmd_pre_valid,    // PRE issued
    input  logic [BANK_BITS-1:0]       cmd_pre_bank,
    input  logic                       cmd_pre_all,      // precharge all banks
    input  logic                       cmd_rd_valid,     // RD issued
    input  logic [BANK_BITS-1:0]       cmd_rd_bank,
    input  logic                       cmd_wr_valid,     // WR issued
    input  logic [BANK_BITS-1:0]       cmd_wr_bank,
    input  logic                       cmd_ref_valid,    // REF issued (all banks)

    // ────────────── Config inputs (from config_regs) ──────────────
    input  logic [7:0]                 cfg_tRCD_nCK,
    input  logic [7:0]                 cfg_tRP_nCK,
    input  logic [7:0]                 cfg_tRAS_nCK,
    input  logic [7:0]                 cfg_tRC_nCK,
    input  logic [7:0]                 cfg_tRRD_nCK,
    input  logic [7:0]                 cfg_tFAW_nCK,
    input  logic [7:0]                 cfg_tWTR_nCK,
    input  logic [7:0]                 cfg_tWR_nCK,
    input  logic [7:0]                 cfg_tRTP_nCK,
    input  logic [7:0]                 cfg_tCCD_nCK,
    input  logic [7:0]                 cfg_tRFC_nCK,

    // ────────────── Per-bank status outputs (to scheduler) ──────────────
    output logic [NUM_BANKS-1:0]       bank_is_active,       // 1 = bank has open row
    output logic [ROW_BITS-1:0]        bank_open_row [NUM_BANKS],  // open row per bank
    output logic [NUM_BANKS-1:0]       bank_act_allowed,     // safe to ACT
    output logic [NUM_BANKS-1:0]       bank_rd_allowed,      // safe to RD
    output logic [NUM_BANKS-1:0]       bank_wr_allowed,      // safe to WR
    output logic [NUM_BANKS-1:0]       bank_pre_allowed,     // safe to PRE
    output logic                       all_banks_idle,       // all banks precharged
    output logic                       faw_allows_act        // tFAW window not full
);

    // ================================================================
    // Bank state enum
    // ================================================================
    typedef enum logic [1:0] {
        BANK_IDLE    = 2'b00,
        BANK_ACTIVE  = 2'b01,
        BANK_PRECHAR = 2'b10
    } bank_state_t;

    // ================================================================
    // Per-bank storage
    // ================================================================
    bank_state_t            bk_state   [NUM_BANKS];
    logic [ROW_BITS-1:0]    bk_row     [NUM_BANKS];

    // Per-bank timing counters (count down to 0)
    logic [CTR_WIDTH-1:0]   ctr_rcd    [NUM_BANKS];  // ACT → RD/WR
    logic [CTR_WIDTH-1:0]   ctr_rp     [NUM_BANKS];  // PRE → ACT
    logic [CTR_WIDTH-1:0]   ctr_ras    [NUM_BANKS];  // ACT → PRE (minimum)
    logic [CTR_WIDTH-1:0]   ctr_rc     [NUM_BANKS];  // ACT → ACT (same bank)
    logic [CTR_WIDTH-1:0]   ctr_wtr    [NUM_BANKS];  // WR → RD
    logic [CTR_WIDTH-1:0]   ctr_wr     [NUM_BANKS];  // WR → PRE
    logic [CTR_WIDTH-1:0]   ctr_rtp    [NUM_BANKS];  // RD → PRE

    // Global timing counters
    logic [CTR_WIDTH-1:0]   ctr_rrd;                  // ACT → ACT (different bank)
    logic [CTR_WIDTH-1:0]   ctr_ccd;                  // CAS → CAS
    logic [CTR_WIDTH-1:0]   ctr_rfc;                  // REF → any command

    // FAW tracking: circular buffer of last 4 ACT timestamps
    logic [CTR_WIDTH-1:0]   faw_pipe [4];
    logic [1:0]             faw_idx;

    // ================================================================
    // Counter decrement — all counters decrement each cycle
    // ================================================================
    integer i;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i < NUM_BANKS; i++) begin
                bk_state[i]  <= BANK_IDLE;
                bk_row[i]    <= '0;
                ctr_rcd[i]   <= '0;
                ctr_rp[i]    <= '0;
                ctr_ras[i]   <= '0;
                ctr_rc[i]    <= '0;
                ctr_wtr[i]   <= '0;
                ctr_wr[i]    <= '0;
                ctr_rtp[i]   <= '0;
            end
            ctr_rrd  <= '0;
            ctr_ccd  <= '0;
            ctr_rfc  <= '0;
            faw_idx  <= '0;
            for (i = 0; i < 4; i++)
                faw_pipe[i] <= '0;
        end else begin

            // Decrement all nonzero counters
            for (i = 0; i < NUM_BANKS; i++) begin
                if (|ctr_rcd[i])  ctr_rcd[i]  <= ctr_rcd[i]  - 1'b1;
                if (|ctr_rp[i])   ctr_rp[i]   <= ctr_rp[i]   - 1'b1;
                if (|ctr_ras[i])  ctr_ras[i]  <= ctr_ras[i]  - 1'b1;
                if (|ctr_rc[i])   ctr_rc[i]   <= ctr_rc[i]   - 1'b1;
                if (|ctr_wtr[i])  ctr_wtr[i]  <= ctr_wtr[i]  - 1'b1;
                if (|ctr_wr[i])   ctr_wr[i]   <= ctr_wr[i]   - 1'b1;
                if (|ctr_rtp[i])  ctr_rtp[i]  <= ctr_rtp[i]  - 1'b1;
            end
            if (|ctr_rrd) ctr_rrd <= ctr_rrd - 1'b1;
            if (|ctr_ccd) ctr_ccd <= ctr_ccd - 1'b1;
            if (|ctr_rfc) ctr_rfc <= ctr_rfc - 1'b1;

            // Shift FAW pipe
            for (i = 0; i < 4; i++)
                if (|faw_pipe[i]) faw_pipe[i] <= faw_pipe[i] - 1'b1;

            // ──── ACT command ────
            if (cmd_act_valid) begin
                bk_state[cmd_act_bank]  <= BANK_ACTIVE;
                bk_row[cmd_act_bank]    <= cmd_act_row;
                ctr_rcd[cmd_act_bank]   <= {CTR_WIDTH{1'b0}} | cfg_tRCD_nCK;
                ctr_ras[cmd_act_bank]   <= {CTR_WIDTH{1'b0}} | cfg_tRAS_nCK;
                ctr_rc[cmd_act_bank]    <= {CTR_WIDTH{1'b0}} | cfg_tRC_nCK;
                ctr_rrd                 <= {CTR_WIDTH{1'b0}} | cfg_tRRD_nCK;
                // FAW: record new ACT
                faw_pipe[faw_idx]       <= {CTR_WIDTH{1'b0}} | cfg_tFAW_nCK;
                faw_idx                 <= faw_idx + 1'b1;
            end

            // ──── PRE command ────
            if (cmd_pre_valid) begin
                if (cmd_pre_all) begin
                    for (i = 0; i < NUM_BANKS; i++) begin
                        bk_state[i] <= BANK_PRECHAR;
                        ctr_rp[i]   <= {CTR_WIDTH{1'b0}} | cfg_tRP_nCK;
                    end
                end else begin
                    bk_state[cmd_pre_bank] <= BANK_PRECHAR;
                    ctr_rp[cmd_pre_bank]   <= {CTR_WIDTH{1'b0}} | cfg_tRP_nCK;
                end
            end

            // ──── PRE → IDLE transition when tRP expires ────
            for (i = 0; i < NUM_BANKS; i++)
                if (bk_state[i] == BANK_PRECHAR && ctr_rp[i] == '0)
                    bk_state[i] <= BANK_IDLE;

            // ──── RD command ────
            if (cmd_rd_valid) begin
                ctr_ccd             <= {CTR_WIDTH{1'b0}} | cfg_tCCD_nCK;
                ctr_rtp[cmd_rd_bank] <= {CTR_WIDTH{1'b0}} | cfg_tRTP_nCK;
            end

            // ──── WR command ────
            if (cmd_wr_valid) begin
                ctr_ccd             <= {CTR_WIDTH{1'b0}} | cfg_tCCD_nCK;
                ctr_wtr[cmd_wr_bank] <= {CTR_WIDTH{1'b0}} | cfg_tWTR_nCK;
                ctr_wr[cmd_wr_bank]  <= {CTR_WIDTH{1'b0}} | cfg_tWR_nCK;
            end

            // ──── REF command ────
            if (cmd_ref_valid) begin
                ctr_rfc <= {CTR_WIDTH{1'b0}} | cfg_tRFC_nCK;
                // All banks return to idle after refresh
                for (i = 0; i < NUM_BANKS; i++)
                    bk_state[i] <= BANK_IDLE;
            end
        end
    end

    // ================================================================
    // Permission outputs — combinational
    // ================================================================
    always_comb begin
        for (int j = 0; j < NUM_BANKS; j++) begin
            bank_is_active[j]   = (bk_state[j] == BANK_ACTIVE);
            bank_open_row[j]    = bk_row[j];

            // ACT allowed: bank idle, tRC/tRRD/tRFC expired, FAW not full
            bank_act_allowed[j] = (bk_state[j] == BANK_IDLE)
                                && (ctr_rc[j]  == '0)
                                && (ctr_rp[j]  == '0)
                                && (ctr_rrd    == '0)
                                && (ctr_rfc    == '0)
                                && faw_allows_act;

            // RD allowed: bank active, tRCD expired, tCCD expired
            bank_rd_allowed[j]  = (bk_state[j] == BANK_ACTIVE)
                                && (ctr_rcd[j] == '0)
                                && (ctr_ccd    == '0)
                                && (ctr_rfc    == '0);

            // WR allowed: bank active, tRCD expired, tCCD expired
            bank_wr_allowed[j]  = (bk_state[j] == BANK_ACTIVE)
                                && (ctr_rcd[j] == '0)
                                && (ctr_ccd    == '0)
                                && (ctr_rfc    == '0);

            // PRE allowed: bank active, tRAS expired, tRTP/tWR expired
            bank_pre_allowed[j] = (bk_state[j] == BANK_ACTIVE)
                                && (ctr_ras[j] == '0)
                                && (ctr_rtp[j] == '0)
                                && (ctr_wr[j]  == '0)
                                && (ctr_wtr[j] == '0)
                                && (ctr_rfc    == '0);
        end
    end

    // All banks idle
    assign all_banks_idle = (bk_state[0] == BANK_IDLE) && (bk_state[1] == BANK_IDLE)
                         && (bk_state[2] == BANK_IDLE) && (bk_state[3] == BANK_IDLE)
                         && (bk_state[4] == BANK_IDLE) && (bk_state[5] == BANK_IDLE)
                         && (bk_state[6] == BANK_IDLE) && (bk_state[7] == BANK_IDLE);

    // FAW: allows ACT if oldest window entry has expired
    assign faw_allows_act = (faw_pipe[faw_idx] == '0);

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // BT-001: No RD/WR to idle bank
    property p_no_rd_idle;
        @(posedge clk) disable iff (!rst_n)
        cmd_rd_valid |-> (bk_state[cmd_rd_bank] == BANK_ACTIVE);
    endproperty
    assert property (p_no_rd_idle) else $error("[BT-001] RD to non-active bank");

    property p_no_wr_idle;
        @(posedge clk) disable iff (!rst_n)
        cmd_wr_valid |-> (bk_state[cmd_wr_bank] == BANK_ACTIVE);
    endproperty
    assert property (p_no_wr_idle) else $error("[BT-001] WR to non-active bank");

    // BT-003: tRCD respected
    property p_trcd;
        @(posedge clk) disable iff (!rst_n)
        (cmd_rd_valid || cmd_wr_valid) |-> (ctr_rcd[cmd_rd_valid ? cmd_rd_bank : cmd_wr_bank] == '0);
    endproperty
    assert property (p_trcd) else $error("[BT-003] tRCD violation");

    // BT-005: tFAW check
    property p_faw;
        @(posedge clk) disable iff (!rst_n)
        cmd_act_valid |-> faw_allows_act;
    endproperty
    assert property (p_faw) else $error("[BT-005] tFAW violation");

    // Coverage
    covergroup cg_bt @(posedge clk);
        option.per_instance = 1;
        cp_act      : coverpoint cmd_act_valid;
        cp_pre      : coverpoint cmd_pre_valid;
        cp_pre_all  : coverpoint cmd_pre_all;
        cp_rd       : coverpoint cmd_rd_valid;
        cp_wr       : coverpoint cmd_wr_valid;
        cp_ref      : coverpoint cmd_ref_valid;
        cp_all_idle : coverpoint all_banks_idle;
    endgroup
    cg_bt cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule
