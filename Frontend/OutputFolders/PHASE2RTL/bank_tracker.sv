//==============================================================================
// bank_tracker.sv
//
// DDR3 Memory Controller Bank Tracker Module
//
// This module maintains per-bank state machines and timing counters for all
// DDR3 timing constraints. It tracks 8 independent banks, each with its own
// state (IDLE/ACTIVE), open row address, and bank-local timing counters.
// Global timing counters (tRRD, tCCD, tRFC) are shared across all banks.
//
// The tFAW (Four Activate Window) constraint is enforced using a 4-slot
// circular buffer of countdown timers, ensuring no more than 4 activates
// occur within any tFAW-cycle window.
//
// Permission outputs are computed combinationally each cycle based on the
// current state and counter values, allowing the scheduler to determine
// which operations are legal on which banks.
//==============================================================================

module bank_tracker #(
    parameter NUM_BANKS  = 8,
    parameter BANK_BITS  = 3,
    parameter ROW_BITS   = 15,
    parameter CTR_WIDTH  = 8
) (
    input  logic                       clk,
    input  logic                       rst_n,

    // Command inputs
    input  logic                       cmd_act_valid,
    input  logic [BANK_BITS-1:0]       cmd_act_bank,
    input  logic [ROW_BITS-1:0]        cmd_act_row,
    input  logic                       cmd_pre_valid,
    input  logic [BANK_BITS-1:0]       cmd_pre_bank,
    input  logic                       cmd_pre_all,
    input  logic                       cmd_rd_valid,
    input  logic [BANK_BITS-1:0]       cmd_rd_bank,
    input  logic                       cmd_wr_valid,
    input  logic [BANK_BITS-1:0]       cmd_wr_bank,
    input  logic                       cmd_ref_valid,

    // Timing configuration (in controller clock cycles)
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

    // Status and permission outputs
    output logic [NUM_BANKS-1:0]       bank_is_active,
    output logic [ROW_BITS-1:0]        bank_open_row [NUM_BANKS],
    output logic [NUM_BANKS-1:0]       bank_act_allowed,
    output logic [NUM_BANKS-1:0]       bank_rd_allowed,
    output logic [NUM_BANKS-1:0]       bank_wr_allowed,
    output logic [NUM_BANKS-1:0]       bank_pre_allowed,
    output logic                       all_banks_idle,
    output logic                       faw_allows_act
);

    //==========================================================================
    // State Encoding
    //==========================================================================
    typedef enum logic [1:0] {
        BANK_IDLE    = 2'b00,
        BANK_ACTIVE  = 2'b01,
        BANK_PRECHAR = 2'b10
    } bank_state_t;

    //==========================================================================
    // Internal State and Counter Declarations
    //==========================================================================
    
    // Per-bank state and row tracking
    bank_state_t                bk_state [NUM_BANKS];
    logic [ROW_BITS-1:0]        bk_row [NUM_BANKS];

    // Per-bank timing counters (required names)
    logic [CTR_WIDTH-1:0]       ctr_rcd [NUM_BANKS];
    logic [CTR_WIDTH-1:0]       ctr_rp [NUM_BANKS];
    logic [CTR_WIDTH-1:0]       ctr_ras [NUM_BANKS];
    logic [CTR_WIDTH-1:0]       ctr_rc [NUM_BANKS];
    logic [CTR_WIDTH-1:0]       ctr_wtr [NUM_BANKS];
    logic [CTR_WIDTH-1:0]       ctr_wr [NUM_BANKS];
    logic [CTR_WIDTH-1:0]       ctr_rtp [NUM_BANKS];

    // Global timing counters (required names)
    logic [CTR_WIDTH-1:0]       ctr_rrd;
    logic [CTR_WIDTH-1:0]       ctr_ccd;
    logic [CTR_WIDTH-1:0]       ctr_rfc;

    // FAW tracking: 4-slot circular buffer
    logic [CTR_WIDTH-1:0]       faw_pipe [4];
    logic [1:0]                 faw_ptr;

    //==========================================================================
    // Sequential Logic: State and Counter Updates
    //==========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all banks to IDLE state
            for (int i = 0; i < NUM_BANKS; i++) begin
                bk_state[i] <= BANK_IDLE;
                bk_row[i]   <= '0;
                ctr_rcd[i]  <= '0;
                ctr_rp[i]   <= '0;
                ctr_ras[i]  <= '0;
                ctr_rc[i]   <= '0;
                ctr_wtr[i]  <= '0;
                ctr_wr[i]   <= '0;
                ctr_rtp[i]  <= '0;
            end

            // Reset global counters
            ctr_rrd <= '0;
            ctr_ccd <= '0;
            ctr_rfc <= '0;

            // Reset FAW tracking
            faw_pipe[0] <= '0;
            faw_pipe[1] <= '0;
            faw_pipe[2] <= '0;
            faw_pipe[3] <= '0;
            faw_ptr     <= '0;

        end else begin
            // Default: decrement all non-zero counters
            for (int i = 0; i < NUM_BANKS; i++) begin
                if (ctr_rcd[i] != 0) ctr_rcd[i] <= ctr_rcd[i] - 1'b1;
                if (ctr_rp[i]  != 0) ctr_rp[i]  <= ctr_rp[i]  - 1'b1;
                if (ctr_ras[i] != 0) ctr_ras[i] <= ctr_ras[i] - 1'b1;
                if (ctr_rc[i]  != 0) ctr_rc[i]  <= ctr_rc[i]  - 1'b1;
                if (ctr_wtr[i] != 0) ctr_wtr[i] <= ctr_wtr[i] - 1'b1;
                if (ctr_wr[i]  != 0) ctr_wr[i]  <= ctr_wr[i]  - 1'b1;
                if (ctr_rtp[i] != 0) ctr_rtp[i] <= ctr_rtp[i] - 1'b1;
            end

            if (ctr_rrd != 0) ctr_rrd <= ctr_rrd - 1'b1;
            if (ctr_ccd != 0) ctr_ccd <= ctr_ccd - 1'b1;
            if (ctr_rfc != 0) ctr_rfc <= ctr_rfc - 1'b1;

            // Decrement FAW pipe slots
            for (int i = 0; i < 4; i++) begin
                if (faw_pipe[i] != 0) faw_pipe[i] <= faw_pipe[i] - 1'b1;
            end

            //----------------------------------------------------------------------
            // REFRESH command: force all banks idle, load tRFC
            //----------------------------------------------------------------------
            if (cmd_ref_valid) begin
                for (int i = 0; i < NUM_BANKS; i++) begin
                    bk_state[i] <= BANK_IDLE;
                end
                ctr_rfc <= cfg_tRFC_nCK;
            end

            //----------------------------------------------------------------------
            // ACTIVATE command
            //----------------------------------------------------------------------
            if (cmd_act_valid) begin
                bk_state[cmd_act_bank] <= BANK_ACTIVE;
                bk_row[cmd_act_bank]   <= cmd_act_row;
                ctr_rcd[cmd_act_bank]  <= cfg_tRCD_nCK;
                ctr_ras[cmd_act_bank]  <= cfg_tRAS_nCK;
                ctr_rc[cmd_act_bank]   <= cfg_tRC_nCK;
                ctr_rrd                <= cfg_tRRD_nCK;

                // Load FAW slot
                faw_pipe[faw_ptr] <= cfg_tFAW_nCK;
                faw_ptr           <= faw_ptr + 1'b1;
            end

            //----------------------------------------------------------------------
            // PRECHARGE command
            //----------------------------------------------------------------------
            if (cmd_pre_valid) begin
                if (cmd_pre_all) begin
                    // Precharge all banks
                    for (int i = 0; i < NUM_BANKS; i++) begin
                        if (bk_state[i] == BANK_ACTIVE) begin
                            bk_state[i] <= BANK_IDLE;
                            ctr_rp[i]   <= cfg_tRP_nCK;
                        end
                    end
                end else begin
                    // Precharge single bank
                    bk_state[cmd_pre_bank] <= BANK_IDLE;
                    ctr_rp[cmd_pre_bank]   <= cfg_tRP_nCK;
                end
            end

            //----------------------------------------------------------------------
            // READ command
            //----------------------------------------------------------------------
            if (cmd_rd_valid) begin
                ctr_ccd              <= cfg_tCCD_nCK;
                ctr_rtp[cmd_rd_bank] <= cfg_tRTP_nCK;
            end

            //----------------------------------------------------------------------
            // WRITE command
            //----------------------------------------------------------------------
            if (cmd_wr_valid) begin
                ctr_ccd              <= cfg_tCCD_nCK;
                ctr_wtr[cmd_wr_bank] <= cfg_tWTR_nCK;
                ctr_wr[cmd_wr_bank]  <= cfg_tWR_nCK;
            end
        end
    end

    //==========================================================================
    // Combinational Logic: Permission Outputs
    //==========================================================================
    always_comb begin
        for (int i = 0; i < NUM_BANKS; i++) begin
            // Bank active status and open row
            bank_is_active[i] = (bk_state[i] == BANK_ACTIVE);
            bank_open_row[i]  = bk_row[i];

            // Activate allowed
            bank_act_allowed[i] = (bk_state[i] == BANK_IDLE) &&
                                  (ctr_rc[i]  == 0) &&
                                  (ctr_rp[i]  == 0) &&
                                  (ctr_rrd    == 0) &&
                                  (ctr_rfc    == 0) &&
                                  faw_allows_act;

            // Read allowed
            bank_rd_allowed[i] = (bk_state[i] == BANK_ACTIVE) &&
                                 (ctr_rcd[i] == 0) &&
                                 (ctr_ccd    == 0) &&
                                 (ctr_rfc    == 0);

            // Write allowed
            bank_wr_allowed[i] = (bk_state[i] == BANK_ACTIVE) &&
                                 (ctr_rcd[i] == 0) &&
                                 (ctr_ccd    == 0) &&
                                 (ctr_rfc    == 0);

            // Precharge allowed
            bank_pre_allowed[i] = (bk_state[i] == BANK_ACTIVE) &&
                                  (ctr_ras[i] == 0) &&
                                  (ctr_rtp[i] == 0) &&
                                  (ctr_wr[i]  == 0) &&
                                  (ctr_wtr[i] == 0) &&
                                  (ctr_rfc    == 0);
        end
    end

    //==========================================================================
    // FAW Permission: At least one slot must be zero
    //==========================================================================
    assign faw_allows_act = (faw_pipe[0] == 0) ||
                            (faw_pipe[1] == 0) ||
                            (faw_pipe[2] == 0) ||
                            (faw_pipe[3] == 0);

    //==========================================================================
    // All Banks Idle: No bank is active
    //==========================================================================
    assign all_banks_idle = (bk_state[0] == BANK_IDLE) &&
                            (bk_state[1] == BANK_IDLE) &&
                            (bk_state[2] == BANK_IDLE) &&
                            (bk_state[3] == BANK_IDLE) &&
                            (bk_state[4] == BANK_IDLE) &&
                            (bk_state[5] == BANK_IDLE) &&
                            (bk_state[6] == BANK_IDLE) &&
                            (bk_state[7] == BANK_IDLE);

endmodule