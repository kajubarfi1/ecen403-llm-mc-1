//==============================================================================
// bank_tracker.sv
//
// DDR3 Memory Controller Bank Tracker Module
//
// Maintains per-bank state machines and timing counters for 8 DDR3 banks.
// Tracks all DDR3 timing constraints (tRCD, tRP, tRAS, tRC, tRRD, tFAW, 
// tWTR, tWR, tRTP, tCCD, tRFC) and provides combinational permission vectors
// to the scheduler indicating which operations are legal on which banks.
//
// Features:
//   - 8 independent bank state machines (IDLE/ACTIVE)
//   - Per-bank timing counters (tRCD, tRP, tRAS, tRC, tWTR, tWR, tRTP)
//   - Global timing counters (tRRD, tCCD, tRFC)
//   - 4-slot circular FAW (Four Activate Window) tracker
//   - Combinational permission outputs for ACT/PRE/RD/WR per bank
//
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

    // Timing configuration inputs
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

    // Bank status outputs
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
    // State enum
    //==========================================================================
    typedef enum logic [1:0] {
        BANK_IDLE    = 2'b00,
        BANK_ACTIVE  = 2'b01,
        BANK_PRECHAR = 2'b10
    } bank_state_t;

    //==========================================================================
    // Internal state and counter declarations
    //==========================================================================
    bank_state_t            bk_state   [NUM_BANKS];
    logic [ROW_BITS-1:0]    bk_row     [NUM_BANKS];

    logic [CTR_WIDTH-1:0]   ctr_rcd    [NUM_BANKS];
    logic [CTR_WIDTH-1:0]   ctr_rp     [NUM_BANKS];
    logic [CTR_WIDTH-1:0]   ctr_ras    [NUM_BANKS];
    logic [CTR_WIDTH-1:0]   ctr_rc     [NUM_BANKS];
    logic [CTR_WIDTH-1:0]   ctr_wtr    [NUM_BANKS];
    logic [CTR_WIDTH-1:0]   ctr_wr     [NUM_BANKS];
    logic [CTR_WIDTH-1:0]   ctr_rtp    [NUM_BANKS];

    logic [CTR_WIDTH-1:0]   ctr_rrd;
    logic [CTR_WIDTH-1:0]   ctr_ccd;
    logic [CTR_WIDTH-1:0]   ctr_rfc;

    logic [CTR_WIDTH-1:0]   faw_pipe   [4];
    logic [1:0]             faw_idx;

    //==========================================================================
    // FAW allows ACT assignment
    //==========================================================================
    assign faw_allows_act = (faw_pipe[0] == '0) || (faw_pipe[1] == '0)
                         || (faw_pipe[2] == '0) || (faw_pipe[3] == '0);

    //==========================================================================
    // All banks idle assignment
    //==========================================================================
    assign all_banks_idle = (bk_state[0] == BANK_IDLE) && (bk_state[1] == BANK_IDLE)
                         && (bk_state[2] == BANK_IDLE) && (bk_state[3] == BANK_IDLE)
                         && (bk_state[4] == BANK_IDLE) && (bk_state[5] == BANK_IDLE)
                         && (bk_state[6] == BANK_IDLE) && (bk_state[7] == BANK_IDLE);

    //==========================================================================
    // Sequential logic: state machines and counters
    //==========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all banks to IDLE
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

            // Reset FAW pipe
            faw_pipe[0] <= '0;
            faw_pipe[1] <= '0;
            faw_pipe[2] <= '0;
            faw_pipe[3] <= '0;
            faw_idx     <= '0;

        end else begin
            //======================================================================
            // REFRESH command - force all banks to IDLE
            //======================================================================
            if (cmd_ref_valid) begin
                for (int i = 0; i < NUM_BANKS; i++) begin
                    bk_state[i] <= BANK_IDLE;
                end
                ctr_rfc <= cfg_tRFC_nCK;
            end else if (ctr_rfc != '0) begin
                ctr_rfc <= ctr_rfc - 1'b1;
            end

            //======================================================================
            // ACTIVATE command
            //======================================================================
            if (cmd_act_valid) begin
                bk_state[cmd_act_bank] <= BANK_ACTIVE;
                bk_row[cmd_act_bank]   <= cmd_act_row;
                ctr_rcd[cmd_act_bank]  <= cfg_tRCD_nCK;
                ctr_ras[cmd_act_bank]  <= cfg_tRAS_nCK;
                ctr_rc[cmd_act_bank]   <= cfg_tRC_nCK;
                ctr_rrd                <= cfg_tRRD_nCK;

                // Update FAW pipe
                faw_pipe[faw_idx] <= cfg_tFAW_nCK;
                faw_idx           <= faw_idx + 1'b1;
            end else if (ctr_rrd != '0) begin
                ctr_rrd <= ctr_rrd - 1'b1;
            end

            //======================================================================
            // PRECHARGE command
            //======================================================================
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

            //======================================================================
            // READ command
            //======================================================================
            if (cmd_rd_valid) begin
                ctr_ccd                <= cfg_tCCD_nCK;
                ctr_rtp[cmd_rd_bank]   <= cfg_tRTP_nCK;
            end else if (ctr_ccd != '0) begin
                ctr_ccd <= ctr_ccd - 1'b1;
            end

            //======================================================================
            // WRITE command
            //======================================================================
            if (cmd_wr_valid) begin
                if (ctr_ccd == '0) begin
                    ctr_ccd <= cfg_tCCD_nCK;
                end
                ctr_wtr[cmd_wr_bank] <= cfg_tWTR_nCK;
                ctr_wr[cmd_wr_bank]  <= cfg_tWR_nCK;
            end

            //======================================================================
            // Decrement per-bank counters
            //======================================================================
            for (int i = 0; i < NUM_BANKS; i++) begin
                // tRCD counter
                if (cmd_act_valid && (cmd_act_bank == i)) begin
                    // Already loaded above
                end else if (ctr_rcd[i] != '0) begin
                    ctr_rcd[i] <= ctr_rcd[i] - 1'b1;
                end

                // tRP counter
                if (cmd_pre_valid && ((cmd_pre_all && bk_state[i] == BANK_ACTIVE) || 
                                      (!cmd_pre_all && cmd_pre_bank == i))) begin
                    // Already loaded above
                end else if (ctr_rp[i] != '0) begin
                    ctr_rp[i] <= ctr_rp[i] - 1'b1;
                end

                // tRAS counter
                if (cmd_act_valid && (cmd_act_bank == i)) begin
                    // Already loaded above
                end else if (ctr_ras[i] != '0) begin
                    ctr_ras[i] <= ctr_ras[i] - 1'b1;
                end

                // tRC counter
                if (cmd_act_valid && (cmd_act_bank == i)) begin
                    // Already loaded above
                end else if (ctr_rc[i] != '0) begin
                    ctr_rc[i] <= ctr_rc[i] - 1'b1;
                end

                // tWTR counter
                if (cmd_wr_valid && (cmd_wr_bank == i)) begin
                    // Already loaded above
                end else if (ctr_wtr[i] != '0) begin
                    ctr_wtr[i] <= ctr_wtr[i] - 1'b1;
                end

                // tWR counter
                if (cmd_wr_valid && (cmd_wr_bank == i)) begin
                    // Already loaded above
                end else if (ctr_wr[i] != '0) begin
                    ctr_wr[i] <= ctr_wr[i] - 1'b1;
                end

                // tRTP counter
                if (cmd_rd_valid && (cmd_rd_bank == i)) begin
                    // Already loaded above
                end else if (ctr_rtp[i] != '0) begin
                    ctr_rtp[i] <= ctr_rtp[i] - 1'b1;
                end
            end

            //======================================================================
            // Decrement FAW pipe
            //======================================================================
            for (int i = 0; i < 4; i++) begin
                if (cmd_act_valid && (faw_idx == i)) begin
                    // Already loaded above
                end else if (faw_pipe[i] != '0) begin
                    faw_pipe[i] <= faw_pipe[i] - 1'b1;
                end
            end
        end
    end

    //==========================================================================
    // Combinational logic: permission outputs
    //==========================================================================
    always_comb begin
        for (int i = 0; i < NUM_BANKS; i++) begin
            // Bank active status
            bank_is_active[i] = (bk_state[i] == BANK_ACTIVE);

            // Open row
            bank_open_row[i] = bk_row[i];

            // ACT allowed
            bank_act_allowed[i] = (bk_state[i] == BANK_IDLE)
                                && (ctr_rc[i]  == '0)
                                && (ctr_rp[i]  == '0)
                                && (ctr_rrd    == '0)
                                && (ctr_rfc    == '0)
                                && faw_allows_act;

            // READ allowed
            bank_rd_allowed[i] = (bk_state[i] == BANK_ACTIVE)
                               && (ctr_rcd[i] == '0)
                               && (ctr_ccd    == '0)
                               && (ctr_rfc    == '0);

            // WRITE allowed
            bank_wr_allowed[i] = (bk_state[i] == BANK_ACTIVE)
                               && (ctr_rcd[i] == '0)
                               && (ctr_ccd    == '0)
                               && (ctr_rfc    == '0);

            // PRECHARGE allowed
            bank_pre_allowed[i] = (bk_state[i] == BANK_ACTIVE)
                                && (ctr_ras[i] == '0)
                                && (ctr_rtp[i] == '0)
                                && (ctr_wr[i]  == '0)
                                && (ctr_wtr[i] == '0)
                                && (ctr_rfc    == '0);
        end
    end

    //==========================================================================
    // Assertions (optional, for verification)
    //==========================================================================
    // synopsys translate_off
    `ifdef SIMULATION
        // Check that only one command is valid at a time
        property p_one_cmd_at_a_time;
            @(posedge clk) disable iff (!rst_n)
            $onehot0({cmd_act_valid, cmd_pre_valid, cmd_rd_valid, cmd_wr_valid, cmd_ref_valid});
        endproperty
        assert property (p_one_cmd_at_a_time)
            else $error("Multiple commands issued in same cycle");

        // Check that ACT only happens when allowed
        property p_act_when_allowed;
            @(posedge clk) disable iff (!rst_n)
            cmd_act_valid |-> bank_act_allowed[cmd_act_bank];
        endproperty
        assert property (p_act_when_allowed)
            else $error("ACT issued when not allowed on bank %0d", cmd_act_bank);

        // Check that RD only happens when allowed
        property p_rd_when_allowed;
            @(posedge clk) disable iff (!rst_n)
            cmd_rd_valid |-> bank_rd_allowed[cmd_rd_bank];
        endproperty
        assert property (p_rd_when_allowed)
            else $error("RD issued when not allowed on bank %0d", cmd_rd_bank);

        // Check that WR only happens when allowed
        property p_wr_when_allowed;
            @(posedge clk) disable iff (!rst_n)
            cmd_wr_valid |-> bank_wr_allowed[cmd_wr_bank];
        endproperty
        assert property (p_wr_when_allowed)
            else $error("WR issued when not allowed on bank %0d", cmd_wr_bank);

        // Check that PRE only happens when allowed
        property p_pre_when_allowed;
            @(posedge clk) disable iff (!rst_n)
            (cmd_pre_valid && !cmd_pre_all) |-> bank_pre_allowed[cmd_pre_bank];
        endproperty
        assert property (p_pre_when_allowed)
            else $error("PRE issued when not allowed on bank %0d", cmd_pre_bank);
    `endif
    // synopsys translate_on

endmodule