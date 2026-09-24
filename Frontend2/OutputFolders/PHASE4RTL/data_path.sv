////////////////////////////////////////////////////////////////////////////////
// Module:    data_path
// File:      data_path.sv
// Generated: 2026-09-24 13:02:05
// Generator:     Data Path / Alignment Generator (Phase 3)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   DDR3 data path and alignment block. Bridges the 200MHz
//   controller domain to the 800MHz DDR domain.
//   Write: serialize 32-bit words into BL8 DDR transfers.
//   Read:  deserialize BL8 captures back to 32-bit words.
//   Alignment: 4:1 ratio, 2 ctrl cycles per BL8 burst.
//
// Key parameters:
//   DATA_WIDTH=32, DQ_WIDTH=16, BL=8
//   CL=11 nCK (3 ctrl), CWL=8 nCK (2 ctrl)
//   AUX_WIDTH=4, RD_FIFO_DEPTH=16
//
// Validation: DP-001 .. DP-012
////////////////////////////////////////////////////////////////////////////////

module data_path #(
    parameter DATA_WIDTH       = 32,
    parameter DQ_WIDTH         = 16,
    parameter DM_WIDTH         = 2,
    parameter SEL_WIDTH        = 4,
    parameter AUX_WIDTH        = 4,
    parameter BURST_LEN        = 8,
    parameter CLK_RATIO        = 4,
    parameter BURST_CTRL_CYC   = 2,
    parameter WORD_BEATS       = 2,
    parameter RD_FIFO_DEPTH    = 16,
    parameter FIFO_PTR_W       = 4,
    parameter CL_CTRL_DEFAULT  = 3,
    parameter CWL_CTRL_DEFAULT = 2
) (
    // Clock / Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // From cmd_gen: command timing signals
    input  logic                    cmd_wr_valid,     // WR command issued this cycle
    input  logic                    cmd_rd_valid,     // RD command issued this cycle
    input  logic [AUX_WIDTH-1:0]    cmd_aux,          // aux tag for this command

    // From wb_port: write data
    input  logic                    wr_data_valid,    // write data available
    input  logic [DATA_WIDTH-1:0]   wr_data,          // write data word
    input  logic [SEL_WIDTH-1:0]    wr_mask,          // byte lane mask
    output logic                    wr_data_ready,    // backpressure to wb_port

    // To wb_port: read response
    output logic                    rd_rsp_valid,     // read data available
    output logic [DATA_WIDTH-1:0]   rd_rsp_data,      // read data word
    output logic [AUX_WIDTH-1:0]    rd_rsp_aux,       // read response tag

    // From config_regs: runtime-configurable latencies
    input  logic [7:0]              cfg_CL_nCK,       // CAS read latency
    input  logic [7:0]              cfg_CWL_nCK,      // CAS write latency

    // DDR3 PHY interface (directly to DRAM pins) -- DQ_WIDTH-wide,
    // the real physical channel width, NOT DATA_WIDTH (the host word
    // width). A host word packs onto the channel over WORD_BEATS
    // cycles (32-bit host word / 16-bit channel = 2 beats).
    output logic [DQ_WIDTH-1:0]     ddr_dq_o,         // write data to DRAM
    output logic                    ddr_dq_oe,        // DQ output enable
    input  logic [DQ_WIDTH-1:0]     ddr_dq_i,         // read data from DRAM
    output logic [DM_WIDTH-1:0]     ddr_dm_o,         // data mask
    output logic                    ddr_dqs_o,        // DQS strobe out
    output logic                    ddr_dqs_oe,       // DQS output enable
    input  logic                    ddr_dqs_i         // DQS strobe in (read)
);

    // ================================================================
    // Write data buffer (FIFO)
    // ================================================================
    // Stores write data + mask until cmd_gen issues WR command.
    // After WR, data is driven onto DQ pins for BURST_CTRL_CYC cycles.

    typedef struct packed {
        logic [DATA_WIDTH-1:0]  data;
        logic [SEL_WIDTH-1:0]   mask;
    } wr_entry_t;

    wr_entry_t wr_buf [0:RD_FIFO_DEPTH-1];
    logic [FIFO_PTR_W:0] wr_wptr, wr_rptr;
    wire  [FIFO_PTR_W:0] wr_count = wr_wptr - wr_rptr;
    wire                  wr_full  = (wr_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);
    wire                  wr_empty = (wr_count == 0);

    assign wr_data_ready = ~wr_full;

    // Write buffer push
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            wr_wptr <= '0;
        else if (wr_data_valid && ~wr_full) begin
            wr_buf[wr_wptr[FIFO_PTR_W-1:0]] <= '{data: wr_data, mask: wr_mask};
            wr_wptr <= wr_wptr + 1'b1;
        end

    // ================================================================
    // Write serialization FSM
    // ================================================================
    // When cmd_wr_valid fires, we wait CWL controller cycles, then
    // drive DQ for BURST_CTRL_CYC cycles (2 cycles for BL8 @ 4:1).

    typedef enum logic [1:0] {
        WR_IDLE   = 2'd0,
        WR_WAIT   = 2'd1,   // waiting CWL latency
        WR_DRIVE  = 2'd2    // driving DQ pins
    } wr_state_t;

    wr_state_t wr_state;
    logic [7:0] wr_lat_ctr;        // CWL countdown
    logic [1:0] wr_burst_ctr;       // burst beat counter
    logic [DATA_WIDTH-1:0] wr_dat_r; // latched write data
    logic [SEL_WIDTH-1:0]  wr_msk_r; // latched mask

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_state     <= WR_IDLE;
            wr_lat_ctr   <= '0;
            wr_burst_ctr <= '0;
            wr_rptr      <= '0;
            wr_dat_r     <= '0;
            wr_msk_r     <= '0;
        end else begin
            case (wr_state)
                WR_IDLE: begin
                    if (cmd_wr_valid && !wr_empty) begin
                        // Latch data from write buffer
                        wr_dat_r <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].data;
                        wr_msk_r <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].mask;
                        wr_rptr  <= wr_rptr + 1'b1;
                        if (cfg_CWL_nCK <= CLK_RATIO[7:0]) begin
                            // CWL fits in one ctrl cycle, go straight to drive
                            wr_state     <= WR_DRIVE;
                            wr_burst_ctr <= '0;
                        end else begin
                            wr_state   <= WR_WAIT;
                            wr_lat_ctr <= (cfg_CWL_nCK >> 2) - 1'b1; // nCK to ctrl cycles
                        end
                    end
                end
                WR_WAIT: begin
                    if (wr_lat_ctr == 0)
                        wr_state <= WR_DRIVE;
                    else
                        wr_lat_ctr <= wr_lat_ctr - 1'b1;
                    wr_burst_ctr <= '0;
                end
                WR_DRIVE: begin
                    if (wr_burst_ctr == WORD_BEATS[1:0] - 1'b1)
                        wr_state <= WR_IDLE;
                    else
                        wr_burst_ctr <= wr_burst_ctr + 1'b1;
                end
                default: wr_state <= WR_IDLE;
            endcase
        end
    end

    // Write data to DDR pins -- wr_dat_r is DATA_WIDTH-wide (one
    // host word); drive it onto the DQ_WIDTH-wide channel over
    // WORD_BEATS beats, low beat first (pack_32_to_16, little-
    // endian: low half of the word goes out first).
    always_comb begin
        ddr_dq_o = wr_dat_r[DQ_WIDTH-1:0];
        for (int wb = 0; wb < WORD_BEATS; wb++)
            if (wr_burst_ctr == wb[1:0])
                ddr_dq_o = wr_dat_r[(wb+1)*DQ_WIDTH-1 -: DQ_WIDTH];
    end
    assign ddr_dq_oe  = (wr_state == WR_DRIVE);

    // Data mask, sliced the same way -- BYTES_PER_BEAT host-side
    // sel bits per channel beat.
    localparam int BYTES_PER_BEAT = DQ_WIDTH / 8;
    logic [BYTES_PER_BEAT-1:0] dm_beat;
    always_comb begin
        dm_beat = wr_msk_r[BYTES_PER_BEAT-1:0];
        for (int wb = 0; wb < WORD_BEATS; wb++)
            if (wr_burst_ctr == wb[1:0])
                dm_beat = wr_msk_r[(wb+1)*BYTES_PER_BEAT-1 -: BYTES_PER_BEAT];
    end
    assign ddr_dm_o   = (wr_state == WR_DRIVE) ? ~dm_beat : '0;  // DM active-high masks
    assign ddr_dqs_o  = (wr_state == WR_DRIVE);  // simplified: DQS toggles during drive
    assign ddr_dqs_oe = (wr_state == WR_DRIVE);

    // ================================================================
    // Read capture and deserialization
    // ================================================================
    // When cmd_rd_valid fires, we start a CL countdown. After CL,
    // we capture DQ data for BURST_CTRL_CYC cycles and push to
    // the read response FIFO with the aux tag.

    typedef enum logic [1:0] {
        RD_IDLE    = 2'd0,
        RD_WAIT    = 2'd1,   // waiting CL latency
        RD_CAPTURE = 2'd2    // capturing DQ data
    } rd_state_t;

    rd_state_t rd_state;
    logic [7:0] rd_lat_ctr;
    logic [1:0] rd_burst_ctr;
    logic [AUX_WIDTH-1:0] rd_aux_r;  // latched aux tag for this read

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_state     <= RD_IDLE;
            rd_lat_ctr   <= '0;
            rd_burst_ctr <= '0;
            rd_aux_r     <= '0;
        end else begin
            case (rd_state)
                RD_IDLE: begin
                    if (cmd_rd_valid) begin
                        rd_aux_r <= cmd_aux;
                        if (cfg_CL_nCK <= CLK_RATIO[7:0]) begin
                            rd_state     <= RD_CAPTURE;
                            rd_burst_ctr <= '0;
                        end else begin
                            rd_state   <= RD_WAIT;
                            rd_lat_ctr <= (cfg_CL_nCK >> 2) - 1'b1;
                        end
                    end
                end
                RD_WAIT: begin
                    if (rd_lat_ctr == 0)
                        rd_state <= RD_CAPTURE;
                    else
                        rd_lat_ctr <= rd_lat_ctr - 1'b1;
                    rd_burst_ctr <= '0;
                end
                RD_CAPTURE: begin
                    if (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1)
                        rd_state <= RD_IDLE;
                    else
                        rd_burst_ctr <= rd_burst_ctr + 1'b1;
                end
                default: rd_state <= RD_IDLE;
            endcase
        end
    end

    // ================================================================
    // Read response FIFO
    // ================================================================
    typedef struct packed {
        logic [DATA_WIDTH-1:0]  data;
        logic [AUX_WIDTH-1:0]   aux;
    } rd_entry_t;

    rd_entry_t rd_fifo [0:RD_FIFO_DEPTH-1];
    logic [FIFO_PTR_W:0] rd_wptr, rd_rptr;
    wire  [FIFO_PTR_W:0] rd_count = rd_wptr - rd_rptr;
    wire                  rd_empty = (rd_count == 0);

    // Assemble WORD_BEATS channel-width captures into one
    // DATA_WIDTH host word before pushing -- pushing per beat
    // (the old behavior) put WORD_BEATS separate, each only
    // partially-real entries into the FIFO per read, which is
    // what showed up downstream as duplicate/X-valued read
    // responses (see Defect 2, Frontend2/VALIDATION_INTEGRATION_
    // PLAN.md). Low beat first (pack_32_to_16, little-endian).
    wire rd_capture_valid = (rd_state == RD_CAPTURE);
    wire rd_word_complete = rd_capture_valid && (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1);

    logic [DATA_WIDTH-1:0] rd_shift_r;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_shift_r <= '0;
        else if (rd_capture_valid && rd_burst_ctr != WORD_BEATS[1:0] - 1'b1)
            rd_shift_r[(rd_burst_ctr+1)*DQ_WIDTH-1 -: DQ_WIDTH] <= ddr_dq_i;
    end

    // Final beat combines the just-arrived ddr_dq_i directly with
    // the earlier beats already shifted into rd_shift_r -- avoids
    // a spurious extra cycle of latency for the last beat.
    wire [DATA_WIDTH-1:0] rd_word_assembled =
        {ddr_dq_i, rd_shift_r[DATA_WIDTH-DQ_WIDTH-1:0]};

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            rd_wptr <= '0;
        else if (rd_word_complete) begin
            rd_fifo[rd_wptr[FIFO_PTR_W-1:0]] <= '{data: rd_word_assembled, aux: rd_aux_r};
            rd_wptr <= rd_wptr + 1'b1;
        end

    // Pop read responses to wb_port
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            rd_rptr <= '0;
        else if (rd_rsp_valid)
            rd_rptr <= rd_rptr + 1'b1;

    assign rd_rsp_valid = ~rd_empty;
    assign rd_rsp_data  = rd_fifo[rd_rptr[FIFO_PTR_W-1:0]].data;
    assign rd_rsp_aux   = rd_fifo[rd_rptr[FIFO_PTR_W-1:0]].aux;

    // ================================================================
    // SVA -- simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // DP-001: Write buffer never overflows
    property p_wr_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        (wr_data_valid && wr_full) |-> 1'b0;
    endproperty
    assert property (p_wr_no_overflow)
        else $error("[DP-001] Write buffer overflow");

    // DP-002: DQ output enable only during WR_DRIVE
    property p_dq_oe_only_drive;
        @(posedge clk) disable iff (!rst_n)
        ddr_dq_oe |-> (wr_state == WR_DRIVE);
    endproperty
    assert property (p_dq_oe_only_drive)
        else $error("[DP-002] DQ OE asserted outside WR_DRIVE");

    // DP-005: Read response valid only when FIFO non-empty
    property p_rd_rsp_valid;
        @(posedge clk) disable iff (!rst_n)
        rd_rsp_valid |-> ~rd_empty;
    endproperty
    assert property (p_rd_rsp_valid)
        else $error("[DP-005] Read response valid with empty FIFO");

    // Coverage
    covergroup cg_dp @(posedge clk);
        option.per_instance = 1;
        cp_wr_drive : coverpoint (wr_state == WR_DRIVE);
        cp_rd_cap   : coverpoint (rd_state == RD_CAPTURE);
        cp_wr_full  : coverpoint wr_full;
        cp_rd_empty : coverpoint rd_empty;
    endgroup
    cg_dp cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule