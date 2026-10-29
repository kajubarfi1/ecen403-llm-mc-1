////////////////////////////////////////////////////////////////////////////////
// Module:    data_path
// File:      data_path.sv
// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)
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
// Validation: DP-001 .. DP-014
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
    //
    // Mirrors the read side exactly (see the comment above Read
    // capture and deserialization below for the full reasoning):
    // the DRAM expects write data CWL cycles after the WR command
    // was issued, not CWL cycles after our engine gets around to
    // it, so a queued command's wait is anchored to wr_cycle_ctr AT
    // ISSUE (Validation addendum 9, 2026-10-28, finding 2, plus the
    // same one-cycle regression addendum 10 found on the read side,
    // 2026-10-29 -- a bare wr_pend_cnt counter has the identical
    // one-cycle-late problem a registered FIFO does). Three paths:
    //  - BYPASS (wr_bypass): engine idle, nothing queued -- same
    //    cycle, zero added latency, matching the original design.
    //  - QUEUED (WR_IDLE): arrived while busy; its deadline has
    //    arrived -- drive now, no WR_WAIT needed.
    //  - CHAINED (WR_DRIVE's own exit): the next queued write's
    //    deadline arrives right as this one's last beat drives --
    //    go straight into its drive instead of detouring through
    //    WR_IDLE, which would cost the one cycle neither this nor
    //    the read side's capture window can spare. The scheduler's
    //    CAS spacing (cas_spacing_ctr, scheduler_gen.py) keeps
    //    deadlines from arriving faster than the engine can drain
    //    them, so chaining is the common case for back-to-back
    //    writes, not an edge case.

    typedef enum logic [1:0] {
        WR_IDLE   = 2'd0,
        WR_WAIT   = 2'd1,   // waiting CWL latency -- bypass path only
        WR_DRIVE  = 2'd2    // driving DQ pins
    } wr_state_t;

    wr_state_t wr_state;
    logic [7:0] wr_lat_ctr;        // CWL countdown -- bypass path only
    logic [1:0] wr_burst_ctr;       // burst beat counter
    logic [DATA_WIDTH-1:0] wr_dat_r; // latched write data
    logic [SEL_WIDTH-1:0]  wr_msk_r; // latched mask

    // Free-running cycle counter, same role as the read side's
    // rd_cycle_ctr.
    logic [31:0] wr_cycle_ctr;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) wr_cycle_ctr <= '0;
        else        wr_cycle_ctr <= wr_cycle_ctr + 1'b1;

    // Controller cycles from issue to the first drive cycle -- same
    // CWL formula the bypass path below uses.
    wire [31:0] wr_wait_cycles = (cfg_CWL_nCK <= CLK_RATIO[7:0])
        ? 32'd1
        : 32'(((cfg_CWL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0])) + 32'd1;

    // Pending-write-command queue: overflow only (a bypassed write
    // never enters it), tracks each queued WR command's deadline.
    // A SEPARATE queue from wr_buf (the write DATA, pushed on
    // wr_data_valid from wb_port, a different event stream) --
    // wr_buf stays the data source, popped in the same order these
    // deadlines are, since both are issue-ordered.
    logic [31:0] wr_pend_deadline [0:RD_FIFO_DEPTH-1];
    logic [FIFO_PTR_W:0] wr_pend_wptr, wr_pend_rptr;
    wire  [FIFO_PTR_W:0] wr_pend_count = wr_pend_wptr - wr_pend_rptr;
    wire                  wr_pend_full  = (wr_pend_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);
    wire                  wr_pend_empty = (wr_pend_count == 0);

    wire wr_bypass = (wr_state == WR_IDLE) && wr_pend_empty && cmd_wr_valid && !wr_empty;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            wr_pend_wptr <= '0;
        else if (cmd_wr_valid && !wr_pend_full && !wr_bypass) begin
            wr_pend_deadline[wr_pend_wptr[FIFO_PTR_W-1:0]] <= wr_cycle_ctr + wr_wait_cycles - 32'd1;
            wr_pend_wptr <= wr_pend_wptr + 1'b1;
        end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_state     <= WR_IDLE;
            wr_lat_ctr   <= '0;
            wr_burst_ctr <= '0;
            wr_rptr      <= '0;
            wr_dat_r     <= '0;
            wr_msk_r     <= '0;
            wr_pend_rptr <= '0;
        end else begin
            case (wr_state)
                WR_IDLE: begin
                    if (!wr_pend_empty && !wr_empty &&
                        (wr_cycle_ctr >= wr_pend_deadline[wr_pend_rptr[FIFO_PTR_W-1:0]])) begin
                        // Queued while busy; its deadline has arrived --
                        // drive now, no separate wait state needed.
                        wr_dat_r     <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].data;
                        wr_msk_r     <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].mask;
                        wr_rptr      <= wr_rptr + 1'b1;
                        wr_pend_rptr <= wr_pend_rptr + 1'b1;
                        wr_state     <= WR_DRIVE;
                        wr_burst_ctr <= '0;
                    end else if (wr_bypass) begin
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
                            // same fix as the read side's rd_lat_ctr (addendum
                            // 4/5, Validation, 2026-10-22/27): ceil(CWL /
                            // CLK_RATIO) - 1, not a hardcoded >> 2 -- the latter
                            // assumed a fixed 4:1 ratio and, like the read side
                            // before its fix, was one cycle off besides.
                            wr_lat_ctr <= (cfg_CWL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] - 1'b1;
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
                    if (wr_burst_ctr == WORD_BEATS[1:0] - 1'b1) begin
                        // Last beat -- chain straight into the next queued
                        // write if its deadline has (or is about to) arrive,
                        // same reasoning as the read side's RD_CAPTURE exit.
                        if (!wr_pend_empty && !wr_empty &&
                            (wr_cycle_ctr + 32'd1 >= wr_pend_deadline[wr_pend_rptr[FIFO_PTR_W-1:0]])) begin
                            wr_dat_r     <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].data;
                            wr_msk_r     <= wr_buf[wr_rptr[FIFO_PTR_W-1:0]].mask;
                            wr_rptr      <= wr_rptr + 1'b1;
                            wr_pend_rptr <= wr_pend_rptr + 1'b1;
                            wr_state     <= WR_DRIVE;
                            wr_burst_ctr <= '0;
                        end else begin
                            wr_state <= WR_IDLE;
                        end
                    end else
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
    // A queue that always adds a cycle before the engine can act is
    // wrong for a read, full stop: the DRAM drives data CL cycles
    // after the RD command was issued, not CL cycles after our
    // internal engine happens to notice the command. The previous
    // version (65dbb0f) routed every read through rd_pend unconditionally,
    // which fixed the drop (Validation addendum 9, finding 2) but
    // shifted every single read's capture window one cycle late --
    // including isolated reads with no contention at all, since a
    // registered FIFO's content isn't visible to its own reader until
    // the cycle after it's pushed (Validation addendum 10, 2026-10-29:
    // 'the capture window is one cycle late ... beat 0 passes before
    // the engine looks and beat 1 lands in slot 0').
    //
    // Two paths now, chosen the moment cmd_rd_valid fires:
    //  - BYPASS (rd_bypass): engine idle, nothing already queued --
    //    handled the same cycle, the same way this design worked
    //    before rd_pend existed. Zero added latency; this is the
    //    common case and where the regression above actually lived.
    //  - QUEUED: engine busy with an earlier read. rd_pend stores
    //    each entry's own deadline -- the absolute cycle (on a
    //    free-running counter) its CL wait elapses, computed from
    //    rd_cycle_ctr AT THE CYCLE IT WAS ISSUED, not recomputed
    //    later. The engine captures once that deadline arrives,
    //    with no separate wait state -- the deadline already prices
    //    in the full CL. The scheduler's CAS spacing (tCCD_eff,
    //    see scheduler_gen.py) keeps the engine from ever actually
    //    falling behind a queued entry's deadline in practice, so
    //    this never needs to 'catch up' across a real burst.

    typedef enum logic [1:0] {
        RD_IDLE    = 2'd0,
        RD_WAIT    = 2'd1,   // waiting CL latency -- bypass path only
        RD_CAPTURE = 2'd2    // capturing DQ data
    } rd_state_t;

    rd_state_t rd_state;
    logic [7:0] rd_lat_ctr;
    logic [1:0] rd_burst_ctr;
    logic [AUX_WIDTH-1:0] rd_aux_r;  // latched aux tag for this read

    // Free-running cycle counter -- never reset mid-run, wide enough
    // that wraparound is not a practical concern -- used only to
    // compute and compare queued-entry deadlines.
    logic [31:0] rd_cycle_ctr;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) rd_cycle_ctr <= '0;
        else        rd_cycle_ctr <= rd_cycle_ctr + 1'b1;

    // Controller cycles from issue to the first capture cycle -- the
    // same CL formula the bypass path below uses, computed once per
    // command at the moment it's queued.
    wire [31:0] rd_wait_cycles = (cfg_CL_nCK <= CLK_RATIO[7:0])
        ? 32'd1
        : 32'(((cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0])) + 32'd1;

    // Pending-read queue: overflow only (a bypassed read never enters
    // it), same RD_FIFO_DEPTH/FIFO_PTR_W sizing as the response FIFO
    // below (an outstanding read can't queue past what the response
    // FIFO could later hold anyway).
    logic [AUX_WIDTH-1:0] rd_pend_aux      [0:RD_FIFO_DEPTH-1];
    logic [31:0]          rd_pend_deadline [0:RD_FIFO_DEPTH-1];
    logic [FIFO_PTR_W:0] rd_pend_wptr, rd_pend_rptr;
    wire  [FIFO_PTR_W:0] rd_pend_count = rd_pend_wptr - rd_pend_rptr;
    wire                  rd_pend_full  = (rd_pend_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);
    wire                  rd_pend_empty = (rd_pend_count == 0);

    wire rd_bypass = (rd_state == RD_IDLE) && rd_pend_empty && cmd_rd_valid;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            rd_pend_wptr <= '0;
        else if (cmd_rd_valid && !rd_pend_full && !rd_bypass) begin
            rd_pend_aux[rd_pend_wptr[FIFO_PTR_W-1:0]]      <= cmd_aux;
            rd_pend_deadline[rd_pend_wptr[FIFO_PTR_W-1:0]] <= rd_cycle_ctr + rd_wait_cycles - 32'd1;
            rd_pend_wptr <= rd_pend_wptr + 1'b1;
        end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_state     <= RD_IDLE;
            rd_lat_ctr   <= '0;
            rd_burst_ctr <= '0;
            rd_aux_r     <= '0;
            rd_pend_rptr <= '0;
        end else begin
            case (rd_state)
                RD_IDLE: begin
                    if (!rd_pend_empty &&
                        (rd_cycle_ctr >= rd_pend_deadline[rd_pend_rptr[FIFO_PTR_W-1:0]])) begin
                        // Queued while busy; its deadline (CL counted from
                        // when IT was issued) has arrived -- capture now,
                        // no separate wait state needed.
                        rd_aux_r     <= rd_pend_aux[rd_pend_rptr[FIFO_PTR_W-1:0]];
                        rd_pend_rptr <= rd_pend_rptr + 1'b1;
                        rd_state     <= RD_CAPTURE;
                        rd_burst_ctr <= '0;
                    end else if (rd_bypass) begin
                        rd_aux_r <= cmd_aux;
                        if (cfg_CL_nCK <= CLK_RATIO[7:0]) begin
                            rd_state     <= RD_CAPTURE;
                            rd_burst_ctr <= '0;
                        end else begin
                            rd_state   <= RD_WAIT;
                            // addendum 4/5 (Validation, 2026-10-22/27): ceil(CL /
                            // CLK_RATIO) alone waited one cycle too long -- the
                            // RD_IDLE -> RD_WAIT transition already spends the cycle
                            // in which the registered command is seen, so the wait
                            // count is one less than the ceiling.
                            rd_lat_ctr <= (cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0] - 1'b1;
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
                    if (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1) begin
                        // Last beat. A real DRAM doesn't pause between back-
                        // to-back bursts, so if the next queued read's deadline
                        // has arrived (or arrives the very next cycle), chain
                        // straight into its capture instead of detouring
                        // through RD_IDLE -- a detour costs a cycle neither
                        // RD_IDLE's own check nor this read's deadline accounts
                        // for, which would silently capture the FOLLOWING
                        // read's beat 1 as if it were this one's, the same
                        // wrong-data shape addendum 10 reported. The +1 looks
                        // one cycle ahead of RD_IDLE's own (unshifted) check
                        // since this decision is made the cycle before the
                        // transition lands, same as every other state change
                        // here.
                        if (!rd_pend_empty &&
                            (rd_cycle_ctr + 32'd1 >= rd_pend_deadline[rd_pend_rptr[FIFO_PTR_W-1:0]])) begin
                            rd_aux_r     <= rd_pend_aux[rd_pend_rptr[FIFO_PTR_W-1:0]];
                            rd_pend_rptr <= rd_pend_rptr + 1'b1;
                            rd_state     <= RD_CAPTURE;
                            rd_burst_ctr <= '0;
                        end else begin
                            rd_state <= RD_IDLE;
                        end
                    end else
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
    // PLAN.md). Low beat first (pack_32_to_16, little-endian):
    // beat 0 (first captured) goes to the LOW DQ_WIDTH bits of
    // the assembled word, matching the write-side packing
    // (wr_dat_r[(wb+1)*DQ_WIDTH-1 -: DQ_WIDTH] with wb=0 driving
    // the low half first). Every beat -- including the final
    // one -- is captured into its own DQ_WIDTH-wide slot at bit
    // position beat_index*DQ_WIDTH, the same positional scheme
    // the write path uses, instead of special-casing the final
    // beat into a fixed top slot via concatenation (which
    // silently assumed WORD_BEATS==2 and got the beat order
    // backwards for the final beat).
    wire rd_capture_valid = (rd_state == RD_CAPTURE);
    wire rd_word_complete = rd_capture_valid && (rd_burst_ctr == WORD_BEATS[1:0] - 1'b1);

    logic [DATA_WIDTH-1:0] rd_shift_r;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_shift_r <= '0;
        else if (rd_capture_valid)
            rd_shift_r[rd_burst_ctr*DQ_WIDTH +: DQ_WIDTH] <= ddr_dq_i;
    end

    // The word is pushed to the FIFO the cycle AFTER the final
    // beat is latched into rd_shift_r (rd_word_complete fires on
    // the final-beat capture cycle itself, but rd_shift_r only
    // updates on the next edge), so delay rd_word_complete and
    // rd_aux_r by one cycle to push the fully-assembled word.
    logic rd_word_complete_d;
    logic [AUX_WIDTH-1:0] rd_aux_push;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_word_complete_d <= 1'b0;
            rd_aux_push        <= '0;
        end else begin
            rd_word_complete_d <= rd_word_complete;
            rd_aux_push        <= rd_aux_r;
        end
    end

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            rd_wptr <= '0;
        else if (rd_word_complete_d) begin
            rd_fifo[rd_wptr[FIFO_PTR_W-1:0]] <= '{data: rd_shift_r, aux: rd_aux_push};
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

    // DP-013: Pending-read queue never overflows (cmd_rd_valid always accepted)
    property p_rd_pend_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        (cmd_rd_valid && rd_pend_full) |-> 1'b0;
    endproperty
    assert property (p_rd_pend_no_overflow)
        else $error("[DP-013] Pending-read queue overflow -- a RD command was dropped");

    // DP-014: Pending-write queue never overflows (cmd_wr_valid always accepted)
    property p_wr_pend_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        (cmd_wr_valid && wr_pend_full) |-> 1'b0;
    endproperty
    assert property (p_wr_pend_no_overflow)
        else $error("[DP-014] Pending-write queue overflow -- a WR command was dropped");

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