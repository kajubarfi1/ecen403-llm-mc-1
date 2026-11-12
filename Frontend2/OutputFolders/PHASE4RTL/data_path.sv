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
// Validation: DP-001 .. DP-015
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
    input  logic [AUX_WIDTH-1:0]    wr_data_aux,      // aux tag for this write's data --
                                                      // addresses wr_buf directly, so a WR
                                                      // command (cmd_aux) always fetches its
                                                      // own write's data regardless of what
                                                      // order the scheduler issues commands in
                                                      // (CONSERVE/WRITE_CMD_TO_BEATS fix,
                                                      // Validation 2026-11-05)
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

    // wr_buf is addressed by each write's own aux tag (low bits),
    // not by wr_wptr/wr_rptr position -- a WR command can be
    // issued out of the order its data was pushed (the FR-FCFS
    // scheduler reorders writes exactly like it reorders reads),
    // so cmd_aux is what actually says whose data to fetch
    // (CONSERVE/WRITE_CMD_TO_BEATS, CONSERVE/WRITE_REQUEST_TO_DATA
    // fix, Validation 2026-11-05). wr_wptr/wr_rptr stay as pure
    // OCCUPANCY counters -- every existing backpressure invariant
    // (wr_data_ready, WB-012, DP-001) is unchanged.
    wr_entry_t wr_buf       [0:RD_FIFO_DEPTH-1];
    logic      wr_buf_valid [0:RD_FIFO_DEPTH-1];
    logic [FIFO_PTR_W:0] wr_wptr, wr_rptr;
    wire  [FIFO_PTR_W:0] wr_count = wr_wptr - wr_rptr;
    wire                  wr_full  = (wr_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);
    wire                  wr_empty = (wr_count == 0);

    // wr_data_ready and the push below are completed further down,
    // after the write FSM -- both need to know whether a pop is
    // happening this very cycle, which only the FSM's own state can
    // say (see wr_pop_this_cycle).

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
    // it, so a queued command's wait is loaded fresh AT ISSUE
    // (Validation addendum 9, 2026-10-28, finding 2, plus the
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

    // Saturating countdown, same reasoning and the same Python-
    // verified design as the read side's rd_pend_wait above --
    // see that comment. wr_head_due_r is the one extra piece: a
    // REGISTERED copy of "the current head of wr_pend has a zero
    // countdown", computed one cycle ahead so wr_data_ready (an
    // output port) never has to combinationally index wr_pend_wait
    // by wr_pend_rptr and compare it itself -- Backend, 2026-11-02:
    // that exact mux-then-compare, on the output path, was the
    // single worst-penalized endpoint on the chip even after the
    // width fix. Checked against the same Python model as the read
    // side (2000 cycles, zero mismatches between wr_head_due_r and
    // a fresh combinational check every single cycle, including
    // through pops that advance which entry is "head").
    //
    // Controller cycles from issue to the first drive cycle -- same
    // CWL formula the bypass path below uses.
    wire [31:0] wr_wait_cycles = (cfg_CWL_nCK <= CLK_RATIO[7:0])
        ? 32'd1
        : 32'(((cfg_CWL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0])) + 32'd1;
    wire [3:0] wr_wait_init = (wr_wait_cycles >= 32'd2) ? 4'(wr_wait_cycles - 32'd2) : 4'd0;

    // Pending-write-command queue: overflow only (a bypassed write
    // never enters it), tracks each queued WR command's countdown.
    // A SEPARATE queue from wr_buf (the write DATA, pushed on
    // wr_data_valid from wb_port, a different event stream). These
    // two streams do NOT stay in lockstep -- the scheduler can issue
    // a later-accepted write's command before an earlier one's (the
    // same FR-FCFS row-hit reordering that affects reads), so
    // wr_pend_aux carries each queued command's own tag (mirroring
    // the read side's rd_pend_aux) and wr_buf is fetched BY that
    // tag below, not by position (CONSERVE/WRITE_CMD_TO_BEATS fix,
    // Validation 2026-11-05 -- this comment used to claim the two
    // queues were issue-ordered together; that was the bug).
    logic [3:0] wr_pend_wait [0:RD_FIFO_DEPTH-1];  // saturating countdown, 0 = due
    logic [AUX_WIDTH-1:0] wr_pend_aux [0:RD_FIFO_DEPTH-1];  // tag of the queued command
    logic [FIFO_PTR_W:0] wr_pend_wptr, wr_pend_rptr;
    wire  [FIFO_PTR_W:0] wr_pend_count = wr_pend_wptr - wr_pend_rptr;
    wire                  wr_pend_full  = (wr_pend_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);
    wire                  wr_pend_empty = (wr_pend_count == 0);
    logic wr_head_due_r;  // declared here, defined after wr_pop_this_cycle exists to read

    wire wr_bypass = (wr_state == WR_IDLE) && wr_pend_empty && cmd_wr_valid && !wr_empty;
    wire wr_pend_push = cmd_wr_valid && !wr_pend_full && !wr_bypass;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            wr_pend_wptr <= '0;
        else if (wr_pend_push)
            wr_pend_wptr <= wr_pend_wptr + 1'b1;

    // Every queued entry's countdown decrements every cycle,
    // independent of queue position -- same reasoning as the read
    // side's rd_pend_wait update.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < RD_FIFO_DEPTH; i++) wr_pend_wait[i] <= '0;
        end else begin
            for (int i = 0; i < RD_FIFO_DEPTH; i++) begin
                if (wr_pend_push && (i == wr_pend_wptr[FIFO_PTR_W-1:0])) begin
                    wr_pend_wait[i] <= wr_wait_init;
                    wr_pend_aux[i]  <= cmd_aux;
                end else if (wr_pend_wait[i] != 0)
                    wr_pend_wait[i] <= wr_pend_wait[i] - 4'd1;
            end
        end
    end

    // NOTE: wr_buf_valid is NOT cleared in this FSM block -- it is
    // driven solely by the write-buffer push block further down
    // (single always_ff driver rule), which clears the popped
    // entry via wr_pop_this_cycle / wr_pop_idx.
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
                    if (!wr_pend_empty && !wr_empty && wr_head_due_r) begin
                        // Queued while busy; its countdown has reached 0 --
                        // drive now, no separate wait state needed. Fetch by
                        // this entry's OWN tag (wr_pend_aux), not by wr_rptr
                        // position -- it may not be the data pushed Nth.
                        wr_dat_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].data;
                        wr_msk_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].mask;
                        wr_rptr      <= wr_rptr + 1'b1;
                        wr_pend_rptr <= wr_pend_rptr + 1'b1;
                        wr_state     <= WR_DRIVE;
                        wr_burst_ctr <= '0;
                    end else if (wr_bypass) begin
                        // Latch data from write buffer. Bypass fires the SAME
                        // cycle as cmd_wr_valid (nothing queued ahead of it),
                        // so this write's own tag is simply this cycle's
                        // cmd_aux -- no wr_pend_aux lookup needed.
                        wr_dat_r <= wr_buf[cmd_aux[FIFO_PTR_W-1:0]].data;
                        wr_msk_r <= wr_buf[cmd_aux[FIFO_PTR_W-1:0]].mask;
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
                        // write if its countdown has reached 0 or will by
                        // next cycle, same reasoning as the read side's
                        // RD_CAPTURE exit. Not registered like wr_head_due_r
                        // above -- this is the rarer back-to-back-chaining
                        // path, not the output port, and the 4-bit compare
                        // here is already an 8x narrower structure than the
                        // 32-bit one Backend measured.
                        if (!wr_pend_empty && !wr_empty &&
                            (wr_pend_wait[wr_pend_rptr[FIFO_PTR_W-1:0]] <= 4'd1)) begin
                            // Fetch by this entry's OWN tag, same as the WR_IDLE
                            // queued path above -- it may not be the data
                            // pushed Nth.
                            wr_dat_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].data;
                            wr_msk_r     <= wr_buf[wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0]].mask;
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

    // wr_data_ready must allow a new push in the same cycle a pop
    // happens, not only when wr_full (a REGISTERED count, this
    // cycle's wr_wptr/wr_rptr) already reads not-full -- without
    // this, a write arriving the instant the buffer is full and also
    // draining this cycle gets refused, because the slot frees up a
    // cycle later than wr_data_ready said no (Validation, 2026-10-29,
    // addendum 11: 1 of 600 write words lost this exact way on
    // refresh-stress traffic). wr_pop_this_cycle mirrors the three
    // places WR_IDLE/WR_DRIVE above pop wr_buf -- the standard
    // full-FIFO same-cycle case, one accept and one release landing
    // together.
    wire wr_pop_this_cycle =
        ((wr_state == WR_IDLE) &&
         ((!wr_pend_empty && !wr_empty && wr_head_due_r) || wr_bypass))
        || ((wr_state == WR_DRIVE) && (wr_burst_ctr == WORD_BEATS[1:0] - 1'b1) &&
            !wr_pend_empty && !wr_empty && (wr_pend_wait[wr_pend_rptr[FIFO_PTR_W-1:0]] <= 4'd1));

    // Which wr_buf entry the pop (if any) frees this cycle: the
    // bypass path fetches by this cycle's cmd_aux; the queued and
    // chained paths fetch by the pending-queue head's own tag.
    // wr_bypass requires wr_pend_empty, so it is mutually exclusive
    // with both other pop paths.
    wire [FIFO_PTR_W-1:0] wr_pop_idx = wr_bypass
        ? cmd_aux[FIFO_PTR_W-1:0]
        : wr_pend_aux[wr_pend_rptr[FIFO_PTR_W-1:0]][FIFO_PTR_W-1:0];

    // Per-slot check, not only occupancy (Validation addendum 19,
    // 2026-11-09, ADDRORDER/..._TAG_REUSE): wr_buf is addressed by the
    // write's own aux, and wb_port's write counter wraps every
    // RD_FIFO_DEPTH writes whether or not the write that last used a
    // tag has issued. Under saturation an old write starves in the
    // queue (FR-FCFS, no age limit) while the count stays below full,
    // so the new word landed in the old write's slot and the old WR
    // later went to DDR with the new data and mask (path_07 on drop
    // 2a18a7929dce: 19 reuses; 405 on each refresh loop). The word is
    // refused while its slot still holds an unissued write, unless
    // that very slot is popped this cycle; wb_port holds the request
    // (req_valid gated on wr_data_ready) until it is taken.
    // always_comb, not a continuous assign: Xcelium re-evaluated the
    // variable-indexed unpacked-array read a cycle late when only the
    // index (wr_data_aux) changed, and the push sampled a stale ready.
    logic wr_slot_busy;
    always_comb
        wr_slot_busy = wr_buf_valid[wr_data_aux[FIFO_PTR_W-1:0]] &&
                       !(wr_pop_this_cycle && (wr_pop_idx == wr_data_aux[FIFO_PTR_W-1:0]));
    assign wr_data_ready = (~wr_full || wr_pop_this_cycle) && !wr_slot_busy;

    // wr_head_due_r's own update -- one cycle behind wr_pop_this_cycle
    // (needed to compute it) and the per-entry countdown decrement
    // above (needed for the fresh-load case below), both declared by
    // this point. Mirrors the verified Python model exactly: the next
    // head is rptr+1 if a pop retires today's head, else rptr
    // unchanged; its value next cycle is a fresh load if it's also
    // the index being pushed into this very cycle (reachable: an
    // empty wr_pend, engine busy, a new command arrives -- wptr and
    // rptr coincide before the push), otherwise the usual decrement-
    // or-saturate.
    wire [FIFO_PTR_W-1:0] wr_pend_head_idx_next =
        wr_pend_rptr[FIFO_PTR_W-1:0] + (wr_pop_this_cycle ? 1'b1 : 1'b0);
    wire wr_pend_head_fresh_load =
        wr_pend_push && (wr_pend_head_idx_next == wr_pend_wptr[FIFO_PTR_W-1:0]);
    wire [3:0] wr_pend_head_wait_next =
        wr_pend_head_fresh_load                      ? wr_wait_init :
        (wr_pend_wait[wr_pend_head_idx_next] != 0)    ? (wr_pend_wait[wr_pend_head_idx_next] - 4'd1) :
                                                         4'd0;
    wire [FIFO_PTR_W:0] wr_pend_count_next =
        wr_pend_count - (wr_pop_this_cycle ? 1'b1 : 1'b0) + (wr_pend_push ? 1'b1 : 1'b0);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            wr_head_due_r <= 1'b0;
        else if (wr_pend_count_next == 0)
            wr_head_due_r <= 1'b0;
        else
            wr_head_due_r <= (wr_pend_head_wait_next == 4'd0);

    // Write buffer push -- stored BY TAG (wr_data_aux), not by
    // wr_wptr position; wr_wptr itself only tracks occupancy now.
    // This is the ONLY always_ff driving wr_buf_valid: the pop's
    // clear comes first, the push's set second, so a push landing
    // on the very slot being freed this cycle stays valid.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_wptr <= '0;
            for (int i = 0; i < RD_FIFO_DEPTH; i++) wr_buf_valid[i] <= 1'b0;
        end else begin
            if (wr_pop_this_cycle)
                wr_buf_valid[wr_pop_idx] <= 1'b0;
            if (wr_data_valid && wr_data_ready) begin
                wr_buf[wr_data_aux[FIFO_PTR_W-1:0]]       <= '{data: wr_data, mask: wr_mask};
                wr_buf_valid[wr_data_aux[FIFO_PTR_W-1:0]] <= 1'b1;
                wr_wptr <= wr_wptr + 1'b1;
            end
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
    //    each entry's own CL wait as a saturating countdown, loaded
    //    AT THE CYCLE IT WAS ISSUED and ticking down every cycle
    //    after regardless of queue position, not recomputed later.
    //    The engine captures once that countdown reaches 0, with no
    //    separate wait state -- the countdown already prices in the
    //    full CL. The scheduler's CAS spacing (tCCD_eff,
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

    // Backend, 2026-11-02: the original design stored each entry's
    // wait as a 32-bit ABSOLUTE timestamp (rd_cycle_ctr, free-
    // running, plus a 32-bit deadline per entry) -- 1,024 flops
    // across both read and write sides that never hold a value past
    // about 5, 27% of the whole chip's flops, and the magnitude
    // comparator landed combinationally on the write side's output
    // port. Measured cost: 99% of the chip's total negative slack
    // and 17% of its die area, isolated by building a width-only
    // variant with everything else byte-identical. A SATURATING
    // COUNTDOWN avoids the problem instead of shrinking it: each
    // entry stores its remaining wait (not an absolute cycle), every
    // entry decrements once per cycle down to 0 and stops -- 'due'
    // is a zero-test, not a magnitude compare, and there's no
    // free-running counter to compare against, so there's nothing to
    // wrap and nothing to be wraparound-safe about. 4 bits covers
    // the full valid CL/CWL/ratio range with room to spare. Checked
    // against a cycle-accurate Python model (isolated due-cycle
    // matching across 5 CL/ratio combinations including both
    // extremes, 5000 cycles of random push/pop traffic with no
    // entry lost or double-popped) before writing this.
    //
    // Controller cycles from issue to the first capture cycle -- the
    // same CL formula the bypass path below uses, computed once per
    // command at the moment it's queued, loaded into the entry's
    // countdown as (wait - 2): the push itself isn't visible to its
    // own reader until the cycle after (same reason as the old
    // design's '- 1'), and the countdown's first decrement doesn't
    // happen until the cycle after THAT -- max(0, ...) saturates the
    // short/bypass-range wait values (1) at an already-due 0 rather
    // than underflowing, so a queued entry with the fastest possible
    // wait is due the first cycle it's visible, same as the bypass
    // path achieves directly.
    wire [31:0] rd_wait_cycles = (cfg_CL_nCK <= CLK_RATIO[7:0])
        ? 32'd1
        : 32'(((cfg_CL_nCK + CLK_RATIO[7:0] - 1'b1) / CLK_RATIO[7:0])) + 32'd1;
    wire [3:0] rd_wait_init = (rd_wait_cycles >= 32'd2) ? 4'(rd_wait_cycles - 32'd2) : 4'd0;

    // Pending-read queue: overflow only (a bypassed read never enters
    // it), same RD_FIFO_DEPTH/FIFO_PTR_W sizing as the response FIFO
    // below (an outstanding read can't queue past what the response
    // FIFO could later hold anyway).
    logic [AUX_WIDTH-1:0] rd_pend_aux  [0:RD_FIFO_DEPTH-1];
    logic [3:0]           rd_pend_wait [0:RD_FIFO_DEPTH-1];  // saturating countdown, 0 = due
    logic [FIFO_PTR_W:0] rd_pend_wptr, rd_pend_rptr;
    wire  [FIFO_PTR_W:0] rd_pend_count = rd_pend_wptr - rd_pend_rptr;
    wire                  rd_pend_full  = (rd_pend_count == RD_FIFO_DEPTH[FIFO_PTR_W:0]);
    wire                  rd_pend_empty = (rd_pend_count == 0);

    wire rd_bypass = (rd_state == RD_IDLE) && rd_pend_empty && cmd_rd_valid;
    wire rd_pend_push = cmd_rd_valid && !rd_pend_full && !rd_bypass;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            rd_pend_wptr <= '0;
        else if (rd_pend_push) begin
            rd_pend_aux[rd_pend_wptr[FIFO_PTR_W-1:0]] <= cmd_aux;
            rd_pend_wptr <= rd_pend_wptr + 1'b1;
        end

    // Every queued entry's countdown decrements every cycle,
    // independent of queue position -- real time passes for an
    // entry whether or not it's at the head, so an entry sitting
    // behind others must still be ticking down the whole time it
    // waits, or it would read as 'due' later than it actually is
    // once it becomes the head.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < RD_FIFO_DEPTH; i++) rd_pend_wait[i] <= '0;
        end else begin
            for (int i = 0; i < RD_FIFO_DEPTH; i++) begin
                if (rd_pend_push && (i == rd_pend_wptr[FIFO_PTR_W-1:0]))
                    rd_pend_wait[i] <= rd_wait_init;
                else if (rd_pend_wait[i] != 0)
                    rd_pend_wait[i] <= rd_pend_wait[i] - 4'd1;
            end
        end
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
                        (rd_pend_wait[rd_pend_rptr[FIFO_PTR_W-1:0]] == 4'd0)) begin
                        // Queued while busy; its countdown (CL counted from
                        // when IT was issued) has reached 0 -- capture now,
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
                        // to-back bursts, so if the next queued read's countdown
                        // has already reached 0, chain straight into its capture
                        // instead of detouring through RD_IDLE -- a detour costs
                        // a cycle neither RD_IDLE's own check nor this read's
                        // countdown accounts for, which would silently capture
                        // the FOLLOWING read's beat 1 as if it were this one's,
                        // the same wrong-data shape addendum 10 reported.
                        // Exactly ==0, not <=1 (Validation, 2026-11-11): a
                        // countdown of 0 seen on this cycle means beat 0 is on
                        // dq NEXT cycle, the same contract RD_IDLE's check uses
                        // (wait==0 seen -> capture next cycle). A countdown of 1
                        // means the next read was issued three cycles after this
                        // one, so a one-cycle bubble separates the bursts;
                        // chaining then captured the idle bubble as beat 0 and
                        // the real beat 0 as beat 1 (random_v2 seeds 5-8 on
                        // path_03: 4 of 400 responses came back as beat0<<16).
                        // RD_IDLE handles the bubble case exactly on time.
                        if (!rd_pend_empty &&
                            (rd_pend_wait[rd_pend_rptr[FIFO_PTR_W-1:0]] == 4'd0)) begin
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

    // DP-001: Write buffer never overflows. wr_data_valid && wr_full
    // is allowed for exactly one reason: wr_pop_this_cycle, the same
    // cycle a slot is also freed (Validation, 2026-10-29, addendum
    // 11) -- that is a push into the slot the pop just vacated, not
    // an overflow. Anything else at wr_full is the real thing.
    property p_wr_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        (wr_data_valid && wr_full && !wr_pop_this_cycle) |-> 1'b0;
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

    // DP-015: a WR command must never be issued before its own
    // write's data has arrived in wr_buf -- the tag-indexed fetch
    // above (CONSERVE/WRITE_CMD_TO_BEATS fix) relies on this: data
    // push (wr_data_valid, host-acceptance order) and command
    // issue (cmd_wr_valid, scheduler order) are independent
    // streams, and by construction issue always lags push (a
    // command can only be issued for an entry already enqueued,
    // and enqueue happens together with the data push) -- checked
    // at runtime rather than only argued, since a future cmd_gen/
    // scheduler latency change could silently break it.
    property p_wr_data_precedes_issue;
        @(posedge clk) disable iff (!rst_n)
        cmd_wr_valid |-> wr_buf_valid[cmd_aux[FIFO_PTR_W-1:0]];
    endproperty
    assert property (p_wr_data_precedes_issue)
        else $error("[DP-015] WR command issued before its data arrived in wr_buf");

    // DP-016: a word is never pushed into a slot that still holds an
    // unissued write (the slot may be popped the same cycle). The
    // defect behind ADDRORDER/..._TAG_REUSE (Validation, 2026-11-09).
    property p_wr_slot_not_overwritten;
        @(posedge clk) disable iff (!rst_n)
        (wr_data_valid && wr_data_ready) |-> (!wr_buf_valid[wr_data_aux[FIFO_PTR_W-1:0]] ||
            (wr_pop_this_cycle && (wr_pop_idx == wr_data_aux[FIFO_PTR_W-1:0])));
    endproperty
    assert property (p_wr_slot_not_overwritten)
        else $error("[DP-016] write word pushed over an unissued write's slot");

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