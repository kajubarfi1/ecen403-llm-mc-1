////////////////////////////////////////////////////////////////////////////////
// Module:    wb_port
// File:      wb_port.sv
// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)
// Generator:     Wishbone Port Interface Generator (Phase 1)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   Wishbone B4 pipelined slave. Backpressure (stall), linear burst (BL8),
//   byte-lane masking, error signalling, auxiliary tag propagation.
//
// Derived: DATA=32 ADDR=29 SEL=4 AUX=4 BURST=8 QUEUE=16
// Validation: WB-001 .. WB-012
////////////////////////////////////////////////////////////////////////////////

module wb_port #(
    parameter DATA_WIDTH     = 32,
    parameter ADDR_WIDTH     = 29,
    parameter SEL_WIDTH      = 4,
    parameter AUX_WIDTH      = 4,
    parameter MAX_BURST_LEN  = 8,
    parameter QUEUE_DEPTH    = 16,
    parameter BURST_CTR_W    = 4,
    parameter TAG_FIFO_DEPTH = 16,
    parameter TAG_PTR_W      = 4,
    parameter WR_TAG_PTR_W   = 4,
    parameter ORD_DEPTH      = 32,
    parameter ORD_PTR_W      = 5
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Wishbone B4 Pipelined Slave
    input  logic                    wb_cyc_i,
    input  logic                    wb_stb_i,
    input  logic                    wb_we_i,
    input  logic [ADDR_WIDTH-1:0]   wb_adr_i,
    input  logic [DATA_WIDTH-1:0]   wb_dat_i,
    input  logic [SEL_WIDTH-1:0]    wb_sel_i,
    input  logic [1:0]              wb_bte_i,
    input  logic [2:0]              wb_cti_i,

    output logic                    wb_ack_o,
    output logic [DATA_WIDTH-1:0]   wb_dat_o,
    output logic                    wb_stall_o,
    output logic                    wb_err_o,

    // Internal -> Command Queue
    output logic                    req_valid,
    output logic                    req_we,
    output logic [ADDR_WIDTH-1:0]   req_addr,
    output logic [DATA_WIDTH-1:0]   req_wdata,
    output logic [SEL_WIDTH-1:0]    req_wmask,
    output logic [AUX_WIDTH-1:0]    req_aux,
    input  logic                    req_ready,

    // Internal <- Data Path
    input  logic                    rsp_valid,
    input  logic [DATA_WIDTH-1:0]   rsp_rdata,
    input  logic [AUX_WIDTH-1:0]    rsp_aux,
    input  logic                    wr_data_ready,

    // Observability only, no fan-in from anything else: true
    // exactly the cycle a READ is being delivered to the host.
    // Exposed so Validation's wb_rsp monitor can qualify on the
    // real per-beat completion instead of on rsp_valid, which
    // (since the HOSTMEM/HOST_002 tag-indexed buffering fix,
    // 2026-11-05/06) no longer coincides with host-visible
    // delivery for a reordered response -- see Validation
    // handoff 2026-11-06 (3).
    output logic                    rd_ack
);

    // CTI / BTE encodings
    localparam logic [2:0] CTI_CLASSIC = 3'b000;
    localparam logic [2:0] CTI_CONST   = 3'b001;
    localparam logic [2:0] CTI_INC     = 3'b010;
    localparam logic [2:0] CTI_END     = 3'b111;
    localparam logic [1:0] BTE_LINEAR  = 2'b00;
    localparam int unsigned ADDR_INC = DATA_WIDTH / 8;

    wire wb_beat = wb_cyc_i & wb_stb_i & ~wb_stall_o;
    logic req_pend;   // skid entry held; req_valid gates it (see Request register)

    // Aux-tag counters (WB-009), declared before tag FIFO --
    // one per kind, not one shared counter. rd_data_buf/wr_buf
    // (below) are addressed directly by a response's/command's own
    // aux value's low bits (HOST_002/HOSTMEM fix, Validation
    // 2026-11-05), which only stays collision-free if each kind's
    // outstanding window has its own tag space: up to
    // RD_BUFFER_DEPTH reads AND, independently, up to
    // WR_BUFFER_DEPTH writes can be outstanding at once (separate
    // backpressure on each side), so one shared counter wraps
    // across both and aliases a read's tag onto a write's (or
    // onto another read's) well before either side's own buffer
    // is actually full.
    logic [AUX_WIDTH-1:0] rd_aux_ctr, wr_aux_ctr;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)                  rd_aux_ctr <= '0;
        else if (wb_beat && !wb_we_i) rd_aux_ctr <= rd_aux_ctr + 1'b1;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)                  wr_aux_ctr <= '0;
        else if (wb_beat &&  wb_we_i) wr_aux_ctr <= wr_aux_ctr + 1'b1;

    // Tag FIFO -- tracks outstanding read requests
    logic [AUX_WIDTH-1:0] tag_mem [0:TAG_FIFO_DEPTH-1];
    logic [TAG_PTR_W:0]   tag_wr, tag_rd;
    wire  [TAG_PTR_W:0]   tag_cnt  = tag_wr - tag_rd;
    wire                   tag_full = (tag_cnt == TAG_FIFO_DEPTH[TAG_PTR_W:0]);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) tag_wr <= '0;
        else if (wb_beat && !wb_we_i) begin
            tag_mem[tag_wr[TAG_PTR_W-1:0]] <= rd_aux_ctr;
            tag_wr <= tag_wr + 1'b1;
        end

    // tag_rd's own update is declared further down (Acknowledge),
    // after rd_ack exists to gate it: tag_rd must now advance on
    // DELIVERY (rd_ack), not on bare arrival (rsp_valid) -- it is
    // the oldest-outstanding-read pointer, and that identity has
    // to persist until the data is actually handed to the host,
    // not just until some response (possibly a later read's)
    // shows up (HOSTMEM fix, Validation 2026-11-05).

    // Ack-ordering tracker (HOST_002: host_interface.
    // ack_ordering = in_request_order) -- one entry per accepted
    // beat, read(1) or write(0), in acceptance order. Sized
    // RD_BUFFER_DEPTH+WR_BUFFER_DEPTH: it can never overflow,
    // since each side's OWN backpressure (tag_full below,
    // wr_data_ready/WB-012) already caps that side's own
    // outstanding count before this would. ord_wr/ord_mem's push
    // only needs wb_beat, defined here; ord_rd's pop needs
    // ord_pop, which needs wr_ack_deliver/rd_ack -- declared
    // here, updated in Acknowledge below.
    logic               ord_mem [0:ORD_DEPTH-1];
    logic [ORD_PTR_W:0] ord_wr, ord_rd;
    wire  [ORD_PTR_W:0] ord_cnt     = ord_wr - ord_rd;
    wire                 ord_empty   = (ord_cnt == 0);
    wire                 ord_head_rd = ord_mem[ord_rd[ORD_PTR_W-1:0]];
    // Full: stall the next beat (Validation addendum 19, 2026-11-09).
    // The sizing argument above holds for reads (tag_full) but not for
    // writes: a write's ord_mem entry lives until it is acknowledged
    // at the head, while its wr_buf slot frees as soon as the WR
    // issues, so behind one slow read the port kept accepting writes
    // until ord_cnt passed ORD_DEPTH (WB-011 x319 on path_07 of drop
    // 2a18a7929dce; 9 of 110 read responses lost, HOST_002 x15).
    wire                 ord_full    = (ord_cnt == ORD_DEPTH[ORD_PTR_W:0]);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ord_wr <= '0;
        else if (wb_beat) begin
            ord_mem[ord_wr[ORD_PTR_W-1:0]] <= ~wb_we_i;
            ord_wr <= ord_wr + 1'b1;
        end

    // Direct-mapped read-response buffer, keyed by the response's
    // OWN tag (rsp_aux), not arrival order: the DRAM-side
    // scheduler can answer a later-accepted read before an
    // earlier one (FR-FCFS row-hit priority), so a response's
    // tag -- not the order it shows up in -- says whose slot it
    // is (HOSTMEM fix, Validation 2026-11-05). Collision-free
    // because rd_aux_ctr is now read-only (see above) and
    // AUX_WIDTH is validated wide enough to index TAG_FIFO_DEPTH.
    logic [DATA_WIDTH-1:0] rd_data_buf   [0:TAG_FIFO_DEPTH-1];
    logic                  rd_data_valid [0:TAG_FIFO_DEPTH-1];

    // Per-tag 'awaiting response' bit (DATA_001/HOST_002, Validation
    // 2026-11-06): set when a read is accepted under that tag,
    // cleared when its FIRST response is taken. Only a response
    // whose tag is actually awaiting one is accepted (rsp_take);
    // a duplicate, late or unmatched response used to set a
    // stale rd_data_valid bit, so the NEXT read reusing that tag
    // acked immediately with old/X data and every later pairing
    // drifted by one.
    logic                  rd_pending    [0:TAG_FIFO_DEPTH-1];
    wire  [TAG_PTR_W-1:0]  rsp_idx  = rsp_aux[TAG_PTR_W-1:0];
    wire                   rsp_take = rsp_valid && rd_pending[rsp_idx];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < TAG_FIFO_DEPTH; i++) rd_pending[i] <= 1'b0;
        end else begin
            if (rsp_take)              rd_pending[rsp_idx] <= 1'b0;
            if (wb_beat && !wb_we_i)   rd_pending[rd_aux_ctr[TAG_PTR_W-1:0]] <= 1'b1;
        end
    end

    // Reset to 0, not left uninitialized: wb_dat_o reads
    // rd_data_buf[rd_head_idx] continuously, not only when
    // actually acking, so an unwritten slot's X would otherwise
    // show up on the port even while idle -- caught live
    // (2026-11-06): Validation's monitor flagged X/Z on wb_dat_o
    // before any read had used that slot.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            for (int i = 0; i < TAG_FIFO_DEPTH; i++) rd_data_buf[i] <= '0;
        end else if (rsp_take) begin
            rd_data_buf[rsp_idx] <= rsp_rdata;
        end

    // Stall generation (WB-005)
    //
    // Stalls on req_valid && !req_ready, not on !req_ready alone: a
    // beat accepted into the (now-held) req_* skid register below is
    // safe to accept even if the queue isn't ready yet this same
    // cycle, because the skid holds it unchanged until it is. Gating
    // on !req_ready alone (the old condition) ignored whether the
    // skid was already occupied: a beat accepted while req_ready was
    // momentarily high got registered into req_*, and if the queue
    // filled before that registered req_valid was ever re-checked,
    // the next beat's data silently overwrote it on the following
    // cycle -- a write the host already got acked for, or a read
    // that never comes back (Validation addendum 9, 2026-10-28,
    // finding 1).
    always_comb begin
        wb_stall_o = 1'b0;
        if (req_pend && !(req_valid && req_ready)) wb_stall_o = 1'b1;
        if (!wb_we_i && tag_full && wb_stb_i)  wb_stall_o = 1'b1;
        if (wb_stb_i && ord_full)              wb_stall_o = 1'b1;  // ack tracker full (addendum 19)
        // HOST_WRITE_BUFFER_BACKPRESSURE ('port_stalls_on_full',
        // 2026-11-05) is carried by the skid gate above: a pending
        // write is not presented to the queue (req_valid low) until
        // data_path can take its word, and the stall on a pending,
        // unconsumed request holds the bus. The former beat-level
        // term on !wr_data_ready read the PENDING request's tag, not
        // the beat's, and would have stalled every write behind the
        // one just pushed once wr_data_ready became per-slot
        // (addendum 19, 2026-11-09).
    end

    // Burst tracker (WB-003, WB-004)
    logic                   burst_active;
    logic [BURST_CTR_W-1:0] burst_cnt;
    logic [ADDR_WIDTH-1:0]  burst_nxt_addr;
    logic                   burst_we;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            burst_active   <= 1'b0;
            burst_cnt      <= '0;
            burst_nxt_addr <= '0;
            burst_we       <= 1'b0;
        end else if (wb_beat) begin
            if (!burst_active && wb_cti_i == CTI_INC) begin
                burst_active   <= 1'b1;
                burst_cnt      <= 'd1;
                burst_nxt_addr <= wb_adr_i + ADDR_INC[ADDR_WIDTH-1:0];
                burst_we       <= wb_we_i;
            end else if (burst_active) begin
                burst_cnt      <= burst_cnt + 1'b1;
                burst_nxt_addr <= burst_nxt_addr + ADDR_INC[ADDR_WIDTH-1:0];
                if (wb_cti_i == CTI_END ||
                    burst_cnt == BURST_CTR_W'(MAX_BURST_LEN - 1)) begin
                    burst_active <= 1'b0;
                    burst_cnt    <= '0;
                end
            end
        end else if (!wb_cyc_i) begin
            burst_active <= 1'b0;
            burst_cnt    <= '0;
        end
    end

    // Request output (WB-001, WB-002)
    //
    // One-entry skid register, not a bare one-cycle pulse: req_valid
    // now holds and req_* stays unchanged across cycles where
    // req_ready is low, instead of unconditionally clearing/
    // overwriting one cycle after wb_beat regardless of whether the
    // queue actually took it (Validation addendum 9, 2026-10-28,
    // finding 1 -- the drop this fixes). wb_stall_o above keeps a new
    // wb_beat from landing while the skid is occupied and not about
    // to clear, so this can never have two different requests'
    // data racing for the same slot: a new beat is only ever
    // latched when the skid is empty, or in the same cycle the
    // entry it holds is actually consumed (req_valid && req_ready),
    // which pipelines straight through with no bubble.
    // req_valid is the skid entry (req_pend) gated on the data path
    // being able to take a write's word (Validation addendum 19,
    // 2026-11-09): wr_data_valid is wired as req_valid && req_we &&
    // enq_ready, so a request the queue took while data_path refused
    // the word (its tag's slot still holding an unissued write) would
    // leave the queue holding a write with no data. Held here instead,
    // the queue never sees it until the word can land; a read is
    // never gated. wr_data_ready only rises while a write is pending
    // (no other push can happen), so a gated request never withdraws.
    assign req_valid = req_pend && (!req_we || wr_data_ready);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_pend <= 1'b0; req_we <= 1'b0; req_addr <= '0;
            req_wdata <= '0; req_wmask <= '0; req_aux <= '0;
        end else if (req_valid && req_ready) begin
            // Consumed this cycle: load the next beat straight
            // through if one is arriving, else go empty.
            if (wb_beat) begin
                req_we    <= wb_we_i;
                req_addr  <= wb_adr_i;
                req_wdata <= wb_dat_i;
                req_wmask <= wb_sel_i;
                req_aux   <= wb_we_i ? wr_aux_ctr : rd_aux_ctr;
            end else begin
                req_pend <= 1'b0;
            end
        end else if (!req_pend && wb_beat) begin
            // Skid was empty; latch the new beat.
            req_pend <= 1'b1;
            req_we    <= wb_we_i;
            req_addr  <= wb_adr_i;
            req_wdata <= wb_dat_i;
            req_wmask <= wb_sel_i;
            req_aux   <= wb_we_i ? wr_aux_ctr : rd_aux_ctr;
        end
        // else: req_pend and not consumed -- hold everything; wb_stall_o
        // guarantees no wb_beat landed this cycle to race it.
    end

    // Acknowledge (WB-002, WB-008: HOST_002, host_interface.
    // ack_ordering = in_request_order)
    //
    // Acks are delivered strictly in request-acceptance order,
    // kind included: only the head of ord_mem may ack. A write
    // head acks immediately -- matches the original one-cycle-
    // after-acceptance timing when nothing is ahead of it, same
    // as the old wr_ack_pending design. A read head acks once
    // its OWN tagged data is available in rd_data_buf, not
    // whenever any response arrives -- that distinction is
    // exactly what let a later-accepted read's data answer an
    // earlier one's slot (HOSTMEM: Validation, 2026-11-05).
    // This also folds in HOST_001 (Validation, 2026-10-29,
    // addendum 11): a write below ord_mem's head simply cannot
    // ack early, so the write-vs-read-ack collision that bug
    // was about cannot recur structurally, not just by counting.
    wire [TAG_PTR_W-1:0] rd_head_idx = tag_mem[tag_rd[TAG_PTR_W-1:0]][TAG_PTR_W-1:0];
    // A response landing exactly for the current head bypasses
    // rd_data_buf and acks the SAME cycle it arrives, same
    // zero-added-latency timing as the original rd_ack=rsp_valid
    // design. rd_data_valid only takes its new value the NEXT
    // edge, so without this bypass EVERY read -- not just a
    // reordered one -- would wait one extra cycle to ack, which
    // is exactly what Validation's HOST_002 caught live
    // (2026-11-06): it expects a read's ack to coincide with
    // rsp_valid, true for the original design and now true again
    // except on the genuinely-reordered path, which still buffers.
    // Gated by rsp_take (not raw rsp_valid): only a response its
    // tag is still awaiting may bypass.
    wire rsp_is_head = rsp_take && (rsp_idx == rd_head_idx);
    wire                 wr_ack_deliver = !ord_empty && !ord_head_rd;
    // rd_ack is an output port (see the header) -- assign, not
    // wire, since it's already declared by the port list.
    assign               rd_ack         = !ord_empty &&  ord_head_rd &&
                                           (rd_data_valid[rd_head_idx] || rsp_is_head);
    wire                 ord_pop        = wr_ack_deliver | rd_ack;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ord_rd <= '0;
        else if (ord_pop) ord_rd <= ord_rd + 1'b1;

    // Deferred from the tag FIFO above: tag_rd now advances on
    // DELIVERY (rd_ack), not bare arrival, so it keeps naming the
    // oldest outstanding read until that read is actually answered.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) tag_rd <= '0;
        else if (rd_ack) tag_rd <= tag_rd + 1'b1;

    // rd_data_valid: set when a response for that tag arrives,
    // cleared when that tag's slot is actually delivered. The
    // common case (rsp_is_head bypass) sets and clears the SAME
    // index in the SAME cycle -- the clear (textually later, so
    // it wins) is correct: the data went straight to wb_dat_o via
    // the bypass mux, so the buffer slot was never the delivery
    // path and has nothing worth marking valid. Any OTHER
    // same-index collision (two responses for one still-
    // outstanding tag) is now filtered by rsp_take/rd_pending.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < TAG_FIFO_DEPTH; i++) rd_data_valid[i] <= 1'b0;
        end else begin
            if (rsp_take)  rd_data_valid[rsp_idx]               <= 1'b1;
            if (rd_ack)    rd_data_valid[rd_head_idx]           <= 1'b0;
        end
    end

    assign wb_ack_o = wr_ack_deliver | rd_ack;
    assign wb_dat_o = rsp_is_head ? rsp_rdata : rd_data_buf[rd_head_idx];

    // Error detection (WB-007)
    logic err_r;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) err_r <= 1'b0;
        else begin
            err_r <= 1'b0;
            if (wb_cyc_i && wb_stb_i) begin
                if (burst_active && (wb_we_i != burst_we)) err_r <= 1'b1;
                if (|wb_adr_i[$clog2(ADDR_INC)-1:0])      err_r <= 1'b1;
            end
        end
    end
    assign wb_err_o = err_r;

    // SVA -- simulation only
    // synopsys translate_off
    // synthesis translate_off

    property p_stall_hold;
        @(posedge clk) disable iff (!rst_n)
        (wb_cyc_i && wb_stb_i && wb_stall_o) |=> (wb_cyc_i && wb_stb_i);
    endproperty
    assert property (p_stall_hold)
        else $error("[WB-005] master released request during stall");

    // WB-009: a response must land on a tag whose slot isn't
    // already holding an earlier, undelivered response -- the
    // real invariant once out-of-order delivery is expected
    // (Validation, 2026-11-05: the old 'responses arrive in
    // acceptance order' version of this check fired 66 times in
    // practice, because that assumption is false under FR-FCFS
    // reordering -- this replaces it, not patches it).
    property p_tag;
        @(posedge clk) disable iff (!rst_n)
        rsp_take |-> !rd_data_valid[rsp_idx];
    endproperty
    assert property (p_tag)
        else $error("[WB-009] response landed on a tag already holding undelivered data");

    // WB-013: every response should match a read still awaiting
    // one; anything else is ignored by rsp_take, flagged here.
    property p_rsp_matches_pending;
        @(posedge clk) disable iff (!rst_n)
        rsp_valid |-> rd_pending[rsp_idx];
    endproperty
    assert property (p_rsp_matches_pending)
        else $warning("[WB-013] response for a tag with no read awaiting it -- ignored");

    property p_burst_len;
        @(posedge clk) disable iff (!rst_n)
        burst_active |-> (burst_cnt < BURST_CTR_W'(MAX_BURST_LEN));
    endproperty
    assert property (p_burst_len)
        else $error("[WB-003/004] burst exceeded MAX_BURST_LEN");

    property p_tag_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (tag_cnt <= TAG_FIFO_DEPTH[TAG_PTR_W:0]);
    endproperty
    assert property (p_tag_no_overflow)
        else $error("[WB-005] tag FIFO overflow");

    property p_sel_nonzero_write;
        @(posedge clk) disable iff (!rst_n)
        (wb_beat && wb_we_i) |-> (|wb_sel_i);
    endproperty
    assert property (p_sel_nonzero_write)
        else $warning("[WB-006] write with zero sel");

    // WB-010: an accepted request held by backpressure never changes
    // or disappears before the queue takes it (VP_FLOW_001 -- no
    // accepted request may be lost while back-pressure is asserted)
    property p_req_held_stable;
        @(posedge clk) disable iff (!rst_n)
        (req_pend && !(req_valid && req_ready)) |=> (req_pend && $stable(req_we) &&
            $stable(req_addr) && $stable(req_wdata) &&
            $stable(req_wmask) && $stable(req_aux));
    endproperty
    assert property (p_req_held_stable)
        else $error("[WB-010] accepted request changed or dropped while queue wasn't ready");

    // WB-011: the ack-ordering tracker can never overflow -- ord_full
    // stalls the next beat (addendum 19, 2026-11-09); before that, each
    // side's own backpressure (tag_full, wr_data_ready) already
    // caps that side's outstanding count below ORD_DEPTH's share
    // for it, so this should be unreachable by construction; it
    // is still checked at runtime (same shape as p_tag_no_overflow
    // above, for ord_mem instead of tag_mem).
    property p_wr_ack_no_wrap;
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (ord_cnt <= ORD_DEPTH[ORD_PTR_W:0]);
    endproperty
    assert property (p_wr_ack_no_wrap)
        else $error("[WB-011] ack-ordering tracker overflow -- an ack would be dropped");

    // WB-012: a pending write is held (bus stalled, not presented to
    // the queue) while the write buffer cannot take its word
    // (HOST_WRITE_BUFFER_BACKPRESSURE; per-slot since 2026-11-09)
    property p_wr_backpressure;
        @(posedge clk) disable iff (!rst_n)
        (req_pend && req_we && !wr_data_ready) |-> (wb_stall_o && !req_valid);
    endproperty
    assert property (p_wr_backpressure)
        else $error("[WB-012] write beat accepted (or not stalled) while wr_data_ready was low");

    covergroup cg_wb @(posedge clk);
        option.per_instance = 1;
        cp_single_rd  : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_CLASSIC);
        cp_single_wr  : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_CLASSIC);
        cp_burst_rd   : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_INC);
        cp_burst_wr   : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_INC);
        cp_burst_end  : coverpoint (wb_beat && wb_cti_i == CTI_END);
        cp_stall      : coverpoint wb_stall_o;
        cp_err        : coverpoint wb_err_o;
        cp_backtoback : coverpoint (wb_ack_o && wb_beat);
        cp_tag_full   : coverpoint tag_full;
    endgroup
    cg_wb cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule