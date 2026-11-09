////////////////////////////////////////////////////////////////////////////////
// Module:    cmd_queue
// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)
// Generator:     Command Queue Generator (Phase 3)
//
// 16-deep command queue. Accepts decoded requests from addr_decoder,
// presents entries to the scheduler via a lookahead window, hiding a
// request behind an older one to the same address (RAW/WAR/WAW) and
// flagging the oldest request that has waited STARVE_CYCLES (entry_urgent).
// Slot store with per-entry valid bits, enqueue on push, dequeue on grant.
////////////////////////////////////////////////////////////////////////////////

module cmd_queue #(
    parameter DEPTH     = 16,
    parameter IDX_BITS  = 4,
    parameter ROW_BITS  = 15,
    parameter COL_BITS  = 10,
    parameter BANK_BITS = 3,
    parameter AUX_WIDTH = 4,
    parameter STARVE_CYCLES = 128
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── Enqueue interface (from addr_decoder / wb_port) ──
    input  logic                    enq_valid,
    output logic                    enq_ready,
    input  logic [ROW_BITS-1:0]     enq_row,
    input  logic [COL_BITS-1:0]     enq_col,
    input  logic [BANK_BITS-1:0]    enq_bank,
    input  logic                    enq_we,         // 1=write, 0=read
    input  logic [AUX_WIDTH-1:0]    enq_aux,        // tag / transaction ID

    // ── Dequeue interface (from scheduler) ──
    input  logic                    deq_grant,      // scheduler grants this entry
    input  logic [IDX_BITS-1:0]     deq_idx,        // which entry to dequeue

    // ── Lookahead window (to scheduler) ──
    output logic [DEPTH-1:0]        entry_valid,
    output logic [ROW_BITS-1:0]     entry_row   [DEPTH],
    output logic [COL_BITS-1:0]     entry_col   [DEPTH],
    output logic [BANK_BITS-1:0]    entry_bank  [DEPTH],
    output logic                    entry_we    [DEPTH],
    output logic [AUX_WIDTH-1:0]    entry_aux   [DEPTH],
    output logic [DEPTH-1:0]        entry_urgent,   // one-hot: oldest entry past STARVE_CYCLES (or 0)

    // ── Status ──
    output logic                    queue_full,
    output logic                    queue_empty,
    output logic [IDX_BITS:0]       queue_count     // 0..DEPTH
);

    // ════════════════════════════════════════════════════
    // Storage
    // ════════════════════════════════════════════════════
    logic [ROW_BITS-1:0]    mem_row   [DEPTH];
    logic [COL_BITS-1:0]    mem_col   [DEPTH];
    logic [BANK_BITS-1:0]   mem_bank  [DEPTH];
    logic                   mem_we    [DEPTH];
    logic [AUX_WIDTH-1:0]   mem_aux   [DEPTH];
    logic [DEPTH-1:0]       mem_valid;

    // Count
    logic [IDX_BITS:0] count;

    assign queue_count = count;
    assign queue_full  = (count == DEPTH);
    assign queue_empty = (count == '0);
    assign enq_ready   = !queue_full;

    // ════════════════════════════════════════════════════
    // Same-address ordering (Validation addendum 19, 2026-11-09,
    // ADDRORDER/SAME_ADDRESS_HOST_ORDER on path_18 of drop 2a18a7929dce:
    // a read reached DDR 40 ns before the older write to its address and
    // the host read stale data). The scheduler may reorder across
    // addresses; two requests to the SAME bank/row/column with a write on
    // either side (RAW, WAR, WAW) must reach the memory in host order. The
    // queue knows arrival order, so it enforces it here: an entry is hidden
    // from the lookahead window while an older conflicting entry is still
    // queued. conf[s][j] = 1 when slot s was enqueued while slot j held an
    // older conflicting request; the hazard lasts as long as j is valid,
    // and conf[*][j] is cleared when j dequeues so a later occupant of j
    // can never be mistaken for the older one. The oldest conflicting entry
    // is never hidden, so a hidden entry always eventually surfaces.
    // ════════════════════════════════════════════════════
    logic [DEPTH-1:0] conf [DEPTH];
    logic [DEPTH-1:0] enq_conf;
    logic [DEPTH-1:0] hazard;
    always_comb begin
        for (int j = 0; j < DEPTH; j++)
            enq_conf[j] = mem_valid[j] && (mem_bank[j] == enq_bank) &&
                          (mem_row[j] == enq_row) && (mem_col[j] == enq_col) &&
                          (enq_we || mem_we[j]);
        for (int i = 0; i < DEPTH; i++)
            hazard[i] = |(conf[i] & mem_valid);
    end

    // ════════════════════════════════════════════════════
    // Anti-starvation (Validation, 2026-11-09): FR-FCFS has no age limit, so
    // under saturation a request can sit while newer row hits keep winning
    // (480 cycles observed). Each entry ages (saturating at STARVE_CYCLES);
    // the OLDEST visible entry that has reached that age is flagged on
    // entry_urgent and the scheduler serves it before any tier it is
    // eligible for, while the other entries stay visible so other banks
    // keep working. (Hiding everything but the starved entries was not
    // enough -- after init most of the queue is past the threshold and
    // FR-FCFS among them starved the same one again, drop 2867a40acc70;
    // hiding everything but the oldest serialised the drain, 85cf24c69ba7.)
    // older[i][j] = entry j was already queued when i arrived (set at
    // enqueue, cleared when j dequeues), a strict total order over the live
    // entries. A starved entry hidden by the same-address rule has an older
    // conflicting entry that is itself at least as old and visible.
    // ════════════════════════════════════════════════════
    localparam int AGE_W = $clog2(STARVE_CYCLES + 1);
    logic [AGE_W-1:0] age   [DEPTH];
    logic [DEPTH-1:0] older [DEPTH];
    logic [DEPTH-1:0] starved, visible, starved_visible, oldest_starved;
    always_comb begin
        for (int i = 0; i < DEPTH; i++)
            starved[i] = mem_valid[i] && (age[i] == AGE_W'(STARVE_CYCLES));
        visible         = mem_valid & ~hazard;
        starved_visible = starved & visible;
        for (int i = 0; i < DEPTH; i++)
            oldest_starved[i] = starved_visible[i] && ~(|(older[i] & starved_visible));
    end

    // Output lookahead
    always_comb begin
        entry_valid  = visible;
        entry_urgent = oldest_starved;
        for (int i = 0; i < DEPTH; i++) begin
            entry_row[i]  = mem_row[i];
            entry_col[i]  = mem_col[i];
            entry_bank[i] = mem_bank[i];
            entry_we[i]   = mem_we[i];
            entry_aux[i]  = mem_aux[i];
        end
    end

    // ════════════════════════════════════════════════════
    // Enqueue / Dequeue logic
    // ════════════════════════════════════════════════════
    // Find first free slot for enqueue
    logic [IDX_BITS-1:0] free_slot;
    logic                free_found;

    always_comb begin
        free_slot  = '0;
        free_found = 1'b0;
        for (int i = 0; i < DEPTH; i++) begin
            if (!mem_valid[i] && !free_found) begin
                free_slot  = i[IDX_BITS-1:0];
                free_found = 1'b1;
            end
        end
    end

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem_valid <= '0;
            count     <= '0;
            for (i = 0; i < DEPTH; i++) begin
                mem_row[i]  <= '0;
                mem_col[i]  <= '0;
                mem_bank[i] <= '0;
                mem_we[i]   <= '0;
                mem_aux[i]  <= '0;
                conf[i]     <= '0;
                age[i]      <= '0;
                older[i]    <= '0;
            end
        end else begin
            // Age every queued entry (saturating); an enqueue below restarts
            // its slot at zero.
            for (i = 0; i < DEPTH; i++)
                if (mem_valid[i] && age[i] != AGE_W'(STARVE_CYCLES)) age[i] <= age[i] + 1'b1;

            // Dequeue
            if (deq_grant && mem_valid[deq_idx]) begin
                mem_valid[deq_idx] <= 1'b0;
                count <= count - 1'b1;
            end

            // Enqueue
            if (enq_valid && enq_ready && free_found) begin
                mem_row[free_slot]   <= enq_row;
                mem_col[free_slot]   <= enq_col;
                mem_bank[free_slot]  <= enq_bank;
                mem_we[free_slot]    <= enq_we;
                mem_aux[free_slot]   <= enq_aux;
                mem_valid[free_slot] <= 1'b1;
                conf[free_slot]      <= enq_conf;
                age[free_slot]       <= '0;
                older[free_slot]     <= mem_valid;
                count <= count + 1'b1;
            end

            // The dequeued slot is nobody's older conflict any more (after
            // the enqueue above, so a same-cycle enqueue does not keep it).
            if (deq_grant && mem_valid[deq_idx])
                for (i = 0; i < DEPTH; i++) begin
                    conf[i][deq_idx]  <= 1'b0;
                    older[i][deq_idx] <= 1'b0;
                end

            // Simultaneous enq + deq: adjust count
            if (enq_valid && enq_ready && free_found && deq_grant && mem_valid[deq_idx])
                count <= count;  // net zero
        end
    end

endmodule
