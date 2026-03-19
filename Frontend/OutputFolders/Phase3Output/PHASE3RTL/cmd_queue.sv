////////////////////////////////////////////////////////////////////////////////
// Module:    cmd_queue
// Generated: 2026-03-19 12:01:05
// Agent:     Command Queue Agent (Phase 3)
//
// 16-deep command queue. Accepts decoded requests from addr_decoder,
// presents oldest entries to scheduler via lookahead window.
// FIFO with per-entry valid bits, enqueue on push, dequeue on grant.
////////////////////////////////////////////////////////////////////////////////

module cmd_queue #(
    parameter DEPTH     = 16,
    parameter IDX_BITS  = 4,
    parameter ROW_BITS  = 15,
    parameter COL_BITS  = 10,
    parameter BANK_BITS = 3,
    parameter AUX_WIDTH = 4
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

    // Output lookahead
    always_comb begin
        entry_valid = mem_valid;
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
            end
        end else begin
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
                count <= count + 1'b1;
            end

            // Simultaneous enq + deq: adjust count
            if (enq_valid && enq_ready && free_found && deq_grant && mem_valid[deq_idx])
                count <= count;  // net zero
        end
    end

endmodule
