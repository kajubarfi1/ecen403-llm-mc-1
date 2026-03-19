////////////////////////////////////////////////////////////////////////////////
// Module:    scheduler
// Generated: 2026-03-19 12:01:05
// Agent:     Scheduler Agent (Phase 3)
//
// FR-FCFS (First-Ready First-Come-First-Served) scheduler.
// Open-page policy: row-hit requests prioritized over row-miss.
// Reads cmd_queue entries and bank_tracker permissions.
// Issues one command per cycle to cmd_gen.
////////////////////////////////////////////////////////////////////////////////

module scheduler #(
    parameter DEPTH     = 16,
    parameter IDX_BITS  = 4,
    parameter ROW_BITS  = 15,
    parameter COL_BITS  = 10,
    parameter BANK_BITS = 3,
    parameter NUM_BANKS = 8,
    parameter AUX_WIDTH = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── From cmd_queue (lookahead) ──
    input  logic [DEPTH-1:0]        q_valid,
    input  logic [ROW_BITS-1:0]     q_row     [DEPTH],
    input  logic [COL_BITS-1:0]     q_col     [DEPTH],
    input  logic [BANK_BITS-1:0]    q_bank    [DEPTH],
    input  logic                    q_we      [DEPTH],
    input  logic [AUX_WIDTH-1:0]    q_aux     [DEPTH],

    // ── From bank_tracker ──
    input  logic [NUM_BANKS-1:0]    bank_is_active,
    input  logic [ROW_BITS-1:0]     bank_open_row [NUM_BANKS],
    input  logic [NUM_BANKS-1:0]    bank_act_allowed,
    input  logic [NUM_BANKS-1:0]    bank_rd_allowed,
    input  logic [NUM_BANKS-1:0]    bank_wr_allowed,
    input  logic [NUM_BANKS-1:0]    bank_pre_allowed,

    // ── From refresh_ctrl ──
    input  logic                    ref_required,
    input  logic                    ref_urgent,
    output logic                    ref_ack,

    // ── Dequeue grant (to cmd_queue) ──
    output logic                    deq_grant,
    output logic [IDX_BITS-1:0]     deq_idx,

    // ── Command output (to cmd_gen) ──
    output logic                    cmd_valid,
    output logic [3:0]              cmd_type,       // ACT/RD/WR/PRE/REF/NOP
    output logic [ROW_BITS-1:0]     cmd_row,
    output logic [COL_BITS-1:0]     cmd_col,
    output logic [BANK_BITS-1:0]    cmd_bank,
    output logic                    cmd_we,
    output logic [AUX_WIDTH-1:0]    cmd_aux
);

    // Command type encoding
    localparam CMD_NOP = 4'd0;
    localparam CMD_ACT = 4'd1;
    localparam CMD_RD  = 4'd2;
    localparam CMD_WR  = 4'd3;
    localparam CMD_PRE = 4'd4;
    localparam CMD_REF = 4'd5;

    // ════════════════════════════════════════════════════
    // Candidate classification
    // ════════════════════════════════════════════════════
    // For each queue entry: is it a row-hit? is it ready for CAS?
    logic [DEPTH-1:0] is_row_hit;
    logic [DEPTH-1:0] is_cas_ready;  // bank active + row hit + timing ok
    logic [DEPTH-1:0] is_act_needed; // bank idle or wrong row

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            logic [BANK_BITS-1:0] b;
            b = q_bank[i];
            is_row_hit[i]   = q_valid[i] && bank_is_active[b] &&
                               (bank_open_row[b] == q_row[i]);
            is_cas_ready[i] = is_row_hit[i] &&
                               (q_we[i] ? bank_wr_allowed[b] : bank_rd_allowed[b]);
            is_act_needed[i] = q_valid[i] && (!bank_is_active[b] ||
                               (bank_open_row[b] != q_row[i]));
        end
    end

    // ════════════════════════════════════════════════════
    // FR-FCFS selection: row-hit CAS > any ACT-needed
    // ════════════════════════════════════════════════════
    logic                    sel_valid;
    logic [IDX_BITS-1:0]     sel_idx;
    logic [3:0]              sel_type;
    logic                    sel_is_ref;

    always_comb begin
        sel_valid  = 1'b0;
        sel_idx    = '0;
        sel_type   = CMD_NOP;
        sel_is_ref = 1'b0;

        // Priority 1: Urgent refresh preempts everything
        if (ref_urgent) begin
            sel_valid  = 1'b1;
            sel_type   = CMD_REF;
            sel_is_ref = 1'b1;
        end
        // Priority 2: Row-hit CAS (first-come = lowest index)
        else begin
            for (int i = 0; i < DEPTH; i++) begin
                if (is_cas_ready[i] && !sel_valid) begin
                    sel_valid = 1'b1;
                    sel_idx   = i[IDX_BITS-1:0];
                    sel_type  = q_we[i] ? CMD_WR : CMD_RD;
                end
            end
            // Priority 3: ACT for row-miss (need PRE first if bank active with wrong row)
            if (!sel_valid) begin
                for (int i = 0; i < DEPTH; i++) begin
                    if (is_act_needed[i] && !sel_valid) begin
                        logic [BANK_BITS-1:0] b;
                        b = q_bank[i];
                        if (bank_is_active[b] && bank_pre_allowed[b]) begin
                            // Need PRE first
                            sel_valid = 1'b1;
                            sel_idx   = i[IDX_BITS-1:0];
                            sel_type  = CMD_PRE;
                        end else if (!bank_is_active[b] && bank_act_allowed[b]) begin
                            // Bank idle, can ACT
                            sel_valid = 1'b1;
                            sel_idx   = i[IDX_BITS-1:0];
                            sel_type  = CMD_ACT;
                        end
                    end
                end
            end
            // Priority 4: Normal refresh (when no other work)
            if (!sel_valid && ref_required) begin
                sel_valid  = 1'b1;
                sel_type   = CMD_REF;
                sel_is_ref = 1'b1;
            end
        end
    end

    // ════════════════════════════════════════════════════
    // Output registration
    // ════════════════════════════════════════════════════
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cmd_valid <= 1'b0;
            cmd_type  <= CMD_NOP;
            cmd_row   <= '0;
            cmd_col   <= '0;
            cmd_bank  <= '0;
            cmd_we    <= 1'b0;
            cmd_aux   <= '0;
            deq_grant <= 1'b0;
            deq_idx   <= '0;
            ref_ack   <= 1'b0;
        end else begin
            cmd_valid <= sel_valid;
            cmd_type  <= sel_type;
            deq_grant <= 1'b0;
            ref_ack   <= 1'b0;

            if (sel_valid) begin
                if (sel_is_ref) begin
                    ref_ack  <= 1'b1;
                    cmd_bank <= '0;
                    cmd_row  <= '0;
                    cmd_col  <= '0;
                    cmd_we   <= 1'b0;
                    cmd_aux  <= '0;
                end else begin
                    cmd_row  <= q_row[sel_idx];
                    cmd_col  <= q_col[sel_idx];
                    cmd_bank <= q_bank[sel_idx];
                    cmd_we   <= q_we[sel_idx];
                    cmd_aux  <= q_aux[sel_idx];
                    // Dequeue only on CAS (RD/WR) — ACT/PRE don't consume entry
                    if (sel_type == CMD_RD || sel_type == CMD_WR) begin
                        deq_grant <= 1'b1;
                        deq_idx   <= sel_idx;
                    end
                end
            end
        end
    end

endmodule
