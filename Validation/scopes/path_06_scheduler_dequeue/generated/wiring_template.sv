    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        deq_grant;
    logic [3:0] deq_idx;

    // ---- Testbench-driven inputs ----
    logic [15:0] q_valid;
    logic [14:0] q_row [0:15];
    logic [9:0] q_col [0:15];
    logic [2:0] q_bank [0:15];
    logic        q_we [0:15];
    logic [3:0] q_aux [0:15];
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [7:0] bank_pre_allowed;
    logic        ref_required;
    logic        ref_urgent;
    logic        enq_valid;
    logic [14:0] enq_row;
    logic [9:0] enq_col;
    logic [2:0] enq_bank;
    logic        enq_we;
    logic [3:0] enq_aux;
    logic        q_valid_0;
    logic [14:0] q_row_0;
    logic [9:0] q_col_0;
    logic [2:0] q_bank_0;
    logic        q_we_0;
    logic [3:0] q_aux_0;
    logic [14:0] bank_open_row_0;

    // ---- Testbench-monitored outputs ----
    logic        ref_ack;
    logic        cmd_valid;
    logic [3:0] cmd_type;
    logic [14:0] cmd_row;
    logic [9:0] cmd_col;
    logic [2:0] cmd_bank;
    logic        cmd_we;
    logic [3:0] cmd_aux;
    logic        enq_ready;
    logic [15:0] entry_valid;
    logic [14:0] entry_row [0:15];
    logic [9:0] entry_col [0:15];
    logic [2:0] entry_bank [0:15];
    logic        entry_we [0:15];
    logic [3:0] entry_aux [0:15];
    logic        queue_full;
    logic        queue_empty;
    logic [4:0] queue_count;

    // ---- Module instantiations ----
    scheduler u_scheduler (
        .clk(clk),
        .rst_n(rst_n),
        .bank_act_allowed(bank_act_allowed),
        .bank_is_active(bank_is_active),
        .bank_open_row(bank_open_row),
        .bank_pre_allowed(bank_pre_allowed),
        .bank_rd_allowed(bank_rd_allowed),
        .bank_wr_allowed(bank_wr_allowed),
        .cmd_aux(cmd_aux),
        .cmd_bank(cmd_bank),
        .cmd_col(cmd_col),
        .cmd_row(cmd_row),
        .cmd_type(cmd_type),
        .cmd_valid(cmd_valid),
        .cmd_we(cmd_we),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .q_aux(q_aux),
        .q_bank(q_bank),
        .q_col(q_col),
        .q_row(q_row),
        .q_valid(q_valid),
        .q_we(q_we),
        .ref_ack(ref_ack),
        .ref_required(ref_required),
        .ref_urgent(ref_urgent)
    );

    cmd_queue u_cmd_queue (
        .clk(clk),
        .rst_n(rst_n),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .enq_aux(enq_aux),
        .enq_bank(enq_bank),
        .enq_col(enq_col),
        .enq_ready(enq_ready),
        .enq_row(enq_row),
        .enq_valid(enq_valid),
        .enq_we(enq_we),
        .entry_aux(entry_aux),
        .entry_bank(entry_bank),
        .entry_col(entry_col),
        .entry_row(entry_row),
        .entry_valid(entry_valid),
        .entry_we(entry_we),
        .queue_count(queue_count),
        .queue_empty(queue_empty),
        .queue_full(queue_full)
    );

    // ---- Single-entry mode: scalar aliases for array entry [0] ----
    assign q_valid[0] = q_valid_0;
    assign q_valid[1] = '0;
    assign q_valid[2] = '0;
    assign q_valid[3] = '0;
    assign q_valid[4] = '0;
    assign q_valid[5] = '0;
    assign q_valid[6] = '0;
    assign q_valid[7] = '0;
    assign q_valid[8] = '0;
    assign q_valid[9] = '0;
    assign q_valid[10] = '0;
    assign q_valid[11] = '0;
    assign q_valid[12] = '0;
    assign q_valid[13] = '0;
    assign q_valid[14] = '0;
    assign q_valid[15] = '0;
    assign q_row[0] = q_row_0;
    assign q_row[1] = '0;
    assign q_row[2] = '0;
    assign q_row[3] = '0;
    assign q_row[4] = '0;
    assign q_row[5] = '0;
    assign q_row[6] = '0;
    assign q_row[7] = '0;
    assign q_row[8] = '0;
    assign q_row[9] = '0;
    assign q_row[10] = '0;
    assign q_row[11] = '0;
    assign q_row[12] = '0;
    assign q_row[13] = '0;
    assign q_row[14] = '0;
    assign q_row[15] = '0;
    assign q_col[0] = q_col_0;
    assign q_col[1] = '0;
    assign q_col[2] = '0;
    assign q_col[3] = '0;
    assign q_col[4] = '0;
    assign q_col[5] = '0;
    assign q_col[6] = '0;
    assign q_col[7] = '0;
    assign q_col[8] = '0;
    assign q_col[9] = '0;
    assign q_col[10] = '0;
    assign q_col[11] = '0;
    assign q_col[12] = '0;
    assign q_col[13] = '0;
    assign q_col[14] = '0;
    assign q_col[15] = '0;
    assign q_bank[0] = q_bank_0;
    assign q_bank[1] = '0;
    assign q_bank[2] = '0;
    assign q_bank[3] = '0;
    assign q_bank[4] = '0;
    assign q_bank[5] = '0;
    assign q_bank[6] = '0;
    assign q_bank[7] = '0;
    assign q_bank[8] = '0;
    assign q_bank[9] = '0;
    assign q_bank[10] = '0;
    assign q_bank[11] = '0;
    assign q_bank[12] = '0;
    assign q_bank[13] = '0;
    assign q_bank[14] = '0;
    assign q_bank[15] = '0;
    assign q_we[0] = q_we_0;
    assign q_we[1] = '0;
    assign q_we[2] = '0;
    assign q_we[3] = '0;
    assign q_we[4] = '0;
    assign q_we[5] = '0;
    assign q_we[6] = '0;
    assign q_we[7] = '0;
    assign q_we[8] = '0;
    assign q_we[9] = '0;
    assign q_we[10] = '0;
    assign q_we[11] = '0;
    assign q_we[12] = '0;
    assign q_we[13] = '0;
    assign q_we[14] = '0;
    assign q_we[15] = '0;
    assign q_aux[0] = q_aux_0;
    assign q_aux[1] = '0;
    assign q_aux[2] = '0;
    assign q_aux[3] = '0;
    assign q_aux[4] = '0;
    assign q_aux[5] = '0;
    assign q_aux[6] = '0;
    assign q_aux[7] = '0;
    assign q_aux[8] = '0;
    assign q_aux[9] = '0;
    assign q_aux[10] = '0;
    assign q_aux[11] = '0;
    assign q_aux[12] = '0;
    assign q_aux[13] = '0;
    assign q_aux[14] = '0;
    assign q_aux[15] = '0;
    assign bank_open_row[0] = bank_open_row_0;
    assign bank_open_row[1] = '0;
    assign bank_open_row[2] = '0;
    assign bank_open_row[3] = '0;
    assign bank_open_row[4] = '0;
    assign bank_open_row[5] = '0;
    assign bank_open_row[6] = '0;
    assign bank_open_row[7] = '0;
