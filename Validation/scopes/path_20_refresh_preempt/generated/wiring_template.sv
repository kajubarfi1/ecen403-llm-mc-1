    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic [2:0] addr_decoder_dec_bank;
    logic [9:0] addr_decoder_dec_col;
    logic [14:0] addr_decoder_dec_row;
    logic [3:0] cmd_queue_entry_aux [0:15];
    logic [2:0] cmd_queue_entry_bank [0:15];
    logic [9:0] cmd_queue_entry_col [0:15];
    logic [14:0] cmd_queue_entry_row [0:15];
    logic [15:0] cmd_queue_entry_valid;
    logic        cmd_queue_entry_we [0:15];
    logic        deq_grant;
    logic [3:0] deq_idx;
    logic        ref_ack;
    logic        ref_required;
    logic        ref_urgent;
    logic [28:0] req_addr;
    logic [3:0] scheduler_cmd_aux;
    logic [2:0] scheduler_cmd_bank;
    logic [9:0] scheduler_cmd_col;
    logic [14:0] scheduler_cmd_row;
    logic [3:0] scheduler_cmd_type;
    logic        scheduler_cmd_valid;
    logic        scheduler_cmd_we;
    logic [3:0] wb_port_req_aux;
    logic        wb_port_req_valid;
    logic        wb_port_req_we;

    // ---- Testbench-driven inputs ----
    logic        wb_cyc_i;
    logic        wb_stb_i;
    logic        wb_we_i;
    logic [28:0] wb_adr_i;
    logic [31:0] wb_dat_i;
    logic [3:0] wb_sel_i;
    logic [1:0] wb_bte_i;
    logic [2:0] wb_cti_i;
    logic        req_ready;
    logic        rsp_valid;
    logic [31:0] rsp_rdata;
    logic [3:0] rsp_aux;
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [7:0] bank_pre_allowed;
    logic        init_done;
    logic        cfg_force_refresh;
    logic [23:0] cfg_tREFI_nCK;
    logic [3:0] cfg_max_postpone;
    logic [3:0] cfg_urgent_threshold;
    logic        cfg_ref_priority;
    logic [14:0] bank_open_row_0;

    // ---- Testbench-monitored outputs ----
    logic        wb_ack_o;
    logic [31:0] wb_dat_o;
    logic        wb_stall_o;
    logic        wb_err_o;
    logic [31:0] req_wdata;
    logic [3:0] req_wmask;
    logic        dec_rank;
    logic        enq_ready;
    logic        queue_full;
    logic        queue_empty;
    logic [4:0] queue_count;
    logic [2:0] ref_pending_cnt;
    logic        ref_starve_flag;
    logic [3:0] ddr_cmd;
    logic [14:0] ddr_addr;
    logic [2:0] ddr_bank;
    logic        ddr_cke;
    logic        ddr_reset_n;
    logic        ddr_odt;
    logic        fb_act_valid;
    logic [2:0] fb_act_bank;
    logic [14:0] fb_act_row;
    logic        fb_pre_valid;
    logic        fb_rd_valid;
    logic        fb_wr_valid;
    logic        fb_ref_valid;

    // ---- Module instantiations ----
    wb_port u_wb_port (
        .clk(clk),
        .rst_n(rst_n),
        .req_addr(req_addr),
        .req_aux(wb_port_req_aux),
        .req_ready(req_ready),
        .req_valid(wb_port_req_valid),
        .req_wdata(req_wdata),
        .req_we(wb_port_req_we),
        .req_wmask(req_wmask),
        .rsp_aux(rsp_aux),
        .rsp_rdata(rsp_rdata),
        .rsp_valid(rsp_valid),
        .wb_ack_o(wb_ack_o),
        .wb_adr_i(wb_adr_i),
        .wb_bte_i(wb_bte_i),
        .wb_cti_i(wb_cti_i),
        .wb_cyc_i(wb_cyc_i),
        .wb_dat_i(wb_dat_i),
        .wb_dat_o(wb_dat_o),
        .wb_err_o(wb_err_o),
        .wb_sel_i(wb_sel_i),
        .wb_stall_o(wb_stall_o),
        .wb_stb_i(wb_stb_i),
        .wb_we_i(wb_we_i)
    );

    addr_decoder u_addr_decoder (
        .dec_bank(addr_decoder_dec_bank),
        .dec_col(addr_decoder_dec_col),
        .dec_rank(dec_rank),
        .dec_row(addr_decoder_dec_row),
        .req_addr(req_addr)
    );

    cmd_queue u_cmd_queue (
        .clk(clk),
        .rst_n(rst_n),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .enq_aux(wb_port_req_aux),
        .enq_bank(addr_decoder_dec_bank),
        .enq_col(addr_decoder_dec_col),
        .enq_ready(enq_ready),
        .enq_row(addr_decoder_dec_row),
        .enq_valid(wb_port_req_valid),
        .enq_we(wb_port_req_we),
        .entry_aux(cmd_queue_entry_aux),
        .entry_bank(cmd_queue_entry_bank),
        .entry_col(cmd_queue_entry_col),
        .entry_row(cmd_queue_entry_row),
        .entry_valid(cmd_queue_entry_valid),
        .entry_we(cmd_queue_entry_we),
        .queue_count(queue_count),
        .queue_empty(queue_empty),
        .queue_full(queue_full)
    );

    scheduler u_scheduler (
        .clk(clk),
        .rst_n(rst_n),
        .bank_act_allowed(bank_act_allowed),
        .bank_is_active(bank_is_active),
        .bank_open_row(bank_open_row),
        .bank_pre_allowed(bank_pre_allowed),
        .bank_rd_allowed(bank_rd_allowed),
        .bank_wr_allowed(bank_wr_allowed),
        .cmd_aux(scheduler_cmd_aux),
        .cmd_bank(scheduler_cmd_bank),
        .cmd_col(scheduler_cmd_col),
        .cmd_row(scheduler_cmd_row),
        .cmd_type(scheduler_cmd_type),
        .cmd_valid(scheduler_cmd_valid),
        .cmd_we(scheduler_cmd_we),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .q_aux(cmd_queue_entry_aux),
        .q_bank(cmd_queue_entry_bank),
        .q_col(cmd_queue_entry_col),
        .q_row(cmd_queue_entry_row),
        .q_valid(cmd_queue_entry_valid),
        .q_we(cmd_queue_entry_we),
        .ref_ack(ref_ack),
        .ref_required(ref_required),
        .ref_urgent(ref_urgent)
    );

    refresh_ctrl u_refresh_ctrl (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_force_refresh(cfg_force_refresh),
        .cfg_max_postpone(cfg_max_postpone),
        .cfg_ref_priority(cfg_ref_priority),
        .cfg_tREFI_nCK(cfg_tREFI_nCK),
        .cfg_urgent_threshold(cfg_urgent_threshold),
        .init_done(init_done),
        .ref_ack(ref_ack),
        .ref_pending_cnt(ref_pending_cnt),
        .ref_required(ref_required),
        .ref_starve_flag(ref_starve_flag),
        .ref_urgent(ref_urgent)
    );

    cmd_gen u_cmd_gen (
        .clk(clk),
        .rst_n(rst_n),
        .ddr_addr(ddr_addr),
        .ddr_bank(ddr_bank),
        .ddr_cke(ddr_cke),
        .ddr_cmd(ddr_cmd),
        .ddr_odt(ddr_odt),
        .ddr_reset_n(ddr_reset_n),
        .fb_act_bank(fb_act_bank),
        .fb_act_row(fb_act_row),
        .fb_act_valid(fb_act_valid),
        .fb_pre_valid(fb_pre_valid),
        .fb_rd_valid(fb_rd_valid),
        .fb_ref_valid(fb_ref_valid),
        .fb_wr_valid(fb_wr_valid),
        .sched_aux(scheduler_cmd_aux),
        .sched_bank(scheduler_cmd_bank),
        .sched_col(scheduler_cmd_col),
        .sched_row(scheduler_cmd_row),
        .sched_type(scheduler_cmd_type),
        .sched_valid(scheduler_cmd_valid),
        .sched_we(scheduler_cmd_we)
    );

    // ---- Single-entry mode: scalar aliases for array entry [0] ----
    assign bank_open_row[0] = bank_open_row_0;
    assign bank_open_row[1] = '0;
    assign bank_open_row[2] = '0;
    assign bank_open_row[3] = '0;
    assign bank_open_row[4] = '0;
    assign bank_open_row[5] = '0;
    assign bank_open_row[6] = '0;
    assign bank_open_row[7] = '0;
