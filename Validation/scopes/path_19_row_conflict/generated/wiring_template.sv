    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic [2:0] addr_decoder_dec_bank;
    logic [9:0] addr_decoder_dec_col;
    logic [14:0] addr_decoder_dec_row;
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_pre_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [2:0] cmd_gen_fb_act_bank;
    logic [14:0] cmd_gen_fb_act_row;
    logic        cmd_gen_fb_act_valid;
    logic        cmd_gen_fb_pre_valid;
    logic        cmd_gen_fb_rd_valid;
    logic        cmd_gen_fb_ref_valid;
    logic        cmd_gen_fb_wr_valid;
    logic [3:0] cmd_queue_entry_aux [0:15];
    logic [2:0] cmd_queue_entry_bank [0:15];
    logic [9:0] cmd_queue_entry_col [0:15];
    logic [14:0] cmd_queue_entry_row [0:15];
    logic [15:0] cmd_queue_entry_valid;
    logic        cmd_queue_entry_we [0:15];
    logic        deq_grant;
    logic [3:0] deq_idx;
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
    logic        ref_required;
    logic        ref_urgent;
    logic [2:0] cmd_pre_bank;
    logic        cmd_pre_all;
    logic [2:0] cmd_rd_bank;
    logic [2:0] cmd_wr_bank;
    logic [7:0] cfg_tRCD_nCK;
    logic [7:0] cfg_tRP_nCK;
    logic [7:0] cfg_tRAS_nCK;
    logic [7:0] cfg_tRC_nCK;
    logic [7:0] cfg_tRRD_nCK;
    logic [7:0] cfg_tFAW_nCK;
    logic [7:0] cfg_tWTR_nCK;
    logic [7:0] cfg_tWR_nCK;
    logic [7:0] cfg_tRTP_nCK;
    logic [7:0] cfg_tCCD_nCK;
    logic [7:0] cfg_tRFC_nCK;

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
    logic        ref_ack;
    logic [3:0] ddr_cmd;
    logic [14:0] ddr_addr;
    logic [2:0] ddr_bank;
    logic        ddr_cke;
    logic        ddr_reset_n;
    logic        ddr_odt;
    logic        all_banks_idle;
    logic        faw_allows_act;

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

    cmd_gen u_cmd_gen (
        .clk(clk),
        .rst_n(rst_n),
        .ddr_addr(ddr_addr),
        .ddr_bank(ddr_bank),
        .ddr_cke(ddr_cke),
        .ddr_cmd(ddr_cmd),
        .ddr_odt(ddr_odt),
        .ddr_reset_n(ddr_reset_n),
        .fb_act_bank(cmd_gen_fb_act_bank),
        .fb_act_row(cmd_gen_fb_act_row),
        .fb_act_valid(cmd_gen_fb_act_valid),
        .fb_pre_valid(cmd_gen_fb_pre_valid),
        .fb_rd_valid(cmd_gen_fb_rd_valid),
        .fb_ref_valid(cmd_gen_fb_ref_valid),
        .fb_wr_valid(cmd_gen_fb_wr_valid),
        .sched_aux(scheduler_cmd_aux),
        .sched_bank(scheduler_cmd_bank),
        .sched_col(scheduler_cmd_col),
        .sched_row(scheduler_cmd_row),
        .sched_type(scheduler_cmd_type),
        .sched_valid(scheduler_cmd_valid),
        .sched_we(scheduler_cmd_we)
    );

    bank_tracker u_bank_tracker (
        .clk(clk),
        .rst_n(rst_n),
        .all_banks_idle(all_banks_idle),
        .bank_act_allowed(bank_act_allowed),
        .bank_is_active(bank_is_active),
        .bank_open_row(bank_open_row),
        .bank_pre_allowed(bank_pre_allowed),
        .bank_rd_allowed(bank_rd_allowed),
        .bank_wr_allowed(bank_wr_allowed),
        .cfg_tCCD_nCK(cfg_tCCD_nCK),
        .cfg_tFAW_nCK(cfg_tFAW_nCK),
        .cfg_tRAS_nCK(cfg_tRAS_nCK),
        .cfg_tRCD_nCK(cfg_tRCD_nCK),
        .cfg_tRC_nCK(cfg_tRC_nCK),
        .cfg_tRFC_nCK(cfg_tRFC_nCK),
        .cfg_tRP_nCK(cfg_tRP_nCK),
        .cfg_tRRD_nCK(cfg_tRRD_nCK),
        .cfg_tRTP_nCK(cfg_tRTP_nCK),
        .cfg_tWR_nCK(cfg_tWR_nCK),
        .cfg_tWTR_nCK(cfg_tWTR_nCK),
        .cmd_act_bank(cmd_gen_fb_act_bank),
        .cmd_act_row(cmd_gen_fb_act_row),
        .cmd_act_valid(cmd_gen_fb_act_valid),
        .cmd_pre_all(cmd_pre_all),
        .cmd_pre_bank(cmd_pre_bank),
        .cmd_pre_valid(cmd_gen_fb_pre_valid),
        .cmd_rd_bank(cmd_rd_bank),
        .cmd_rd_valid(cmd_gen_fb_rd_valid),
        .cmd_ref_valid(cmd_gen_fb_ref_valid),
        .cmd_wr_bank(cmd_wr_bank),
        .cmd_wr_valid(cmd_gen_fb_wr_valid),
        .faw_allows_act(faw_allows_act)
    );

    // ---- Derived signals (wired from internal scheduler_cmd_bank) ----
    assign cmd_pre_bank = scheduler_cmd_bank;
    assign cmd_rd_bank = scheduler_cmd_bank;
    assign cmd_wr_bank = scheduler_cmd_bank;
    assign cmd_pre_all = 1'b0;
