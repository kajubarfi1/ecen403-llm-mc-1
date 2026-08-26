    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        cfg_force_refresh;
    logic [3:0] cfg_max_postpone;
    logic        cfg_ref_priority;
    logic [23:0] cfg_tREFI_nCK;
    logic [3:0] cfg_urgent_threshold;
    logic        ref_ack;
    logic        ref_required;
    logic        ref_urgent;

    // ---- Testbench-driven inputs ----
    logic        csr_cyc_i;
    logic        csr_stb_i;
    logic        csr_we_i;
    logic [7:0] csr_adr_i;
    logic [31:0] csr_dat_i;
    logic [3:0] csr_sel_i;
    logic        sts_init_done;
    logic        sts_cal_done;
    logic        sts_cal_fail;
    logic        sts_bist_done;
    logic        sts_bist_fail;
    logic [2:0] sts_ref_pending_cnt;
    logic        sts_self_refresh_active;
    logic [15:0] sts_ecc_ce_count;
    logic        sts_ecc_ue_event;
    logic        sts_ref_starve_event;
    logic        sts_init_fail_event;
    logic [12:0] sts_bist_fail_addr;
    logic        init_done;
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
    logic        q_valid_0;
    logic [14:0] q_row_0;
    logic [9:0] q_col_0;
    logic [2:0] q_bank_0;
    logic        q_we_0;
    logic [3:0] q_aux_0;
    logic [14:0] bank_open_row_0;

    // ---- Testbench-monitored outputs ----
    logic        csr_ack_o;
    logic [31:0] csr_dat_o;
    logic        csr_err_o;
    logic [7:0] cfg_tRCD_nCK;
    logic [7:0] cfg_tRP_nCK;
    logic [7:0] cfg_tRAS_nCK;
    logic [7:0] cfg_tRC_nCK;
    logic [7:0] cfg_tRRD_nCK;
    logic [7:0] cfg_tWTR_nCK;
    logic [7:0] cfg_tFAW_nCK;
    logic [7:0] cfg_tRFC_nCK;
    logic [7:0] cfg_tWR_nCK;
    logic [7:0] cfg_tRTP_nCK;
    logic [7:0] cfg_CL_nCK;
    logic [7:0] cfg_CWL_nCK;
    logic [7:0] cfg_tCCD_nCK;
    logic        cfg_sched_policy;
    logic        cfg_row_policy;
    logic [1:0] cfg_self_ref_mode;
    logic        cfg_ecc_enable;
    logic        cfg_bist_start;
    logic        cfg_force_self_ref;
    logic [2:0] cfg_bist_pattern;
    logic        cfg_bist_addr_mode;
    logic [28:0] cfg_bist_addr_start;
    logic [28:0] cfg_bist_addr_end;
    logic [2:0] ref_pending_cnt;
    logic        ref_starve_flag;
    logic        cmd_valid;
    logic [3:0] cmd_type;
    logic [14:0] cmd_row;
    logic [9:0] cmd_col;
    logic [2:0] cmd_bank;
    logic        cmd_we;
    logic [3:0] cmd_aux;
    logic        deq_grant;
    logic [3:0] deq_idx;

    // ---- Module instantiations ----
    config_regs u_config_regs (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_CL_nCK(cfg_CL_nCK),
        .cfg_CWL_nCK(cfg_CWL_nCK),
        .cfg_bist_addr_end(cfg_bist_addr_end),
        .cfg_bist_addr_mode(cfg_bist_addr_mode),
        .cfg_bist_addr_start(cfg_bist_addr_start),
        .cfg_bist_pattern(cfg_bist_pattern),
        .cfg_bist_start(cfg_bist_start),
        .cfg_ecc_enable(cfg_ecc_enable),
        .cfg_force_refresh(cfg_force_refresh),
        .cfg_force_self_ref(cfg_force_self_ref),
        .cfg_max_postpone(cfg_max_postpone),
        .cfg_ref_priority(cfg_ref_priority),
        .cfg_row_policy(cfg_row_policy),
        .cfg_sched_policy(cfg_sched_policy),
        .cfg_self_ref_mode(cfg_self_ref_mode),
        .cfg_tCCD_nCK(cfg_tCCD_nCK),
        .cfg_tFAW_nCK(cfg_tFAW_nCK),
        .cfg_tRAS_nCK(cfg_tRAS_nCK),
        .cfg_tRCD_nCK(cfg_tRCD_nCK),
        .cfg_tRC_nCK(cfg_tRC_nCK),
        .cfg_tREFI_nCK(cfg_tREFI_nCK),
        .cfg_tRFC_nCK(cfg_tRFC_nCK),
        .cfg_tRP_nCK(cfg_tRP_nCK),
        .cfg_tRRD_nCK(cfg_tRRD_nCK),
        .cfg_tRTP_nCK(cfg_tRTP_nCK),
        .cfg_tWR_nCK(cfg_tWR_nCK),
        .cfg_tWTR_nCK(cfg_tWTR_nCK),
        .cfg_urgent_threshold(cfg_urgent_threshold),
        .csr_ack_o(csr_ack_o),
        .csr_adr_i(csr_adr_i),
        .csr_cyc_i(csr_cyc_i),
        .csr_dat_i(csr_dat_i),
        .csr_dat_o(csr_dat_o),
        .csr_err_o(csr_err_o),
        .csr_sel_i(csr_sel_i),
        .csr_stb_i(csr_stb_i),
        .csr_we_i(csr_we_i),
        .sts_bist_done(sts_bist_done),
        .sts_bist_fail(sts_bist_fail),
        .sts_bist_fail_addr(sts_bist_fail_addr),
        .sts_cal_done(sts_cal_done),
        .sts_cal_fail(sts_cal_fail),
        .sts_ecc_ce_count(sts_ecc_ce_count),
        .sts_ecc_ue_event(sts_ecc_ue_event),
        .sts_init_done(sts_init_done),
        .sts_init_fail_event(sts_init_fail_event),
        .sts_ref_pending_cnt(sts_ref_pending_cnt),
        .sts_ref_starve_event(sts_ref_starve_event),
        .sts_self_refresh_active(sts_self_refresh_active)
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
