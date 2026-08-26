    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        calibration_cal_done;
    logic        calibration_cal_fail;
    logic        init_done;
    logic        init_fsm_init_fail;

    // ---- Testbench-driven inputs ----
    logic        enable;
    logic        zqcs_ack;
    logic        csr_cyc_i;
    logic        csr_stb_i;
    logic        csr_we_i;
    logic [7:0] csr_adr_i;
    logic [31:0] csr_dat_i;
    logic [3:0] csr_sel_i;
    logic        sts_bist_done;
    logic        sts_bist_fail;
    logic [2:0] sts_ref_pending_cnt;
    logic        sts_self_refresh_active;
    logic [15:0] sts_ecc_ce_count;
    logic        sts_ecc_ue_event;
    logic        sts_ref_starve_event;
    logic [12:0] sts_bist_fail_addr;

    // ---- Testbench-monitored outputs ----
    logic        init_cmd_valid;
    logic [3:0] init_cmd;
    logic [14:0] init_addr;
    logic [2:0] init_bank;
    logic        init_cke;
    logic        init_reset_n;
    logic [3:0] init_state;
    logic        zqcs_req;
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
    logic [23:0] cfg_tREFI_nCK;
    logic        cfg_sched_policy;
    logic        cfg_row_policy;
    logic [1:0] cfg_self_ref_mode;
    logic        cfg_ecc_enable;
    logic        cfg_bist_start;
    logic        cfg_force_refresh;
    logic        cfg_force_self_ref;
    logic [3:0] cfg_max_postpone;
    logic [3:0] cfg_urgent_threshold;
    logic        cfg_ref_priority;
    logic [2:0] cfg_bist_pattern;
    logic        cfg_bist_addr_mode;
    logic [28:0] cfg_bist_addr_start;
    logic [28:0] cfg_bist_addr_end;

    // ---- Module instantiations ----
    init_fsm u_init_fsm (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .init_addr(init_addr),
        .init_bank(init_bank),
        .init_cke(init_cke),
        .init_cmd(init_cmd),
        .init_cmd_valid(init_cmd_valid),
        .init_done(init_done),
        .init_fail(init_fsm_init_fail),
        .init_reset_n(init_reset_n),
        .init_state(init_state)
    );

    calibration u_calibration (
        .clk(clk),
        .rst_n(rst_n),
        .cal_done(calibration_cal_done),
        .cal_fail(calibration_cal_fail),
        .init_done(init_done),
        .zqcs_ack(zqcs_ack),
        .zqcs_req(zqcs_req)
    );

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
        .sts_cal_done(calibration_cal_done),
        .sts_cal_fail(calibration_cal_fail),
        .sts_ecc_ce_count(sts_ecc_ce_count),
        .sts_ecc_ue_event(sts_ecc_ue_event),
        .sts_init_done(init_done),
        .sts_init_fail_event(init_fsm_init_fail),
        .sts_ref_pending_cnt(sts_ref_pending_cnt),
        .sts_ref_starve_event(sts_ref_starve_event),
        .sts_self_refresh_active(sts_self_refresh_active)
    );
