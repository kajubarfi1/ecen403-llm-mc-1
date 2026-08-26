    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        init_done;

    // ---- Testbench-driven inputs ----
    logic        enable;
    logic        cfg_force_refresh;
    logic [23:0] cfg_tREFI_nCK;
    logic [3:0] cfg_max_postpone;
    logic [3:0] cfg_urgent_threshold;
    logic        cfg_ref_priority;
    logic        ref_ack;

    // ---- Testbench-monitored outputs ----
    logic        init_fail;
    logic        init_cmd_valid;
    logic [3:0] init_cmd;
    logic [14:0] init_addr;
    logic [2:0] init_bank;
    logic        init_cke;
    logic        init_reset_n;
    logic [3:0] init_state;
    logic        ref_required;
    logic        ref_urgent;
    logic [2:0] ref_pending_cnt;
    logic        ref_starve_flag;

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
        .init_fail(init_fail),
        .init_reset_n(init_reset_n),
        .init_state(init_state)
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
