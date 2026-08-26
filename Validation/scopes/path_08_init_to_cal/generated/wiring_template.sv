    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        init_done;

    // ---- Testbench-driven inputs ----
    logic        enable;
    logic        zqcs_ack;

    // ---- Testbench-monitored outputs ----
    logic        init_fail;
    logic        init_cmd_valid;
    logic [3:0] init_cmd;
    logic [14:0] init_addr;
    logic [2:0] init_bank;
    logic        init_cke;
    logic        init_reset_n;
    logic [3:0] init_state;
    logic        cal_done;
    logic        cal_fail;
    logic        zqcs_req;

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

    calibration u_calibration (
        .clk(clk),
        .rst_n(rst_n),
        .cal_done(cal_done),
        .cal_fail(cal_fail),
        .init_done(init_done),
        .zqcs_ack(zqcs_ack),
        .zqcs_req(zqcs_req)
    );
