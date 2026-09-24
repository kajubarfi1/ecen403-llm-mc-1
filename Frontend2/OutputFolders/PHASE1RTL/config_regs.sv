module config_regs #(
    parameter CSR_ADDR_W = 8,
    parameter CSR_DATA_W = 32
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // CSR Wishbone Slave
    input  logic                    csr_cyc_i,
    input  logic                    csr_stb_i,
    input  logic                    csr_we_i,
    input  logic [CSR_ADDR_W-1:0]   csr_adr_i,
    input  logic [CSR_DATA_W-1:0]   csr_dat_i,
    input  logic [3:0]              csr_sel_i,
    output logic                    csr_ack_o,
    output logic [CSR_DATA_W-1:0]   csr_dat_o,
    output logic                    csr_err_o,

    // Status inputs
    input  logic                    sts_init_done,
    input  logic                    sts_cal_done,
    input  logic                    sts_cal_fail,
    input  logic                    sts_bist_done,
    input  logic                    sts_bist_fail,
    input  logic [2:0]              sts_ref_pending_cnt,
    input  logic                    sts_self_refresh_active,
    input  logic [15:0]             sts_ecc_ce_count,
    input  logic                    sts_ecc_ue_event,
    input  logic                    sts_ref_starve_event,
    input  logic                    sts_init_fail_event,
    input  logic [12:0]             sts_bist_fail_addr,

    // Config outputs
    output logic [7:0]  cfg_tRCD_nCK, output logic [7:0]  cfg_tRP_nCK,
    output logic [7:0]  cfg_tRAS_nCK, output logic [7:0]  cfg_tRC_nCK,
    output logic [7:0]  cfg_tRRD_nCK, output logic [7:0]  cfg_tWTR_nCK,
    output logic [7:0]  cfg_tFAW_nCK, output logic [7:0]  cfg_tRFC_nCK,
    output logic [7:0]  cfg_tWR_nCK,  output logic [7:0]  cfg_tRTP_nCK,
    output logic [7:0]  cfg_CL_nCK,   output logic [7:0]  cfg_CWL_nCK,
    output logic [7:0]  cfg_tCCD_nCK, output logic [23:0] cfg_tREFI_nCK,
    output logic        cfg_sched_policy, output logic     cfg_row_policy,
    output logic [1:0]  cfg_self_ref_mode, output logic    cfg_ecc_enable,
    output logic        cfg_bist_start, output logic       cfg_force_refresh,
    output logic        cfg_force_self_ref,
    output logic [3:0]  cfg_max_postpone, output logic [3:0] cfg_urgent_threshold,
    output logic        cfg_ref_priority,
    output logic [2:0]  cfg_bist_pattern, output logic     cfg_bist_addr_mode,
    output logic [28:0] cfg_bist_addr_start, output logic [28:0] cfg_bist_addr_end
);

    // Register address map
    localparam [CSR_ADDR_W-1:0] ADDR_CTRL_STATUS = 8'h00;
    localparam [CSR_ADDR_W-1:0] ADDR_CTRL_CONFIG = 8'h04;
    localparam [CSR_ADDR_W-1:0] ADDR_TIMING_0 = 8'h08;
    localparam [CSR_ADDR_W-1:0] ADDR_TIMING_1 = 8'h0C;
    localparam [CSR_ADDR_W-1:0] ADDR_TIMING_2 = 8'h10;
    localparam [CSR_ADDR_W-1:0] ADDR_TIMING_3 = 8'h14;
    localparam [CSR_ADDR_W-1:0] ADDR_REFRESH_CONFIG = 8'h18;
    localparam [CSR_ADDR_W-1:0] ADDR_ERROR_STATUS = 8'h1C;
    localparam [CSR_ADDR_W-1:0] ADDR_BIST_CONFIG = 8'h20;
    localparam [CSR_ADDR_W-1:0] ADDR_BIST_ADDR_START = 8'h24;
    localparam [CSR_ADDR_W-1:0] ADDR_BIST_ADDR_END = 8'h28;

    // Bus request decode
    wire csr_req = csr_cyc_i & csr_stb_i;
    wire csr_wr  = csr_req & csr_we_i;
    wire csr_rd  = csr_req & ~csr_we_i;
    wire addr_valid =
        (csr_adr_i == ADDR_CTRL_STATUS) ||
        (csr_adr_i == ADDR_CTRL_CONFIG) ||
        (csr_adr_i == ADDR_TIMING_0) ||
        (csr_adr_i == ADDR_TIMING_1) ||
        (csr_adr_i == ADDR_TIMING_2) ||
        (csr_adr_i == ADDR_TIMING_3) ||
        (csr_adr_i == ADDR_REFRESH_CONFIG) ||
        (csr_adr_i == ADDR_ERROR_STATUS) ||
        (csr_adr_i == ADDR_BIST_CONFIG) ||
        (csr_adr_i == ADDR_BIST_ADDR_START) ||
        (csr_adr_i == ADDR_BIST_ADDR_END);

    // ACK generation (internal register + continuous assign)
    logic ack_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ack_r <= 1'b0;
        else        ack_r <= csr_req & ~ack_r;
    assign csr_ack_o = ack_r;

    // Error generation (internal register + continuous assign)
    logic err_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) err_r <= 1'b0;
        else        err_r <= csr_req & ~addr_valid & ~ack_r;
    assign csr_err_o = err_r;

    // Register storage
    logic [31:0] reg_timing_0;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_timing_0 <= 32'h271C0B0B;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_TIMING_0) reg_timing_0 <= csr_dat_i;

    logic [31:0] reg_timing_1;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_timing_1 <= 32'h80200606;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_TIMING_1) reg_timing_1 <= csr_dat_i;

    logic [31:0] reg_timing_2;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_timing_2 <= 32'h080B060C;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_TIMING_2) reg_timing_2 <= csr_dat_i;

    logic [31:0] reg_timing_3;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_timing_3 <= 32'h00186004;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_TIMING_3) reg_timing_3 <= csr_dat_i;

    logic [31:0] reg_refresh_config;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_refresh_config <= 32'h00000168;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_REFRESH_CONFIG)
            reg_refresh_config <= (csr_dat_i & 32'h000001FF) | (reg_refresh_config & 32'hFFFFFE00);  // reserved bits pinned

    logic [31:0] reg_bist_config;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_bist_config <= 32'h00000000;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_BIST_CONFIG)
            reg_bist_config <= (csr_dat_i & 32'h0000000F) | (reg_bist_config & 32'hFFFFFFF0);  // reserved bits pinned

    logic [31:0] reg_bist_addr_start;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_bist_addr_start <= 32'h00000000;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_BIST_ADDR_START)
            reg_bist_addr_start <= (csr_dat_i & 32'h1FFFFFFF) | (reg_bist_addr_start & 32'hE0000000);  // reserved bits pinned

    logic [31:0] reg_bist_addr_end;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) reg_bist_addr_end <= 32'h1FFFFFFF;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_BIST_ADDR_END)
            reg_bist_addr_end <= (csr_dat_i & 32'h1FFFFFFF) | (reg_bist_addr_end & 32'hE0000000);  // reserved bits pinned

    logic [31:0] reg_ctrl_config;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) reg_ctrl_config <= 32'h00000009;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_CTRL_CONFIG)
            reg_ctrl_config <= (csr_dat_i & 32'h000000FF) | (reg_ctrl_config & 32'hFFFFFF00);  // reserved bits pinned
        else begin
            reg_ctrl_config[5] <= 1'b0;  // bist_start self-clear
            reg_ctrl_config[6] <= 1'b0;  // force_refresh self-clear
            reg_ctrl_config[7] <= 1'b0;  // force_self_ref self-clear
        end
    end

    // ERROR_STATUS (RW1C flags; count/addr fields are live status passthrough)
    logic ecc_ue_flag_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ecc_ue_flag_r <= 1'b0;
        else if (sts_ecc_ue_event) ecc_ue_flag_r <= 1'b1;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_ERROR_STATUS && csr_dat_i[16]) ecc_ue_flag_r <= 1'b0;
    logic ref_starve_flag_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ref_starve_flag_r <= 1'b0;
        else if (sts_ref_starve_event) ref_starve_flag_r <= 1'b1;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_ERROR_STATUS && csr_dat_i[17]) ref_starve_flag_r <= 1'b0;
    logic init_fail_flag_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) init_fail_flag_r <= 1'b0;
        else if (sts_init_fail_event) init_fail_flag_r <= 1'b1;
        else if (csr_wr && addr_valid && csr_adr_i == ADDR_ERROR_STATUS && csr_dat_i[18]) init_fail_flag_r <= 1'b0;

    // Read data mux
    logic [31:0] rdata_mux;
    always_comb begin
        case (csr_adr_i)
            ADDR_CTRL_STATUS: rdata_mux = {23'b0, sts_self_refresh_active, sts_ref_pending_cnt, sts_bist_fail, sts_bist_done, sts_cal_fail, sts_cal_done, sts_init_done};
            ADDR_CTRL_CONFIG: rdata_mux = reg_ctrl_config;
            ADDR_TIMING_0: rdata_mux = reg_timing_0;
            ADDR_TIMING_1: rdata_mux = reg_timing_1;
            ADDR_TIMING_2: rdata_mux = reg_timing_2;
            ADDR_TIMING_3: rdata_mux = reg_timing_3;
            ADDR_REFRESH_CONFIG: rdata_mux = reg_refresh_config;
            ADDR_BIST_CONFIG: rdata_mux = reg_bist_config;
            ADDR_BIST_ADDR_START: rdata_mux = reg_bist_addr_start;
            ADDR_BIST_ADDR_END: rdata_mux = reg_bist_addr_end;
            ADDR_ERROR_STATUS: rdata_mux = {sts_bist_fail_addr, init_fail_flag_r, ref_starve_flag_r, ecc_ue_flag_r, sts_ecc_ce_count};
            default: rdata_mux = 32'h0;
        endcase
    end

    // Read data output (latch on csr_rd, hold value)
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) csr_dat_o <= 32'h0;
        else if (csr_rd) csr_dat_o <= rdata_mux;

    // Config outputs
    assign cfg_tRCD_nCK         = reg_timing_0[7:0];
    assign cfg_tRP_nCK          = reg_timing_0[15:8];
    assign cfg_tRAS_nCK         = reg_timing_0[23:16];
    assign cfg_tRC_nCK          = reg_timing_0[31:24];
    assign cfg_tRRD_nCK         = reg_timing_1[7:0];
    assign cfg_tWTR_nCK         = reg_timing_1[15:8];
    assign cfg_tFAW_nCK         = reg_timing_1[23:16];
    assign cfg_tRFC_nCK         = reg_timing_1[31:24];
    assign cfg_tWR_nCK          = reg_timing_2[7:0];
    assign cfg_tRTP_nCK         = reg_timing_2[15:8];
    assign cfg_CL_nCK           = reg_timing_2[23:16];
    assign cfg_CWL_nCK          = reg_timing_2[31:24];
    assign cfg_tCCD_nCK         = reg_timing_3[7:0];
    assign cfg_tREFI_nCK        = reg_timing_3[31:8];
    assign cfg_sched_policy     = reg_ctrl_config[0];
    assign cfg_row_policy       = reg_ctrl_config[1];
    assign cfg_self_ref_mode    = reg_ctrl_config[3:2];
    assign cfg_ecc_enable       = reg_ctrl_config[4];
    assign cfg_bist_start       = reg_ctrl_config[5];
    assign cfg_force_refresh    = reg_ctrl_config[6];
    assign cfg_force_self_ref   = reg_ctrl_config[7];
    assign cfg_max_postpone     = reg_refresh_config[3:0];
    assign cfg_urgent_threshold = reg_refresh_config[7:4];
    assign cfg_ref_priority     = reg_refresh_config[8];
    assign cfg_bist_pattern     = reg_bist_config[2:0];
    assign cfg_bist_addr_mode   = reg_bist_config[3];
    assign cfg_bist_addr_start  = reg_bist_addr_start[28:0];
    assign cfg_bist_addr_end    = reg_bist_addr_end[28:0];

    // synopsys translate_off
    property p_rw_retain;
        @(posedge clk) disable iff (!rst_n)
        (csr_wr && addr_valid && csr_adr_i == ADDR_TIMING_0) |=> (reg_timing_0 == $past(csr_dat_i));
    endproperty
    assert property (p_rw_retain);

    property p_bad_addr;
        @(posedge clk) disable iff (!rst_n)
        (csr_req && !addr_valid) |=> csr_err_o;
    endproperty
    assert property (p_bad_addr);
    // synopsys translate_on

endmodule
