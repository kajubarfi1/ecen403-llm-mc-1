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

    // ========================================================================
    // Address Map Localparams
    // ========================================================================
    localparam logic [7:0] ADDR_CTRL_STATUS          = 8'h00;
    localparam logic [7:0] ADDR_CTRL_CONFIG          = 8'h04;
    localparam logic [7:0] ADDR_TIMING_0             = 8'h08;
    localparam logic [7:0] ADDR_TIMING_1             = 8'h0C;
    localparam logic [7:0] ADDR_TIMING_2             = 8'h10;
    localparam logic [7:0] ADDR_TIMING_3             = 8'h14;
    localparam logic [7:0] ADDR_REFRESH_CONFIG       = 8'h18;
    localparam logic [7:0] ADDR_ERROR_STATUS         = 8'h1C;
    localparam logic [7:0] ADDR_BIST_CONFIG          = 8'h20;
    localparam logic [7:0] ADDR_BIST_ADDR_START      = 8'h24;
    localparam logic [7:0] ADDR_BIST_ADDR_END        = 8'h28;

    // ========================================================================
    // Register Storage
    // ========================================================================
    logic [31:0] reg_ctrl_config;
    logic [31:0] reg_timing_0;
    logic [31:0] reg_timing_1;
    logic [31:0] reg_timing_2;
    logic [31:0] reg_timing_3;
    logic [31:0] reg_refresh_config;
    logic [31:0] reg_error_status;
    logic [31:0] reg_bist_config;
    logic [31:0] reg_bist_addr_start;
    logic [31:0] reg_bist_addr_end;

    // ========================================================================
    // Wishbone Request Decode
    // ========================================================================
    logic wb_req;
    logic wb_wr;
    logic wb_rd;
    logic addr_valid;

    assign wb_req = csr_cyc_i & csr_stb_i;
    assign wb_wr  = wb_req & csr_we_i;
    assign wb_rd  = wb_req & ~csr_we_i;

    always_comb begin
        addr_valid = 1'b0;
        case (csr_adr_i)
            ADDR_CTRL_STATUS,
            ADDR_CTRL_CONFIG,
            ADDR_TIMING_0,
            ADDR_TIMING_1,
            ADDR_TIMING_2,
            ADDR_TIMING_3,
            ADDR_REFRESH_CONFIG,
            ADDR_ERROR_STATUS,
            ADDR_BIST_CONFIG,
            ADDR_BIST_ADDR_START,
            ADDR_BIST_ADDR_END: addr_valid = 1'b1;
            default:            addr_valid = 1'b0;
        endcase
    end

    // ========================================================================
    // Write Logic
    // ========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_ctrl_config <= 32'h00000009;
            reg_timing_0 <= 32'h271C0B0B;
            reg_timing_1 <= 32'h80200606;
            reg_timing_2 <= 32'h080B060C;
            reg_timing_3 <= 32'h00186004;
            reg_refresh_config <= 32'h00000168;
            reg_error_status <= 32'h00000000;
            reg_bist_config <= 32'h00000000;
            reg_bist_addr_start <= 32'h00000000;
            reg_bist_addr_end <= 32'h1FFFFFFF;
        end else begin
            // Self-clearing write-once fields in CTRL_CONFIG
            reg_ctrl_config[5] <= 1'b0;  // bist_start
            reg_ctrl_config[6] <= 1'b0;  // force_refresh
            reg_ctrl_config[7] <= 1'b0;  // force_self_ref

            // Latch error events (RW1C)
            if (sts_ecc_ue_event)
                reg_error_status[16] <= 1'b1;
            if (sts_ref_starve_event)
                reg_error_status[17] <= 1'b1;
            if (sts_init_fail_event)
                reg_error_status[18] <= 1'b1;

            // Update read-only fields in ERROR_STATUS
            reg_error_status[15:0]  <= sts_ecc_ce_count;
            reg_error_status[31:19] <= sts_bist_fail_addr;

            // Handle writes
            if (wb_wr && addr_valid) begin
                case (csr_adr_i)
                    ADDR_CTRL_STATUS: begin
                        // Read-only, ignore writes
                    end
                    ADDR_CTRL_CONFIG: begin
                        if (csr_sel_i[0]) reg_ctrl_config[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_ctrl_config[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_ctrl_config[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_ctrl_config[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_TIMING_0: begin
                        if (csr_sel_i[0]) reg_timing_0[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_timing_0[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_timing_0[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_timing_0[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_TIMING_1: begin
                        if (csr_sel_i[0]) reg_timing_1[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_timing_1[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_timing_1[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_timing_1[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_TIMING_2: begin
                        if (csr_sel_i[0]) reg_timing_2[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_timing_2[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_timing_2[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_timing_2[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_TIMING_3: begin
                        if (csr_sel_i[0]) reg_timing_3[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_timing_3[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_timing_3[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_timing_3[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_REFRESH_CONFIG: begin
                        if (csr_sel_i[0]) reg_refresh_config[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_refresh_config[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_refresh_config[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_refresh_config[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_ERROR_STATUS: begin
                        // RW1C: Write 1 to clear
                        if (csr_sel_i[2]) begin
                            if (csr_dat_i[16]) reg_error_status[16] <= 1'b0;
                            if (csr_dat_i[17]) reg_error_status[17] <= 1'b0;
                            if (csr_dat_i[18]) reg_error_status[18] <= 1'b0;
                        end
                    end
                    ADDR_BIST_CONFIG: begin
                        if (csr_sel_i[0]) reg_bist_config[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_bist_config[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_bist_config[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_bist_config[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_BIST_ADDR_START: begin
                        if (csr_sel_i[0]) reg_bist_addr_start[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_bist_addr_start[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_bist_addr_start[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_bist_addr_start[31:24] <= csr_dat_i[31:24];
                    end
                    ADDR_BIST_ADDR_END: begin
                        if (csr_sel_i[0]) reg_bist_addr_end[7:0]   <= csr_dat_i[7:0];
                        if (csr_sel_i[1]) reg_bist_addr_end[15:8]  <= csr_dat_i[15:8];
                        if (csr_sel_i[2]) reg_bist_addr_end[23:16] <= csr_dat_i[23:16];
                        if (csr_sel_i[3]) reg_bist_addr_end[31:24] <= csr_dat_i[31:24];
                    end
                    default: begin
                    end
                endcase
            end
        end
    end

    // ========================================================================
    // Read Mux
    // ========================================================================
    logic [31:0] read_data;

    always_comb begin
        read_data = 32'h00000000;
        case (csr_adr_i)
            ADDR_CTRL_STATUS: begin
                read_data = {23'b0,
                             sts_self_refresh_active,
                             sts_ref_pending_cnt,
                             sts_bist_fail,
                             sts_bist_done,
                             sts_cal_fail,
                             sts_cal_done,
                             sts_init_done};
            end
            ADDR_CTRL_CONFIG:    read_data = reg_ctrl_config;
            ADDR_TIMING_0:       read_data = reg_timing_0;
            ADDR_TIMING_1:       read_data = reg_timing_1;
            ADDR_TIMING_2:       read_data = reg_timing_2;
            ADDR_TIMING_3:       read_data = reg_timing_3;
            ADDR_REFRESH_CONFIG: read_data = reg_refresh_config;
            ADDR_ERROR_STATUS:   read_data = reg_error_status;
            ADDR_BIST_CONFIG:    read_data = reg_bist_config;
            ADDR_BIST_ADDR_START:read_data = reg_bist_addr_start;
            ADDR_BIST_ADDR_END:  read_data = reg_bist_addr_end;
            default:             read_data = 32'h00000000;
        endcase
    end

    // ========================================================================
    // Wishbone Response
    // ========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            csr_ack_o <= 1'b0;
            csr_dat_o <= 32'h00000000;
            csr_err_o <= 1'b0;
        end else begin
            csr_ack_o <= wb_req & addr_valid;
            csr_dat_o <= read_data;
            csr_err_o <= wb_req & ~addr_valid;
        end
    end

    // ========================================================================
    // Config Output Assignments
    // ========================================================================
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

    // ========================================================================
    // SVA Assertions
    // ========================================================================
    // synopsys translate_off
    property p_rw_retain;
        logic [31:0] captured_val;
        @(posedge clk) disable iff (!rst_n)
        (wb_wr && addr_valid && (csr_adr_i == ADDR_TIMING_0), captured_val = csr_dat_i) |=> (reg_timing_0 == captured_val);
    endproperty
    assert_p_rw_retain: assert property (p_rw_retain)
        else $error("TIMING_0 write value not retained");

    property p_bad_addr;
        @(posedge clk) disable iff (!rst_n)
        (wb_req && !addr_valid) |=> csr_err_o;
    endproperty
    assert_p_bad_addr: assert property (p_bad_addr)
        else $error("Invalid address did not produce csr_err_o");
    // synopsys translate_on

endmodule
