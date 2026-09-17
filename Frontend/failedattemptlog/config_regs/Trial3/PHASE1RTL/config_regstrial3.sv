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

    // Address map localparams
    localparam logic [CSR_ADDR_W-1:0] ADDR_CTRL_STATUS          = 8'h00;
    localparam logic [CSR_ADDR_W-1:0] ADDR_CTRL_CONFIG          = 8'h04;
    localparam logic [CSR_ADDR_W-1:0] ADDR_TIMING_0             = 8'h08;
    localparam logic [CSR_ADDR_W-1:0] ADDR_TIMING_1             = 8'h0C;
    localparam logic [CSR_ADDR_W-1:0] ADDR_TIMING_2             = 8'h10;
    localparam logic [CSR_ADDR_W-1:0] ADDR_TIMING_3             = 8'h14;
    localparam logic [CSR_ADDR_W-1:0] ADDR_REFRESH_CONFIG       = 8'h18;
    localparam logic [CSR_ADDR_W-1:0] ADDR_ERROR_STATUS         = 8'h1C;
    localparam logic [CSR_ADDR_W-1:0] ADDR_BIST_CONFIG          = 8'h20;
    localparam logic [CSR_ADDR_W-1:0] ADDR_BIST_ADDR_START      = 8'h24;
    localparam logic [CSR_ADDR_W-1:0] ADDR_BIST_ADDR_END        = 8'h28;

    // Register storage
    logic [CSR_DATA_W-1:0] reg_ctrl_config;
    logic [CSR_DATA_W-1:0] reg_timing_0;
    logic [CSR_DATA_W-1:0] reg_timing_1;
    logic [CSR_DATA_W-1:0] reg_timing_2;
    logic [CSR_DATA_W-1:0] reg_timing_3;
    logic [CSR_DATA_W-1:0] reg_refresh_config;
    logic [CSR_DATA_W-1:0] reg_error_status;
    logic [CSR_DATA_W-1:0] reg_bist_config;
    logic [CSR_DATA_W-1:0] reg_bist_addr_start;
    logic [CSR_DATA_W-1:0] reg_bist_addr_end;

    // Bus decode
    logic bus_req;
    logic bus_wr;
    logic bus_rd;
    logic addr_valid;

    assign bus_req = csr_cyc_i & csr_stb_i;
    assign bus_wr  = bus_req & csr_we_i;
    assign bus_rd  = bus_req & ~csr_we_i;

    // Address decode
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
            default: addr_valid = 1'b0;
        endcase
    end

    // Wishbone ack generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            csr_ack_o <= 1'b0;
        end else begin
            csr_ack_o <= bus_req & ~csr_ack_o;
        end
    end

    // Wishbone error generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            csr_err_o <= 1'b0;
        end else begin
            csr_err_o <= bus_req & ~addr_valid & ~csr_err_o;
        end
    end

    // Write logic
    logic [CSR_DATA_W-1:0] wr_data;
    logic [3:0] wr_be;

    assign wr_be = csr_sel_i;

    always_comb begin
        for (int i = 0; i < 4; i++) begin
            wr_data[i*8 +: 8] = wr_be[i] ? csr_dat_i[i*8 +: 8] : 8'h00;
        end
    end

    // Register writes
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

            // RW1C ERROR_STATUS latching
            if (sts_ecc_ue_event) begin
                reg_error_status[16] <= 1'b1;
            end
            if (sts_ref_starve_event) begin
                reg_error_status[17] <= 1'b1;
            end
            if (sts_init_fail_event) begin
                reg_error_status[18] <= 1'b1;
            end

            // Write operations
            if (bus_wr && addr_valid) begin
                case (csr_adr_i)
                    ADDR_CTRL_CONFIG: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_ctrl_config[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_TIMING_0: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_timing_0[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_TIMING_1: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_timing_1[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_TIMING_2: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_timing_2[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_TIMING_3: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_timing_3[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_REFRESH_CONFIG: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_refresh_config[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_ERROR_STATUS: begin
                        // RW1C: write 1 to clear
                        if (wr_be[2]) begin
                            if (csr_dat_i[16]) reg_error_status[16] <= 1'b0;
                            if (csr_dat_i[17]) reg_error_status[17] <= 1'b0;
                            if (csr_dat_i[18]) reg_error_status[18] <= 1'b0;
                        end
                    end
                    ADDR_BIST_CONFIG: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_bist_config[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_BIST_ADDR_START: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_bist_addr_start[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    ADDR_BIST_ADDR_END: begin
                        for (int i = 0; i < 4; i++) begin
                            if (wr_be[i]) begin
                                reg_bist_addr_end[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                            end
                        end
                    end
                    default: ;
                endcase
            end
        end
    end

    // Read mux
    logic [CSR_DATA_W-1:0] rd_data;

    always_comb begin
        rd_data = 32'h00000000;
        case (csr_adr_i)
            ADDR_CTRL_STATUS: begin
                rd_data[0] = sts_init_done;
                rd_data[1] = sts_cal_done;
                rd_data[2] = sts_cal_fail;
                rd_data[3] = sts_bist_done;
                rd_data[4] = sts_bist_fail;
                rd_data[7:5] = sts_ref_pending_cnt;
                rd_data[8] = sts_self_refresh_active;
                rd_data[31:9] = 23'b0;
            end
            ADDR_CTRL_CONFIG: begin
                rd_data = reg_ctrl_config;
            end
            ADDR_TIMING_0: begin
                rd_data = reg_timing_0;
            end
            ADDR_TIMING_1: begin
                rd_data = reg_timing_1;
            end
            ADDR_TIMING_2: begin
                rd_data = reg_timing_2;
            end
            ADDR_TIMING_3: begin
                rd_data = reg_timing_3;
            end
            ADDR_REFRESH_CONFIG: begin
                rd_data = reg_refresh_config;
            end
            ADDR_ERROR_STATUS: begin
                rd_data[15:0] = sts_ecc_ce_count;
                rd_data[16] = reg_error_status[16];
                rd_data[17] = reg_error_status[17];
                rd_data[18] = reg_error_status[18];
                rd_data[31:19] = sts_bist_fail_addr;
            end
            ADDR_BIST_CONFIG: begin
                rd_data = reg_bist_config;
            end
            ADDR_BIST_ADDR_START: begin
                rd_data = reg_bist_addr_start;
            end
            ADDR_BIST_ADDR_END: begin
                rd_data = reg_bist_addr_end;
            end
            default: rd_data = 32'h00000000;
        endcase
    end

    // Read data output register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            csr_dat_o <= 32'h00000000;
        end else if (bus_rd) begin
            csr_dat_o <= rd_data;
        end
    end

    // Config output assignments
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

    // SVA assertions
    // synopsys translate_off
    logic [CSR_DATA_W-1:0] timing_0_snapshot;

    p_rw_retain: assert property (
        @(posedge clk) disable iff (!rst_n)
        (bus_wr && addr_valid && (csr_adr_i == ADDR_TIMING_0)) |=>
        (reg_timing_0 == $past(timing_0_snapshot))
    );

    always_ff @(posedge clk) begin
        if (bus_wr && addr_valid && (csr_adr_i == ADDR_TIMING_0)) begin
            for (int i = 0; i < 4; i++) begin
                if (wr_be[i]) begin
                    timing_0_snapshot[i*8 +: 8] <= csr_dat_i[i*8 +: 8];
                end else begin
                    timing_0_snapshot[i*8 +: 8] <= reg_timing_0[i*8 +: 8];
                end
            end
        end
    end

    p_bad_addr: assert property (
        @(posedge clk) disable iff (!rst_n)
        (bus_req && !addr_valid) |=> csr_err_o
    );
    // synopsys translate_on

endmodule
