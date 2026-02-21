////////////////////////////////////////////////////////////////////////////////
// Module:    config_regs
// File:      config_regs.sv
// Generated: 2026-02-20 13:27:05
// Agent:     Config/CSR Registers Agent (Phase 1)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
// Schema:    2.0.0
//
// Description:
//   11 CSR registers, 46 bit fields.
//   Wishbone B4 classic slave on secondary CSR bus.
//   Access types: RO, RW, RW1C, WO (self-clearing).
//   Outputs cfg_* buses consumed by bank_tracker, scheduler,
//   refresh_ctrl, and init_fsm.
//
// Validation: CA-001 .. CA-004  (ddr3_validation_checklist_v2.docx)
////////////////////////////////////////////////////////////////////////////////

module config_regs #(
    parameter CSR_ADDR_W = 8,
    parameter CSR_DATA_W = 32
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,
    input  logic                    rst_n,

    // ────────────── CSR Wishbone Slave ──────────────
    input  logic                    csr_cyc_i,
    input  logic                    csr_stb_i,
    input  logic                    csr_we_i,
    input  logic [CSR_ADDR_W-1:0]   csr_adr_i,
    input  logic [CSR_DATA_W-1:0]   csr_dat_i,
    input  logic [3:0]              csr_sel_i,

    output logic                    csr_ack_o,
    output logic [CSR_DATA_W-1:0]   csr_dat_o,
    output logic                    csr_err_o,

    // ────────────── Status inputs (from other modules) ──────────────
    input  logic                    sts_init_done,
    input  logic                    sts_cal_done,
    input  logic                    sts_cal_fail,
    input  logic                    sts_bist_done,
    input  logic                    sts_bist_fail,
    input  logic [2:0]              sts_ref_pending_cnt,
    input  logic                    sts_self_refresh_active,
    input  logic [15:0]             sts_ecc_ce_count,
    input  logic                    sts_ecc_ue_event,      // pulse
    input  logic                    sts_ref_starve_event,  // pulse
    input  logic                    sts_init_fail_event,   // pulse
    input  logic [12:0]             sts_bist_fail_addr,

    // ────────────── Config outputs (to other modules) ──────────────
    // Timing (from TIMING_0..3)
    output logic [7:0]              cfg_tRCD_nCK,
    output logic [7:0]              cfg_tRP_nCK,
    output logic [7:0]              cfg_tRAS_nCK,
    output logic [7:0]              cfg_tRC_nCK,
    output logic [7:0]              cfg_tRRD_nCK,
    output logic [7:0]              cfg_tWTR_nCK,
    output logic [7:0]              cfg_tFAW_nCK,
    output logic [7:0]              cfg_tRFC_nCK,
    output logic [7:0]              cfg_tWR_nCK,
    output logic [7:0]              cfg_tRTP_nCK,
    output logic [7:0]              cfg_CL_nCK,
    output logic [7:0]              cfg_CWL_nCK,
    output logic [7:0]              cfg_tCCD_nCK,
    output logic [23:0]             cfg_tREFI_nCK,

    // Control (from CTRL_CONFIG)
    output logic                    cfg_sched_policy,     // 0=in_order, 1=fr_fcfs
    output logic                    cfg_row_policy,       // 0=open, 1=close
    output logic [1:0]              cfg_self_ref_mode,
    output logic                    cfg_ecc_enable,
    output logic                    cfg_bist_start,       // pulse (self-clearing)
    output logic                    cfg_force_refresh,    // pulse (self-clearing)
    output logic                    cfg_force_self_ref,   // pulse (self-clearing)

    // Refresh (from REFRESH_CONFIG)
    output logic [3:0]              cfg_max_postpone,
    output logic [3:0]              cfg_urgent_threshold,
    output logic                    cfg_ref_priority,

    // BIST (from BIST_CONFIG, BIST_ADDR_START/END)
    output logic [2:0]              cfg_bist_pattern,
    output logic                    cfg_bist_addr_mode,
    output logic [28:0]             cfg_bist_addr_start,
    output logic [28:0]             cfg_bist_addr_end
);

    // ================================================================
    // Register offsets
    // ================================================================
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

    // ================================================================
    // Register storage
    // ================================================================
    // CTRL_STATUS — read-only, assembled from status inputs
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

    // ================================================================
    // CSR bus handshake
    // ================================================================
    wire csr_req = csr_cyc_i & csr_stb_i;
    wire csr_wr  = csr_req & csr_we_i;
    wire csr_rd  = csr_req & ~csr_we_i;

    // Ack — one-cycle response (classic Wishbone)
    logic ack_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) ack_r <= 1'b0;
        else        ack_r <= csr_req & ~ack_r;  // single-cycle ack
    assign csr_ack_o = ack_r;

    // Address decode — error on unmapped address
    logic addr_valid;
    always_comb begin
        addr_valid = 1'b0;
        case (csr_adr_i)
            ADDR_CTRL_STATUS         : addr_valid = 1'b1;
            ADDR_CTRL_CONFIG         : addr_valid = 1'b1;
            ADDR_TIMING_0            : addr_valid = 1'b1;
            ADDR_TIMING_1            : addr_valid = 1'b1;
            ADDR_TIMING_2            : addr_valid = 1'b1;
            ADDR_TIMING_3            : addr_valid = 1'b1;
            ADDR_REFRESH_CONFIG      : addr_valid = 1'b1;
            ADDR_ERROR_STATUS        : addr_valid = 1'b1;
            ADDR_BIST_CONFIG         : addr_valid = 1'b1;
            ADDR_BIST_ADDR_START     : addr_valid = 1'b1;
            ADDR_BIST_ADDR_END       : addr_valid = 1'b1;
            default: addr_valid = 1'b0;
        endcase
    end

    logic err_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) err_r <= 1'b0;
        else        err_r <= csr_req & ~addr_valid & ~ack_r;
    assign csr_err_o = err_r;

    // ================================================================
    // Write logic
    // ================================================================
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

            // Self-clearing WO fields (pulse for one cycle)
            reg_ctrl_config[5:5] <= 1'b0;  // bist_start (WO self-clear)
            reg_ctrl_config[6:6] <= 1'b0;  // force_refresh (WO self-clear)
            reg_ctrl_config[7:7] <= 1'b0;  // force_self_ref (WO self-clear)

            // RW1C fields — latch on event, clear on write-1
            if (sts_ecc_ue_event)
                reg_error_status[16] <= 1'b1;  // latch ecc_ue_flag
            if (sts_ref_starve_event)
                reg_error_status[17] <= 1'b1;  // latch ref_starve_flag
            if (sts_init_fail_event)
                reg_error_status[18] <= 1'b1;  // latch init_fail_flag

            // Bus writes
            if (csr_wr && addr_valid) begin
                case (csr_adr_i)
                    ADDR_CTRL_CONFIG: begin
                        reg_ctrl_config[0] <= csr_dat_i[0];  // sched_policy
                        reg_ctrl_config[1] <= csr_dat_i[1];  // row_policy
                        reg_ctrl_config[3:2] <= csr_dat_i[3:2];  // self_ref_mode
                        reg_ctrl_config[4] <= csr_dat_i[4];  // ecc_enable
                        reg_ctrl_config[5] <= csr_dat_i[5];  // bist_start
                        reg_ctrl_config[6] <= csr_dat_i[6];  // force_refresh
                        reg_ctrl_config[7] <= csr_dat_i[7];  // force_self_ref
                    end
                    ADDR_TIMING_0: begin
                        reg_timing_0[7:0] <= csr_dat_i[7:0];  // tRCD_nCK
                        reg_timing_0[15:8] <= csr_dat_i[15:8];  // tRP_nCK
                        reg_timing_0[23:16] <= csr_dat_i[23:16];  // tRAS_nCK
                        reg_timing_0[31:24] <= csr_dat_i[31:24];  // tRC_nCK
                    end
                    ADDR_TIMING_1: begin
                        reg_timing_1[7:0] <= csr_dat_i[7:0];  // tRRD_nCK
                        reg_timing_1[15:8] <= csr_dat_i[15:8];  // tWTR_nCK
                        reg_timing_1[23:16] <= csr_dat_i[23:16];  // tFAW_nCK
                        reg_timing_1[31:24] <= csr_dat_i[31:24];  // tRFC_nCK
                    end
                    ADDR_TIMING_2: begin
                        reg_timing_2[7:0] <= csr_dat_i[7:0];  // tWR_nCK
                        reg_timing_2[15:8] <= csr_dat_i[15:8];  // tRTP_nCK
                        reg_timing_2[23:16] <= csr_dat_i[23:16];  // CL_nCK
                        reg_timing_2[31:24] <= csr_dat_i[31:24];  // CWL_nCK
                    end
                    ADDR_TIMING_3: begin
                        reg_timing_3[7:0] <= csr_dat_i[7:0];  // tCCD_nCK
                        reg_timing_3[31:8] <= csr_dat_i[31:8];  // tREFI_nCK
                    end
                    ADDR_REFRESH_CONFIG: begin
                        reg_refresh_config[3:0] <= csr_dat_i[3:0];  // max_postpone
                        reg_refresh_config[7:4] <= csr_dat_i[7:4];  // urgent_threshold
                        reg_refresh_config[8] <= csr_dat_i[8];  // ref_priority
                    end
                    ADDR_ERROR_STATUS: begin
                        if (csr_dat_i[16]) reg_error_status[16] <= 1'b0;  // W1C ecc_ue_flag
                        if (csr_dat_i[17]) reg_error_status[17] <= 1'b0;  // W1C ref_starve_flag
                        if (csr_dat_i[18]) reg_error_status[18] <= 1'b0;  // W1C init_fail_flag
                    end
                    ADDR_BIST_CONFIG: begin
                        reg_bist_config[2:0] <= csr_dat_i[2:0];  // bist_pattern
                        reg_bist_config[3] <= csr_dat_i[3];  // bist_addr_mode
                    end
                    ADDR_BIST_ADDR_START: begin
                        reg_bist_addr_start[28:0] <= csr_dat_i[28:0];  // start_addr
                    end
                    ADDR_BIST_ADDR_END: begin
                        reg_bist_addr_end[28:0] <= csr_dat_i[28:0];  // end_addr
                    end
                    default: ;
                endcase
            end
        end
    end

    // ================================================================
    // Read mux
    // ================================================================
    logic [CSR_DATA_W-1:0] rdata_mux;

    always_comb begin
        rdata_mux = 32'h0;
        case (csr_adr_i)
            ADDR_CTRL_STATUS: begin
                rdata_mux = 32'h0;
                rdata_mux[0] = sts_init_done;
                rdata_mux[1] = sts_cal_done;
                rdata_mux[2] = sts_cal_fail;
                rdata_mux[3] = sts_bist_done;
                rdata_mux[4] = sts_bist_fail;
                rdata_mux[7:5] = sts_ref_pending_cnt;
                rdata_mux[8] = sts_self_refresh_active;
                rdata_mux[31:9] = 23'b0;
            end
            ADDR_CTRL_CONFIG: begin
                rdata_mux = reg_ctrl_config;
            end
            ADDR_TIMING_0: begin
                rdata_mux = reg_timing_0;
            end
            ADDR_TIMING_1: begin
                rdata_mux = reg_timing_1;
            end
            ADDR_TIMING_2: begin
                rdata_mux = reg_timing_2;
            end
            ADDR_TIMING_3: begin
                rdata_mux = reg_timing_3;
            end
            ADDR_REFRESH_CONFIG: begin
                rdata_mux = reg_refresh_config;
            end
            ADDR_ERROR_STATUS: begin
                rdata_mux = reg_error_status;
            end
            ADDR_BIST_CONFIG: begin
                rdata_mux = reg_bist_config;
            end
            ADDR_BIST_ADDR_START: begin
                rdata_mux = reg_bist_addr_start;
            end
            ADDR_BIST_ADDR_END: begin
                rdata_mux = reg_bist_addr_end;
            end
            default: rdata_mux = 32'hDEAD_BEEF;
        endcase
    end

    // Registered read output
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) csr_dat_o <= 32'h0;
        else if (csr_rd) csr_dat_o <= rdata_mux;

    // ================================================================
    // Configuration outputs
    // ================================================================

    // Timing (TIMING_0)
    assign cfg_tRCD_nCK       = reg_timing_0[7:0];
    assign cfg_tRP_nCK        = reg_timing_0[15:8];
    assign cfg_tRAS_nCK       = reg_timing_0[23:16];
    assign cfg_tRC_nCK        = reg_timing_0[31:24];

    // Timing (TIMING_1)
    assign cfg_tRRD_nCK       = reg_timing_1[7:0];
    assign cfg_tWTR_nCK       = reg_timing_1[15:8];
    assign cfg_tFAW_nCK       = reg_timing_1[23:16];
    assign cfg_tRFC_nCK       = reg_timing_1[31:24];

    // Timing (TIMING_2)
    assign cfg_tWR_nCK        = reg_timing_2[7:0];
    assign cfg_tRTP_nCK       = reg_timing_2[15:8];
    assign cfg_CL_nCK         = reg_timing_2[23:16];
    assign cfg_CWL_nCK        = reg_timing_2[31:24];

    // Timing (TIMING_3)
    assign cfg_tCCD_nCK       = reg_timing_3[7:0];
    assign cfg_tREFI_nCK      = reg_timing_3[31:8];

    // Control (CTRL_CONFIG)
    assign cfg_sched_policy   = reg_ctrl_config[0];
    assign cfg_row_policy     = reg_ctrl_config[1];
    assign cfg_self_ref_mode  = reg_ctrl_config[3:2];
    assign cfg_ecc_enable     = reg_ctrl_config[4];
    assign cfg_bist_start     = reg_ctrl_config[5];
    assign cfg_force_refresh  = reg_ctrl_config[6];
    assign cfg_force_self_ref = reg_ctrl_config[7];

    // Refresh (REFRESH_CONFIG)
    assign cfg_max_postpone      = reg_refresh_config[3:0];
    assign cfg_urgent_threshold  = reg_refresh_config[7:4];
    assign cfg_ref_priority      = reg_refresh_config[8];

    // BIST
    assign cfg_bist_pattern      = reg_bist_config[2:0];
    assign cfg_bist_addr_mode    = reg_bist_config[3];
    assign cfg_bist_addr_start   = reg_bist_addr_start[28:0];
    assign cfg_bist_addr_end     = reg_bist_addr_end[28:0];

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // CA-001: Read after write — RW register retains value
    property p_rw_retain;
        @(posedge clk) disable iff (!rst_n)
        (csr_wr && csr_adr_i == ADDR_TIMING_0) |=>
            (reg_timing_0[7:0] == $past(csr_dat_i[7:0]));
    endproperty
    assert property (p_rw_retain)
        else $error("[CA-001] RW register did not retain written value");

    // CA-002: RO register ignores writes
    property p_ro_ignore;
        @(posedge clk) disable iff (!rst_n)
        (csr_wr && csr_adr_i == ADDR_CTRL_STATUS) |=>
            1'b1;  // no storage for CTRL_STATUS, always assembled from inputs
    endproperty
    assert property (p_ro_ignore)
        else $error("[CA-002] RO register was modified");

    // CA-003: WO self-clearing fields clear after one cycle
    property p_wo_clear;
        @(posedge clk) disable iff (!rst_n)
        (csr_wr && csr_adr_i == ADDR_CTRL_CONFIG && csr_dat_i[5]) |=>
            (reg_ctrl_config[5] == 1'b1) ##1 (reg_ctrl_config[5] == 1'b0);
    endproperty
    assert property (p_wo_clear)
        else $error("[CA-003] WO field did not self-clear");

    // CA-004: Invalid address returns error
    property p_bad_addr;
        @(posedge clk) disable iff (!rst_n)
        (csr_req && !addr_valid) |=> csr_err_o;
    endproperty
    assert property (p_bad_addr)
        else $error("[CA-004] No error on invalid CSR address");

    // Functional coverage
    covergroup cg_csr @(posedge clk);
        option.per_instance = 1;
        cp_write   : coverpoint (csr_wr && addr_valid);
        cp_read    : coverpoint (csr_rd && addr_valid);
        cp_err     : coverpoint csr_err_o;
        cp_bist_go : coverpoint cfg_bist_start;
        cp_fref    : coverpoint cfg_force_refresh;
    endgroup
    cg_csr cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule