////////////////////////////////////////////////////////////////////////////////
// Module:    wb_port
// File:      wb_port.sv
// Generated: 2026-03-23 14:56:02
// Agent:     Wishbone Port Interface Agent (Phase 1)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// Description:
//   Wishbone B4 pipelined slave. Backpressure (stall), linear burst (BL8),
//   byte-lane masking, error signalling, auxiliary tag propagation.
//
// Derived: DATA=32 ADDR=29 SEL=4 AUX=4 BURST=8 QUEUE=16
// Validation: WB-001 .. WB-009
////////////////////////////////////////////////////////////////////////////////

module wb_port #(
    parameter DATA_WIDTH     = 32,
    parameter ADDR_WIDTH     = 29,
    parameter SEL_WIDTH      = 4,
    parameter AUX_WIDTH      = 4,
    parameter MAX_BURST_LEN  = 8,
    parameter QUEUE_DEPTH    = 16,
    parameter BURST_CTR_W    = 4,
    parameter TAG_FIFO_DEPTH = 16,
    parameter TAG_PTR_W      = 5
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Wishbone B4 Pipelined Slave
    input  logic                    wb_cyc_i,
    input  logic                    wb_stb_i,
    input  logic                    wb_we_i,
    input  logic [ADDR_WIDTH-1:0]   wb_adr_i,
    input  logic [DATA_WIDTH-1:0]   wb_dat_i,
    input  logic [SEL_WIDTH-1:0]    wb_sel_i,
    input  logic [1:0]              wb_bte_i,
    input  logic [2:0]              wb_cti_i,

    output logic                    wb_ack_o,
    output logic [DATA_WIDTH-1:0]   wb_dat_o,
    output logic                    wb_stall_o,
    output logic                    wb_err_o,

    // Internal -> Command Queue
    output logic                    req_valid,
    output logic                    req_we,
    output logic [ADDR_WIDTH-1:0]   req_addr,
    output logic [DATA_WIDTH-1:0]   req_wdata,
    output logic [SEL_WIDTH-1:0]    req_wmask,
    output logic [AUX_WIDTH-1:0]    req_aux,
    input  logic                    req_ready,

    // Internal <- Data Path
    input  logic                    rsp_valid,
    input  logic [DATA_WIDTH-1:0]   rsp_rdata,
    input  logic [AUX_WIDTH-1:0]    rsp_aux
);

    // CTI / BTE encodings
    localparam logic [2:0] CTI_CLASSIC = 3'b000;
    localparam logic [2:0] CTI_CONST   = 3'b001;
    localparam logic [2:0] CTI_INC     = 3'b010;
    localparam logic [2:0] CTI_END     = 3'b111;
    localparam logic [1:0] BTE_LINEAR  = 2'b00;
    localparam int unsigned ADDR_INC = DATA_WIDTH / 8;

    wire wb_beat = wb_cyc_i & wb_stb_i & ~wb_stall_o;

    // Aux-tag counter (WB-009) -- declared before tag FIFO
    logic [AUX_WIDTH-1:0] aux_ctr;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)       aux_ctr <= '0;
        else if (wb_beat) aux_ctr <= aux_ctr + 1'b1;

    // Tag FIFO -- tracks outstanding read requests
    logic [AUX_WIDTH-1:0] tag_mem [0:TAG_FIFO_DEPTH-1];
    logic [TAG_PTR_W:0]   tag_wr, tag_rd;
    wire  [TAG_PTR_W:0]   tag_cnt  = tag_wr - tag_rd;
    wire                   tag_full = (tag_cnt == TAG_FIFO_DEPTH[TAG_PTR_W:0]);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) tag_wr <= '0;
        else if (wb_beat && !wb_we_i) begin
            tag_mem[tag_wr[TAG_PTR_W-1:0]] <= aux_ctr;
            tag_wr <= tag_wr + 1'b1;
        end

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) tag_rd <= '0;
        else if (rsp_valid) tag_rd <= tag_rd + 1'b1;

    // Stall generation (WB-005)
    always_comb begin
        wb_stall_o = 1'b0;
        if (!req_ready)                        wb_stall_o = 1'b1;
        if (!wb_we_i && tag_full && wb_stb_i)  wb_stall_o = 1'b1;
    end

    // Burst tracker (WB-003, WB-004)
    logic                   burst_active;
    logic [BURST_CTR_W-1:0] burst_cnt;
    logic [ADDR_WIDTH-1:0]  burst_nxt_addr;
    logic                   burst_we;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            burst_active   <= 1'b0;
            burst_cnt      <= '0;
            burst_nxt_addr <= '0;
            burst_we       <= 1'b0;
        end else if (wb_beat) begin
            if (!burst_active && wb_cti_i == CTI_INC) begin
                burst_active   <= 1'b1;
                burst_cnt      <= 'd1;
                burst_nxt_addr <= wb_adr_i + ADDR_INC[ADDR_WIDTH-1:0];
                burst_we       <= wb_we_i;
            end else if (burst_active) begin
                burst_cnt      <= burst_cnt + 1'b1;
                burst_nxt_addr <= burst_nxt_addr + ADDR_INC[ADDR_WIDTH-1:0];
                if (wb_cti_i == CTI_END ||
                    burst_cnt == BURST_CTR_W'(MAX_BURST_LEN - 1)) begin
                    burst_active <= 1'b0;
                    burst_cnt    <= '0;
                end
            end
        end else if (!wb_cyc_i) begin
            burst_active <= 1'b0;
            burst_cnt    <= '0;
        end
    end

    // Request output (WB-001, WB-002)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_valid <= 1'b0; req_we <= 1'b0; req_addr <= '0;
            req_wdata <= '0; req_wmask <= '0; req_aux <= '0;
        end else begin
            req_valid <= 1'b0;
            if (wb_beat) begin
                req_valid <= 1'b1;
                req_we    <= wb_we_i;
                req_addr  <= wb_adr_i;
                req_wdata <= wb_dat_i;
                req_wmask <= wb_sel_i;
                req_aux   <= aux_ctr;
            end
        end
    end

    // Write acknowledge (WB-002, WB-008)
    logic wr_ack_r;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) wr_ack_r <= 1'b0;
        else        wr_ack_r <= wb_beat & wb_we_i;

    wire rd_ack = rsp_valid;
    assign wb_ack_o = wr_ack_r | rd_ack;
    assign wb_dat_o = rsp_rdata;

    // Error detection (WB-007)
    logic err_r;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) err_r <= 1'b0;
        else begin
            err_r <= 1'b0;
            if (wb_cyc_i && wb_stb_i) begin
                if (burst_active && (wb_we_i != burst_we)) err_r <= 1'b1;
                if (|wb_adr_i[$clog2(ADDR_INC)-1:0])      err_r <= 1'b1;
            end
        end
    end
    assign wb_err_o = err_r;

    // SVA -- simulation only
    // synopsys translate_off
    // synthesis translate_off

    property p_stall_hold;
        @(posedge clk) disable iff (!rst_n)
        (wb_cyc_i && wb_stb_i && wb_stall_o) |=> (wb_cyc_i && wb_stb_i);
    endproperty
    assert property (p_stall_hold)
        else $error("[WB-005] master released request during stall");

    property p_tag;
        @(posedge clk) disable iff (!rst_n)
        (rsp_valid && tag_cnt > 0) |-> (rsp_aux == tag_mem[tag_rd[TAG_PTR_W-1:0]]);
    endproperty
    assert property (p_tag)
        else $error("[WB-009] aux tag mismatch");

    property p_burst_len;
        @(posedge clk) disable iff (!rst_n)
        burst_active |-> (burst_cnt < BURST_CTR_W'(MAX_BURST_LEN));
    endproperty
    assert property (p_burst_len)
        else $error("[WB-003/004] burst exceeded MAX_BURST_LEN");

    property p_tag_no_overflow;
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (tag_cnt <= TAG_FIFO_DEPTH[TAG_PTR_W:0]);
    endproperty
    assert property (p_tag_no_overflow)
        else $error("[WB-005] tag FIFO overflow");

    property p_sel_nonzero_write;
        @(posedge clk) disable iff (!rst_n)
        (wb_beat && wb_we_i) |-> (|wb_sel_i);
    endproperty
    assert property (p_sel_nonzero_write)
        else $warning("[WB-006] write with zero sel");

    covergroup cg_wb @(posedge clk);
        option.per_instance = 1;
        cp_single_rd  : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_CLASSIC);
        cp_single_wr  : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_CLASSIC);
        cp_burst_rd   : coverpoint (wb_beat && !wb_we_i && wb_cti_i == CTI_INC);
        cp_burst_wr   : coverpoint (wb_beat &&  wb_we_i && wb_cti_i == CTI_INC);
        cp_burst_end  : coverpoint (wb_beat && wb_cti_i == CTI_END);
        cp_stall      : coverpoint wb_stall_o;
        cp_err        : coverpoint wb_err_o;
        cp_backtoback : coverpoint (wb_ack_o && wb_beat);
        cp_tag_full   : coverpoint tag_full;
    endgroup
    cg_wb cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule