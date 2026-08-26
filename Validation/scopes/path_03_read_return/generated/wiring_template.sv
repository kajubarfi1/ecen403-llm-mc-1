    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic [3:0] rsp_aux;
    logic [31:0] rsp_rdata;
    logic        rsp_valid;

    // ---- Testbench-driven inputs ----
    logic        cmd_wr_valid;
    logic        cmd_rd_valid;
    logic [3:0] cmd_aux;
    logic        wr_data_valid;
    logic [31:0] wr_data;
    logic [3:0] wr_mask;
    logic [7:0] cfg_CL_nCK;
    logic [7:0] cfg_CWL_nCK;
    logic [31:0] ddr_dq_i;
    logic        ddr_dqs_i;
    logic        wb_cyc_i;
    logic        wb_stb_i;
    logic        wb_we_i;
    logic [28:0] wb_adr_i;
    logic [31:0] wb_dat_i;
    logic [3:0] wb_sel_i;
    logic [1:0] wb_bte_i;
    logic [2:0] wb_cti_i;
    logic        req_ready;

    // ---- Testbench-monitored outputs ----
    logic        wr_data_ready;
    logic        rd_rsp_valid;
    logic [31:0] rd_rsp_data;
    logic [3:0] rd_rsp_aux;
    logic [31:0] ddr_dq_o;
    logic        ddr_dq_oe;
    logic [3:0] ddr_dm_o;
    logic        ddr_dqs_o;
    logic        ddr_dqs_oe;
    logic        wb_ack_o;
    logic [31:0] wb_dat_o;
    logic        wb_stall_o;
    logic        wb_err_o;
    logic        req_valid;
    logic        req_we;
    logic [28:0] req_addr;
    logic [31:0] req_wdata;
    logic [3:0] req_wmask;
    logic [3:0] req_aux;

    // ---- Module instantiations ----
    data_path u_data_path (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_CL_nCK(cfg_CL_nCK),
        .cfg_CWL_nCK(cfg_CWL_nCK),
        .cmd_aux(cmd_aux),
        .cmd_rd_valid(cmd_rd_valid),
        .cmd_wr_valid(cmd_wr_valid),
        .ddr_dm_o(ddr_dm_o),
        .ddr_dq_i(ddr_dq_i),
        .ddr_dq_o(ddr_dq_o),
        .ddr_dq_oe(ddr_dq_oe),
        .ddr_dqs_i(ddr_dqs_i),
        .ddr_dqs_o(ddr_dqs_o),
        .ddr_dqs_oe(ddr_dqs_oe),
        .rd_rsp_aux(rd_rsp_aux),
        .rd_rsp_data(rd_rsp_data),
        .rd_rsp_valid(rd_rsp_valid),
        .wr_data(wr_data),
        .wr_data_ready(wr_data_ready),
        .wr_data_valid(wr_data_valid),
        .wr_mask(wr_mask)
    );

    wb_port u_wb_port (
        .clk(clk),
        .rst_n(rst_n),
        .req_addr(req_addr),
        .req_aux(req_aux),
        .req_ready(req_ready),
        .req_valid(req_valid),
        .req_wdata(req_wdata),
        .req_we(req_we),
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
