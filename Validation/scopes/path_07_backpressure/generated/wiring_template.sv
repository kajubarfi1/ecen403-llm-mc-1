    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        cmd_queue_enq_ready;

    // ---- Testbench-driven inputs ----
    logic        enq_valid;
    logic [14:0] enq_row;
    logic [9:0] enq_col;
    logic [2:0] enq_bank;
    logic        enq_we;
    logic [3:0] enq_aux;
    logic        deq_grant;
    logic [3:0] deq_idx;
    logic        wb_cyc_i;
    logic        wb_stb_i;
    logic        wb_we_i;
    logic [28:0] wb_adr_i;
    logic [31:0] wb_dat_i;
    logic [3:0] wb_sel_i;
    logic [1:0] wb_bte_i;
    logic [2:0] wb_cti_i;
    logic        rsp_valid;
    logic [31:0] rsp_rdata;
    logic [3:0] rsp_aux;

    // ---- Testbench-monitored outputs ----
    logic [15:0] entry_valid;
    logic [14:0] entry_row [0:15];
    logic [9:0] entry_col [0:15];
    logic [2:0] entry_bank [0:15];
    logic        entry_we [0:15];
    logic [3:0] entry_aux [0:15];
    logic        queue_full;
    logic        queue_empty;
    logic [4:0] queue_count;
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
    cmd_queue u_cmd_queue (
        .clk(clk),
        .rst_n(rst_n),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .enq_aux(enq_aux),
        .enq_bank(enq_bank),
        .enq_col(enq_col),
        .enq_ready(cmd_queue_enq_ready),
        .enq_row(enq_row),
        .enq_valid(enq_valid),
        .enq_we(enq_we),
        .entry_aux(entry_aux),
        .entry_bank(entry_bank),
        .entry_col(entry_col),
        .entry_row(entry_row),
        .entry_valid(entry_valid),
        .entry_we(entry_we),
        .queue_count(queue_count),
        .queue_empty(queue_empty),
        .queue_full(queue_full)
    );

    wb_port u_wb_port (
        .clk(clk),
        .rst_n(rst_n),
        .req_addr(req_addr),
        .req_aux(req_aux),
        .req_ready(cmd_queue_enq_ready),
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
