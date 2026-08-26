module path_01_write_cmd_tb;

    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic [2:0] addr_decoder_dec_bank;
    logic [9:0] addr_decoder_dec_col;
    logic [14:0] addr_decoder_dec_row;
    logic [3:0] cmd_queue_entry_aux [0:15];
    logic [2:0] cmd_queue_entry_bank [0:15];
    logic [9:0] cmd_queue_entry_col [0:15];
    logic [14:0] cmd_queue_entry_row [0:15];
    logic [15:0] cmd_queue_entry_valid;
    logic        cmd_queue_entry_we [0:15];
    logic        deq_grant;
    logic [3:0] deq_idx;
    logic [28:0] req_addr;
    logic [3:0] scheduler_cmd_aux;
    logic [2:0] scheduler_cmd_bank;
    logic [9:0] scheduler_cmd_col;
    logic [14:0] scheduler_cmd_row;
    logic [3:0] scheduler_cmd_type;
    logic        scheduler_cmd_valid;
    logic        scheduler_cmd_we;
    logic [3:0] wb_port_req_aux;
    logic        wb_port_req_valid;
    logic        wb_port_req_we;

    // ---- Testbench-driven inputs ----
    logic        wb_cyc_i;
    logic        wb_stb_i;
    logic        wb_we_i;
    logic [28:0] wb_adr_i;
    logic [31:0] wb_dat_i;
    logic [3:0] wb_sel_i;
    logic [1:0] wb_bte_i;
    logic [2:0] wb_cti_i;
    logic        req_ready;
    logic        rsp_valid;
    logic [31:0] rsp_rdata;
    logic [3:0] rsp_aux;
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [7:0] bank_pre_allowed;
    logic        ref_required;
    logic        ref_urgent;
    logic [14:0] bank_open_row_0;

    // ---- Testbench-monitored outputs ----
    logic        wb_ack_o;
    logic [31:0] wb_dat_o;
    logic        wb_stall_o;
    logic        wb_err_o;
    logic [31:0] req_wdata;
    logic [3:0] req_wmask;
    logic        dec_rank;
    logic        enq_ready;
    logic        queue_full;
    logic        queue_empty;
    logic [4:0] queue_count;
    logic        ref_ack;
    logic [3:0] ddr_cmd;
    logic [14:0] ddr_addr;
    logic [2:0] ddr_bank;
    logic        ddr_cke;
    logic        ddr_reset_n;
    logic        ddr_odt;
    logic        fb_act_valid;
    logic [2:0] fb_act_bank;
    logic [14:0] fb_act_row;
    logic        fb_pre_valid;
    logic        fb_rd_valid;
    logic        fb_wr_valid;
    logic        fb_ref_valid;

    // ---- Module instantiations ----
    wb_port u_wb_port (
        .clk(clk),
        .rst_n(rst_n),
        .req_addr(req_addr),
        .req_aux(wb_port_req_aux),
        .req_ready(req_ready),
        .req_valid(wb_port_req_valid),
        .req_wdata(req_wdata),
        .req_we(wb_port_req_we),
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

    addr_decoder u_addr_decoder (
        .dec_bank(addr_decoder_dec_bank),
        .dec_col(addr_decoder_dec_col),
        .dec_rank(dec_rank),
        .dec_row(addr_decoder_dec_row),
        .req_addr(req_addr)
    );

    cmd_queue u_cmd_queue (
        .clk(clk),
        .rst_n(rst_n),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .enq_aux(wb_port_req_aux),
        .enq_bank(addr_decoder_dec_bank),
        .enq_col(addr_decoder_dec_col),
        .enq_ready(enq_ready),
        .enq_row(addr_decoder_dec_row),
        .enq_valid(wb_port_req_valid),
        .enq_we(wb_port_req_we),
        .entry_aux(cmd_queue_entry_aux),
        .entry_bank(cmd_queue_entry_bank),
        .entry_col(cmd_queue_entry_col),
        .entry_row(cmd_queue_entry_row),
        .entry_valid(cmd_queue_entry_valid),
        .entry_we(cmd_queue_entry_we),
        .queue_count(queue_count),
        .queue_empty(queue_empty),
        .queue_full(queue_full)
    );

    scheduler u_scheduler (
        .clk(clk),
        .rst_n(rst_n),
        .bank_act_allowed(bank_act_allowed),
        .bank_is_active(bank_is_active),
        .bank_open_row(bank_open_row),
        .bank_pre_allowed(bank_pre_allowed),
        .bank_rd_allowed(bank_rd_allowed),
        .bank_wr_allowed(bank_wr_allowed),
        .cmd_aux(scheduler_cmd_aux),
        .cmd_bank(scheduler_cmd_bank),
        .cmd_col(scheduler_cmd_col),
        .cmd_row(scheduler_cmd_row),
        .cmd_type(scheduler_cmd_type),
        .cmd_valid(scheduler_cmd_valid),
        .cmd_we(scheduler_cmd_we),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .q_aux(cmd_queue_entry_aux),
        .q_bank(cmd_queue_entry_bank),
        .q_col(cmd_queue_entry_col),
        .q_row(cmd_queue_entry_row),
        .q_valid(cmd_queue_entry_valid),
        .q_we(cmd_queue_entry_we),
        .ref_ack(ref_ack),
        .ref_required(ref_required),
        .ref_urgent(ref_urgent)
    );

    cmd_gen u_cmd_gen (
        .clk(clk),
        .rst_n(rst_n),
        .ddr_addr(ddr_addr),
        .ddr_bank(ddr_bank),
        .ddr_cke(ddr_cke),
        .ddr_cmd(ddr_cmd),
        .ddr_odt(ddr_odt),
        .ddr_reset_n(ddr_reset_n),
        .fb_act_bank(fb_act_bank),
        .fb_act_row(fb_act_row),
        .fb_act_valid(fb_act_valid),
        .fb_pre_valid(fb_pre_valid),
        .fb_rd_valid(fb_rd_valid),
        .fb_ref_valid(fb_ref_valid),
        .fb_wr_valid(fb_wr_valid),
        .sched_aux(scheduler_cmd_aux),
        .sched_bank(scheduler_cmd_bank),
        .sched_col(scheduler_cmd_col),
        .sched_row(scheduler_cmd_row),
        .sched_type(scheduler_cmd_type),
        .sched_valid(scheduler_cmd_valid),
        .sched_we(scheduler_cmd_we)
    );

    // ---- Single-entry mode: scalar aliases for array entry [0] ----
    assign bank_open_row[0] = bank_open_row_0;
    assign bank_open_row[1] = '0;
    assign bank_open_row[2] = '0;
    assign bank_open_row[3] = '0;
    assign bank_open_row[4] = '0;
    assign bank_open_row[5] = '0;
    assign bank_open_row[6] = '0;
    assign bank_open_row[7] = '0;

    // ---- Clock generation ----
    initial begin
        clk = 1'b0;
        forever #2.5 clk = ~clk;
    end

    // ---- Output history buffer for ±2 cycle tolerance checking ----
    logic [31:0] out_history [0:2];
    always @(posedge clk) begin
        out_history[2] <= out_history[1];
        out_history[1] <= out_history[0];
        out_history[0] <= pack_outputs();
    end

    // ---- Mandatory functions ----
    function automatic logic [31:0] pack_outputs();
        logic [31:0] packed_val;
        packed_val = 32'b0;
        packed_val[0] = wb_ack_o;
        return packed_val;
    endfunction

    task automatic unpack_drive(input logic [31:0] packed_val);
        wb_cyc_i = packed_val[0];
        wb_stb_i = packed_val[1];
        wb_we_i = packed_val[2];
        wb_adr_i = packed_val[31:3];
    endtask

    task automatic check_with_tolerance(
        input int vec_num,
        input logic [31:0] expected,
        inout int pass_count,
        inout int fail_count,
        inout int total_tests
    );
        logic [31:0] actual;
        actual = pack_outputs();
        total_tests = total_tests + 1;
        if (actual === expected ||
            out_history[0] === expected ||
            out_history[1] === expected ||
            out_history[2] === expected) begin
            pass_count = pass_count + 1;
        end else begin
            fail_count = fail_count + 1;
            $display("MISMATCH vec=%0d expected=0x%08X actual=0x%08X", vec_num, expected, actual);
        end
    endtask

    task automatic handle_reset();
        rst_n = 1'b0;
        wb_cyc_i = '0;
        wb_stb_i = '0;
        wb_we_i = '0;
        wb_adr_i = '0;
        repeat(4) @(posedge clk);
        rst_n = 1'b1;
        @(posedge clk);
    endtask

    // ---- Watchdog timer ----
    initial begin
        repeat(200000) @(posedge clk);
        $display("ERROR: Watchdog timeout after 200000 cycles");
        $finish;
    end

    // ---- Main test sequence ----
    initial begin
        string vector_file;
        int fd;
        int status;
        int vec_num;
        int pass_count;
        int fail_count;
        int total_tests;
        logic [7:0] opcode;
        logic [31:0] param;
        logic [31:0] drive_val;
        logic [31:0] expect_val;

        // Initialize counters
        pass_count = 0;
        fail_count = 0;
        total_tests = 0;
        vec_num = 0;

        // Initialize testbench-driven inputs to defaults
        rst_n = 1'b1;
        wb_cyc_i = '0;
        wb_stb_i = '0;
        wb_we_i = '0;
        wb_adr_i = '0;
        wb_dat_i = '0;
        wb_sel_i = '0;
        wb_bte_i = '0;
        wb_cti_i = '0;
        req_ready = 1'b1;
        rsp_valid = '0;
        rsp_rdata = '0;
        rsp_aux = '0;
        bank_is_active = '0;
        bank_open_row_0 = '0;
        bank_act_allowed = 8'hFF;
        bank_rd_allowed = 8'hFF;
        bank_wr_allowed = 8'hFF;
        bank_pre_allowed = 8'hFF;
        ref_required = '0;
        ref_urgent = '0;

        // Initialize output history
        out_history[0] = '0;
        out_history[1] = '0;
        out_history[2] = '0;

        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "path_01_write_cmd_vectors.hex";
        end

        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Cannot open vector file: %s", vector_file);
            $finish;
        end

        // Wait for initial clock edge
        @(posedge clk);

        // Process vectors
        while (!$feof(fd)) begin
            status = $fscanf(fd, "%h %h %h %h", opcode, param, drive_val, expect_val);
            if (status != 4) begin
                continue;
            end

            case (opcode)
                8'h00: begin
                    // Reset
                    handle_reset();
                end
                8'h01: begin
                    // Drive
                    unpack_drive(drive_val);
                    @(posedge clk);
                end
                8'h02: begin
                    // Check
                    @(posedge clk);
                    check_with_tolerance(vec_num, expect_val, pass_count, fail_count, total_tests);
                end
                8'h03: begin
                    // Step
                    repeat(param) @(posedge clk);
                end
                default: begin
                    $display("WARNING: Unknown opcode 0x%02X at vector %0d", opcode, vec_num);
                end
            endcase

            vec_num = vec_num + 1;
        end

        $fclose(fd);

        // Print summary
        $display("==================================================");
        $display("Test: path_01_write_cmd");
        $display("Total tests: %0d", total_tests);
        $display("Pass: %0d", pass_count);
        $display("Fail: %0d", fail_count);
        $display("==================================================");

        if (fail_count == 0) begin
            $display("PASS: All tests passed");
        end else begin
            $display("FAIL: %0d tests failed", fail_count);
        end

        $finish;
    end

endmodule