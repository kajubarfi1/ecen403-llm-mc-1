module path_backpressure_tb;

    // Clock and reset
    logic clk, rst_n;

    // Wishbone bus (driven by testbench)
    logic        wb_cyc_i, wb_stb_i, wb_we_i;
    logic [28:0] wb_adr_i;
    logic [31:0] wb_dat_i;
    logic [3:0]  wb_sel_i;
    logic [1:0]  wb_bte_i;
    logic [2:0]  wb_cti_i;

    // Wishbone outputs (from wb_port)
    logic        wb_ack_o, wb_stall_o, wb_err_o;
    logic [31:0] wb_dat_o;

    // Internal wiring: wb_port -> cmd_queue
    logic        req_valid, req_we;
    logic [28:0] req_addr;
    logic [31:0] req_wdata;
    logic [3:0]  req_wmask;
    logic [3:0]  req_aux;
    logic        req_ready;   // cmd_queue -> wb_port (backpressure)

    // Read response (tie off — no data_path in this scope)
    logic        rsp_valid;
    logic [31:0] rsp_rdata;
    logic [3:0]  rsp_aux;

    // Address decode (inline combinational)
    wire [14:0] dec_row  = req_addr[28:17];
    wire [9:0]  dec_col  = req_addr[16:7];
    wire [2:0]  dec_bank = req_addr[6:4];

    // Queue status outputs
    logic        enq_ready;
    logic [15:0] entry_valid;
    logic [4:0]  queue_count;
    logic        queue_empty, queue_full;

    // Queue dequeue interface (driven by testbench)
    logic        deq_grant;
    logic [3:0]  deq_idx;

    // Tie off read response
    assign rsp_valid = 1'b0;
    assign rsp_rdata = 32'h0;
    assign rsp_aux   = 4'h0;

    // Backpressure wire
    assign req_ready = enq_ready;

    wb_port u_wb_port (
        .clk(clk), .rst_n(rst_n),
        .wb_cyc_i(wb_cyc_i), .wb_stb_i(wb_stb_i), .wb_we_i(wb_we_i),
        .wb_adr_i(wb_adr_i), .wb_dat_i(wb_dat_i), .wb_sel_i(wb_sel_i),
        .wb_bte_i(wb_bte_i), .wb_cti_i(wb_cti_i),
        .wb_ack_o(wb_ack_o), .wb_dat_o(wb_dat_o),
        .wb_stall_o(wb_stall_o), .wb_err_o(wb_err_o),
        .req_valid(req_valid), .req_we(req_we), .req_addr(req_addr),
        .req_wdata(req_wdata), .req_wmask(req_wmask), .req_aux(req_aux),
        .req_ready(req_ready),
        .rsp_valid(rsp_valid), .rsp_rdata(rsp_rdata), .rsp_aux(rsp_aux)
    );

    cmd_queue u_cmd_queue (
        .clk(clk), .rst_n(rst_n),
        .enq_valid(req_valid), .enq_we(req_we),
        .enq_row(dec_row), .enq_col(dec_col), .enq_bank(dec_bank),
        .enq_aux(req_aux),
        .enq_ready(enq_ready),
        .entry_valid(entry_valid),
        .entry_row(), .entry_col(), .entry_bank(), .entry_we(), .entry_aux(),
        .queue_count(queue_count), .queue_empty(queue_empty), .queue_full(queue_full),
        .deq_grant(deq_grant), .deq_idx(deq_idx)
    );

    // Clock generation: 5.0ns period (200MHz)
    localparam real CLK_PERIOD = 5.0;
    initial begin
        clk = 1'b0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // Test vector variables
    integer fd;
    integer scan_ret;
    integer vec_num;
    integer total_tests;
    integer pass_count;
    integer fail_count;
    integer cycle_count;

    logic [7:0]  opcode;
    logic [31:0] addr;
    logic [31:0] wdata;
    logic [31:0] expected;

    logic [7:0] actual_status;
    logic [7:0] expected_status;

    string vector_file;

    // Watchdog timeout
    localparam int WATCHDOG_CYCLES = 200000;

    // Watchdog process
    initial begin
        cycle_count = 0;
        forever begin
            @(posedge clk);
            cycle_count = cycle_count + 1;
            if (cycle_count >= WATCHDOG_CYCLES) begin
                $display("TIMEOUT: Watchdog expired after %0d cycles", WATCHDOG_CYCLES);
                $display("=========================================");
                $display("SUMMARY: Total=%0d Passed=%0d Failed=%0d", total_tests, pass_count, fail_count);
                $display("=========================================");
                $finish;
            end
        end
    end

    // Main test process
    initial begin
        // Initialize signals
        rst_n = 1'b1;
        wb_cyc_i = 1'b0;
        wb_stb_i = 1'b0;
        wb_we_i = 1'b0;
        wb_adr_i = 29'h0;
        wb_dat_i = 32'h0;
        wb_sel_i = 4'h0;
        wb_bte_i = 2'b00;
        wb_cti_i = 3'b000;
        deq_grant = 1'b0;
        deq_idx = 4'h0;

        total_tests = 0;
        pass_count = 0;
        fail_count = 0;
        vec_num = 0;

        // Get vector file name from plusarg or use default
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "path_backpressure_vectors.hex";
        end

        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Could not open vector file: %s", vector_file);
            $finish;
        end

        $display("Starting path_backpressure testbench");
        $display("Reading vectors from: %s", vector_file);

        // Wait for initial clock edge
        @(posedge clk);

        // Process vectors
        while (!$feof(fd)) begin
            scan_ret = $fscanf(fd, "%h %h %h %h", opcode, addr, wdata, expected);
            if (scan_ret != 4) begin
                continue;
            end

            vec_num = vec_num + 1;
            expected_status = expected[7:0];

            case (opcode)
                8'h00: begin
                    // Reset operation
                    $display("Vec %0d: RESET", vec_num);
                    rst_n = 1'b0;
                    wb_cyc_i = 1'b0;
                    wb_stb_i = 1'b0;
                    wb_we_i = 1'b0;
                    wb_adr_i = 29'h0;
                    wb_dat_i = 32'h0;
                    wb_sel_i = 4'h0;
                    wb_bte_i = 2'b00;
                    wb_cti_i = 3'b000;
                    deq_grant = 1'b0;
                    deq_idx = 4'h0;
                    repeat (4) @(posedge clk);
                    rst_n = 1'b1;
                    @(posedge clk);
                end

                8'h01: begin
                    // Read request
                    total_tests = total_tests + 1;
                    wb_cyc_i = 1'b1;
                    wb_stb_i = 1'b1;
                    wb_we_i = 1'b0;
                    wb_adr_i = addr[28:0];
                    wb_dat_i = 32'h0;
                    wb_sel_i = 4'hF;
                    wb_cti_i = 3'b000;
                    wb_bte_i = 2'b00;
                    @(posedge clk);
                    // Sample status
                    actual_status = {queue_full, wb_stall_o, wb_ack_o, queue_count[4:0]};
                    if (actual_status !== expected_status) begin
                        $display("MISMATCH vec=%0d op=0x%02X expected=0x%02X actual=0x%02X", 
                                 vec_num, opcode, expected_status, actual_status);
                        fail_count = fail_count + 1;
                    end else begin
                        pass_count = pass_count + 1;
                    end
                    // Deassert strobe
                    wb_stb_i = 1'b0;
                    wb_cyc_i = 1'b0;
                    @(posedge clk);
                end

                8'h02: begin
                    // Write request
                    total_tests = total_tests + 1;
                    wb_cyc_i = 1'b1;
                    wb_stb_i = 1'b1;
                    wb_we_i = 1'b1;
                    wb_adr_i = addr[28:0];
                    wb_dat_i = wdata;
                    wb_sel_i = 4'hF;
                    wb_cti_i = 3'b000;
                    wb_bte_i = 2'b00;
                    @(posedge clk);
                    // Sample status
                    actual_status = {queue_full, wb_stall_o, wb_ack_o, queue_count[4:0]};
                    if (actual_status !== expected_status) begin
                        $display("MISMATCH vec=%0d op=0x%02X expected=0x%02X actual=0x%02X", 
                                 vec_num, opcode, expected_status, actual_status);
                        fail_count = fail_count + 1;
                    end else begin
                        pass_count = pass_count + 1;
                    end
                    // Deassert strobe
                    wb_stb_i = 1'b0;
                    wb_cyc_i = 1'b0;
                    @(posedge clk);
                end

                8'h03: begin
                    // Dequeue operation
                    total_tests = total_tests + 1;
                    deq_grant = 1'b1;
                    deq_idx = addr[3:0];
                    @(posedge clk);
                    deq_grant = 1'b0;
                    @(posedge clk);
                    // Sample status after dequeue settles
                    actual_status = {queue_full, 1'b0, enq_ready, queue_count[4:0]};
                    if (actual_status !== expected_status) begin
                        $display("MISMATCH vec=%0d op=0x%02X expected=0x%02X actual=0x%02X", 
                                 vec_num, opcode, expected_status, actual_status);
                        fail_count = fail_count + 1;
                    end else begin
                        pass_count = pass_count + 1;
                    end
                end

                8'h04: begin
                    // Check stall (no bus activity)
                    total_tests = total_tests + 1;
                    // Sample status
                    actual_status = {queue_full, wb_stall_o, 1'b0, queue_count[4:0]};
                    if (actual_status !== expected_status) begin
                        $display("MISMATCH vec=%0d op=0x%02X expected=0x%02X actual=0x%02X", 
                                 vec_num, opcode, expected_status, actual_status);
                        fail_count = fail_count + 1;
                    end else begin
                        pass_count = pass_count + 1;
                    end
                    @(posedge clk);
                end

                default: begin
                    $display("WARNING: Unknown opcode 0x%02X at vec %0d", opcode, vec_num);
                end
            endcase
        end

        $fclose(fd);

        // Print summary
        $display("=========================================");
        $display("SUMMARY: Total=%0d Passed=%0d Failed=%0d", total_tests, pass_count, fail_count);
        $display("=========================================");

        if (fail_count == 0) begin
            $display("TEST PASSED");
        end else begin
            $display("TEST FAILED");
        end

        $finish;
    end

endmodule