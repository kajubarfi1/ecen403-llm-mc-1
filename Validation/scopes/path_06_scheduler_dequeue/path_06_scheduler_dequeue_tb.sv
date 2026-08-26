module path_06_scheduler_dequeue_tb;

    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        deq_grant;
    logic [3:0] deq_idx;

    // ---- Testbench-driven inputs ----
    logic [15:0] q_valid;
    logic [14:0] q_row [0:15];
    logic [9:0] q_col [0:15];
    logic [2:0] q_bank [0:15];
    logic        q_we [0:15];
    logic [3:0] q_aux [0:15];
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [7:0] bank_pre_allowed;
    logic        ref_required;
    logic        ref_urgent;
    logic        enq_valid;
    logic [14:0] enq_row;
    logic [9:0] enq_col;
    logic [2:0] enq_bank;
    logic        enq_we;
    logic [3:0] enq_aux;

    // ---- Testbench-monitored outputs ----
    logic        ref_ack;
    logic        cmd_valid;
    logic [3:0] cmd_type;
    logic [14:0] cmd_row;
    logic [9:0] cmd_col;
    logic [2:0] cmd_bank;
    logic        cmd_we;
    logic [3:0] cmd_aux;
    logic        enq_ready;
    logic [15:0] entry_valid;
    logic [14:0] entry_row [0:15];
    logic [9:0] entry_col [0:15];
    logic [2:0] entry_bank [0:15];
    logic        entry_we [0:15];
    logic [3:0] entry_aux [0:15];
    logic        queue_full;
    logic        queue_empty;
    logic [4:0] queue_count;

    // ---- Module instantiations ----
    scheduler u_scheduler (
        .clk(clk), .rst_n(rst_n),
        .bank_act_allowed(bank_act_allowed),
        .bank_is_active(bank_is_active),
        .bank_open_row(bank_open_row),
        .bank_pre_allowed(bank_pre_allowed),
        .bank_rd_allowed(bank_rd_allowed),
        .bank_wr_allowed(bank_wr_allowed),
        .cmd_aux(cmd_aux),
        .cmd_bank(cmd_bank),
        .cmd_col(cmd_col),
        .cmd_row(cmd_row),
        .cmd_type(cmd_type),
        .cmd_valid(cmd_valid),
        .cmd_we(cmd_we),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .q_aux(q_aux),
        .q_bank(q_bank),
        .q_col(q_col),
        .q_row(q_row),
        .q_valid(q_valid),
        .q_we(q_we),
        .ref_ack(ref_ack),
        .ref_required(ref_required),
        .ref_urgent(ref_urgent)
    );

    cmd_queue u_cmd_queue (
        .clk(clk), .rst_n(rst_n),
        .deq_grant(deq_grant),
        .deq_idx(deq_idx),
        .enq_aux(enq_aux),
        .enq_bank(enq_bank),
        .enq_col(enq_col),
        .enq_ready(enq_ready),
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

    // ---- Clock generation ----
    localparam real CLOCK_PERIOD = 5.0;
    initial begin
        clk = 1'b0;
        forever #(CLOCK_PERIOD/2) clk = ~clk;
    end

    // ---- Testbench variables ----
    integer fd;
    integer scan_ret;
    string vector_file;
    integer vec_num;
    integer total_tests;
    integer pass_count;
    integer fail_count;
    integer watchdog_count;

    logic [7:0] opcode;
    logic [31:0] param;
    logic [31:0] drive_data;
    logic [31:0] expected_data;
    logic [31:0] actual_data;

    integer i, j;

    // ---- Task: Initialize all inputs to zero ----
    task init_inputs;
        begin
            q_valid = 16'h0;
            bank_is_active = 8'h0;
            bank_act_allowed = 8'h0;
            bank_rd_allowed = 8'h0;
            bank_wr_allowed = 8'h0;
            bank_pre_allowed = 8'h0;
            ref_required = 1'b0;
            ref_urgent = 1'b0;
            enq_valid = 1'b0;
            enq_row = 15'h0;
            enq_col = 10'h0;
            enq_bank = 3'h0;
            enq_we = 1'b0;
            enq_aux = 4'h0;
            for (i = 0; i < 16; i = i + 1) begin
                q_row[i] = 15'h0;
                q_col[i] = 10'h0;
                q_bank[i] = 3'h0;
                q_we[i] = 1'b0;
                q_aux[i] = 4'h0;
            end
            for (i = 0; i < 8; i = i + 1) begin
                bank_open_row[i] = 15'h0;
            end
        end
    endtask

    // ---- Task: Apply reset ----
    task do_reset;
        begin
            rst_n = 1'b0;
            init_inputs();
            repeat (4) @(posedge clk);
            rst_n = 1'b1;
            @(posedge clk);
        end
    endtask

    // ---- Task: Drive inputs from packed data ----
    task do_drive(input logic [31:0] data);
        begin
            q_valid = data[15:0];
            bank_is_active = data[23:16];
            bank_act_allowed = data[31:24];
            @(posedge clk);
        end
    endtask

    // ---- Task: Check outputs against expected ----
    task do_check(input logic [31:0] expected);
        begin
            actual_data = 32'h0;
            actual_data[0] = ref_ack;
            actual_data[1] = cmd_valid;
            actual_data[5:2] = cmd_type;
            actual_data[20:6] = cmd_row;
            actual_data[30:21] = cmd_col;

            total_tests = total_tests + 1;
            if (actual_data === expected) begin
                pass_count = pass_count + 1;
            end else begin
                fail_count = fail_count + 1;
                $display("MISMATCH vec=%0d expected=0x%08X actual=0x%08X", vec_num, expected, actual_data);
            end
        end
    endtask

    // ---- Task: Step N cycles ----
    task do_step(input logic [31:0] cycles);
        integer c;
        begin
            for (c = 0; c < cycles; c = c + 1) begin
                @(posedge clk);
                watchdog_count = watchdog_count + 1;
                if (watchdog_count >= 200000) begin
                    $display("ERROR: Watchdog timeout at %0d cycles", watchdog_count);
                    $display("========================================");
                    $display("FAIL: Watchdog timeout");
                    $display("========================================");
                    $finish;
                end
            end
        end
    endtask

    // ---- Main test sequence ----
    initial begin
        // Initialize
        vec_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;
        watchdog_count = 0;
        rst_n = 1'b1;
        init_inputs();

        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "path_06_scheduler_dequeue_vectors.hex";
        end

        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Could not open vector file: %s", vector_file);
            $finish;
        end

        // Process vectors
        while (!$feof(fd)) begin
            scan_ret = $fscanf(fd, "%h %h %h %h\n", opcode, param, drive_data, expected_data);
            if (scan_ret == 4) begin
                vec_num = vec_num + 1;
                watchdog_count = watchdog_count + 1;
                if (watchdog_count >= 200000) begin
                    $display("ERROR: Watchdog timeout at %0d cycles", watchdog_count);
                    $display("========================================");
                    $display("FAIL: Watchdog timeout");
                    $display("========================================");
                    $fclose(fd);
                    $finish;
                end

                case (opcode)
                    8'h00: begin
                        // Reset
                        do_reset();
                    end
                    8'h01: begin
                        // Drive
                        do_drive(drive_data);
                    end
                    8'h02: begin
                        // Check
                        do_check(expected_data);
                    end
                    8'h03: begin
                        // Step
                        do_step(param);
                    end
                    default: begin
                        $display("WARNING: Unknown opcode 0x%02X at vector %0d", opcode, vec_num);
                    end
                endcase
            end
        end

        // Close file
        $fclose(fd);

        // Print summary
        $display("========================================");
        $display("Test Summary:");
        $display("  Total tests: %0d", total_tests);
        $display("  Passed:      %0d", pass_count);
        $display("  Failed:      %0d", fail_count);
        $display("========================================");
        if (fail_count == 0 && total_tests > 0) begin
            $display("PASS: All tests passed");
        end else if (total_tests == 0) begin
            $display("FAIL: No tests executed");
        end else begin
            $display("FAIL: %0d tests failed", fail_count);
        end
        $display("========================================");
        $finish;
    end

endmodule