module path_07_backpressure_tb;

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

    // ---- Clock generation ----
    initial begin
        clk = 1'b0;
        forever #2.5 clk = ~clk;
    end

    // ---- Mandatory functions ----
    function automatic logic [31:0] pack_outputs();
        logic [31:0] packed_val;
        packed_val = 32'b0;
        packed_val[15:0] = entry_valid;
        packed_val[16] = queue_full;
        packed_val[17] = queue_empty;
        packed_val[22:18] = queue_count;
        packed_val[23] = wb_ack_o;
        return packed_val;
    endfunction

    task automatic unpack_drive(input logic [31:0] packed_val);
        enq_valid = packed_val[0];
        enq_row = packed_val[15:1];
        enq_col = packed_val[25:16];
        enq_bank = packed_val[28:26];
        enq_we = packed_val[29];
        deq_grant = packed_val[30];
    endtask

    // Output history buffer for ±2 cycle tolerance checking
    logic [31:0] out_history [0:2];
    always @(posedge clk) begin
        out_history[2] <= out_history[1];
        out_history[1] <= out_history[0];
        out_history[0] <= pack_outputs();
    end

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

    // ==========================================================================
    // Event-Mode Verification Task Library
    // ==========================================================================

    localparam int MAX_SIG_ID = 32;

    // Per-signal arrival tracking. arrival_cycle[id] == -1 means "not yet seen".
    int  arrival_cycle [0:MAX_SIG_ID-1];
    int  arrival_value [0:MAX_SIG_ID-1];
    int  sim_cycle;  // cycles since last event_start() (or event_reset())

    // --- Latching predicate tracking (Stage 4 bugfix) ---
    int  first_seen [0:MAX_SIG_ID-1];
    int  latch_cycle;
    bit  latch_enabled;

    function automatic logic [31:0] sample_signal(input int id);
        sample_signal = 32'h0;
    endfunction

    always_ff @(posedge clk) begin
        if (latch_enabled) begin
            latch_cycle <= latch_cycle + 1;
            for (int _li = 0; _li < MAX_SIG_ID; _li++) begin
                if (first_seen[_li] < 0 && sample_signal(_li) != 32'h0) begin
                    first_seen[_li] <= latch_cycle + 1;
                end
            end
        end
    end

    task automatic event_reset();
        for (int i = 0; i < MAX_SIG_ID; i++) begin
            arrival_cycle[i] = -1;
            arrival_value[i] = 0;
            first_seen[i] = -1;
        end
        sim_cycle = 0;
        latch_cycle = 0;
        latch_enabled = 1'b0;
    endtask

    task automatic event_start();
        for (int _si = 0; _si < MAX_SIG_ID; _si++) first_seen[_si] = -1;
        sim_cycle = 0;
        latch_cycle = 0;
        latch_enabled = 1'b1;
    endtask

    task automatic event_tick();
        @(posedge clk);
        sim_cycle = sim_cycle + 1;
    endtask

    task automatic wait_for(
        input int          sig_id,
        input logic [31:0] value,
        input int          timeout,
        input int          vec_num,
        inout int          pass_count,
        inout int          fail_count,
        inout int          total_tests
    );
        int waited;
        logic [31:0] obs;
        bit done;
        waited = 0;
        done = 1'b0;
        total_tests = total_tests + 1;

        if (value == 32'h1 && first_seen[sig_id] >= 0) begin
            arrival_cycle[sig_id] = first_seen[sig_id];
            arrival_value[sig_id] = 32'h1;
            pass_count = pass_count + 1;
            done = 1'b1;
        end

        while (!done) begin
            if (value == 32'h1) begin
                if (first_seen[sig_id] >= 0) begin
                    arrival_cycle[sig_id] = first_seen[sig_id];
                    arrival_value[sig_id] = 32'h1;
                    pass_count = pass_count + 1;
                    done = 1'b1;
                end else if (waited >= timeout) begin
                    fail_count = fail_count + 1;
                    $display("WAIT_FOR TIMEOUT vec=%0d sig=%0d expected=0x%08X after=%0d",
                             vec_num, sig_id, value, waited);
                    done = 1'b1;
                end else begin
                    event_tick();
                    waited = waited + 1;
                end
            end else begin
                obs = sample_signal(sig_id);
                if (obs === value) begin
                    arrival_cycle[sig_id] = sim_cycle;
                    arrival_value[sig_id] = obs;
                    pass_count = pass_count + 1;
                    done = 1'b1;
                end else if (waited >= timeout) begin
                    fail_count = fail_count + 1;
                    $display("WAIT_FOR TIMEOUT vec=%0d sig=%0d expected=0x%08X last=0x%08X after=%0d",
                             vec_num, sig_id, value, obs, waited);
                    done = 1'b1;
                end else begin
                    event_tick();
                    waited = waited + 1;
                end
            end
        end
    endtask

    task automatic check_at(
        input int          sig_id,
        input logic [31:0] value,
        input int          target,
        input int          vec_num,
        inout int          pass_count,
        inout int          fail_count,
        inout int          total_tests
    );
        logic [31:0] obs;
        total_tests = total_tests + 1;
        while (sim_cycle < target) event_tick();
        obs = sample_signal(sig_id);
        if (obs === value) begin
            pass_count = pass_count + 1;
        end else begin
            fail_count = fail_count + 1;
            $display("CHECK_AT MISMATCH vec=%0d sig=%0d cycle=%0d expected=0x%08X actual=0x%08X",
                     vec_num, sig_id, target, value, obs);
        end
    endtask

    task automatic check_not_yet(
        input int          sig_id,
        input logic [31:0] value,
        input int          until_cycle,
        input int          vec_num,
        inout int          pass_count,
        inout int          fail_count,
        inout int          total_tests
    );
        logic [31:0] obs;
        bit violated;
        total_tests = total_tests + 1;
        violated = 1'b0;
        while (sim_cycle < until_cycle) begin
            if (!violated) begin
                obs = sample_signal(sig_id);
                if (obs === value) begin
                    fail_count = fail_count + 1;
                    $display("CHECK_NOT_YET VIOLATION vec=%0d sig=%0d value=0x%08X arrived=%0d min=%0d",
                             vec_num, sig_id, value, sim_cycle, until_cycle);
                    violated = 1'b1;
                end
            end
            event_tick();
        end
        if (!violated) pass_count = pass_count + 1;
    endtask

    task automatic expect_handshake(
        input int valid_id,
        input int ready_id,
        input int timeout,
        input int vec_num,
        inout int pass_count,
        inout int fail_count,
        inout int total_tests
    );
        int waited;
        bit done;
        waited = 0;
        done = 1'b0;
        total_tests = total_tests + 1;
        while (!done) begin
            if (sample_signal(valid_id) === 32'h1 &&
                sample_signal(ready_id) === 32'h1) begin
                arrival_cycle[valid_id] = sim_cycle;
                arrival_value[valid_id] = 1;
                pass_count = pass_count + 1;
                done = 1'b1;
            end else if (waited >= timeout) begin
                fail_count = fail_count + 1;
                $display("HANDSHAKE TIMEOUT vec=%0d valid_sig=%0d ready_sig=%0d after=%0d",
                         vec_num, valid_id, ready_id, waited);
                done = 1'b1;
            end else begin
                event_tick();
                waited = waited + 1;
            end
        end
    endtask

    task automatic check_order(
        input int first_id,
        input int second_id,
        input int min_gap,
        input int vec_num,
        inout int pass_count,
        inout int fail_count,
        inout int total_tests
    );
        int gap;
        bit done;
        done = 1'b0;
        total_tests = total_tests + 1;
        if (arrival_cycle[first_id] < 0) begin
            fail_count = fail_count + 1;
            $display("CHECK_ORDER MISSING vec=%0d first_sig=%0d never observed", vec_num, first_id);
            done = 1'b1;
        end
        if (!done && arrival_cycle[second_id] < 0) begin
            fail_count = fail_count + 1;
            $display("CHECK_ORDER MISSING vec=%0d second_sig=%0d never observed", vec_num, second_id);
            done = 1'b1;
        end
        if (!done) begin
            gap = arrival_cycle[second_id] - arrival_cycle[first_id];
            if (gap < min_gap) begin
                fail_count = fail_count + 1;
                $display("CHECK_ORDER VIOLATION vec=%0d first=%0d@%0d second=%0d@%0d gap=%0d min=%0d",
                         vec_num, first_id, arrival_cycle[first_id],
                         second_id, arrival_cycle[second_id], gap, min_gap);
            end else begin
                pass_count = pass_count + 1;
            end
        end
    endtask

    task automatic handle_reset();
        rst_n = 1'b0;
        enq_valid = '0;
        enq_row = '0;
        enq_col = '0;
        enq_bank = '0;
        enq_we = '0;
        deq_grant = '0;
        repeat(4) @(posedge clk);
        rst_n = 1'b1;
        @(posedge clk);
        event_reset();
    endtask

    // ---- Main test process ----
    initial begin
        string vector_file;
        int fd;
        int status;
        int vec_num;
        int total_tests;
        int pass_count;
        int fail_count;
        int watchdog;

        logic [7:0]  opcode;
        logic [31:0] param;
        logic [31:0] drive_val;
        logic [31:0] expect_val;

        // Default driven signals that are not controlled by unpack_drive
        enq_aux = '0;
        deq_idx = '0;
        wb_cyc_i = '0;
        wb_stb_i = '0;
        wb_we_i = '0;
        wb_adr_i = '0;
        wb_dat_i = '0;
        wb_sel_i = '0;
        wb_bte_i = '0;
        wb_cti_i = '0;
        rsp_valid = '0;
        rsp_rdata = '0;
        rsp_aux = '0;
        rst_n = 1'b0;
        enq_valid = '0;
        enq_row = '0;
        enq_col = '0;
        enq_bank = '0;
        enq_we = '0;
        deq_grant = '0;

        vec_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;

        if (!$value$plusargs("VECTORS=%s", vector_file))
            vector_file = "path_07_backpressure_vectors.hex";

        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Cannot open vector file: %s", vector_file);
            $finish;
        end

        // Watchdog
        fork
            begin
                repeat(200000) @(posedge clk);
                $display("WATCHDOG TIMEOUT after 200000 cycles");
                $display("RESULTS: %0d/%0d passed, %0d failed", pass_count, total_tests, fail_count);
                $finish;
            end
        join_none

        while (!$feof(fd)) begin
            status = $fscanf(fd, "%h %h %h %h", opcode, param, drive_val, expect_val);
            if (status != 4) begin
                // Skip malformed lines
                continue;
            end

            case (opcode)
                8'h00: begin
                    handle_reset();
                end
                8'h01: begin
                    unpack_drive(drive_val);
                    @(posedge clk);
                end
                8'h02: begin
                    @(posedge clk);
                    check_with_tolerance(vec_num, expect_val, pass_count, fail_count, total_tests);
                end
                8'h03: begin
                    repeat(param) event_tick();
                end
                8'h04: begin
                    // wait_for: param[7:0]=sig_id, param[31:8]=timeout, drive_val=value
                    wait_for(
                        param[7:0],
                        drive_val,
                        param[31:8],
                        vec_num,
                        pass_count,
                        fail_count,
                        total_tests
                    );
                end
                8'h05: begin
                    // check_at: param[7:0]=sig_id, param[31:8]=target, drive_val=value
                    check_at(
                        param[7:0],
                        drive_val,
                        param[31:8],
                        vec_num,
                        pass_count,
                        fail_count,
                        total_tests
                    );
                end
                8'h06: begin
                    // check_not_yet: param[7:0]=sig_id, param[31:8]=until_cycle, drive_val=value
                    check_not_yet(
                        param[7:0],
                        drive_val,
                        param[31:8],
                        vec_num,
                        pass_count,
                        fail_count,
                        total_tests
                    );
                end
                8'h07: begin
                    // expect_handshake: param[7:0]=valid_id, param[15:8]=ready_id, param[31:16]=timeout
                    expect_handshake(
                        param[7:0],
                        param[15:8],
                        param[31:16],
                        vec_num,
                        pass_count,
                        fail_count,
                        total_tests
                    );
                end
                8'h08: begin
                    // check_order: param[7:0]=first_id, param[15:8]=second_id, param[31:16]=min_gap
                    check_order(
                        param[7:0],
                        param[15:8],
                        param[31:16],
                        vec_num,
                        pass_count,
                        fail_count,
                        total_tests
                    );
                end
                8'h09: begin
                    // event_start
                    event_start();
                end
                default: begin
                    // Unknown opcode, skip
                end
            endcase

            vec_num = vec_num + 1;
        end

        $fclose(fd);

        $display("=== SIMULATION COMPLETE ===");
        $display("RESULTS: %0d/%0d passed, %0d failed", pass_count, total_tests, fail_count);
        if (fail_count == 0)
            $display("STATUS: PASS");
        else
            $display("STATUS: FAIL");
        $finish;
    end

endmodule