module path_18_full_write_tb;

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

    // ---- Mandatory functions and tasks ----
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
    // SPEC AUTHORING GUIDANCE:
    // - Prefer sampling FSM state registers (e.g. init_fsm.init_state) over
    //   chaining command-output handshakes. One wait_for on the terminal state
    //   is clearer than 8 expect_handshakes on intermediate MRS commands.
    // - Use check_not_yet immediately after event_start() to guard JEDEC
    //   minimum-time constraints (e.g. init_done >= 140000 cycles from start).
    // - check_order between two wait_for'd events validates relative ordering
    //   without depending on absolute cycle counts.
    // ==========================================================================

    localparam int MAX_SIG_ID = 32;

    // Per-signal arrival tracking. arrival_cycle[id] == -1 means "not yet seen".
    int  arrival_cycle [0:MAX_SIG_ID-1];
    int  arrival_value [0:MAX_SIG_ID-1];
    int  sim_cycle;  // cycles since last event_start() (or event_reset())

    // --- Latching predicate tracking (Stage 4 bugfix) ---
    // first_seen[id] is the first latch_cycle at which sample_signal(id) was
    // nonzero. Set to -1 until observed. This lets wait_for capture narrow
    // 1-cycle predicates even when called after the pulse has already fired.
    int  first_seen [0:MAX_SIG_ID-1];
    int  latch_cycle;       // advances every posedge after latch_enabled
    bit  latch_enabled;     // gated by event_start()

    // Codegen'd per-path by Stage 2. Returns current value of signal `id`
    // as a 32-bit word. Stub returns 0 so template compiles standalone.
    function automatic logic [31:0] sample_signal(input int id);
        sample_signal = 32'h0;
        // __SAMPLE_SIGNAL_CASES__
    endfunction

    // Latch block: records first cycle each signal is nonzero. Runs on every
    // posedge once latch_enabled is set by event_start(). Gives wait_for a
    // reliable fast path for 1-cycle predicates and already-asserted signals.
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

    // Pulse the DUT's start signal (e.g. init_fsm.enable) and zero sim_cycle
    // at THAT moment. Codegen'd per-path; stub is a no-op for paths with no
    // autonomous start (e.g. CSR-only tail paths).
    task automatic event_start();
        // __EVENT_START_BODY__
        for (int _si = 0; _si < MAX_SIG_ID; _si++) first_seen[_si] = -1;
        sim_cycle = 0;
        latch_cycle = 0;
        latch_enabled = 1'b1;
    endtask

    // CRITICAL INVARIANT: any code that advances simulation time outside this
    // task will cause sim_cycle drift. The opcode 03 (step) dispatch in Stage 4
    // MUST call this task in a loop, NOT bare @(posedge clk). Mixing modes
    // without going through event_tick() will silently break check_at and
    // check_not_yet timing relative to event_start().
    task automatic event_tick();
        @(posedge clk);
        sim_cycle = sim_cycle + 1;
    endtask

    // --------------------------------------------------------------------------
    // wait_for: block until sample_signal(id) == value, up to `timeout` cycles.
    // Records arrival on success. Counts as one test.
    // --------------------------------------------------------------------------
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

        // FAST PATH (value == 1): consult the latch. If the signal was ever
        // observed nonzero, use the recorded fire cycle — don't re-sample.
        // This handles narrow 1-cycle predicates and already-latched signals
        // correctly regardless of when wait_for was called.
        if (value == 32'h1 && first_seen[sig_id] >= 0) begin
            arrival_cycle[sig_id] = first_seen[sig_id];
            arrival_value[sig_id] = 32'h1;
            pass_count = pass_count + 1;
            done = 1'b1;
        end

        while (!done) begin
            if (value == 32'h1) begin
                // Poll the latch each tick — parallel latch block records
                // first_seen[sig_id] the instant the predicate fires.
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
                // Non-1 target (rare: "wait for signal to be deasserted"):
                // live-sample fallback, unchanged from the original semantics.
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

    // --------------------------------------------------------------------------
    // check_at: advance to absolute cycle `target` (relative to last event_start)
    // and verify sample_signal(id) == value.
    // --------------------------------------------------------------------------
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

    // --------------------------------------------------------------------------
    // check_not_yet: from current sim_cycle through `until_cycle`, verify the
    // signal never equals `value`. JEDEC minimum-time guard. NB: `until` is a
    // SystemVerilog reserved word, hence `until_cycle`.
    // --------------------------------------------------------------------------
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

    // --------------------------------------------------------------------------
    // expect_handshake: wait for valid && ready on the same posedge. Records
    // arrival under valid_id.
    // --------------------------------------------------------------------------
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

    // --------------------------------------------------------------------------
    // check_order: verify two prior wait_for/expect_handshake events occurred
    // in the right order with at least `min_gap` cycles between them.
    // --------------------------------------------------------------------------
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
        wb_cyc_i = '0;
        wb_stb_i = '0;
        wb_we_i = '0;
        wb_adr_i = '0;
        repeat(4) @(posedge clk);
        rst_n = 1'b1;
        @(posedge clk);
        event_reset();  // clear arrival tracking + sim_cycle
    endtask

    // ---- Main test execution ----
    initial begin
        string vector_file;
        int fd;
        int vec_num;
        int total_tests;
        int pass_count;
        int fail_count;
        int watchdog;
        int scan_result;
        logic [7:0] opcode;
        logic [31:0] param;
        logic [31:0] drive_val;
        logic [31:0] expect_val;

        // Initialize signals
        rst_n = 1'b0;
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
        bank_act_allowed = '1;
        bank_rd_allowed = '1;
        bank_wr_allowed = '1;
        bank_pre_allowed = '1;
        ref_required = '0;
        ref_urgent = '0;

        // Initialize history buffer
        out_history[0] = 32'b0;
        out_history[1] = 32'b0;
        out_history[2] = 32'b0;

        // Initialize counters
        vec_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;
        watchdog = 0;

        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "path_18_full_write_vectors.hex";
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
        while (!$feof(fd) && watchdog < 200000) begin
            scan_result = $fscanf(fd, "%h %h %h %h", opcode, param, drive_val, expect_val);
            if (scan_result != 4) begin
                if (!$feof(fd)) begin
                    $display("WARNING: Skipping malformed line at vec=%0d", vec_num);
                end
                continue;
            end

            case (opcode)
                8'h00: begin // reset
                    handle_reset();
                end

                8'h01: begin // drive
                    unpack_drive(drive_val);
                    @(posedge clk);
                    watchdog = watchdog + 1;
                end

                8'h02: begin // check
                    @(posedge clk);
                    watchdog = watchdog + 1;
                    check_with_tolerance(vec_num, expect_val, pass_count, fail_count, total_tests);
                end

                8'h03: begin // step
                    repeat(param) begin
                        event_tick();
                        watchdog = watchdog + 1;
                    end
                end

                8'h04: begin // wait_for
                    // sig_id = param[7:0], value = param[15:8], timeout = drive_val
                    wait_for(param[7:0], {24'b0, param[15:8]}, drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h05: begin // check_at
                    // sig_id = param[7:0], value = param[15:8], target = drive_val
                    check_at(param[7:0], {24'b0, param[15:8]}, drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h06: begin // check_not_yet
                    // sig_id = param[7:0], value = param[15:8], until_cycle = drive_val
                    check_not_yet(param[7:0], {24'b0, param[15:8]}, drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h07: begin // expect_handshake
                    // valid_id = param[7:0], ready_id = param[15:8], timeout = drive_val
                    expect_handshake(param[7:0], param[15:8], drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h08: begin // check_order
                    // first_id = param[7:0], second_id = param[15:8], min_gap = drive_val
                    check_order(param[7:0], param[15:8], drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h09: begin // event_start
                    event_start();
                end

                default: begin
                    $display("WARNING: Unknown opcode 0x%02X at vec=%0d", opcode, vec_num);
                end
            endcase

            vec_num = vec_num + 1;
        end

        $fclose(fd);

        // Check for watchdog timeout
        if (watchdog >= 200000) begin
            $display("ERROR: Watchdog timeout after %0d cycles", watchdog);
        end

        // Print summary
        $display("==========================================");
        $display("TEST SUMMARY: path_18_full_write");
        $display("==========================================");
        $display("Total tests: %0d", total_tests);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("==========================================");
        if (fail_count == 0) begin
            $display("RESULT: PASS");
        end else begin
            $display("RESULT: FAIL");
        end
        $display("==========================================");

        $finish;
    end

endmodule