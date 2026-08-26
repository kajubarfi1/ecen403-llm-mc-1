module path_04_scheduler_bank_loop_tb;

    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_pre_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [2:0] cmd_gen_fb_act_bank;
    logic [14:0] cmd_gen_fb_act_row;
    logic        cmd_gen_fb_act_valid;
    logic        cmd_gen_fb_pre_valid;
    logic        cmd_gen_fb_rd_valid;
    logic        cmd_gen_fb_ref_valid;
    logic        cmd_gen_fb_wr_valid;
    logic [3:0] scheduler_cmd_aux;
    logic [2:0] scheduler_cmd_bank;
    logic [9:0] scheduler_cmd_col;
    logic [14:0] scheduler_cmd_row;
    logic [3:0] scheduler_cmd_type;
    logic        scheduler_cmd_valid;
    logic        scheduler_cmd_we;

    // ---- Testbench-driven inputs ----
    logic [15:0] q_valid;
    logic [14:0] q_row [0:15];
    logic [9:0] q_col [0:15];
    logic [2:0] q_bank [0:15];
    logic        q_we [0:15];
    logic [3:0] q_aux [0:15];
    logic        ref_required;
    logic        ref_urgent;
    logic [2:0] cmd_pre_bank;
    logic        cmd_pre_all;
    logic [2:0] cmd_rd_bank;
    logic [2:0] cmd_wr_bank;
    logic [7:0] cfg_tRCD_nCK;
    logic [7:0] cfg_tRP_nCK;
    logic [7:0] cfg_tRAS_nCK;
    logic [7:0] cfg_tRC_nCK;
    logic [7:0] cfg_tRRD_nCK;
    logic [7:0] cfg_tFAW_nCK;
    logic [7:0] cfg_tWTR_nCK;
    logic [7:0] cfg_tWR_nCK;
    logic [7:0] cfg_tRTP_nCK;
    logic [7:0] cfg_tCCD_nCK;
    logic [7:0] cfg_tRFC_nCK;
    logic        q_valid_0;
    logic [14:0] q_row_0;
    logic [9:0] q_col_0;
    logic [2:0] q_bank_0;
    logic        q_we_0;
    logic [3:0] q_aux_0;

    // ---- Testbench-monitored outputs ----
    logic        ref_ack;
    logic        deq_grant;
    logic [3:0] deq_idx;
    logic [3:0] ddr_cmd;
    logic [14:0] ddr_addr;
    logic [2:0] ddr_bank;
    logic        ddr_cke;
    logic        ddr_reset_n;
    logic        ddr_odt;
    logic        all_banks_idle;
    logic        faw_allows_act;

    // ---- Module instantiations ----
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

    cmd_gen u_cmd_gen (
        .clk(clk),
        .rst_n(rst_n),
        .ddr_addr(ddr_addr),
        .ddr_bank(ddr_bank),
        .ddr_cke(ddr_cke),
        .ddr_cmd(ddr_cmd),
        .ddr_odt(ddr_odt),
        .ddr_reset_n(ddr_reset_n),
        .fb_act_bank(cmd_gen_fb_act_bank),
        .fb_act_row(cmd_gen_fb_act_row),
        .fb_act_valid(cmd_gen_fb_act_valid),
        .fb_pre_valid(cmd_gen_fb_pre_valid),
        .fb_rd_valid(cmd_gen_fb_rd_valid),
        .fb_ref_valid(cmd_gen_fb_ref_valid),
        .fb_wr_valid(cmd_gen_fb_wr_valid),
        .sched_aux(scheduler_cmd_aux),
        .sched_bank(scheduler_cmd_bank),
        .sched_col(scheduler_cmd_col),
        .sched_row(scheduler_cmd_row),
        .sched_type(scheduler_cmd_type),
        .sched_valid(scheduler_cmd_valid),
        .sched_we(scheduler_cmd_we)
    );

    bank_tracker u_bank_tracker (
        .clk(clk),
        .rst_n(rst_n),
        .all_banks_idle(all_banks_idle),
        .bank_act_allowed(bank_act_allowed),
        .bank_is_active(bank_is_active),
        .bank_open_row(bank_open_row),
        .bank_pre_allowed(bank_pre_allowed),
        .bank_rd_allowed(bank_rd_allowed),
        .bank_wr_allowed(bank_wr_allowed),
        .cfg_tCCD_nCK(cfg_tCCD_nCK),
        .cfg_tFAW_nCK(cfg_tFAW_nCK),
        .cfg_tRAS_nCK(cfg_tRAS_nCK),
        .cfg_tRCD_nCK(cfg_tRCD_nCK),
        .cfg_tRC_nCK(cfg_tRC_nCK),
        .cfg_tRFC_nCK(cfg_tRFC_nCK),
        .cfg_tRP_nCK(cfg_tRP_nCK),
        .cfg_tRRD_nCK(cfg_tRRD_nCK),
        .cfg_tRTP_nCK(cfg_tRTP_nCK),
        .cfg_tWR_nCK(cfg_tWR_nCK),
        .cfg_tWTR_nCK(cfg_tWTR_nCK),
        .cmd_act_bank(cmd_gen_fb_act_bank),
        .cmd_act_row(cmd_gen_fb_act_row),
        .cmd_act_valid(cmd_gen_fb_act_valid),
        .cmd_pre_all(cmd_pre_all),
        .cmd_pre_bank(cmd_pre_bank),
        .cmd_pre_valid(cmd_gen_fb_pre_valid),
        .cmd_rd_bank(cmd_rd_bank),
        .cmd_rd_valid(cmd_gen_fb_rd_valid),
        .cmd_ref_valid(cmd_gen_fb_ref_valid),
        .cmd_wr_bank(cmd_wr_bank),
        .cmd_wr_valid(cmd_gen_fb_wr_valid),
        .faw_allows_act(faw_allows_act)
    );

    // ---- Single-entry mode: scalar aliases for array entry [0] ----
    assign q_valid[0] = q_valid_0;
    assign q_valid[1] = '0;
    assign q_valid[2] = '0;
    assign q_valid[3] = '0;
    assign q_valid[4] = '0;
    assign q_valid[5] = '0;
    assign q_valid[6] = '0;
    assign q_valid[7] = '0;
    assign q_valid[8] = '0;
    assign q_valid[9] = '0;
    assign q_valid[10] = '0;
    assign q_valid[11] = '0;
    assign q_valid[12] = '0;
    assign q_valid[13] = '0;
    assign q_valid[14] = '0;
    assign q_valid[15] = '0;
    assign q_row[0] = q_row_0;
    assign q_row[1] = '0;
    assign q_row[2] = '0;
    assign q_row[3] = '0;
    assign q_row[4] = '0;
    assign q_row[5] = '0;
    assign q_row[6] = '0;
    assign q_row[7] = '0;
    assign q_row[8] = '0;
    assign q_row[9] = '0;
    assign q_row[10] = '0;
    assign q_row[11] = '0;
    assign q_row[12] = '0;
    assign q_row[13] = '0;
    assign q_row[14] = '0;
    assign q_row[15] = '0;
    assign q_col[0] = q_col_0;
    assign q_col[1] = '0;
    assign q_col[2] = '0;
    assign q_col[3] = '0;
    assign q_col[4] = '0;
    assign q_col[5] = '0;
    assign q_col[6] = '0;
    assign q_col[7] = '0;
    assign q_col[8] = '0;
    assign q_col[9] = '0;
    assign q_col[10] = '0;
    assign q_col[11] = '0;
    assign q_col[12] = '0;
    assign q_col[13] = '0;
    assign q_col[14] = '0;
    assign q_col[15] = '0;
    assign q_bank[0] = q_bank_0;
    assign q_bank[1] = '0;
    assign q_bank[2] = '0;
    assign q_bank[3] = '0;
    assign q_bank[4] = '0;
    assign q_bank[5] = '0;
    assign q_bank[6] = '0;
    assign q_bank[7] = '0;
    assign q_bank[8] = '0;
    assign q_bank[9] = '0;
    assign q_bank[10] = '0;
    assign q_bank[11] = '0;
    assign q_bank[12] = '0;
    assign q_bank[13] = '0;
    assign q_bank[14] = '0;
    assign q_bank[15] = '0;
    assign q_we[0] = q_we_0;
    assign q_we[1] = '0;
    assign q_we[2] = '0;
    assign q_we[3] = '0;
    assign q_we[4] = '0;
    assign q_we[5] = '0;
    assign q_we[6] = '0;
    assign q_we[7] = '0;
    assign q_we[8] = '0;
    assign q_we[9] = '0;
    assign q_we[10] = '0;
    assign q_we[11] = '0;
    assign q_we[12] = '0;
    assign q_we[13] = '0;
    assign q_we[14] = '0;
    assign q_we[15] = '0;
    assign q_aux[0] = q_aux_0;
    assign q_aux[1] = '0;
    assign q_aux[2] = '0;
    assign q_aux[3] = '0;
    assign q_aux[4] = '0;
    assign q_aux[5] = '0;
    assign q_aux[6] = '0;
    assign q_aux[7] = '0;
    assign q_aux[8] = '0;
    assign q_aux[9] = '0;
    assign q_aux[10] = '0;
    assign q_aux[11] = '0;
    assign q_aux[12] = '0;
    assign q_aux[13] = '0;
    assign q_aux[14] = '0;
    assign q_aux[15] = '0;

    // ---- Derived signals (wired from internal scheduler_cmd_bank) ----
    assign cmd_pre_bank = scheduler_cmd_bank;
    assign cmd_rd_bank = scheduler_cmd_bank;
    assign cmd_wr_bank = scheduler_cmd_bank;
    assign cmd_pre_all = 1'b0;

    // ---- Clock generation ----
    initial begin
        clk = 1'b0;
        forever #2.5 clk = ~clk;
    end

    // ---- Mandatory functions ----
    function automatic logic [31:0] pack_outputs();
        logic [31:0] packed_val;
        packed_val = 32'b0;
        packed_val[0] = ref_ack;
        packed_val[1] = deq_grant;
        packed_val[5:2] = deq_idx;
        packed_val[9:6] = ddr_cmd;
        packed_val[24:10] = ddr_addr;
        packed_val[27:25] = ddr_bank;
        packed_val[28] = ddr_cke;
        packed_val[29] = ddr_reset_n;
        packed_val[30] = ddr_odt;
        return packed_val;
    endfunction

    task automatic unpack_drive(input logic [31:0] packed_val);
        q_valid_0 = packed_val[0];
        q_row_0 = packed_val[15:1];
        q_col_0 = packed_val[25:16];
        q_bank_0 = packed_val[28:26];
        q_we_0 = packed_val[29];
        ref_required = packed_val[30];
        ref_urgent = packed_val[31];
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
    int  latch_cycle;       // advances every posedge after latch_enabled
    bit  latch_enabled;     // gated by event_start()

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
        q_valid_0 = '0;
        q_row_0 = '0;
        q_col_0 = '0;
        q_bank_0 = '0;
        q_we_0 = '0;
        ref_required = '0;
        ref_urgent = '0;
        repeat(4) @(posedge clk);
        rst_n = 1'b1;
        // DDR3-1600K timing defaults
        cfg_tRCD_nCK = 8'd11;
        cfg_tRP_nCK = 8'd11;
        cfg_tRAS_nCK = 8'd28;
        cfg_tRC_nCK = 8'd39;
        cfg_tRRD_nCK = 8'd6;
        cfg_tFAW_nCK = 8'd32;
        cfg_tWTR_nCK = 8'd6;
        cfg_tWR_nCK = 8'd12;
        cfg_tRTP_nCK = 8'd6;
        cfg_tCCD_nCK = 8'd4;
        cfg_tRFC_nCK = 8'd128;
        @(posedge clk);
        event_reset();  // clear arrival tracking + sim_cycle
    endtask

    // ---- Main test process ----
    initial begin
        string vector_file;
        int fd;
        int vec_num;
        int total_tests;
        int pass_count;
        int fail_count;
        int watchdog;
        int scan_ret;
        logic [7:0] opcode;
        logic [31:0] param;
        logic [31:0] drive_val;
        logic [31:0] expect_val;

        // Initialize counters
        vec_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;
        watchdog = 0;

        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "path_04_scheduler_bank_loop_vectors.hex";
        end

        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Cannot open vector file %s", vector_file);
            $finish;
        end

        // Initialize signals before reset
        rst_n = 1'b0;
        q_valid_0 = '0;
        q_row_0 = '0;
        q_col_0 = '0;
        q_bank_0 = '0;
        q_we_0 = '0;
        q_aux_0 = '0;
        ref_required = '0;
        ref_urgent = '0;
        cfg_tRCD_nCK = '0;
        cfg_tRP_nCK = '0;
        cfg_tRAS_nCK = '0;
        cfg_tRC_nCK = '0;
        cfg_tRRD_nCK = '0;
        cfg_tFAW_nCK = '0;
        cfg_tWTR_nCK = '0;
        cfg_tWR_nCK = '0;
        cfg_tRTP_nCK = '0;
        cfg_tCCD_nCK = '0;
        cfg_tRFC_nCK = '0;

        // Wait for first clock edge
        @(posedge clk);

        // Process vectors
        while (!$feof(fd) && watchdog < 200000) begin
            scan_ret = $fscanf(fd, "%h %h %h %h", opcode, param, drive_val, expect_val);
            if (scan_ret != 4) begin
                if (!$feof(fd)) begin
                    $display("WARNING: Incomplete vector read at vec=%0d", vec_num);
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
                    wait_for(param[7:0], expect_val, drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h05: begin // check_at
                    check_at(param[7:0], expect_val, drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h06: begin // check_not_yet
                    check_not_yet(param[7:0], expect_val, drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h07: begin // expect_handshake
                    expect_handshake(param[7:0], param[15:8], drive_val, vec_num, pass_count, fail_count, total_tests);
                end

                8'h08: begin // check_order
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

        // Print summary
        $display("========================================");
        $display("SIMULATION COMPLETE");
        $display("Total tests: %0d", total_tests);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("========================================");

        if (watchdog >= 200000) begin
            $display("WARNING: Watchdog timeout reached!");
        end

        if (fail_count == 0 && total_tests > 0) begin
            $display("RESULT: PASS");
        end else begin
            $display("RESULT: FAIL");
        end

        $finish;
    end

endmodule