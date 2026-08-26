module path_12_csr_timing_to_scheduling_tb;

    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic [7:0] bank_act_allowed;
    logic [7:0] bank_is_active;
    logic [14:0] bank_open_row [0:7];
    logic [7:0] bank_pre_allowed;
    logic [7:0] bank_rd_allowed;
    logic [7:0] bank_wr_allowed;
    logic [7:0] cfg_tCCD_nCK;
    logic [7:0] cfg_tFAW_nCK;
    logic [7:0] cfg_tRAS_nCK;
    logic [7:0] cfg_tRCD_nCK;
    logic [7:0] cfg_tRC_nCK;
    logic [7:0] cfg_tRFC_nCK;
    logic [7:0] cfg_tRP_nCK;
    logic [7:0] cfg_tRRD_nCK;
    logic [7:0] cfg_tRTP_nCK;
    logic [7:0] cfg_tWR_nCK;
    logic [7:0] cfg_tWTR_nCK;

    // ---- Testbench-driven inputs ----
    logic        csr_cyc_i;
    logic        csr_stb_i;
    logic        csr_we_i;
    logic [7:0] csr_adr_i;
    logic [31:0] csr_dat_i;
    logic [3:0] csr_sel_i;
    logic        sts_init_done;
    logic        sts_cal_done;
    logic        sts_cal_fail;
    logic        sts_bist_done;
    logic        sts_bist_fail;
    logic [2:0] sts_ref_pending_cnt;
    logic        sts_self_refresh_active;
    logic [15:0] sts_ecc_ce_count;
    logic        sts_ecc_ue_event;
    logic        sts_ref_starve_event;
    logic        sts_init_fail_event;
    logic [12:0] sts_bist_fail_addr;
    logic        cmd_act_valid;
    logic [2:0] cmd_act_bank;
    logic [14:0] cmd_act_row;
    logic        cmd_pre_valid;
    logic [2:0] cmd_pre_bank;
    logic        cmd_pre_all;
    logic        cmd_rd_valid;
    logic [2:0] cmd_rd_bank;
    logic        cmd_wr_valid;
    logic [2:0] cmd_wr_bank;
    logic        cmd_ref_valid;
    logic [15:0] q_valid;
    logic [14:0] q_row [0:15];
    logic [9:0] q_col [0:15];
    logic [2:0] q_bank [0:15];
    logic        q_we [0:15];
    logic [3:0] q_aux [0:15];
    logic        ref_required;
    logic        ref_urgent;
    logic        q_valid_0;
    logic [14:0] q_row_0;
    logic [9:0] q_col_0;
    logic [2:0] q_bank_0;
    logic        q_we_0;
    logic [3:0] q_aux_0;

    // ---- Testbench-monitored outputs ----
    logic        csr_ack_o;
    logic [31:0] csr_dat_o;
    logic        csr_err_o;
    logic [7:0] cfg_CL_nCK;
    logic [7:0] cfg_CWL_nCK;
    logic [23:0] cfg_tREFI_nCK;
    logic        cfg_sched_policy;
    logic        cfg_row_policy;
    logic [1:0] cfg_self_ref_mode;
    logic        cfg_ecc_enable;
    logic        cfg_bist_start;
    logic        cfg_force_refresh;
    logic        cfg_force_self_ref;
    logic [3:0] cfg_max_postpone;
    logic [3:0] cfg_urgent_threshold;
    logic        cfg_ref_priority;
    logic [2:0] cfg_bist_pattern;
    logic        cfg_bist_addr_mode;
    logic [28:0] cfg_bist_addr_start;
    logic [28:0] cfg_bist_addr_end;
    logic        all_banks_idle;
    logic        faw_allows_act;
    logic        ref_ack;
    logic        cmd_valid;
    logic [3:0] cmd_type;
    logic [14:0] cmd_row;
    logic [9:0] cmd_col;
    logic [2:0] cmd_bank;
    logic        cmd_we;
    logic [3:0] cmd_aux;
    logic        deq_grant;
    logic [3:0] deq_idx;

    // ---- Module instantiations ----
    config_regs u_config_regs (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_CL_nCK(cfg_CL_nCK),
        .cfg_CWL_nCK(cfg_CWL_nCK),
        .cfg_bist_addr_end(cfg_bist_addr_end),
        .cfg_bist_addr_mode(cfg_bist_addr_mode),
        .cfg_bist_addr_start(cfg_bist_addr_start),
        .cfg_bist_pattern(cfg_bist_pattern),
        .cfg_bist_start(cfg_bist_start),
        .cfg_ecc_enable(cfg_ecc_enable),
        .cfg_force_refresh(cfg_force_refresh),
        .cfg_force_self_ref(cfg_force_self_ref),
        .cfg_max_postpone(cfg_max_postpone),
        .cfg_ref_priority(cfg_ref_priority),
        .cfg_row_policy(cfg_row_policy),
        .cfg_sched_policy(cfg_sched_policy),
        .cfg_self_ref_mode(cfg_self_ref_mode),
        .cfg_tCCD_nCK(cfg_tCCD_nCK),
        .cfg_tFAW_nCK(cfg_tFAW_nCK),
        .cfg_tRAS_nCK(cfg_tRAS_nCK),
        .cfg_tRCD_nCK(cfg_tRCD_nCK),
        .cfg_tRC_nCK(cfg_tRC_nCK),
        .cfg_tREFI_nCK(cfg_tREFI_nCK),
        .cfg_tRFC_nCK(cfg_tRFC_nCK),
        .cfg_tRP_nCK(cfg_tRP_nCK),
        .cfg_tRRD_nCK(cfg_tRRD_nCK),
        .cfg_tRTP_nCK(cfg_tRTP_nCK),
        .cfg_tWR_nCK(cfg_tWR_nCK),
        .cfg_tWTR_nCK(cfg_tWTR_nCK),
        .cfg_urgent_threshold(cfg_urgent_threshold),
        .csr_ack_o(csr_ack_o),
        .csr_adr_i(csr_adr_i),
        .csr_cyc_i(csr_cyc_i),
        .csr_dat_i(csr_dat_i),
        .csr_dat_o(csr_dat_o),
        .csr_err_o(csr_err_o),
        .csr_sel_i(csr_sel_i),
        .csr_stb_i(csr_stb_i),
        .csr_we_i(csr_we_i),
        .sts_bist_done(sts_bist_done),
        .sts_bist_fail(sts_bist_fail),
        .sts_bist_fail_addr(sts_bist_fail_addr),
        .sts_cal_done(sts_cal_done),
        .sts_cal_fail(sts_cal_fail),
        .sts_ecc_ce_count(sts_ecc_ce_count),
        .sts_ecc_ue_event(sts_ecc_ue_event),
        .sts_init_done(sts_init_done),
        .sts_init_fail_event(sts_init_fail_event),
        .sts_ref_pending_cnt(sts_ref_pending_cnt),
        .sts_ref_starve_event(sts_ref_starve_event),
        .sts_self_refresh_active(sts_self_refresh_active)
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
        .cmd_act_bank(cmd_act_bank),
        .cmd_act_row(cmd_act_row),
        .cmd_act_valid(cmd_act_valid),
        .cmd_pre_all(cmd_pre_all),
        .cmd_pre_bank(cmd_pre_bank),
        .cmd_pre_valid(cmd_pre_valid),
        .cmd_rd_bank(cmd_rd_bank),
        .cmd_rd_valid(cmd_rd_valid),
        .cmd_ref_valid(cmd_ref_valid),
        .cmd_wr_bank(cmd_wr_bank),
        .cmd_wr_valid(cmd_wr_valid),
        .faw_allows_act(faw_allows_act)
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

    // ---- Clock generation ----
    initial begin
        clk = 1'b0;
        forever #2.5 clk = ~clk;
    end

    // ---- Mandatory functions and tasks ----

    function automatic logic [31:0] pack_outputs();
        logic [31:0] packed_val;
        packed_val = 32'b0;
        packed_val[0] = csr_ack_o;
        return packed_val;
    endfunction

    task automatic unpack_drive(input logic [31:0] packed_val);
        csr_cyc_i = packed_val[0];
        csr_stb_i = packed_val[1];
        csr_we_i = packed_val[2];
        csr_adr_i = packed_val[10:3];
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

    int  arrival_cycle [0:MAX_SIG_ID-1];
    int  arrival_value [0:MAX_SIG_ID-1];
    int  sim_cycle;

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
        csr_cyc_i = '0;
        csr_stb_i = '0;
        csr_we_i = '0;
        csr_adr_i = '0;
        repeat(4) @(posedge clk);
        rst_n = 1'b1;
        @(posedge clk);
        event_reset();
    endtask

    // ---- Main stimulus ----
    initial begin
        string vector_file;
        int fd;
        int status;
        int vec_num;
        int total_tests, pass_count, fail_count;
        logic [7:0]  opcode;
        logic [31:0] param;
        logic [31:0] drive_val;
        logic [31:0] expect_val;
        int watchdog;

        // Default undriven inputs
        csr_dat_i = '0;
        csr_sel_i = 4'hF;
        sts_init_done = '0;
        sts_cal_done = '0;
        sts_cal_fail = '0;
        sts_bist_done = '0;
        sts_bist_fail = '0;
        sts_ref_pending_cnt = '0;
        sts_self_refresh_active = '0;
        sts_ecc_ce_count = '0;
        sts_ecc_ue_event = '0;
        sts_ref_starve_event = '0;
        sts_init_fail_event = '0;
        sts_bist_fail_addr = '0;
        cmd_act_valid = '0;
        cmd_act_bank = '0;
        cmd_act_row = '0;
        cmd_pre_valid = '0;
        cmd_pre_bank = '0;
        cmd_pre_all = '0;
        cmd_rd_valid = '0;
        cmd_rd_bank = '0;
        cmd_wr_valid = '0;
        cmd_wr_bank = '0;
        cmd_ref_valid = '0;
        q_valid_0 = '0;
        q_row_0 = '0;
        q_col_0 = '0;
        q_bank_0 = '0;
        q_we_0 = '0;
        q_aux_0 = '0;
        ref_required = '0;
        ref_urgent = '0;
        csr_cyc_i = '0;
        csr_stb_i = '0;
        csr_we_i = '0;
        csr_adr_i = '0;
        rst_n = 1'b0;

        if (!$value$plusargs("VECTORS=%s", vector_file))
            vector_file = "path_12_csr_timing_to_scheduling_vectors.hex";

        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Cannot open vector file: %s", vector_file);
            $finish;
        end

        vec_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;
        watchdog = 0;

        while (!$feof(fd)) begin
            status = $fscanf(fd, "%h %h %h %h", opcode, param, drive_val, expect_val);
            if (status != 4) begin
                // skip malformed or empty lines
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
                    // wait_for: param=timeout, drive_val={sig_id[15:0], value[15:0]}, expect_val unused
                    wait_for(
                        int'(drive_val[31:16]),
                        {16'b0, drive_val[15:0]},
                        int'(param),
                        vec_num,
                        pass_count, fail_count, total_tests
                    );
                end
                8'h05: begin
                    // check_at: param=target_cycle, drive_val={sig_id[15:0], value[15:0]}
                    check_at(
                        int'(drive_val[31:16]),
                        {16'b0, drive_val[15:0]},
                        int'(param),
                        vec_num,
                        pass_count, fail_count, total_tests
                    );
                end
                8'h06: begin
                    // check_not_yet: param=until_cycle, drive_val={sig_id[15:0], value[15:0]}
                    check_not_yet(
                        int'(drive_val[31:16]),
                        {16'b0, drive_val[15:0]},
                        int'(param),
                        vec_num,
                        pass_count, fail_count, total_tests
                    );
                end
                8'h07: begin
                    // expect_handshake: param=timeout, drive_val={valid_id[15:0], ready_id[15:0]}
                    expect_handshake(
                        int'(drive_val[31:16]),
                        int'(drive_val[15:0]),
                        int'(param),
                        vec_num,
                        pass_count, fail_count, total_tests
                    );
                end
                8'h08: begin
                    // check_order: param=min_gap, drive_val={first_id[15:0], second_id[15:0]}
                    check_order(
                        int'(drive_val[31:16]),
                        int'(drive_val[15:0]),
                        int'(param),
                        vec_num,
                        pass_count, fail_count, total_tests
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
            watchdog = watchdog + 1;
            if (watchdog > 200000) begin
                $display("WATCHDOG TIMEOUT after %0d vectors", vec_num);
                break;
            end
        end

        $fclose(fd);

        $display("=== SIMULATION SUMMARY ===");
        $display("Total tests: %0d", total_tests);
        $display("Pass:        %0d", pass_count);
        $display("Fail:        %0d", fail_count);
        if (fail_count == 0)
            $display("RESULT: PASS");
        else
            $display("RESULT: FAIL");

        $finish;
    end

    // ---- Watchdog timer based on simulation time ----
    initial begin
        #(200000 * 5.0);
        $display("WATCHDOG: Simulation time limit reached");
        $finish;
    end

endmodule