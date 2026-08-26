module path_16_status_refresh_tb;

    // ---- Clock and reset ----
    logic clk, rst_n;

    // ---- Internal wires (between blocks) ----
    logic        cfg_force_refresh;
    logic [3:0] cfg_max_postpone;
    logic        cfg_ref_priority;
    logic [23:0] cfg_tREFI_nCK;
    logic [3:0] cfg_urgent_threshold;
    logic [2:0] refresh_ctrl_ref_pending_cnt;
    logic        refresh_ctrl_ref_starve_flag;

    // ---- Testbench-driven inputs ----
    logic        init_done;
    logic        ref_ack;
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
    logic        sts_self_refresh_active;
    logic [15:0] sts_ecc_ce_count;
    logic        sts_ecc_ue_event;
    logic        sts_init_fail_event;
    logic [12:0] sts_bist_fail_addr;

    // ---- Testbench-monitored outputs ----
    logic        ref_required;
    logic        ref_urgent;
    logic        csr_ack_o;
    logic [31:0] csr_dat_o;
    logic        csr_err_o;
    logic [7:0] cfg_tRCD_nCK;
    logic [7:0] cfg_tRP_nCK;
    logic [7:0] cfg_tRAS_nCK;
    logic [7:0] cfg_tRC_nCK;
    logic [7:0] cfg_tRRD_nCK;
    logic [7:0] cfg_tWTR_nCK;
    logic [7:0] cfg_tFAW_nCK;
    logic [7:0] cfg_tRFC_nCK;
    logic [7:0] cfg_tWR_nCK;
    logic [7:0] cfg_tRTP_nCK;
    logic [7:0] cfg_CL_nCK;
    logic [7:0] cfg_CWL_nCK;
    logic [7:0] cfg_tCCD_nCK;
    logic        cfg_sched_policy;
    logic        cfg_row_policy;
    logic [1:0] cfg_self_ref_mode;
    logic        cfg_ecc_enable;
    logic        cfg_bist_start;
    logic        cfg_force_self_ref;
    logic [2:0] cfg_bist_pattern;
    logic        cfg_bist_addr_mode;
    logic [28:0] cfg_bist_addr_start;
    logic [28:0] cfg_bist_addr_end;

    // ---- Module instantiations ----
    refresh_ctrl u_refresh_ctrl (
        .clk(clk), .rst_n(rst_n),
        .cfg_force_refresh(cfg_force_refresh),
        .cfg_max_postpone(cfg_max_postpone),
        .cfg_ref_priority(cfg_ref_priority),
        .cfg_tREFI_nCK(cfg_tREFI_nCK),
        .cfg_urgent_threshold(cfg_urgent_threshold),
        .init_done(init_done),
        .ref_ack(ref_ack),
        .ref_pending_cnt(refresh_ctrl_ref_pending_cnt),
        .ref_required(ref_required),
        .ref_starve_flag(refresh_ctrl_ref_starve_flag),
        .ref_urgent(ref_urgent)
    );

    config_regs u_config_regs (
        .clk(clk), .rst_n(rst_n),
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
        .sts_ref_pending_cnt(refresh_ctrl_ref_pending_cnt),
        .sts_ref_starve_event(refresh_ctrl_ref_starve_flag),
        .sts_self_refresh_active(sts_self_refresh_active)
    );

    // ---- Packing functions ----
    function automatic logic [31:0] pack_outputs();
        logic [31:0] packed_val;
        packed_val = 32'b0;
        packed_val[0] = ref_required;
        packed_val[1] = ref_urgent;
        packed_val[2] = csr_ack_o;
        return packed_val;
    endfunction

    task automatic unpack_drive(input logic [31:0] packed_val);
        init_done = packed_val[0];
        ref_ack = packed_val[1];
        csr_cyc_i = packed_val[2];
        csr_stb_i = packed_val[3];
        csr_we_i = packed_val[4];
        csr_adr_i = packed_val[12:5];
    endtask

    // ---- Clock generation ----
    localparam real CLK_PERIOD = 5.0;
    initial begin
        clk = 1'b0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // ---- Testbench variables ----
    integer fd;
    integer scan_ret;
    string vector_file;
    integer vec_num;
    integer total_tests;
    integer pass_count;
    integer fail_count;
    integer cycle_count;

    logic [7:0]  opcode;
    logic [31:0] param;
    logic [31:0] drive_val;
    logic [31:0] expected_val;
    logic [31:0] actual_val;

    // ---- Task to initialize all TB-driven inputs ----
    task automatic init_inputs();
        init_done = 1'b0;
        ref_ack = 1'b0;
        csr_cyc_i = 1'b0;
        csr_stb_i = 1'b0;
        csr_we_i = 1'b0;
        csr_adr_i = 8'b0;
        csr_dat_i = 32'b0;
        csr_sel_i = 4'b0;
        sts_init_done = 1'b0;
        sts_cal_done = 1'b0;
        sts_cal_fail = 1'b0;
        sts_bist_done = 1'b0;
        sts_bist_fail = 1'b0;
        sts_self_refresh_active = 1'b0;
        sts_ecc_ce_count = 16'b0;
        sts_ecc_ue_event = 1'b0;
        sts_init_fail_event = 1'b0;
        sts_bist_fail_addr = 13'b0;
    endtask

    // ---- Task to perform reset sequence ----
    task automatic do_reset();
        rst_n = 1'b0;
        init_inputs();
        repeat (4) @(posedge clk);
        rst_n = 1'b1;
        @(posedge clk);
    endtask

    // ---- Watchdog timer ----
    initial begin
        cycle_count = 0;
        forever begin
            @(posedge clk);
            cycle_count = cycle_count + 1;
            if (cycle_count >= 200000) begin
                $display("ERROR: Watchdog timeout at %0d cycles", cycle_count);
                $display("========================================");
                $display("TESTBENCH TIMEOUT");
                $display("Total tests: %0d, Passed: %0d, Failed: %0d", total_tests, pass_count, fail_count);
                $display("========================================");
                $finish;
            end
        end
    end

    // ---- Main test sequence ----
    initial begin
        // Initialize
        rst_n = 1'b1;
        init_inputs();
        vec_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;

        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "path_16_status_refresh_vectors.hex";
        end

        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Could not open vector file: %s", vector_file);
            $finish;
        end

        $display("========================================");
        $display("Starting path_16_status_refresh testbench");
        $display("Vector file: %s", vector_file);
        $display("========================================");

        // Wait for initial clock edge
        @(posedge clk);

        // Read and process vectors
        while (!$feof(fd)) begin
            scan_ret = $fscanf(fd, "%h %h %h %h", opcode, param, drive_val, expected_val);
            if (scan_ret != 4) begin
                continue; // Skip malformed lines
            end

            case (opcode)
                8'h00: begin
                    // Reset operation
                    do_reset();
                    vec_num = vec_num + 1;
                end

                8'h01: begin
                    // Drive operation
                    unpack_drive(drive_val);
                    @(posedge clk);
                    vec_num = vec_num + 1;
                end

                8'h02: begin
                    // Check operation
                    actual_val = pack_outputs();
                    total_tests = total_tests + 1;
                    if (actual_val !== expected_val) begin
                        $display("MISMATCH vec=%0d expected=0x%08X actual=0x%08X", vec_num, expected_val, actual_val);
                        fail_count = fail_count + 1;
                    end else begin
                        pass_count = pass_count + 1;
                    end
                    vec_num = vec_num + 1;
                end

                8'h03: begin
                    // Step operation
                    repeat (param) @(posedge clk);
                    vec_num = vec_num + 1;
                end

                default: begin
                    $display("WARNING: Unknown opcode 0x%02X at vector %0d", opcode, vec_num);
                    vec_num = vec_num + 1;
                end
            endcase
        end

        // Close file
        $fclose(fd);

        // Print summary
        $display("========================================");
        $display("TESTBENCH COMPLETE");
        $display("Total tests: %0d, Passed: %0d, Failed: %0d", total_tests, pass_count, fail_count);
        if (fail_count == 0) begin
            $display("STATUS: PASS");
        end else begin
            $display("STATUS: FAIL");
        end
        $display("========================================");

        $finish;
    end

endmodule