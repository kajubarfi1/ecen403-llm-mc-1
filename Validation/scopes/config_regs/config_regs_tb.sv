module config_regs_tb;

    // clock_reset
    logic                    clk;
    logic                    rst_n;

    // csr_bus_in
    logic                    csr_cyc_i;
    logic                    csr_stb_i;
    logic                    csr_we_i;
    logic [ 7:0]             csr_adr_i;
    logic [31:0]             csr_dat_i;
    logic [ 3:0]             csr_sel_i;

    // csr_bus_out
    logic                    csr_ack_o;
    logic [31:0]             csr_dat_o;
    logic                    csr_err_o;

    // status_in
    logic                    sts_init_done;
    logic                    sts_cal_done;
    logic                    sts_cal_fail;
    logic                    sts_bist_done;
    logic                    sts_bist_fail;
    logic [ 2:0]             sts_ref_pending_cnt;
    logic                    sts_self_refresh_active;
    logic [15:0]             sts_ecc_ce_count;
    logic                    sts_ecc_ue_event;
    logic                    sts_ref_starve_event;
    logic                    sts_init_fail_event;
    logic [12:0]             sts_bist_fail_addr;

    // config_out
    logic [ 7:0]             cfg_tRCD_nCK;
    logic [ 7:0]             cfg_tRP_nCK;
    logic [ 7:0]             cfg_tRAS_nCK;
    logic [ 7:0]             cfg_tRC_nCK;
    logic [ 7:0]             cfg_tRRD_nCK;
    logic [ 7:0]             cfg_tWTR_nCK;
    logic [ 7:0]             cfg_tFAW_nCK;
    logic [ 7:0]             cfg_tRFC_nCK;
    logic [ 7:0]             cfg_tWR_nCK;
    logic [ 7:0]             cfg_tRTP_nCK;
    logic [ 7:0]             cfg_CL_nCK;
    logic [ 7:0]             cfg_CWL_nCK;
    logic [ 7:0]             cfg_tCCD_nCK;
    logic [23:0]             cfg_tREFI_nCK;
    logic                    cfg_sched_policy;
    logic                    cfg_row_policy;
    logic [ 1:0]             cfg_self_ref_mode;
    logic                    cfg_ecc_enable;
    logic                    cfg_bist_start;
    logic                    cfg_force_refresh;
    logic                    cfg_force_self_ref;
    logic [ 3:0]             cfg_max_postpone;
    logic [ 3:0]             cfg_urgent_threshold;
    logic                    cfg_ref_priority;
    logic [ 2:0]             cfg_bist_pattern;
    logic                    cfg_bist_addr_mode;
    logic [28:0]             cfg_bist_addr_start;
    logic [28:0]             cfg_bist_addr_end;

    config_regs dut (
        .clk(clk),
        .rst_n(rst_n),
        .csr_cyc_i(csr_cyc_i),
        .csr_stb_i(csr_stb_i),
        .csr_we_i(csr_we_i),
        .csr_adr_i(csr_adr_i),
        .csr_dat_i(csr_dat_i),
        .csr_sel_i(csr_sel_i),
        .csr_ack_o(csr_ack_o),
        .csr_dat_o(csr_dat_o),
        .csr_err_o(csr_err_o),
        .sts_init_done(sts_init_done),
        .sts_cal_done(sts_cal_done),
        .sts_cal_fail(sts_cal_fail),
        .sts_bist_done(sts_bist_done),
        .sts_bist_fail(sts_bist_fail),
        .sts_ref_pending_cnt(sts_ref_pending_cnt),
        .sts_self_refresh_active(sts_self_refresh_active),
        .sts_ecc_ce_count(sts_ecc_ce_count),
        .sts_ecc_ue_event(sts_ecc_ue_event),
        .sts_ref_starve_event(sts_ref_starve_event),
        .sts_init_fail_event(sts_init_fail_event),
        .sts_bist_fail_addr(sts_bist_fail_addr),
        .cfg_tRCD_nCK(cfg_tRCD_nCK),
        .cfg_tRP_nCK(cfg_tRP_nCK),
        .cfg_tRAS_nCK(cfg_tRAS_nCK),
        .cfg_tRC_nCK(cfg_tRC_nCK),
        .cfg_tRRD_nCK(cfg_tRRD_nCK),
        .cfg_tWTR_nCK(cfg_tWTR_nCK),
        .cfg_tFAW_nCK(cfg_tFAW_nCK),
        .cfg_tRFC_nCK(cfg_tRFC_nCK),
        .cfg_tWR_nCK(cfg_tWR_nCK),
        .cfg_tRTP_nCK(cfg_tRTP_nCK),
        .cfg_CL_nCK(cfg_CL_nCK),
        .cfg_CWL_nCK(cfg_CWL_nCK),
        .cfg_tCCD_nCK(cfg_tCCD_nCK),
        .cfg_tREFI_nCK(cfg_tREFI_nCK),
        .cfg_sched_policy(cfg_sched_policy),
        .cfg_row_policy(cfg_row_policy),
        .cfg_self_ref_mode(cfg_self_ref_mode),
        .cfg_ecc_enable(cfg_ecc_enable),
        .cfg_bist_start(cfg_bist_start),
        .cfg_force_refresh(cfg_force_refresh),
        .cfg_force_self_ref(cfg_force_self_ref),
        .cfg_max_postpone(cfg_max_postpone),
        .cfg_urgent_threshold(cfg_urgent_threshold),
        .cfg_ref_priority(cfg_ref_priority),
        .cfg_bist_pattern(cfg_bist_pattern),
        .cfg_bist_addr_mode(cfg_bist_addr_mode),
        .cfg_bist_addr_start(cfg_bist_addr_start),
        .cfg_bist_addr_end(cfg_bist_addr_end)
    );

    // Clock generation: 5ns period (200MHz)
    localparam CLOCK_PERIOD = 5.0;
    
    initial begin
        clk = 1'b0;
        forever #(CLOCK_PERIOD/2) clk = ~clk;
    end

    // Testbench variables
    integer fd;
    integer scan_result;
    integer vector_num;
    integer total_tests;
    integer pass_count;
    integer fail_count;
    integer cycle_count;
    integer timeout_count;
    
    logic [7:0]  opcode;
    logic [7:0]  addr;
    logic [31:0] wdata;
    logic [31:0] expected;
    
    string vector_file;

    // Watchdog timeout
    initial begin
        timeout_count = 0;
        forever begin
            @(posedge clk);
            timeout_count = timeout_count + 1;
            if (timeout_count >= 100000) begin
                $display("ERROR: Watchdog timeout after %0d cycles", timeout_count);
                $display("FAIL: %0d/%0d", pass_count, total_tests);
                $finish;
            end
        end
    end

    // Task to perform reset
    task do_reset();
        begin
            rst_n = 1'b0;
            // Reset all status inputs
            sts_init_done = 1'b0;
            sts_cal_done = 1'b0;
            sts_cal_fail = 1'b0;
            sts_bist_done = 1'b0;
            sts_bist_fail = 1'b0;
            sts_ref_pending_cnt = 3'b0;
            sts_self_refresh_active = 1'b0;
            sts_ecc_ce_count = 16'b0;
            sts_ecc_ue_event = 1'b0;
            sts_ref_starve_event = 1'b0;
            sts_init_fail_event = 1'b0;
            sts_bist_fail_addr = 13'b0;
            // Deassert bus
            csr_cyc_i = 1'b0;
            csr_stb_i = 1'b0;
            csr_we_i = 1'b0;
            csr_adr_i = 8'b0;
            csr_dat_i = 32'b0;
            csr_sel_i = 4'hF;
            // Hold reset for 4 cycles
            repeat(4) @(posedge clk);
            rst_n = 1'b1;
            @(posedge clk);
        end
    endtask

    // Task to perform write
    task do_write(input [7:0] address, input [31:0] data);
        begin
            @(posedge clk);
            csr_cyc_i = 1'b1;
            csr_stb_i = 1'b1;
            csr_we_i = 1'b1;
            csr_adr_i = address;
            csr_dat_i = data;
            csr_sel_i = 4'hF;
            // Wait for ack
            while (!csr_ack_o) begin
                @(posedge clk);
            end
            @(posedge clk);
            // Deassert bus
            csr_cyc_i = 1'b0;
            csr_stb_i = 1'b0;
            csr_we_i = 1'b0;
            csr_adr_i = 8'b0;
            csr_dat_i = 32'b0;
        end
    endtask

    // Task to perform read and check
    task do_read(input [7:0] address, input [31:0] exp_data, input integer vec_num);
        logic [31:0] actual_data;
        begin
            @(posedge clk);
            csr_cyc_i = 1'b1;
            csr_stb_i = 1'b1;
            csr_we_i = 1'b0;
            csr_adr_i = address;
            csr_dat_i = 32'b0;
            csr_sel_i = 4'hF;
            // Wait for ack
            while (!csr_ack_o) begin
                @(posedge clk);
            end
            actual_data = csr_dat_o;
            @(posedge clk);
            // Deassert bus
            csr_cyc_i = 1'b0;
            csr_stb_i = 1'b0;
            csr_we_i = 1'b0;
            csr_adr_i = 8'b0;
            // Compare
            total_tests = total_tests + 1;
            if (actual_data === exp_data) begin
                pass_count = pass_count + 1;
            end else begin
                fail_count = fail_count + 1;
                $display("MISMATCH: Vector %0d, Address 0x%02h, Expected 0x%08h, Actual 0x%08h",
                         vec_num, address, exp_data, actual_data);
            end
        end
    endtask

    // Task to inject status bits
    task do_inject(input [31:0] data);
        begin
            @(posedge clk);
            // Level-driven status bits
            sts_init_done = data[0];
            sts_cal_done = data[1];
            sts_cal_fail = data[2];
            sts_bist_done = data[3];
            sts_bist_fail = data[4];
            sts_ref_pending_cnt = data[7:5];
            sts_self_refresh_active = data[8];
            // Pulse event bits for 1 cycle
            sts_ecc_ue_event = data[16];
            sts_ref_starve_event = data[17];
            sts_init_fail_event = data[18];
            @(posedge clk);
            // Deassert event pulses
            sts_ecc_ue_event = 1'b0;
            sts_ref_starve_event = 1'b0;
            sts_init_fail_event = 1'b0;
        end
    endtask

    // Task to inject wide status bits
    task do_inject_wide(input [31:0] data);
        begin
            @(posedge clk);
            sts_ecc_ce_count = data[15:0];
            sts_bist_fail_addr = data[28:16];
        end
    endtask

    // Main test process
    initial begin
        // Initialize signals
        clk = 1'b0;
        rst_n = 1'b1;
        csr_cyc_i = 1'b0;
        csr_stb_i = 1'b0;
        csr_we_i = 1'b0;
        csr_adr_i = 8'b0;
        csr_dat_i = 32'b0;
        csr_sel_i = 4'hF;
        sts_init_done = 1'b0;
        sts_cal_done = 1'b0;
        sts_cal_fail = 1'b0;
        sts_bist_done = 1'b0;
        sts_bist_fail = 1'b0;
        sts_ref_pending_cnt = 3'b0;
        sts_self_refresh_active = 1'b0;
        sts_ecc_ce_count = 16'b0;
        sts_ecc_ue_event = 1'b0;
        sts_ref_starve_event = 1'b0;
        sts_init_fail_event = 1'b0;
        sts_bist_fail_addr = 13'b0;
        
        vector_num = 0;
        total_tests = 0;
        pass_count = 0;
        fail_count = 0;
        
        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "config_regs_vectors.hex";
        end
        
        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Cannot open vector file: %s", vector_file);
            $finish;
        end
        
        // Wait for clock to stabilize
        @(posedge clk);
        @(posedge clk);
        
        // Process vectors
        while (!$feof(fd)) begin
            scan_result = $fscanf(fd, "%h %h %h %h", opcode, addr, wdata, expected);
            if (scan_result == 4) begin
                vector_num = vector_num + 1;
                
                case (opcode)
                    8'h00: begin // Reset
                        do_reset();
                    end
                    8'h01: begin // Read
                        do_read(addr, expected, vector_num);
                    end
                    8'h02: begin // Write
                        do_write(addr, wdata);
                    end
                    8'h03: begin // Inject status
                        do_inject(wdata);
                    end
                    8'h04: begin // Inject wide
                        do_inject_wide(wdata);
                    end
                    default: begin
                        $display("WARNING: Unknown opcode 0x%02h at vector %0d", opcode, vector_num);
                    end
                endcase
            end
        end
        
        $fclose(fd);
        
        // Print summary
        @(posedge clk);
        if (fail_count == 0) begin
            $display("PASS: %0d/%0d", pass_count, total_tests);
        end else begin
            $display("FAIL: %0d/%0d", pass_count, total_tests);
        end
        
        $finish;
    end

endmodule