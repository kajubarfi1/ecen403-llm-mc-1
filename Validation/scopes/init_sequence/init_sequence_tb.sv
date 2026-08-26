module init_sequence_tb;

    // clock_reset
    logic                    clk;
    logic                    rst_n;

    // control
    logic                    enable;

    // status_out
    logic                    init_done;
    logic                    init_fail;

    // ddr_cmd_out
    logic                    init_cmd_valid;
    logic [ 3:0]             init_cmd;
    logic [14:0]             init_addr;
    logic [ 2:0]             init_bank;

    // ddr_ctrl_out
    logic                    init_cke;
    logic                    init_reset_n;

    // debug
    logic [ 3:0]             init_state;

    // DUT instantiation
    init_fsm dut (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .init_done(init_done),
        .init_fail(init_fail),
        .init_cmd_valid(init_cmd_valid),
        .init_cmd(init_cmd),
        .init_addr(init_addr),
        .init_bank(init_bank),
        .init_cke(init_cke),
        .init_reset_n(init_reset_n),
        .init_state(init_state)
    );

    // Clock parameters
    localparam real CLK_PERIOD = 5.0;
    localparam real CLK_HALF   = CLK_PERIOD / 2.0;

    // Command encodings (typical DDR3)
    localparam logic [3:0] CMD_NOP  = 4'b0111;
    localparam logic [3:0] CMD_MRS  = 4'b0000;
    localparam logic [3:0] CMD_ZQCL = 4'b0110;

    // Vector storage
    localparam int MAX_VECTORS = 1024;
    logic [7:0]  vec_opcode   [MAX_VECTORS];
    logic [31:0] vec_param    [MAX_VECTORS];
    logic [31:0] vec_signal   [MAX_VECTORS];
    logic [31:0] vec_value    [MAX_VECTORS];
    int          num_vectors;

    // Cycle tracking for wait_for events
    // Using fixed arrays indexed by signal_id (0-5) and value (0-15)
    logic [31:0] event_cycle [6][16];
    logic        event_valid [6][16];

    // Test counters
    int pass_count;
    int fail_count;
    int cycle_count;
    logic [3:0] prev_init_state;

    // Vector file
    string vector_file;
    int fd;

    // Clock generation
    initial begin
        clk = 1'b0;
        forever #(CLK_HALF) clk = ~clk;
    end

    // Cycle counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            cycle_count <= 0;
        else
            cycle_count <= cycle_count + 1;
    end

    // State transition monitoring
    always @(posedge clk) begin
        if (rst_n) begin
            if (init_state !== prev_init_state) begin
                $display("[%0t] STATE TRANSITION: %0d -> %0d (cycle %0d)", 
                         $time, prev_init_state, init_state, cycle_count);
            end
            prev_init_state <= init_state;
        end
    end

    // Function to sample signal by ID
    function automatic logic [31:0] sample_signal(input int sig_id);
        case (sig_id)
            0: return {31'b0, init_reset_n};
            1: return {31'b0, init_cke};
            2: return {28'b0, init_cmd_valid, init_bank};  // mrs composite
            3: return {28'b0, init_cmd_valid, init_cmd};   // zqcl composite
            4: return {31'b0, init_done};
            5: return {31'b0, init_fail};
            default: return 32'hDEADBEEF;
        endcase
    endfunction

    // Function to check signal match
    function automatic logic check_signal_match(input int sig_id, input logic [31:0] expected);
        logic [31:0] actual;
        actual = sample_signal(sig_id);
        case (sig_id)
            0: return (actual[0] == expected[0]);
            1: return (actual[0] == expected[0]);
            2: begin
                // mrs: init_cmd_valid must be 1 and init_bank must match expected
                return (actual[3] == 1'b1) && (actual[2:0] == expected[2:0]);
            end
            3: begin
                // zqcl: init_cmd_valid must be 1 and init_cmd must be ZQCL encoding
                return (actual[3] == 1'b1) && (actual[2:0] == CMD_ZQCL[2:0]) && (init_cmd == CMD_ZQCL);
            end
            4: return (actual[0] == expected[0]);
            5: return (actual[0] == expected[0]);
            default: return 1'b0;
        endcase
    endfunction

    // Function to get signal name
    function automatic string get_signal_name(input int sig_id);
        case (sig_id)
            0: return "init_reset_n";
            1: return "init_cke";
            2: return "mrs";
            3: return "zqcl";
            4: return "init_done";
            5: return "init_fail";
            default: return "UNKNOWN";
        endcase
    endfunction

    // Main test process
    initial begin
        // Initialize
        rst_n = 1'b0;
        enable = 1'b0;
        pass_count = 0;
        fail_count = 0;
        num_vectors = 0;
        prev_init_state = 4'b0;

        // Initialize event tracking arrays
        for (int i = 0; i < 6; i++) begin
            for (int j = 0; j < 16; j++) begin
                event_cycle[i][j] = 0;
                event_valid[i][j] = 1'b0;
            end
        end

        // Get vector filename
        if (!$value$plusargs("VECTOR_FILE=%s", vector_file)) begin
            vector_file = "init_sequence_vectors.hex";
        end
        $display("[%0t] Using vector file: %s", $time, vector_file);

        // Open and read vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("[%0t] ERROR: Cannot open vector file: %s", $time, vector_file);
            $finish;
        end

        // Read all vectors
        while (!$feof(fd) && num_vectors < MAX_VECTORS) begin
            int scan_result;
            logic [7:0] op;
            logic [31:0] p, s, v;
            scan_result = $fscanf(fd, "%h %h %h %h\n", op, p, s, v);
            if (scan_result == 4) begin
                vec_opcode[num_vectors] = op;
                vec_param[num_vectors] = p;
                vec_signal[num_vectors] = s;
                vec_value[num_vectors] = v;
                num_vectors = num_vectors + 1;
            end
        end
        $fclose(fd);
        $display("[%0t] Loaded %0d vectors", $time, num_vectors);

        // Process vectors
        for (int vec_idx = 0; vec_idx < num_vectors; vec_idx++) begin
            logic [7:0] opcode;
            logic [31:0] param, sig_id, expected;
            
            opcode = vec_opcode[vec_idx];
            param = vec_param[vec_idx];
            sig_id = vec_signal[vec_idx];
            expected = vec_value[vec_idx];

            case (opcode)
                8'h00: begin
                    // Reset
                    $display("[%0t] VEC[%0d] RESET", $time, vec_idx);
                    rst_n = 1'b0;
                    enable = 1'b0;
                    repeat (10) @(posedge clk);
                    rst_n = 1'b1;
                    enable = 1'b1;
                    @(posedge clk);
                    $display("[%0t] Reset complete, enable asserted", $time);
                end

                8'h01: begin
                    // check_not_yet: at cycle P, signal S must NOT equal V
                    int target_cycle;
                    logic [31:0] actual;
                    target_cycle = param;
                    
                    // Wait until target cycle
                    while (cycle_count < target_cycle) begin
                        @(posedge clk);
                        if (cycle_count > 800000) begin
                            $display("[%0t] ERROR: Simulation timeout", $time);
                            $display("SUMMARY: PASS=%0d FAIL=%0d", pass_count, fail_count);
                            $finish;
                        end
                    end
                    
                    actual = sample_signal(sig_id);
                    if (!check_signal_match(sig_id, expected)) begin
                        $display("[%0t] VEC[%0d] PASS: check_not_yet %s != 0x%0h at cycle %0d (actual=0x%0h)",
                                 $time, vec_idx, get_signal_name(sig_id), expected, cycle_count, actual);
                        pass_count = pass_count + 1;
                    end else begin
                        $display("[%0t] VEC[%0d] FAIL: check_not_yet %s == 0x%0h at cycle %0d (should NOT match)",
                                 $time, vec_idx, get_signal_name(sig_id), expected, cycle_count);
                        fail_count = fail_count + 1;
                    end
                end

                8'h02: begin
                    // wait_for: wait until signal S equals V, timeout P cycles
                    int timeout;
                    int start_cycle;
                    logic matched;
                    int val_idx;
                    
                    timeout = param;
                    start_cycle = cycle_count;
                    matched = 1'b0;
                    val_idx = expected[3:0];  // Use lower 4 bits as index
                    
                    $display("[%0t] VEC[%0d] wait_for: %s == 0x%0h (timeout=%0d cycles)",
                             $time, vec_idx, get_signal_name(sig_id), expected, timeout);
                    
                    while (!matched && (cycle_count - start_cycle) < timeout) begin
                        if (check_signal_match(sig_id, expected)) begin
                            matched = 1'b1;
                            // Store event cycle using blocking assignment
                            event_cycle[sig_id][val_idx] = cycle_count;
                            event_valid[sig_id][val_idx] = 1'b1;
                            $display("[%0t] VEC[%0d] PASS: wait_for %s == 0x%0h at cycle %0d",
                                     $time, vec_idx, get_signal_name(sig_id), expected, cycle_count);
                            pass_count = pass_count + 1;
                        end else begin
                            @(posedge clk);
                        end
                        
                        if (cycle_count > 800000) begin
                            $display("[%0t] ERROR: Simulation timeout", $time);
                            $display("SUMMARY: PASS=%0d FAIL=%0d", pass_count, fail_count);
                            $finish;
                        end
                    end
                    
                    if (!matched) begin
                        $display("[%0t] VEC[%0d] FAIL: wait_for %s == 0x%0h TIMEOUT after %0d cycles",
                                 $time, vec_idx, get_signal_name(sig_id), expected, timeout);
                        fail_count = fail_count + 1;
                    end
                end

                8'h03: begin
                    // check_order: verify event A happened before event B with >= P cycle gap
                    int first_sig, second_sig;
                    int first_val, second_val;
                    int min_gap;
                    int first_cycle_stored, second_cycle_stored;
                    int actual_gap;
                    
                    first_sig = sig_id[31:16];
                    second_sig = sig_id[15:0];
                    first_val = expected[31:16];
                    second_val = expected[15:0];
                    min_gap = param;
                    
                    first_cycle_stored = event_cycle[first_sig][first_val[3:0]];
                    second_cycle_stored = event_cycle[second_sig][second_val[3:0]];
                    
                    if (!event_valid[first_sig][first_val[3:0]]) begin
                        $display("[%0t] VEC[%0d] FAIL: check_order - first event (%s=0x%0h) not recorded",
                                 $time, vec_idx, get_signal_name(first_sig), first_val);
                        fail_count = fail_count + 1;
                    end else if (!event_valid[second_sig][second_val[3:0]]) begin
                        $display("[%0t] VEC[%0d] FAIL: check_order - second event (%s=0x%0h) not recorded",
                                 $time, vec_idx, get_signal_name(second_sig), second_val);
                        fail_count = fail_count + 1;
                    end else begin
                        actual_gap = second_cycle_stored - first_cycle_stored;
                        if (actual_gap >= min_gap) begin
                            $display("[%0t] VEC[%0d] PASS: check_order %s->%s gap=%0d (min=%0d)",
                                     $time, vec_idx, get_signal_name(first_sig), 
                                     get_signal_name(second_sig), actual_gap, min_gap);
                            pass_count = pass_count + 1;
                        end else begin
                            $display("[%0t] VEC[%0d] FAIL: check_order %s->%s gap=%0d < min=%0d",
                                     $time, vec_idx, get_signal_name(first_sig), 
                                     get_signal_name(second_sig), actual_gap, min_gap);
                            fail_count = fail_count + 1;
                        end
                    end
                end

                8'h04: begin
                    // final_check: at current sim time, signal S must equal V
                    logic [31:0] actual;
                    actual = sample_signal(sig_id);
                    
                    if (check_signal_match(sig_id, expected)) begin
                        $display("[%0t] VEC[%0d] PASS: final_check %s == 0x%0h",
                                 $time, vec_idx, get_signal_name(sig_id), expected);
                        pass_count = pass_count + 1;
                    end else begin
                        $display("[%0t] VEC[%0d] FAIL: final_check %s != 0x%0h (actual=0x%0h)",
                                 $time, vec_idx, get_signal_name(sig_id), expected, actual);
                        fail_count = fail_count + 1;
                    end
                end

                default: begin
                    $display("[%0t] VEC[%0d] WARNING: Unknown opcode 0x%0h", 
                             $time, vec_idx, opcode);
                end
            endcase
        end

        // Allow some additional cycles for final settling
        repeat (100) @(posedge clk);

        // Print summary
        $display("");
        $display("========================================");
        $display("TEST SUMMARY");
        $display("========================================");
        $display("Total vectors processed: %0d", num_vectors);
        $display("PASS: %0d", pass_count);
        $display("FAIL: %0d", fail_count);
        if (fail_count == 0)
            $display("RESULT: ALL TESTS PASSED");
        else
            $display("RESULT: SOME TESTS FAILED");
        $display("========================================");
        $display("");
        
        $finish;
    end

    // Global timeout watchdog
    initial begin
        #(800000 * CLK_PERIOD);
        $display("[%0t] ERROR: Global simulation timeout (800000 cycles)", $time);
        $display("SUMMARY: PASS=%0d FAIL=%0d", pass_count, fail_count);
        $finish;
    end

endmodule