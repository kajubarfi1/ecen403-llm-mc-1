module wb_port_tb;

    // clock_reset
    logic                    clk;
    logic                    rst_n;

    // external_in
    logic                    wb_cyc_i;
    logic                    wb_stb_i;
    logic                    wb_we_i;
    logic [28:0]             wb_adr_i;
    logic [31:0]             wb_dat_i;
    logic [ 3:0]             wb_sel_i;
    logic [ 1:0]             wb_bte_i;
    logic [ 2:0]             wb_cti_i;

    // external_out
    logic                    wb_ack_o;
    logic [31:0]             wb_dat_o;
    logic                    wb_stall_o;
    logic                    wb_err_o;

    // internal_out
    logic                    req_valid;
    logic                    req_we;
    logic [28:0]             req_addr;
    logic [31:0]             req_wdata;
    logic [ 3:0]             req_wmask;
    logic [ 3:0]             req_aux;

    // internal_in
    logic                    req_ready;
    logic                    rsp_valid;
    logic [31:0]             rsp_rdata;
    logic [ 3:0]             rsp_aux;

    // Testbench variables
    integer                  fd;
    integer                  scan_result;
    integer                  pass_count;
    integer                  fail_count;
    integer                  vector_count;
    integer                  timeout_count;
    
    logic [7:0]              opcode;
    logic [31:0]             addr;
    logic [31:0]             wdata;
    logic [31:0]             expected;
    
    string                   vector_file;
    
    // Watchdog parameters
    localparam WATCHDOG_TIMEOUT = 10000;
    
    // Don't-care sentinel
    localparam DONT_CARE = 32'hDEAD0000;

    // Clock generation: 5.0ns period (200MHz)
    initial begin
        clk = 1'b0;
        forever #2.5 clk = ~clk;
    end

    // DUT instantiation
    wb_port dut (
        .clk(clk),
        .rst_n(rst_n),
        .wb_cyc_i(wb_cyc_i),
        .wb_stb_i(wb_stb_i),
        .wb_we_i(wb_we_i),
        .wb_adr_i(wb_adr_i),
        .wb_dat_i(wb_dat_i),
        .wb_sel_i(wb_sel_i),
        .wb_bte_i(wb_bte_i),
        .wb_cti_i(wb_cti_i),
        .wb_ack_o(wb_ack_o),
        .wb_dat_o(wb_dat_o),
        .wb_stall_o(wb_stall_o),
        .wb_err_o(wb_err_o),
        .req_valid(req_valid),
        .req_we(req_we),
        .req_addr(req_addr),
        .req_wdata(req_wdata),
        .req_wmask(req_wmask),
        .req_aux(req_aux),
        .req_ready(req_ready),
        .rsp_valid(rsp_valid),
        .rsp_rdata(rsp_rdata),
        .rsp_aux(rsp_aux)
    );

    // Simple memory model for read responses
    logic [31:0] mem_model [logic [28:0]];
    logic [3:0]  pending_aux_queue [$];
    logic [31:0] pending_data_queue [$];

    // Handle request ready - always accept
    assign req_ready = 1'b1;

    // Generate read responses based on stored write data
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rsp_valid <= 1'b0;
            rsp_rdata <= 32'h0;
            rsp_aux <= 4'h0;
        end else begin
            if (pending_aux_queue.size() > 0) begin
                rsp_valid <= 1'b1;
                rsp_rdata <= pending_data_queue[0];
                rsp_aux <= pending_aux_queue[0];
            end else begin
                rsp_valid <= 1'b0;
                rsp_rdata <= 32'h0;
                rsp_aux <= 4'h0;
            end
        end
    end

    // Pop from queues using blocking assignments
    always @(posedge clk) begin
        if (rst_n && pending_aux_queue.size() > 0) begin
            void'(pending_aux_queue.pop_front());
            void'(pending_data_queue.pop_front());
        end
    end

    // Capture requests and queue responses
    always @(posedge clk) begin
        if (rst_n && req_valid && req_ready) begin
            if (!req_we) begin
                // Read request - queue response
                if (mem_model.exists(req_addr)) begin
                    pending_data_queue.push_back(mem_model[req_addr]);
                end else begin
                    pending_data_queue.push_back(32'hDEADBEEF);
                end
                pending_aux_queue.push_back(req_aux);
            end else begin
                // Write request - store data
                mem_model[req_addr] = req_wdata;
            end
        end
    end

    // Task to perform reset
    task do_reset();
        begin
            rst_n = 1'b0;
            wb_cyc_i = 1'b0;
            wb_stb_i = 1'b0;
            wb_we_i = 1'b0;
            wb_adr_i = 29'h0;
            wb_dat_i = 32'h0;
            wb_sel_i = 4'h0;
            wb_bte_i = 2'b00;
            wb_cti_i = 3'b000;
            // Clear queues using blocking
            pending_aux_queue = {};
            pending_data_queue = {};
            mem_model.delete();
            repeat(4) @(posedge clk);
            rst_n = 1'b1;
            @(posedge clk);
        end
    endtask

    // Task to perform write
    task do_write(input logic [31:0] address, input logic [31:0] data);
        integer wait_cycles;
        begin
            @(posedge clk);
            wb_cyc_i = 1'b1;
            wb_stb_i = 1'b1;
            wb_we_i = 1'b1;
            wb_adr_i = address[28:0];
            wb_dat_i = data;
            wb_sel_i = 4'hF;
            wb_bte_i = 2'b00;
            wb_cti_i = 3'b000;
            
            wait_cycles = 0;
            while (!wb_ack_o && wait_cycles < WATCHDOG_TIMEOUT) begin
                @(posedge clk);
                // Deassert stb if stalled
                if (!wb_stall_o) begin
                    wb_stb_i = 1'b0;
                end
                wait_cycles = wait_cycles + 1;
            end
            
            if (wait_cycles >= WATCHDOG_TIMEOUT) begin
                $display("[%0t] TIMEOUT: Write to addr 0x%08h did not complete", $time, address);
                fail_count = fail_count + 1;
            end else begin
                $display("[%0t] Write PASS: addr=0x%08h data=0x%08h (ack received)", $time, address, data);
                pass_count = pass_count + 1;
            end
            
            @(posedge clk);
            wb_cyc_i = 1'b0;
            wb_stb_i = 1'b0;
            wb_we_i = 1'b0;
        end
    endtask

    // Task to perform read
    task do_read(input logic [31:0] address, input logic [31:0] exp_data);
        integer wait_cycles;
        logic [31:0] read_data;
        begin
            @(posedge clk);
            wb_cyc_i = 1'b1;
            wb_stb_i = 1'b1;
            wb_we_i = 1'b0;
            wb_adr_i = address[28:0];
            wb_dat_i = 32'h0;
            wb_sel_i = 4'hF;
            wb_bte_i = 2'b00;
            wb_cti_i = 3'b000;
            
            wait_cycles = 0;
            while (!wb_ack_o && wait_cycles < WATCHDOG_TIMEOUT) begin
                @(posedge clk);
                // Deassert stb if not stalled
                if (!wb_stall_o) begin
                    wb_stb_i = 1'b0;
                end
                wait_cycles = wait_cycles + 1;
            end
            
            if (wait_cycles >= WATCHDOG_TIMEOUT) begin
                $display("[%0t] TIMEOUT: Read from addr 0x%08h did not complete", $time, address);
                fail_count = fail_count + 1;
            end else begin
                read_data = wb_dat_o;
                if (exp_data == DONT_CARE) begin
                    $display("[%0t] Read PASS (don't-care): addr=0x%08h data=0x%08h", $time, address, read_data);
                    pass_count = pass_count + 1;
                end else if (read_data == exp_data) begin
                    $display("[%0t] Read PASS: addr=0x%08h expected=0x%08h actual=0x%08h", $time, address, exp_data, read_data);
                    pass_count = pass_count + 1;
                end else begin
                    $display("[%0t] Read FAIL: addr=0x%08h expected=0x%08h actual=0x%08h", $time, address, exp_data, read_data);
                    fail_count = fail_count + 1;
                end
            end
            
            @(posedge clk);
            wb_cyc_i = 1'b0;
            wb_stb_i = 1'b0;
            wb_we_i = 1'b0;
        end
    endtask

    // Task to do idle cycle
    task do_idle();
        begin
            wb_cyc_i = 1'b0;
            wb_stb_i = 1'b0;
            wb_we_i = 1'b0;
            @(posedge clk);
        end
    endtask

    // Main test process
    initial begin
        // Initialize counters
        pass_count = 0;
        fail_count = 0;
        vector_count = 0;
        
        // Initialize signals
        rst_n = 1'b0;
        wb_cyc_i = 1'b0;
        wb_stb_i = 1'b0;
        wb_we_i = 1'b0;
        wb_adr_i = 29'h0;
        wb_dat_i = 32'h0;
        wb_sel_i = 4'h0;
        wb_bte_i = 2'b00;
        wb_cti_i = 3'b000;
        
        // Get vector file name
        if (!$value$plusargs("VECTORS=%s", vector_file)) begin
            vector_file = "wb_port_vectors.hex";
        end
        
        $display("=========================================");
        $display("Starting wb_port testbench");
        $display("Vector file: %s", vector_file);
        $display("=========================================");
        
        // Open vector file
        fd = $fopen(vector_file, "r");
        if (fd == 0) begin
            $display("ERROR: Could not open vector file: %s", vector_file);
            $finish;
        end
        
        // Initial reset
        do_reset();
        
        // Process vectors
        while (!$feof(fd)) begin
            scan_result = $fscanf(fd, "%h %h %h %h\n", opcode, addr, wdata, expected);
            if (scan_result == 4) begin
                vector_count = vector_count + 1;
                
                case (opcode)
                    8'h00: begin // Reset
                        $display("[%0t] Vector %0d: RESET", $time, vector_count);
                        do_reset();
                    end
                    
                    8'h01: begin // Read
                        $display("[%0t] Vector %0d: READ addr=0x%08h expected=0x%08h", $time, vector_count, addr, expected);
                        do_read(addr, expected);
                    end
                    
                    8'h02: begin // Write
                        $display("[%0t] Vector %0d: WRITE addr=0x%08h data=0x%08h", $time, vector_count, addr, wdata);
                        do_write(addr, wdata);
                    end
                    
                    8'h03: begin // Idle
                        $display("[%0t] Vector %0d: IDLE", $time, vector_count);
                        do_idle();
                    end
                    
                    default: begin
                        $display("[%0t] Vector %0d: UNKNOWN opcode 0x%02h - skipping", $time, vector_count, opcode);
                    end
                endcase
            end
        end
        
        $fclose(fd);
        
        // Print summary
        $display("");
        $display("=========================================");
        $display("Testbench Summary");
        $display("=========================================");
        $display("Total vectors: %0d", vector_count);
        $display("PASS: %0d", pass_count);
        $display("FAIL: %0d", fail_count);
        $display("=========================================");
        
        if (fail_count == 0) begin
            $display("TEST PASSED");
        end else begin
            $display("TEST FAILED");
        end
        
        $display("=========================================");
        
        #100;
        $finish;
    end

    // Watchdog timer
    initial begin
        #(WATCHDOG_TIMEOUT * 100);
        $display("ERROR: Global watchdog timeout reached!");
        $display("PASS: %0d  FAIL: %0d", pass_count, fail_count);
        $finish;
    end

endmodule