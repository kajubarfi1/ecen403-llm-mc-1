`timescale 1ns/1ps

module init_fsm_tb;

  // Parameters
  localparam DDR_ADDR_W = 16;
  localparam DDR_BANK_W = 3;
  localparam CLK_PERIOD = 5.0; // 200 MHz
  localparam TIMEOUT_CYCLES = 140362 + 10000; // generous margin
  
  // DUT signals
  logic                    clk;
  logic                    rst_n;
  logic                    enable;
  logic                    init_done;
  logic                    init_fail;
  logic                    init_cmd_valid;
  logic [3:0]              init_cmd;
  logic [DDR_ADDR_W-1:0]   init_addr;
  logic [DDR_BANK_W-1:0]   init_bank;
  logic                    init_cke;
  logic                    init_reset_n;
  logic [3:0]              init_state;

  // Command definitions
  localparam [3:0] CMD_MRS  = 4'b0000;
  localparam [3:0] CMD_ZQCL = 4'b0110;
  localparam [3:0] CMD_NOP  = 4'b0111;
  
  // MR bank addresses
  localparam [2:0] MR0 = 3'b000;
  localparam [2:0] MR1 = 3'b001;
  localparam [2:0] MR2 = 3'b010;
  localparam [2:0] MR3 = 3'b011;

  // Testbench variables
  int cycle_count;
  logic [2:0] mr_sequence[$];
  int zqcl_count;
  logic test_pass;
  logic timeout_fail;
  logic mr_order_fail;
  logic zqcl_fail;
  logic cke_fail;
  
  // DUT instantiation
  init_fsm #(
    .DDR_ADDR_W(DDR_ADDR_W),
    .DDR_BANK_W(DDR_BANK_W)
  ) dut (
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

  // Clock generation
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // VCD dump
  initial begin
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);
  end

  // Monitor MRS commands to capture MR programming order
  always @(posedge clk) begin
    if (rst_n && init_cmd_valid && init_cmd == CMD_MRS) begin
      mr_sequence.push_back(init_bank);
      $display("Time %0t: MRS command detected - MR%0d", $time, init_bank);
    end
    
    if (rst_n && init_cmd_valid && init_cmd == CMD_ZQCL) begin
      zqcl_count++;
      $display("Time %0t: ZQCL command detected", $time);
    end
  end

  // Check CKE behavior during reset/wait
  always @(posedge clk) begin
    if (rst_n && !init_done) begin
      // During early states (reset, CKE wait), CKE should be low
      // We'll check that CKE is low when reset_n is low
      if (!init_reset_n && init_cke) begin
        cke_fail = 1;
        $display("Time %0t: [ERROR] CKE high while init_reset_n is low", $time);
      end
    end
  end

  // Main test sequence
  initial begin
    // Initialize
    rst_n = 0;
    enable = 0;
    cycle_count = 0;
    zqcl_count = 0;
    test_pass = 1;
    timeout_fail = 0;
    mr_order_fail = 0;
    zqcl_fail = 0;
    cke_fail = 0;
    
    $display("========================================");
    $display("Starting init_fsm testbench");
    $display("Clock period: %0.2f ns (200 MHz)", CLK_PERIOD);
    $display("========================================");
    
    // Apply async reset
    $display("Time %0t: Applying reset", $time);
    repeat(10) @(posedge clk);
    
    // Deassert reset
    rst_n = 1;
    $display("Time %0t: Reset deasserted", $time);
    repeat(5) @(posedge clk);
    
    // Pulse enable
    $display("Time %0t: Asserting enable", $time);
    enable = 1;
    @(posedge clk);
    enable = 1; // Keep high or pulse - keeping high for safety
    
    // Wait for init_done or timeout
    fork
      begin
        // Wait for init_done
        wait(init_done);
        $display("Time %0t: init_done asserted at cycle %0d", $time, cycle_count);
      end
      begin
        // Timeout watchdog
        repeat(TIMEOUT_CYCLES) @(posedge clk);
        if (!init_done) begin
          timeout_fail = 1;
          $display("Time %0t: [ERROR] Timeout - init_done not asserted within %0d cycles", 
                   $time, TIMEOUT_CYCLES);
        end
      end
    join_any
    
    // Wait a few more cycles to ensure all commands are captured
    repeat(10) @(posedge clk);
    
    // Check results
    $display("\n========================================");
    $display("Checking results...");
    $display("========================================");
    
    // Check timeout
    if (timeout_fail) begin
      test_pass = 0;
      $display("[FAIL] Initialization timeout");
    end else begin
      $display("[PASS] Initialization completed within timeout");
    end
    
    // Check MR programming order: MR2 -> MR3 -> MR1 -> MR0
    $display("\nMR sequence captured: %p", mr_sequence);
    if (mr_sequence.size() < 4) begin
      mr_order_fail = 1;
      test_pass = 0;
      $display("[FAIL] Expected at least 4 MRS commands, got %0d", mr_sequence.size());
    end else begin
      // Check first 4 MRS commands match expected order
      if (mr_sequence[0] == MR2 && 
          mr_sequence[1] == MR3 && 
          mr_sequence[2] == MR1 && 
          mr_sequence[3] == MR0) begin
        $display("[PASS] MR programming order correct: MR2->MR3->MR1->MR0");
      end else begin
        mr_order_fail = 1;
        test_pass = 0;
        $display("[FAIL] MR programming order incorrect");
        $display("       Expected: MR2->MR3->MR1->MR0");
        $display("       Got:      MR%0d->MR%0d->MR%0d->MR%0d", 
                 mr_sequence[0], mr_sequence[1], mr_sequence[2], mr_sequence[3]);
      end
    end
    
    // Check ZQCL
    $display("\nZQCL commands detected: %0d", zqcl_count);
    if (zqcl_count >= 1) begin
      $display("[PASS] ZQCL command issued at least once");
    end else begin
      zqcl_fail = 1;
      test_pass = 0;
      $display("[FAIL] ZQCL command not detected");
    end
    
    // Check CKE behavior
    if (cke_fail) begin
      test_pass = 0;
      $display("[FAIL] CKE behavior incorrect during reset");
    end else begin
      $display("[PASS] CKE behavior correct");
    end
    
    // Check init_fail
    if (init_fail) begin
      test_pass = 0;
      $display("[FAIL] init_fail asserted unexpectedly");
    end else begin
      $display("[PASS] init_fail not asserted");
    end
    
    // Final summary
    $display("\n========================================");
    $display("TEST SUMMARY");
    $display("========================================");
    if (test_pass) begin
      $display("[PASS] All checks passed!");
    end else begin
      $display("[FAIL] One or more checks failed");
      if (timeout_fail) $display("  - Timeout failure");
      if (mr_order_fail) $display("  - MR order failure");
      if (zqcl_fail) $display("  - ZQCL failure");
      if (cke_fail) $display("  - CKE failure");
    end
    $display("========================================\n");
    
    $finish;
  end

  // Cycle counter
  always @(posedge clk) begin
    if (rst_n) cycle_count++;
  end

  // Safety timeout
  initial begin
    #(CLK_PERIOD * TIMEOUT_CYCLES * 2);
    $display("FATAL: Absolute timeout reached");
    $finish;
  end

endmodule
