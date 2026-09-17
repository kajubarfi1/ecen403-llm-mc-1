module init_fsm_tb;

  // Parameters
  localparam int DDR_ADDR_W = 15;
  localparam int DDR_BANK_W = 3;
  localparam int CLK_PERIOD = 5; // ns (200 MHz)
  localparam int TIMEOUT = 145162;

  // DUT signals
  logic                   clk;
  logic                   rst_n;
  logic                   enable;
  logic                   init_done;
  logic                   init_fail;
  logic                   init_cmd_valid;
  logic [3:0]             init_cmd;
  logic [DDR_ADDR_W-1:0]  init_addr;
  logic [DDR_BANK_W-1:0]  init_bank;
  logic                   init_cke;
  logic                   init_reset_n;
  logic [3:0]             init_state;

  // Testbench counters and flags
  int cycle_count;
  int reset_n_low_cycles;
  int cke_low_cycles;
  int cke_violations;
  int mrs_count;
  logic [2:0] mrs_banks[4];
  logic [DDR_ADDR_W-1:0] mrs_addrs[4];
  int zqcl_count;
  logic zqcl_addr10_high;
  logic done_seen;
  logic fail_seen;
  logic state_14_seen;

  // Test results
  int tests_passed;
  int tests_failed;
  int total_tests;

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
  initial clk = 0;
  always #2.5 clk = ~clk;

  // Sampling and counting (RULE 1 & RULE 2: sample before increment)
  always @(posedge clk) begin
    if (rst_n) begin
      // Sample signals first, then increment counters
      
      // Count RESET# low cycles
      if (!init_reset_n) begin
        reset_n_low_cycles <= reset_n_low_cycles + 1;
      end
      
      // Count CKE low cycles (total, we'll use this for the CKE-delay phase)
      if (!init_cke) begin
        cke_low_cycles <= cke_low_cycles + 1;
      end
      
      // Count CKE violations during RESET# low (RULE 4)
      if (!init_reset_n && init_cke) begin
        cke_violations <= cke_violations + 1;
      end
      
      // Capture MRS commands
      if (init_cmd_valid && init_cmd == 4'b0000) begin
        mrs_banks[mrs_count] <= init_bank;
        mrs_addrs[mrs_count] <= init_addr;
        mrs_count <= mrs_count + 1;
      end
      
      // Capture ZQCL commands
      if (init_cmd_valid && init_cmd == 4'b0110) begin
        zqcl_count <= zqcl_count + 1;
        if (init_addr[10] == 1'b1) begin
          zqcl_addr10_high <= 1'b1;
        end
      end
      
      // Track done and fail
      if (init_done) done_seen <= 1'b1;
      if (init_fail) fail_seen <= 1'b1;
      if (init_state == 4'd14) state_14_seen <= 1'b1;
      
      cycle_count <= cycle_count + 1;
    end
  end

  // Main test sequence
  initial begin
    // Waveform dump
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);

    // Initialize
    rst_n = 0;
    enable = 0;
    cycle_count = 0;
    reset_n_low_cycles = 0;
    cke_low_cycles = 0;
    cke_violations = 0;
    mrs_count = 0;
    zqcl_count = 0;
    zqcl_addr10_high = 0;
    done_seen = 0;
    fail_seen = 0;
    state_14_seen = 0;
    tests_passed = 0;
    tests_failed = 0;
    total_tests = 0;

    // Reset for 10 cycles
    repeat(10) @(posedge clk);
    rst_n = 1;
    
    // Wait one cycle then pulse enable
    @(posedge clk);
    enable = 1;
    @(posedge clk);
    enable = 0;

    // Wait for init_done or timeout
    fork
      begin
        wait(init_done);
      end
      begin
        repeat(TIMEOUT) @(posedge clk);
      end
    join_any

    // Give a few extra cycles for any final state transitions
    repeat(10) @(posedge clk);

    // Run all checks
    run_checks();

    // Print summary
    $display("\n========================================");
    if (tests_failed == 0) begin
      $display("ALL %0d TESTS PASSED", total_tests);
    end else begin
      $display("%0d of %0d TESTS FAILED", tests_failed, total_tests);
    end
    $display("========================================\n");

    $finish;
  end

  // Check functions
  task run_checks();
    // Test 1: init_done eventually asserts
    total_tests++;
    if (done_seen) begin
      $display("[PASS] 1: init_done asserted");
      tests_passed++;
    end else begin
      $display("[FAIL] 1: init_done never asserted");
      tests_failed++;
    end

    // Test 2: init_fail never asserts
    total_tests++;
    if (!fail_seen) begin
      $display("[PASS] 2: init_fail never asserted");
      tests_passed++;
    end else begin
      $display("[FAIL] 2: init_fail asserted (should never happen)");
      tests_failed++;
    end

    // Test 3: init_state reaches 4'd14
    total_tests++;
    if (state_14_seen) begin
      $display("[PASS] 3: init_state reached 4'd14 (S_DONE)");
      tests_passed++;
    end else begin
      $display("[FAIL] 3: init_state never reached 4'd14, final state = %0d", init_state);
      tests_failed++;
    end

    // Test 4: RESET# low for >= 40000 cycles
    total_tests++;
    if (reset_n_low_cycles >= 40000) begin
      $display("[PASS] 4: RESET# low for %0d cycles (>= 40000)", reset_n_low_cycles);
      tests_passed++;
    end else begin
      $display("[FAIL] 4: RESET# low for %0d cycles (expected >= 40000)", reset_n_low_cycles);
      tests_failed++;
    end

    // Test 5: CKE low for >= 100000 cycles during CKE-delay phase
    // Note: This counts all cycles where CKE was low after reset
    total_tests++;
    if (cke_low_cycles >= 100000) begin
      $display("[PASS] 5: CKE low for %0d cycles (>= 100000)", cke_low_cycles);
      tests_passed++;
    end else begin
      $display("[FAIL] 5: CKE low for %0d cycles (expected >= 100000)", cke_low_cycles);
      tests_failed++;
    end

    // Test 6: Exactly 4 MRS commands issued
    total_tests++;
    if (mrs_count == 4) begin
      $display("[PASS] 6: Exactly 4 MRS commands issued");
      tests_passed++;
    end else begin
      $display("[FAIL] 6: %0d MRS commands issued (expected 4)", mrs_count);
      tests_failed++;
    end

    // Test 7: MR program order is bank 2 -> 3 -> 1 -> 0
    total_tests++;
    if (mrs_count == 4 && 
        mrs_banks[0] == 3'd2 && 
        mrs_banks[1] == 3'd3 && 
        mrs_banks[2] == 3'd1 && 
        mrs_banks[3] == 3'd0) begin
      $display("[PASS] 7: MR program order correct (2->3->1->0)");
      tests_passed++;
    end else begin
      $display("[FAIL] 7: MR program order incorrect, got banks: %0d->%0d->%0d->%0d", 
               mrs_count >= 1 ? mrs_banks[0] : -1,
               mrs_count >= 2 ? mrs_banks[1] : -1,
               mrs_count >= 3 ? mrs_banks[2] : -1,
               mrs_count >= 4 ? mrs_banks[3] : -1);
      tests_failed++;
    end

    // Test 8: MR address values match
    total_tests++;
    if (mrs_count == 4 &&
        mrs_addrs[0] == 15'h0218 &&  // MR2
        mrs_addrs[1] == 15'h0000 &&  // MR3
        mrs_addrs[2] == 15'h0004 &&  // MR1
        mrs_addrs[3] == 15'h1D34) begin  // MR0
      $display("[PASS] 8: MR address values correct");
      tests_passed++;
    end else begin
      $display("[FAIL] 8: MR address values incorrect");
      if (mrs_count >= 1) $display("       MR2 = 0x%04h (expected 0x0218)", mrs_addrs[0]);
      if (mrs_count >= 2) $display("       MR3 = 0x%04h (expected 0x0000)", mrs_addrs[1]);
      if (mrs_count >= 3) $display("       MR1 = 0x%04h (expected 0x0004)", mrs_addrs[2]);
      if (mrs_count >= 4) $display("       MR0 = 0x%04h (expected 0x1D34)", mrs_addrs[3]);
      tests_failed++;
    end

    // Test 9: ZQCL command issued at least once
    total_tests++;
    if (zqcl_count >= 1) begin
      $display("[PASS] 9: ZQCL command issued (%0d times)", zqcl_count);
      tests_passed++;
    end else begin
      $display("[FAIL] 9: ZQCL command never issued");
      tests_failed++;
    end

    // Test 10: ZQCL has init_addr[10] === 1'b1
    total_tests++;
    if (zqcl_addr10_high) begin
      $display("[PASS] 10: ZQCL init_addr[10] = 1");
      tests_passed++;
    end else begin
      $display("[FAIL] 10: ZQCL init_addr[10] not set to 1");
      tests_failed++;
    end

    // Test 11: CKE violations during RESET# low == 0
    total_tests++;
    if (cke_violations == 0) begin
      $display("[PASS] 11: No CKE violations during RESET# low");
      tests_passed++;
    end else begin
      $display("[FAIL] 11: %0d CKE violations during RESET# low (CKE went high while RESET# low)", cke_violations);
      tests_failed++;
    end
  endtask

endmodule
