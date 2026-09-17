module init_fsm_tb;

  // Parameters
  localparam int DDR_ADDR_W = 15;
  localparam int DDR_BANK_W = 3;
  localparam int CLK_PERIOD = 5; // 5 ns = 200 MHz
  localparam int TIMEOUT = 145162;

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

  // Testbench counters and variables
  int cycle_count;
  int reset_n_low_cycles;
  int cke_low_cycles;
  int cke_violations;
  int mrs_count;
  logic [2:0] mrs_banks[4];
  logic [DDR_ADDR_W-1:0] mrs_addrs[4];
  int zqcl_count;
  logic zqcl_addr10_correct;
  
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

  // Cycle counter
  always @(posedge clk) begin
    if (rst_n) begin
      cycle_count <= cycle_count + 1;
    end else begin
      cycle_count <= 0;
    end
  end

  // Count RESET# low cycles
  always @(posedge clk) begin
    if (rst_n) begin
      if (!init_reset_n) begin
        reset_n_low_cycles <= reset_n_low_cycles + 1;
      end
    end
  end

  // Count CKE low cycles (during entire run)
  always @(posedge clk) begin
    if (rst_n) begin
      if (!init_cke) begin
        cke_low_cycles <= cke_low_cycles + 1;
      end
    end
  end

  // Count CKE violations (CKE high while RESET# low)
  always @(posedge clk) begin
    if (rst_n && !init_reset_n && init_cke) begin
      cke_violations <= cke_violations + 1;
    end
  end

  // Capture MRS commands
  always @(posedge clk) begin
    if (rst_n && init_cmd_valid && init_cmd == 4'b0000) begin
      mrs_banks[mrs_count] <= init_bank;
      mrs_addrs[mrs_count] <= init_addr;
      mrs_count <= mrs_count + 1;
    end
  end

  // Capture ZQCL commands
  always @(posedge clk) begin
    if (rst_n && init_cmd_valid && init_cmd == 4'b0110) begin
      zqcl_count <= zqcl_count + 1;
      if (init_addr[10] == 1'b1) begin
        zqcl_addr10_correct <= 1'b1;
      end
    end
  end

  // Main test sequence
  initial begin
    // Initialize
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);
    
    // Initialize signals and counters
    rst_n = 0;
    enable = 0;
    cycle_count = 0;
    reset_n_low_cycles = 0;
    cke_low_cycles = 0;
    cke_violations = 0;
    mrs_count = 0;
    zqcl_count = 0;
    zqcl_addr10_correct = 0;
    tests_passed = 0;
    tests_failed = 0;
    total_tests = 0;

    // Apply reset
    repeat(10) @(posedge clk);
    rst_n = 1;
    
    // Pulse enable
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

    // Wait a few more cycles to ensure all counters settle
    repeat(10) @(posedge clk);

    // Run checks
    $display("\n========== TEST RESULTS ==========\n");

    // Check 1: init_done asserted
    total_tests++;
    if (init_done) begin
      $display("[PASS] 1: init_done asserted");
      tests_passed++;
    end else begin
      $display("[FAIL] 1: init_done not asserted (init_done=%0b)", init_done);
      tests_failed++;
    end

    // Check 2: init_fail never asserts
    total_tests++;
    if (!init_fail) begin
      $display("[PASS] 2: init_fail never asserted");
      tests_passed++;
    end else begin
      $display("[FAIL] 2: init_fail asserted (init_fail=%0b)", init_fail);
      tests_failed++;
    end

    // Check 3: init_state reaches 4'd14
    total_tests++;
    if (init_state == 4'd14) begin
      $display("[PASS] 3: init_state reached 4'd14");
      tests_passed++;
    end else begin
      $display("[FAIL] 3: init_state did not reach 4'd14 (init_state=%0d)", init_state);
      tests_failed++;
    end

    // Check 4: RESET# low for >= 40000 cycles
    total_tests++;
    if (reset_n_low_cycles >= 40000) begin
      $display("[PASS] 4: RESET# low for >= 40000 cycles (actual=%0d)", reset_n_low_cycles);
      tests_passed++;
    end else begin
      $display("[FAIL] 4: RESET# low cycles insufficient (actual=%0d, required=40000)", reset_n_low_cycles);
      tests_failed++;
    end

    // Check 5: CKE low for >= 100000 cycles
    total_tests++;
    if (cke_low_cycles >= 100000) begin
      $display("[PASS] 5: CKE low for >= 100000 cycles (actual=%0d)", cke_low_cycles);
      tests_passed++;
    end else begin
      $display("[FAIL] 5: CKE low cycles insufficient (actual=%0d, required=100000)", cke_low_cycles);
      tests_failed++;
    end

    // Check 6: Exactly 4 MRS commands
    total_tests++;
    if (mrs_count == 4) begin
      $display("[PASS] 6: Exactly 4 MRS commands issued");
      tests_passed++;
    end else begin
      $display("[FAIL] 6: Wrong number of MRS commands (actual=%0d, expected=4)", mrs_count);
      tests_failed++;
    end

    // Check 7: MRS bank order is 2->3->1->0
    total_tests++;
    if (mrs_count == 4 && 
        mrs_banks[0] == 3'd2 && 
        mrs_banks[1] == 3'd3 && 
        mrs_banks[2] == 3'd1 && 
        mrs_banks[3] == 3'd0) begin
      $display("[PASS] 7: MRS bank order correct (2->3->1->0)");
      tests_passed++;
    end else begin
      if (mrs_count == 4) begin
        $display("[FAIL] 7: MRS bank order incorrect (actual=%0d->%0d->%0d->%0d, expected=2->3->1->0)", 
                 mrs_banks[0], mrs_banks[1], mrs_banks[2], mrs_banks[3]);
      end else begin
        $display("[FAIL] 7: Cannot check MRS order (insufficient MRS commands)");
      end
      tests_failed++;
    end

    // Check 8: MR address values
    total_tests++;
    if (mrs_count == 4 &&
        mrs_addrs[0] == 15'h0218 &&
        mrs_addrs[1] == 15'h0000 &&
        mrs_addrs[2] == 15'h0004 &&
        mrs_addrs[3] == 15'h1D34) begin
      $display("[PASS] 8: MR address values correct");
      tests_passed++;
    end else begin
      if (mrs_count == 4) begin
        $display("[FAIL] 8: MR address values incorrect");
        $display("         MR2: actual=0x%04h, expected=0x0218", mrs_addrs[0]);
        $display("         MR3: actual=0x%04h, expected=0x0000", mrs_addrs[1]);
        $display("         MR1: actual=0x%04h, expected=0x0004", mrs_addrs[2]);
        $display("         MR0: actual=0x%04h, expected=0x1D34", mrs_addrs[3]);
      end else begin
        $display("[FAIL] 8: Cannot check MR values (insufficient MRS commands)");
      end
      tests_failed++;
    end

    // Check 9: ZQCL command issued
    total_tests++;
    if (zqcl_count >= 1) begin
      $display("[PASS] 9: ZQCL command issued (count=%0d)", zqcl_count);
      tests_passed++;
    end else begin
      $display("[FAIL] 9: ZQCL command not issued (count=%0d)", zqcl_count);
      tests_failed++;
    end

    // Check 10: ZQCL addr[10] = 1
    total_tests++;
    if (zqcl_addr10_correct) begin
      $display("[PASS] 10: ZQCL addr[10] = 1");
      tests_passed++;
    end else begin
      $display("[FAIL] 10: ZQCL addr[10] not set correctly");
      tests_failed++;
    end

    // Check 11: CKE violations during RESET#
    total_tests++;
    if (cke_violations == 0) begin
      $display("[PASS] 11: No CKE violations during RESET# low");
      tests_passed++;
    end else begin
      $display("[FAIL] 11: CKE violations detected (count=%0d)", cke_violations);
      tests_failed++;
    end

    // Summary
    $display("\n========== SUMMARY ==========");
    if (tests_failed == 0) begin
      $display("ALL %0d TESTS PASSED", total_tests);
    end else begin
      $display("%0d of %0d TESTS FAILED", tests_failed, total_tests);
    end
    $display("=============================\n");

    $finish;
  end

  // Timeout watchdog
  initial begin
    repeat(TIMEOUT + 100) @(posedge clk);
    $display("\n[ERROR] Simulation timeout after %0d cycles", TIMEOUT);
    $finish;
  end

endmodule
