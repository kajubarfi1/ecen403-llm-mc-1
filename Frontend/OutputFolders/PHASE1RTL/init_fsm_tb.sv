module init_fsm_tb;

  // Parameters
  localparam int DDR_ADDR_W = 15;
  localparam int DDR_BANK_W = 3;
  localparam int CLK_PERIOD = 5; // ns (200 MHz)
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

  // Testbench variables
  int cycle_count;
  int reset_n_low_count;
  int cke_low_count;
  int cke_violations;
  int mrs_count;
  logic [2:0] mrs_banks[4];
  logic [DDR_ADDR_W-1:0] mrs_addrs[4];
  int zqcl_count;
  logic zqcl_addr10_high;
  logic done_seen;
  logic fail_seen;
  logic state_14_seen;

  int pass_count;
  int fail_count;
  int test_num;

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

  // Sampling and counting (RULE 1 & 2)
  always @(posedge clk) begin
    if (rst_n) begin
      cycle_count <= cycle_count + 1;
      
      // Count RESET# low cycles
      if (!init_reset_n) begin
        reset_n_low_count <= reset_n_low_count + 1;
      end
      
      // Count CKE low cycles (during CKE-delay phase: reset_n high, CKE low)
      if (init_reset_n && !init_cke) begin
        cke_low_count <= cke_low_count + 1;
      end
      
      // Count CKE violations (RULE 4)
      if (!init_reset_n && init_cke) begin
        cke_violations <= cke_violations + 1;
      end
      
      // Capture MRS commands
      if (init_cmd_valid && init_cmd == 4'b0000) begin
        mrs_banks[mrs_count] = init_bank;
        mrs_addrs[mrs_count] = init_addr;
        mrs_count <= mrs_count + 1;
      end
      
      // Capture ZQCL commands
      if (init_cmd_valid && init_cmd == 4'b0110) begin
        zqcl_count <= zqcl_count + 1;
        if (init_addr[10]) begin
          zqcl_addr10_high <= 1'b1;
        end
      end
      
      // Monitor done, fail, and state
      if (init_done) begin
        done_seen <= 1'b1;
      end
      
      if (init_fail) begin
        fail_seen <= 1'b1;
      end
      
      if (init_state == 4'd14) begin
        state_14_seen <= 1'b1;
      end
    end
  end

  // Main test sequence
  initial begin
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);

    // Initialize
    rst_n = 0;
    enable = 0;
    cycle_count = 0;
    reset_n_low_count = 0;
    cke_low_count = 0;
    cke_violations = 0;
    mrs_count = 0;
    zqcl_count = 0;
    zqcl_addr10_high = 0;
    done_seen = 0;
    fail_seen = 0;
    state_14_seen = 0;
    pass_count = 0;
    fail_count = 0;
    test_num = 0;

    // Apply reset for 10 cycles
    repeat(10) @(posedge clk);
    rst_n = 1;
    
    // Pulse enable
    @(posedge clk);
    enable = 1;
    @(posedge clk);
    enable = 0;

    // Wait for completion or timeout
    fork
      begin
        wait(init_done);
      end
      begin
        repeat(TIMEOUT) @(posedge clk);
      end
    join_any

    // Give a few more cycles for final checks
    repeat(10) @(posedge clk);

    // Run all checks
    $display("\n=== Test Results ===\n");

    // Test 1: init_done asserts
    test_num++;
    if (done_seen) begin
      $display("[PASS] %0d: init_done asserted", test_num);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: init_done never asserted", test_num);
      fail_count++;
    end

    // Test 2: init_fail never asserts
    test_num++;
    if (!fail_seen) begin
      $display("[PASS] %0d: init_fail never asserted", test_num);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: init_fail asserted", test_num);
      fail_count++;
    end

    // Test 3: init_state reaches 4'd14
    test_num++;
    if (state_14_seen) begin
      $display("[PASS] %0d: init_state reached 4'd14 (S_DONE)", test_num);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: init_state never reached 4'd14 (final state=%0d)", test_num, init_state);
      fail_count++;
    end

    // Test 4: RESET# low for >= 40000 cycles
    test_num++;
    if (reset_n_low_count >= 40000) begin
      $display("[PASS] %0d: RESET# low for %0d cycles (>= 40000)", test_num, reset_n_low_count);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: RESET# low for %0d cycles (expected >= 40000)", test_num, reset_n_low_count);
      fail_count++;
    end

    // Test 5: CKE low for >= 100000 cycles during CKE-delay phase
    test_num++;
    if (cke_low_count >= 100000) begin
      $display("[PASS] %0d: CKE low for %0d cycles (>= 100000)", test_num, cke_low_count);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: CKE low for %0d cycles (expected >= 100000)", test_num, cke_low_count);
      fail_count++;
    end

    // Test 6: Exactly 4 MRS commands
    test_num++;
    if (mrs_count == 4) begin
      $display("[PASS] %0d: Exactly 4 MRS commands issued", test_num);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: %0d MRS commands issued (expected 4)", test_num, mrs_count);
      fail_count++;
    end

    // Test 7: MR program order is bank 2 -> 3 -> 1 -> 0
    test_num++;
    if (mrs_count == 4 && 
        mrs_banks[0] == 3'd2 && 
        mrs_banks[1] == 3'd3 && 
        mrs_banks[2] == 3'd1 && 
        mrs_banks[3] == 3'd0) begin
      $display("[PASS] %0d: MRS bank order is 2->3->1->0", test_num);
      pass_count++;
    end else begin
      if (mrs_count >= 1) begin
        $display("[FAIL] %0d: MRS bank order incorrect (got %0d->%0d->%0d->%0d, expected 2->3->1->0)", 
                 test_num, 
                 mrs_count >= 1 ? mrs_banks[0] : 0,
                 mrs_count >= 2 ? mrs_banks[1] : 0,
                 mrs_count >= 3 ? mrs_banks[2] : 0,
                 mrs_count >= 4 ? mrs_banks[3] : 0);
      end else begin
        $display("[FAIL] %0d: MRS bank order incorrect (insufficient MRS commands)", test_num);
      end
      fail_count++;
    end

    // Test 8: MR address values match
    test_num++;
    if (mrs_count == 4 &&
        mrs_addrs[0] == 15'h0218 &&
        mrs_addrs[1] == 15'h0000 &&
        mrs_addrs[2] == 15'h0004 &&
        mrs_addrs[3] == 15'h1D34) begin
      $display("[PASS] %0d: MR address values correct", test_num);
      pass_count++;
    end else begin
      if (mrs_count >= 1) begin
        $display("[FAIL] %0d: MR address values incorrect", test_num);
        $display("       MR2 (bank 2): got 0x%04h, expected 0x0218", mrs_addrs[0]);
        $display("       MR3 (bank 3): got 0x%04h, expected 0x0000", mrs_addrs[1]);
        $display("       MR1 (bank 1): got 0x%04h, expected 0x0004", mrs_addrs[2]);
        $display("       MR0 (bank 0): got 0x%04h, expected 0x1D34", mrs_addrs[3]);
      end else begin
        $display("[FAIL] %0d: MR address values incorrect (insufficient MRS commands)", test_num);
      end
      fail_count++;
    end

    // Test 9: ZQCL command issued at least once
    test_num++;
    if (zqcl_count >= 1) begin
      $display("[PASS] %0d: ZQCL command (4'b0110) issued %0d time(s)", test_num, zqcl_count);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: ZQCL command never issued", test_num);
      fail_count++;
    end

    // Test 10: ZQCL has init_addr[10] === 1'b1
    test_num++;
    if (zqcl_addr10_high) begin
      $display("[PASS] %0d: ZQCL init_addr[10] === 1'b1", test_num);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: ZQCL init_addr[10] not high", test_num);
      fail_count++;
    end

    // Test 11: CKE violations == 0
    test_num++;
    if (cke_violations == 0) begin
      $display("[PASS] %0d: No CKE violations during RESET# low", test_num);
      pass_count++;
    end else begin
      $display("[FAIL] %0d: %0d CKE violations (CKE=1 while RESET#=0)", test_num, cke_violations);
      fail_count++;
    end

    // Summary
    $display("\n=== Summary ===");
    if (fail_count == 0) begin
      $display("ALL %0d TESTS PASSED\n", test_num);
    end else begin
      $display("%0d of %0d TESTS FAILED\n", fail_count, test_num);
    end

    $finish;
  end

  // Timeout watchdog
  initial begin
    repeat(TIMEOUT + 100) @(posedge clk);
    $display("\n[TIMEOUT] Simulation exceeded %0d cycles", TIMEOUT + 100);
    $finish;
  end

endmodule
