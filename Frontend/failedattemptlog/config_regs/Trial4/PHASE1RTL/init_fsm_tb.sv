module init_fsm_tb;

  // Parameters
  localparam int DDR_ADDR_W = 15;
  localparam int DDR_BANK_W = 3;
  localparam int TIMEOUT = 145162;

  // Clock and reset
  logic clk;
  logic rst_n;

  // DUT signals
  logic enable;
  logic init_done;
  logic init_fail;
  logic init_cmd_valid;
  logic [3:0] init_cmd;
  logic [DDR_ADDR_W-1:0] init_addr;
  logic [DDR_BANK_W-1:0] init_bank;
  logic init_cke;
  logic init_reset_n;
  logic [3:0] init_state;

  // DUT instance
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

  // Clock generation: 200 MHz (5.0 ns period)
  initial clk = 0;
  always #2.5 clk = ~clk;

  // Counters and tracking variables
  int cycle_count;
  int reset_n_low_cycles;
  int cke_low_cycles;
  int cke_violations;
  int mrs_count;
  logic [2:0] mrs_banks[4];
  logic [DDR_ADDR_W-1:0] mrs_addrs[4];
  int zqcl_count;
  logic zqcl_addr10_correct;
  logic done_seen;
  logic fail_seen;
  logic state_14_seen;

  // Sample and count on every posedge
  always @(posedge clk) begin
    if (rst_n) begin
      // Count cycles where init_reset_n is low
      if (!init_reset_n) begin
        reset_n_low_cycles <= reset_n_low_cycles + 1;
      end

      // Count cycles where init_cke is low (after reset_n is high)
      if (init_reset_n && !init_cke) begin
        cke_low_cycles <= cke_low_cycles + 1;
      end

      // Count CKE violations (CKE high while RESET# is low)
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
        if (init_addr[10] == 1'b1) begin
          zqcl_addr10_correct <= 1'b1;
        end
      end

      // Track init_done
      if (init_done) begin
        done_seen <= 1'b1;
      end

      // Track init_fail
      if (init_fail) begin
        fail_seen <= 1'b1;
      end

      // Track state 14
      if (init_state == 4'd14) begin
        state_14_seen <= 1'b1;
      end

      cycle_count <= cycle_count + 1;
    end
  end

  // Main test sequence
  initial begin
    // Initialize VCD dump
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);

    // Initialize signals
    rst_n = 0;
    enable = 0;
    cycle_count = 0;
    reset_n_low_cycles = 0;
    cke_low_cycles = 0;
    cke_violations = 0;
    mrs_count = 0;
    zqcl_count = 0;
    zqcl_addr10_correct = 0;
    done_seen = 0;
    fail_seen = 0;
    state_14_seen = 0;

    // Apply reset for 10 cycles
    repeat(10) @(posedge clk);
    rst_n = 1;

    // Wait a few cycles, then pulse enable
    repeat(5) @(posedge clk);
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

    // Give a few more cycles to ensure all counters are updated
    repeat(10) @(posedge clk);

    // Run checks
    run_checks();

    $finish;
  end

  // Check results
  task run_checks();
    int pass_count = 0;
    int fail_count = 0;
    int total_tests = 11;

    $display("\n=== Test Results ===\n");

    // Check 1: init_done asserted
    if (done_seen) begin
      $display("[PASS] 1: init_done asserted");
      pass_count++;
    end else begin
      $display("[FAIL] 1: init_done never asserted");
      fail_count++;
    end

    // Check 2: init_fail never asserted
    if (!fail_seen) begin
      $display("[PASS] 2: init_fail never asserted");
      pass_count++;
    end else begin
      $display("[FAIL] 2: init_fail was asserted");
      fail_count++;
    end

    // Check 3: init_state reached 4'd14
    if (state_14_seen) begin
      $display("[PASS] 3: init_state reached 4'd14 (S_DONE)");
      pass_count++;
    end else begin
      $display("[FAIL] 3: init_state never reached 4'd14 (final state = %d)", init_state);
      fail_count++;
    end

    // Check 4: RESET# low for >= 40000 cycles
    if (reset_n_low_cycles >= 40000) begin
      $display("[PASS] 4: RESET# low for >= 40000 cycles (measured: %0d)", reset_n_low_cycles);
      pass_count++;
    end else begin
      $display("[FAIL] 4: RESET# low for < 40000 cycles (measured: %0d)", reset_n_low_cycles);
      fail_count++;
    end

    // Check 5: CKE low for >= 100000 cycles during CKE-delay phase
    if (cke_low_cycles >= 100000) begin
      $display("[PASS] 5: CKE low for >= 100000 cycles (measured: %0d)", cke_low_cycles);
      pass_count++;
    end else begin
      $display("[FAIL] 5: CKE low for < 100000 cycles (measured: %0d)", cke_low_cycles);
      fail_count++;
    end

    // Check 6: Exactly 4 MRS commands
    if (mrs_count == 4) begin
      $display("[PASS] 6: Exactly 4 MRS commands issued");
      pass_count++;
    end else begin
      $display("[FAIL] 6: Expected 4 MRS commands, got %0d", mrs_count);
      fail_count++;
    end

    // Check 7: MR program order (bank 2 -> 3 -> 1 -> 0)
    if (mrs_count == 4 && 
        mrs_banks[0] == 3'd2 && 
        mrs_banks[1] == 3'd3 && 
        mrs_banks[2] == 3'd1 && 
        mrs_banks[3] == 3'd0) begin
      $display("[PASS] 7: MR program order correct (2->3->1->0)");
      pass_count++;
    end else begin
      if (mrs_count == 4) begin
        $display("[FAIL] 7: MR program order incorrect (got %0d->%0d->%0d->%0d)", 
                 mrs_banks[0], mrs_banks[1], mrs_banks[2], mrs_banks[3]);
      end else begin
        $display("[FAIL] 7: MR program order check skipped (insufficient MRS commands)");
      end
      fail_count++;
    end

    // Check 8: MR address values
    if (mrs_count == 4 && 
        mrs_addrs[0] == 15'h0218 && 
        mrs_addrs[1] == 15'h0000 && 
        mrs_addrs[2] == 15'h0004 && 
        mrs_addrs[3] == 15'h1D34) begin
      $display("[PASS] 8: MR address values correct (MR2=0x0218, MR3=0x0000, MR1=0x0004, MR0=0x1D34)");
      pass_count++;
    end else begin
      if (mrs_count == 4) begin
        $display("[FAIL] 8: MR address values incorrect");
        $display("       MR2: expected 0x0218, got 0x%04x", mrs_addrs[0]);
        $display("       MR3: expected 0x0000, got 0x%04x", mrs_addrs[1]);
        $display("       MR1: expected 0x0004, got 0x%04x", mrs_addrs[2]);
        $display("       MR0: expected 0x1D34, got 0x%04x", mrs_addrs[3]);
      end else begin
        $display("[FAIL] 8: MR address check skipped (insufficient MRS commands)");
      end
      fail_count++;
    end

    // Check 9: ZQCL command issued
    if (zqcl_count >= 1) begin
      $display("[PASS] 9: ZQCL command (4'b0110) issued (count: %0d)", zqcl_count);
      pass_count++;
    end else begin
      $display("[FAIL] 9: ZQCL command never issued");
      fail_count++;
    end

    // Check 10: ZQCL addr[10] = 1
    if (zqcl_addr10_correct) begin
      $display("[PASS] 10: ZQCL has init_addr[10] = 1");
      pass_count++;
    end else begin
      $display("[FAIL] 10: ZQCL init_addr[10] was not 1");
      fail_count++;
    end

    // Check 11: CKE violations during reset
    if (cke_violations == 0) begin
      $display("[PASS] 11: No CKE violations during RESET# low phase");
      pass_count++;
    end else begin
      $display("[FAIL] 11: CKE violations during RESET# low phase (count: %0d)", cke_violations);
      fail_count++;
    end

    // Summary
    $display("\n===================");
    if (fail_count == 0) begin
      $display("ALL %0d TESTS PASSED", total_tests);
    end else begin
      $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
    end
    $display("===================\n");
  endtask

endmodule
