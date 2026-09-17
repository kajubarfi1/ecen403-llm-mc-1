module init_fsm_tb;

  localparam int DDR_ADDR_W = 15;
  localparam int DDR_BANK_W = 3;
  localparam int TIMEOUT = 145162;

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

  // Clock generation: 200 MHz -> 5.0 ns period
  initial clk = 0;
  always #2.5 clk = ~clk;

  // Counters and tracking variables
  int cycle_count;
  int reset_n_low_count;
  int cke_low_count;
  int cke_violations;
  int mrs_count;
  logic [2:0] mrs_banks [4];
  logic [14:0] mrs_addrs [4];
  int zqcl_count;
  logic zqcl_addr10_correct;
  logic done_seen;
  logic fail_seen;
  logic state_14_seen;

  // Sample signals and count on posedge clk
  always @(posedge clk) begin
    if (rst_n) begin
      cycle_count <= cycle_count + 1;

      // Count RESET# low cycles
      if (!init_reset_n) begin
        reset_n_low_count <= reset_n_low_count + 1;
      end

      // Count CKE low cycles (total, we'll use this for the CKE-delay phase)
      if (!init_cke) begin
        cke_low_count <= cke_low_count + 1;
      end

      // Count CKE violations (CKE high while RESET# low)
      if (!init_reset_n && init_cke) begin
        cke_violations <= cke_violations + 1;
      end

      // Detect MRS commands
      if (init_cmd_valid && init_cmd == 4'b0000) begin
        mrs_banks[mrs_count] = init_bank;
        mrs_addrs[mrs_count] = init_addr;
        mrs_count <= mrs_count + 1;
      end

      // Detect ZQCL commands
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

      // Timeout
      if (cycle_count >= TIMEOUT) begin
        run_checks();
        $finish;
      end

      // End when done
      if (init_done && cycle_count > 10) begin
        // Give a few more cycles to ensure stable
        repeat(10) @(posedge clk);
        run_checks();
        $finish;
      end
    end else begin
      cycle_count <= 0;
      reset_n_low_count <= 0;
      cke_low_count <= 0;
      cke_violations <= 0;
      mrs_count <= 0;
      zqcl_count <= 0;
      zqcl_addr10_correct <= 1'b0;
      done_seen <= 1'b0;
      fail_seen <= 1'b0;
      state_14_seen <= 1'b0;
    end
  end

  // Test execution
  initial begin
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);

    // Reset sequence
    rst_n = 0;
    enable = 0;
    repeat(10) @(posedge clk);
    rst_n = 1;
    @(posedge clk);

    // Pulse enable
    enable = 1;
    @(posedge clk);
    enable = 0;

    // Wait for completion or timeout (handled in always block)
  end

  task run_checks();
    int pass_count = 0;
    int fail_count = 0;
    int total_tests = 11;

    $display("\n========== TEST RESULTS ==========");

    // Check 1: init_done asserts
    if (done_seen) begin
      $display("[PASS] 1: init_done asserted");
      pass_count++;
    end else begin
      $display("[FAIL] 1: init_done never asserted");
      fail_count++;
    end

    // Check 2: init_fail never asserts
    if (!fail_seen) begin
      $display("[PASS] 2: init_fail never asserted");
      pass_count++;
    end else begin
      $display("[FAIL] 2: init_fail asserted");
      fail_count++;
    end

    // Check 3: init_state reaches 14
    if (state_14_seen) begin
      $display("[PASS] 3: init_state reached 4'd14");
      pass_count++;
    end else begin
      $display("[FAIL] 3: init_state never reached 4'd14");
      fail_count++;
    end

    // Check 4: RESET# low for >= 40000 cycles
    if (reset_n_low_count >= 40000) begin
      $display("[PASS] 4: RESET# low for %0d cycles (>= 40000)", reset_n_low_count);
      pass_count++;
    end else begin
      $display("[FAIL] 4: RESET# low for %0d cycles (expected >= 40000)", reset_n_low_count);
      fail_count++;
    end

    // Check 5: CKE low for >= 100000 cycles during CKE-delay phase
    if (cke_low_count >= 100000) begin
      $display("[PASS] 5: CKE low for %0d cycles (>= 100000)", cke_low_count);
      pass_count++;
    end else begin
      $display("[FAIL] 5: CKE low for %0d cycles (expected >= 100000)", cke_low_count);
      fail_count++;
    end

    // Check 6: Exactly 4 MRS commands
    if (mrs_count == 4) begin
      $display("[PASS] 6: Exactly 4 MRS commands issued");
      pass_count++;
    end else begin
      $display("[FAIL] 6: %0d MRS commands issued (expected 4)", mrs_count);
      fail_count++;
    end

    // Check 7: MRS bank order is 2, 3, 1, 0
    if (mrs_count == 4 && 
        mrs_banks[0] == 3'd2 && 
        mrs_banks[1] == 3'd3 && 
        mrs_banks[2] == 3'd1 && 
        mrs_banks[3] == 3'd0) begin
      $display("[PASS] 7: MRS bank order correct (2->3->1->0)");
      pass_count++;
    end else begin
      if (mrs_count == 4) begin
        $display("[FAIL] 7: MRS bank order %0d->%0d->%0d->%0d (expected 2->3->1->0)", 
                 mrs_banks[0], mrs_banks[1], mrs_banks[2], mrs_banks[3]);
      end else begin
        $display("[FAIL] 7: Cannot check MRS order (only %0d MRS commands)", mrs_count);
      end
      fail_count++;
    end

    // Check 8: MRS address values
    if (mrs_count == 4 &&
        mrs_addrs[0] == 15'h0218 &&
        mrs_addrs[1] == 15'h0000 &&
        mrs_addrs[2] == 15'h0004 &&
        mrs_addrs[3] == 15'h1D34) begin
      $display("[PASS] 8: MRS address values correct");
      pass_count++;
    end else begin
      if (mrs_count == 4) begin
        $display("[FAIL] 8: MRS addresses MR2=0x%04h MR3=0x%04h MR1=0x%04h MR0=0x%04h (expected 0x0218,0x0000,0x0004,0x1D34)",
                 mrs_addrs[0], mrs_addrs[1], mrs_addrs[2], mrs_addrs[3]);
      end else begin
        $display("[FAIL] 8: Cannot check MRS addresses (only %0d MRS commands)", mrs_count);
      end
      fail_count++;
    end

    // Check 9: ZQCL command issued
    if (zqcl_count >= 1) begin
      $display("[PASS] 9: ZQCL command issued (%0d times)", zqcl_count);
      pass_count++;
    end else begin
      $display("[FAIL] 9: ZQCL command never issued");
      fail_count++;
    end

    // Check 10: ZQCL addr[10] = 1
    if (zqcl_addr10_correct) begin
      $display("[PASS] 10: ZQCL addr[10] = 1");
      pass_count++;
    end else begin
      $display("[FAIL] 10: ZQCL addr[10] != 1");
      fail_count++;
    end

    // Check 11: CKE violations during RESET# low
    if (cke_violations == 0) begin
      $display("[PASS] 11: No CKE violations during RESET# low");
      pass_count++;
    end else begin
      $display("[FAIL] 11: %0d CKE violations (CKE=1 while RESET#=0)", cke_violations);
      fail_count++;
    end

    $display("==================================");
    if (fail_count == 0) begin
      $display("ALL %0d TESTS PASSED", total_tests);
    end else begin
      $display("%0d of %0d TESTS FAILED", fail_count, total_tests);
    end
    $display("==================================\n");
  endtask

endmodule
