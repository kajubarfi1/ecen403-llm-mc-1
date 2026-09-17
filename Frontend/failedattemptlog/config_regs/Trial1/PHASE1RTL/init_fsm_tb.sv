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

  // Testbench counters
  int reset_n_low_count;
  int cke_low_count;
  int cke_violations;
  int mrs_count;
  int zqcl_count;
  int cycle_count;
  
  // MRS tracking
  logic [2:0] mrs_banks[4];
  logic [14:0] mrs_addrs[4];
  int mrs_idx;
  
  // Test results
  int pass_count;
  int fail_count;
  
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

  // Waveform dump
  initial begin
    $dumpfile("init_fsm_tb.vcd");
    $dumpvars(0, init_fsm_tb);
  end

  // Counter for RESET# low cycles
  always @(posedge clk) begin
    if (rst_n) begin
      if (!init_reset_n) begin
        reset_n_low_count <= reset_n_low_count + 1;
      end
    end
  end

  // Counter for CKE low cycles (after RESET# is released)
  always @(posedge clk) begin
    if (rst_n) begin
      if (init_reset_n && !init_cke) begin
        cke_low_count <= cke_low_count + 1;
      end
    end
  end

  // CKE violation counter (CKE high while RESET# low)
  always @(posedge clk) begin
    if (rst_n && !init_reset_n && init_cke) begin
      cke_violations <= cke_violations + 1;
    end
  end

  // MRS and ZQCL command capture
  always @(posedge clk) begin
    if (rst_n && init_cmd_valid) begin
      if (init_cmd == 4'b0000) begin
        // MRS command
        mrs_banks[mrs_idx] = init_bank;
        mrs_addrs[mrs_idx] = init_addr;
        mrs_idx <= mrs_idx + 1;
        mrs_count <= mrs_count + 1;
      end else if (init_cmd == 4'b0110) begin
        // ZQCL command
        zqcl_count <= zqcl_count + 1;
      end
    end
  end

  // Cycle counter and timeout
  always @(posedge clk) begin
    if (rst_n) begin
      cycle_count <= cycle_count + 1;
      if (cycle_count >= TIMEOUT) begin
        $display("[TIMEOUT] Simulation exceeded %0d cycles", TIMEOUT);
        run_checks();
        $finish;
      end
    end
  end

  // Monitor for init_done
  always @(posedge clk) begin
    if (rst_n && init_done) begin
      // Give a few cycles for final state settling
      repeat(10) @(posedge clk);
      run_checks();
      $finish;
    end
  end

  // Main stimulus
  initial begin
    // Initialize
    rst_n = 0;
    enable = 0;
    reset_n_low_count = 0;
    cke_low_count = 0;
    cke_violations = 0;
    mrs_count = 0;
    zqcl_count = 0;
    mrs_idx = 0;
    cycle_count = 0;
    pass_count = 0;
    fail_count = 0;

    // Apply reset for 10 cycles
    repeat(10) @(posedge clk);
    rst_n = 1;
    
    // Wait a few cycles then pulse enable
    repeat(5) @(posedge clk);
    enable = 1;
    @(posedge clk);
    enable = 0;

    // Wait for completion or timeout (handled by always blocks above)
  end

  // Self-checking task
  task run_checks();
    $display("\n========================================");
    $display("Running Self-Checks");
    $display("========================================");

    // Check 1: init_done asserted
    if (init_done) begin
      $display("[PASS] 1: init_done asserted (value=%0b)", init_done);
      pass_count++;
    end else begin
      $display("[FAIL] 1: init_done not asserted (value=%0b)", init_done);
      fail_count++;
    end

    // Check 2: init_fail never asserts
    if (!init_fail) begin
      $display("[PASS] 2: init_fail never asserted (value=%0b)", init_fail);
      pass_count++;
    end else begin
      $display("[FAIL] 2: init_fail asserted (value=%0b)", init_fail);
      fail_count++;
    end

    // Check 3: init_state reaches 4'd14 (S_DONE)
    if (init_state == 4'd14) begin
      $display("[PASS] 3: init_state reached S_DONE (value=%0d)", init_state);
      pass_count++;
    end else begin
      $display("[FAIL] 3: init_state did not reach S_DONE (value=%0d, expected=14)", init_state);
      fail_count++;
    end

    // Check 4: RESET# low for >= 40000 cycles
    if (reset_n_low_count >= 40000) begin
      $display("[PASS] 4: RESET# low cycles (count=%0d, required>=40000)", reset_n_low_count);
      pass_count++;
    end else begin
      $display("[FAIL] 4: RESET# low cycles insufficient (count=%0d, required>=40000)", reset_n_low_count);
      fail_count++;
    end

    // Check 5: CKE low for >= 100000 cycles during CKE-delay phase
    if (cke_low_count >= 100000) begin
      $display("[PASS] 5: CKE low cycles during delay phase (count=%0d, required>=100000)", cke_low_count);
      pass_count++;
    end else begin
      $display("[FAIL] 5: CKE low cycles insufficient (count=%0d, required>=100000)", cke_low_count);
      fail_count++;
    end

    // Check 6: Exactly 4 MRS commands issued
    if (mrs_count == 4) begin
      $display("[PASS] 6: Exactly 4 MRS commands issued (count=%0d)", mrs_count);
      pass_count++;
    end else begin
      $display("[FAIL] 6: MRS command count incorrect (count=%0d, expected=4)", mrs_count);
      fail_count++;
    end

    // Check 7: MR program order is bank 2 -> 3 -> 1 -> 0
    if (mrs_count >= 4 && 
        mrs_banks[0] == 3'd2 && 
        mrs_banks[1] == 3'd3 && 
        mrs_banks[2] == 3'd1 && 
        mrs_banks[3] == 3'd0) begin
      $display("[PASS] 7: MRS bank order correct (2->3->1->0)");
      pass_count++;
    end else begin
      if (mrs_count >= 4) begin
        $display("[FAIL] 7: MRS bank order incorrect (got %0d->%0d->%0d->%0d, expected 2->3->1->0)", 
                 mrs_banks[0], mrs_banks[1], mrs_banks[2], mrs_banks[3]);
      end else begin
        $display("[FAIL] 7: MRS bank order check skipped (insufficient MRS count=%0d)", mrs_count);
      end
      fail_count++;
    end

    // Check 8: MR address values match
    if (mrs_count >= 4 &&
        mrs_addrs[0] == 15'h0218 &&
        mrs_addrs[1] == 15'h0000 &&
        mrs_addrs[2] == 15'h0004 &&
        mrs_addrs[3] == 15'h1D34) begin
      $display("[PASS] 8: MR address values correct (MR2=0x0218, MR3=0x0000, MR1=0x0004, MR0=0x1D34)");
      pass_count++;
    end else begin
      if (mrs_count >= 4) begin
        $display("[FAIL] 8: MR address values incorrect");
        $display("         MR2: got=0x%04h, expected=0x0218", mrs_addrs[0]);
        $display("         MR3: got=0x%04h, expected=0x0000", mrs_addrs[1]);
        $display("         MR1: got=0x%04h, expected=0x0004", mrs_addrs[2]);
        $display("         MR0: got=0x%04h, expected=0x1D34", mrs_addrs[3]);
      end else begin
        $display("[FAIL] 8: MR address check skipped (insufficient MRS count=%0d)", mrs_count);
      end
      fail_count++;
    end

    // Check 9: ZQCL command (4'b0110) issued at least once
    if (zqcl_count >= 1) begin
      $display("[PASS] 9: ZQCL command issued (count=%0d)", zqcl_count);
      pass_count++;
    end else begin
      $display("[FAIL] 9: ZQCL command not issued (count=%0d)", zqcl_count);
      fail_count++;
    end

    // Check 10: ZQCL has init_addr[10] === 1'b1
    // We need to capture this during the ZQCL command
    // Adding a separate tracker for this
    // For now, we'll check if we saw it (implementation below will track it)
    if (zqcl_addr10_check) begin
      $display("[PASS] 10: ZQCL init_addr[10] = 1");
      pass_count++;
    end else begin
      $display("[FAIL] 10: ZQCL init_addr[10] not set to 1");
      fail_count++;
    end

    // Check 11: CKE-during-reset violation count == 0
    if (cke_violations == 0) begin
      $display("[PASS] 11: No CKE violations during RESET# low (count=%0d)", cke_violations);
      pass_count++;
    end else begin
      $display("[FAIL] 11: CKE violations detected during RESET# low (count=%0d)", cke_violations);
      fail_count++;
    end

    // Summary
    $display("\n========================================");
    if (fail_count == 0) begin
      $display("ALL %0d TESTS PASSED", pass_count);
    end else begin
      $display("%0d of %0d TESTS FAILED", fail_count, pass_count + fail_count);
    end
    $display("========================================\n");
  endtask

  // Track ZQCL addr[10] bit
  logic zqcl_addr10_check;
  initial zqcl_addr10_check = 0;
  
  always @(posedge clk) begin
    if (rst_n && init_cmd_valid && init_cmd == 4'b0110) begin
      if (init_addr[10] == 1'b1) begin
        zqcl_addr10_check <= 1;
      end
    end
  end

endmodule
