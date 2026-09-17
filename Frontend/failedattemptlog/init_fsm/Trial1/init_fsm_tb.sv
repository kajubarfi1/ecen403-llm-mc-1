`timescale 1ns/1ps

module init_fsm_tb;

  // Parameters
  parameter DDR_ADDR_W = 15;
  parameter DDR_BANK_W = 3;
  parameter CLK_PERIOD = 5.0; // 200 MHz
  parameter TIMEOUT_CYCLES = 150000; // 140362 + margin

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

  // Testbench variables
  int cycle_count;
  logic [DDR_BANK_W-1:0] mr_sequence[$];
  logic zqcl_issued;
  logic cke_stayed_low;
  int test_passed;
  int test_failed;

  // Instantiate DUT
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

  // Monitor MRS commands and capture sequence
  always @(posedge clk) begin
    if (init_cmd_valid && init_cmd == CMD_MRS) begin
      mr_sequence.push_back(init_bank);
      $display("Time %0t: MRS command to MR%0d (bank=%0d)", $time, init_bank, init_bank);
    end
    if (init_cmd_valid && init_cmd == CMD_ZQCL) begin
      zqcl_issued = 1;
      $display("Time %0t: ZQCL command issued", $time);
    end
  end

  // Check that CKE stays low during reset/cke-wait phases
  always @(posedge clk) begin
    if (!rst_n || !enable) begin
      if (init_cke !== 0) begin
        cke_stayed_low = 0;
      end
    end
  end

  // Main test stimulus
  initial begin
    // Initialize
    test_passed = 0;
    test_failed = 0;
    cycle_count = 0;
    zqcl_issued = 0;
    cke_stayed_low = 1;
    rst_n = 0;
    enable = 0;

    // Apply async reset
    #(CLK_PERIOD * 10);
    rst_n = 1;
    #(CLK_PERIOD * 5);

    // Pulse enable
    enable = 1;
    $display("Time %0t: Enable asserted", $time);

    // Wait for init_done or timeout
    fork
      begin
        wait(init_done);
        $display("Time %0t: init_done asserted at cycle %0d", $time, cycle_count);
      end
      begin
        repeat(TIMEOUT_CYCLES) @(posedge clk) cycle_count++;
        if (!init_done) begin
          $display("[FAIL] Timeout: init_done not asserted within %0d cycles", TIMEOUT_CYCLES);
          test_failed++;
        end
      end
    join_any
    disable fork;

    // Small delay to ensure all captures complete
    #(CLK_PERIOD * 10);

    // Check 1: init_done asserted
    if (init_done) begin
      $display("[PASS] init_done asserted");
      test_passed++;
    end else begin
      $display("[FAIL] init_done not asserted");
      test_failed++;
    end

    // Check 2: init_fail should not be asserted
    if (!init_fail) begin
      $display("[PASS] init_fail not asserted");
      test_passed++;
    end else begin
      $display("[FAIL] init_fail was asserted");
      test_failed++;
    end

    // Check 3: MR programming order MR2 -> MR3 -> MR1 -> MR0
    $display("Captured MR sequence (%0d entries):", mr_sequence.size());
    foreach(mr_sequence[i]) begin
      $display("  [%0d] MR%0d", i, mr_sequence[i]);
    end

    if (mr_sequence.size() >= 4) begin
      if (mr_sequence[0] == 2 && mr_sequence[1] == 3 && 
          mr_sequence[2] == 1 && mr_sequence[3] == 0) begin
        $display("[PASS] MR programming order correct: MR2->MR3->MR1->MR0");
        test_passed++;
      end else begin
        $display("[FAIL] MR programming order incorrect");
        $display("       Expected: MR2->MR3->MR1->MR0");
        $display("       Got: MR%0d->MR%0d->MR%0d->MR%0d", 
                 mr_sequence[0], mr_sequence[1], mr_sequence[2], mr_sequence[3]);
        test_failed++;
      end
    end else begin
      $display("[FAIL] Insufficient MRS commands captured (expected at least 4, got %0d)", 
               mr_sequence.size());
      test_failed++;
    end

    // Check 4: ZQCL issued
    if (zqcl_issued) begin
      $display("[PASS] ZQCL command issued");
      test_passed++;
    end else begin
      $display("[FAIL] ZQCL command not issued");
      test_failed++;
    end

    // Check 5: CKE stayed low during reset/cke-wait
    if (cke_stayed_low) begin
      $display("[PASS] init_cke stayed low during reset/cke-wait");
      test_passed++;
    end else begin
      $display("[FAIL] init_cke went high during reset/cke-wait");
      test_failed++;
    end

    // Summary
    $display("\n========================================");
    $display("Test Summary:");
    $display("  Passed: %0d", test_passed);
    $display("  Failed: %0d", test_failed);
    if (test_failed == 0) begin
      $display("[PASS] All tests passed!");
    end else begin
      $display("[FAIL] Some tests failed!");
    end
    $display("========================================\n");

    $finish;
  end

  // Watchdog timer
  initial begin
    #(CLK_PERIOD * TIMEOUT_CYCLES * 2);
    $display("[FAIL] Watchdog timeout - simulation ran too long");
    $finish;
  end

endmodule
