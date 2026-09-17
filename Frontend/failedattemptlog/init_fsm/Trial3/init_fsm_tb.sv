`timescale 1ns/1ps

module init_fsm_tb;

  // Parameters
  localparam DDR_ADDR_W = 15;
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
  localparam [3:0] CMD_DESELECT = 4'b1111;
  localparam [3:0] CMD_NOP      = 4'b0111;
  localparam [3:0] CMD_MRS      = 4'b0000;
  localparam [3:0] CMD_ZQCL     = 4'b0110;
  localparam [3:0] CMD_PRECHARGE = 4'b0010;
  
  // MR bank addresses
  localparam [2:0] MR0 = 3'b000;
  localparam [2:0] MR1 = 3'b001;
  localparam [2:0] MR2 = 3'b010;
  localparam [2:0] MR3 = 3'b011;

  // Test tracking variables
  logic [2:0] mr_sequence[$];
  logic zqcl_issued;
  logic cke_error;
  int cycle_count;
  logic test_pass;

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

  // Monitor MRS commands to check sequence
  always @(posedge clk) begin
    if (init_cmd_valid && init_cmd == CMD_MRS) begin
      mr_sequence.push_back(init_bank);
      $display("Time %0t: MRS command to MR%0d", $time, init_bank);
    end
    if (init_cmd_valid && init_cmd == CMD_ZQCL) begin
      zqcl_issued = 1;
      $display("Time %0t: ZQCL command issued", $time);
    end
  end

  // Check CKE behavior during reset/initialization
  always @(posedge clk) begin
    if (!rst_n || init_state < 4) begin // Early states should have CKE low
      if (init_cke !== 1'b0) begin
        cke_error = 1;
        $display("Time %0t: [ERROR] CKE should be low during reset/wait states", $time);
      end
    end
  end

  // Main test sequence
  initial begin
    // Initialize
    rst_n = 0;
    enable = 0;
    zqcl_issued = 0;
    cke_error = 0;
    cycle_count = 0;
    test_pass = 1;
    
    $display("========================================");
    $display("Starting init_fsm testbench");
    $display("Clock period: %0.1f ns (200 MHz)", CLK_PERIOD);
    $display("========================================");

    // Apply reset
    repeat(10) @(posedge clk);
    rst_n = 1;
    $display("Time %0t: Reset deasserted", $time);
    
    // Wait a few cycles then pulse enable
    repeat(5) @(posedge clk);
    enable = 1;
    $display("Time %0t: Enable asserted", $time);
    @(posedge clk);
    enable = 0;

    // Wait for init_done with timeout
    fork
      begin
        wait(init_done);
        $display("Time %0t: init_done asserted after %0d cycles", $time, cycle_count);
      end
      begin
        repeat(TIMEOUT_CYCLES) @(posedge clk) cycle_count++;
        if (!init_done) begin
          $display("Time %0t: [ERROR] Timeout waiting for init_done", $time);
          test_pass = 0;
        end
      end
    join_any
    disable fork;

    // Give a few more cycles for any final commands
    repeat(10) @(posedge clk);

    // Check results
    $display("\n========================================");
    $display("Test Results:");
    $display("========================================");

    // Check init_done
    if (init_done) begin
      $display("[PASS] init_done asserted within timeout");
    end else begin
      $display("[FAIL] init_done did not assert within %0d cycles", TIMEOUT_CYCLES);
      test_pass = 0;
    end

    // Check init_fail
    if (init_fail) begin
      $display("[FAIL] init_fail asserted unexpectedly");
      test_pass = 0;
    end else begin
      $display("[PASS] init_fail remained low");
    end

    // Check MR sequence: MR2 -> MR3 -> MR1 -> MR0
    $display("\nMRS Command Sequence:");
    foreach(mr_sequence[i]) begin
      $display("  %0d: MR%0d", i, mr_sequence[i]);
    end
    
    if (mr_sequence.size() >= 4) begin
      if (mr_sequence[0] == MR2 && 
          mr_sequence[1] == MR3 && 
          mr_sequence[2] == MR1 && 
          mr_sequence[3] == MR0) begin
        $display("[PASS] MR programming order correct: MR2 -> MR3 -> MR1 -> MR0");
      end else begin
        $display("[FAIL] MR programming order incorrect");
        $display("       Expected: MR2 -> MR3 -> MR1 -> MR0");
        $display("       Got:      MR%0d -> MR%0d -> MR%0d -> MR%0d", 
                 mr_sequence[0], mr_sequence[1], mr_sequence[2], mr_sequence[3]);
        test_pass = 0;
      end
    end else begin
      $display("[FAIL] Insufficient MRS commands detected (got %0d, expected at least 4)", 
               mr_sequence.size());
      test_pass = 0;
    end

    // Check ZQCL
    if (zqcl_issued) begin
      $display("[PASS] ZQCL command issued");
    end else begin
      $display("[FAIL] ZQCL command not detected");
      test_pass = 0;
    end

    // Check CKE behavior
    if (cke_error) begin
      $display("[FAIL] CKE behavior incorrect during reset/wait");
      test_pass = 0;
    end else begin
      $display("[PASS] CKE stayed low during reset/wait states");
    end

    // Final summary
    $display("\n========================================");
    if (test_pass) begin
      $display("[PASS] All tests passed!");
    end else begin
      $display("[FAIL] Some tests failed");
    end
    $display("========================================\n");

    $finish;
  end

  // Watchdog timer
  initial begin
    #(CLK_PERIOD * TIMEOUT_CYCLES * 2);
    $display("\n[FAIL] Simulation watchdog timeout");
    $finish;
  end

endmodule
