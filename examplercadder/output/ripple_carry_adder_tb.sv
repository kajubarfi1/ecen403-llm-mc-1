// =============================================================================
// 8-Bit Ripple Carry Adder - Comprehensive Testbench
// =============================================================================
// This testbench thoroughly verifies the ripple_carry_adder module with:
//   - Corner case testing (all zeros, all ones)
//   - Carry propagation testing (maximum carry chain)
//   - Edge cases (overflow, alternating patterns)
//   - Random value testing
//   - Self-checking with expected results
//
// Date: 2026-02-10
// =============================================================================

`timescale 1ns / 1ps

module ripple_carry_adder_tb;

    // =========================================================================
    // Signal Declarations
    // =========================================================================
    logic [7:0] A;       // First operand
    logic [7:0] B;       // Second operand
    logic       Cin;     // Carry input
    logic [7:0] S;       // Sum output
    logic       Cout;    // Carry output

    // Expected results for self-checking
    logic [8:0] expected_result;  // 9-bit expected {Cout, S}
    logic [8:0] actual_result;    // 9-bit actual {Cout, S}

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // =========================================================================
    // Device Under Test (DUT) Instantiation
    // =========================================================================
    ripple_carry_adder #(
        .WIDTH(8)
    ) dut (
        .A    (A),
        .B    (B),
        .Cin  (Cin),
        .S    (S),
        .Cout (Cout)
    );

    // =========================================================================
    // Task: Check Result
    // =========================================================================
    // Compares actual output with expected and reports PASS/FAIL
    task automatic check_result(
        input string test_name,
        input [7:0] a_val,
        input [7:0] b_val,
        input       cin_val,
        input [7:0] expected_s,
        input       expected_cout
    );
        test_count++;
        actual_result = {Cout, S};
        expected_result = {expected_cout, expected_s};

        if (actual_result === expected_result) begin
            $display("PASS: %s", test_name);
            $display("      A=0x%02h (%3d), B=0x%02h (%3d), Cin=%b",
                     a_val, a_val, b_val, b_val, cin_val);
            $display("      Expected: S=0x%02h (%3d), Cout=%b",
                     expected_s, expected_s, expected_cout);
            $display("      Actual:   S=0x%02h (%3d), Cout=%b",
                     S, S, Cout);
            pass_count++;
        end else begin
            $display("FAIL: %s", test_name);
            $display("      A=0x%02h (%3d), B=0x%02h (%3d), Cin=%b",
                     a_val, a_val, b_val, b_val, cin_val);
            $display("      Expected: S=0x%02h (%3d), Cout=%b",
                     expected_s, expected_s, expected_cout);
            $display("      Actual:   S=0x%02h (%3d), Cout=%b",
                     S, S, Cout);
            $display("      ERROR: Result mismatch!");
            fail_count++;
        end
        $display("");  // Blank line for readability
    endtask

    // =========================================================================
    // Task: Run Test
    // =========================================================================
    // Applies inputs, waits for propagation, and checks result
    task automatic run_test(
        input string test_name,
        input [7:0] a_val,
        input [7:0] b_val,
        input       cin_val
    );
        logic [8:0] expected;

        // Apply inputs
        A = a_val;
        B = b_val;
        Cin = cin_val;

        // Wait for combinational logic to settle
        #10;

        // Calculate expected result
        expected = a_val + b_val + cin_val;

        // Check result
        check_result(test_name, a_val, b_val, cin_val,
                    expected[7:0], expected[8]);
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        $display("=============================================================================");
        $display("8-Bit Ripple Carry Adder Testbench");
        $display("=============================================================================");
        $display("");

        // Initialize inputs
        A = 8'h00;
        B = 8'h00;
        Cin = 1'b0;
        #5;  // Initial settling time

        // =====================================================================
        // Test Category 1: Corner Cases
        // =====================================================================
        $display("---------------------------------------------------------------------");
        $display("Test Category 1: Corner Cases");
        $display("---------------------------------------------------------------------");

        // Test 1: All zeros
        run_test("All zeros (no carry)", 8'h00, 8'h00, 1'b0);

        // Test 2: All zeros with carry-in
        run_test("All zeros with Cin=1", 8'h00, 8'h00, 1'b1);

        // Test 3: All ones (maximum values)
        run_test("All ones (0xFF + 0xFF + 0)", 8'hFF, 8'hFF, 1'b0);

        // Test 4: All ones with carry-in
        run_test("All ones with Cin=1 (max carry)", 8'hFF, 8'hFF, 1'b1);

        // Test 5: One operand zero
        run_test("A=0xFF, B=0x00", 8'hFF, 8'h00, 1'b0);

        // Test 6: Other operand zero
        run_test("A=0x00, B=0xFF", 8'h00, 8'hFF, 1'b0);

        // =====================================================================
        // Test Category 2: Carry Propagation
        // =====================================================================
        $display("---------------------------------------------------------------------");
        $display("Test Category 2: Carry Propagation");
        $display("---------------------------------------------------------------------");

        // Test 7: Maximum carry propagation (ripple through all bits)
        run_test("Max carry propagation (0xFF + 0x01)", 8'hFF, 8'h01, 1'b0);

        // Test 8: Carry propagation from Cin
        run_test("Carry propagation with Cin (0xFF + 0x00 + 1)", 8'hFF, 8'h00, 1'b1);

        // Test 9: No carry propagation
        run_test("No carry (0x55 + 0x22)", 8'h55, 8'h22, 1'b0);

        // Test 10: Partial carry propagation
        run_test("Partial carry (0x0F + 0x01)", 8'h0F, 8'h01, 1'b0);

        // Test 11: Carry in lower nibble only
        run_test("Lower nibble carry (0x08 + 0x09)", 8'h08, 8'h09, 1'b0);

        // Test 12: Carry in upper nibble only
        run_test("Upper nibble carry (0x80 + 0x90)", 8'h80, 8'h90, 1'b0);

        // =====================================================================
        // Test Category 3: Alternating and Pattern Tests
        // =====================================================================
        $display("---------------------------------------------------------------------");
        $display("Test Category 3: Alternating and Pattern Tests");
        $display("---------------------------------------------------------------------");

        // Test 13: Alternating bits (0xAA pattern)
        run_test("Alternating 0xAA + 0xAA", 8'hAA, 8'hAA, 1'b0);

        // Test 14: Alternating bits (0x55 pattern)
        run_test("Alternating 0x55 + 0x55", 8'h55, 8'h55, 1'b0);

        // Test 15: Complementary patterns
        run_test("Complementary (0xAA + 0x55)", 8'hAA, 8'h55, 1'b0);

        // Test 16: Complementary with carry
        run_test("Complementary with Cin (0xAA + 0x55 + 1)", 8'hAA, 8'h55, 1'b1);

        // Test 17: Power-of-2 addition
        run_test("Powers of 2 (0x80 + 0x80)", 8'h80, 8'h80, 1'b0);

        // Test 18: Single bit set
        run_test("Single bit (0x01 + 0x01)", 8'h01, 8'h01, 1'b0);

        // =====================================================================
        // Test Category 4: Typical Operations
        // =====================================================================
        $display("---------------------------------------------------------------------");
        $display("Test Category 4: Typical Operations");
        $display("---------------------------------------------------------------------");

        // Test 19: Basic addition (from spec example)
        run_test("Basic addition (0x42 + 0x1F)", 8'h42, 8'h1F, 1'b0);

        // Test 20: Addition producing carry-out
        run_test("Addition with Cout (0xFF + 0x01)", 8'hFF, 8'h01, 1'b0);

        // Test 21: Mid-range values
        run_test("Mid-range (0x7F + 0x7F)", 8'h7F, 8'h7F, 1'b0);

        // Test 22: Sequential values
        run_test("Sequential (0x12 + 0x34)", 8'h12, 8'h34, 1'b0);

        // Test 23: Near-overflow
        run_test("Near overflow (0xFE + 0x01)", 8'hFE, 8'h01, 1'b0);

        // Test 24: Near-overflow with Cin
        run_test("Overflow trigger (0xFE + 0x01 + 1)", 8'hFE, 8'h01, 1'b1);

        // =====================================================================
        // Test Category 5: Random Values
        // =====================================================================
        $display("---------------------------------------------------------------------");
        $display("Test Category 5: Random Value Testing");
        $display("---------------------------------------------------------------------");

        // Seed the random number generator for reproducibility
        // (Remove or change seed for different random patterns)

        // Test 25-34: Random tests
        for (int i = 0; i < 10; i++) begin
            automatic logic [7:0] rand_a = $urandom_range(0, 255);
            automatic logic [7:0] rand_b = $urandom_range(0, 255);
            automatic logic       rand_cin = $urandom_range(0, 1);
            automatic string test_name = $sformatf("Random test %0d", i+1);
            run_test(test_name, rand_a, rand_b, rand_cin);
        end

        // =====================================================================
        // Test Category 6: Multi-Precision Chaining Test
        // =====================================================================
        $display("---------------------------------------------------------------------");
        $display("Test Category 6: Multi-Precision Chaining");
        $display("---------------------------------------------------------------------");

        // Test 35: Simulating 16-bit addition (lower byte)
        // 16-bit: 0x1234 + 0x5678 = 0x68AC
        // Lower: 0x34 + 0x78 = 0xAC, Cout=0
        run_test("16-bit chain: lower byte (0x34 + 0x78)", 8'h34, 8'h78, 1'b0);

        // Test 36: Upper byte with carry from lower
        // Upper: 0x12 + 0x56 + 0 = 0x68, Cout=0
        run_test("16-bit chain: upper byte (0x12 + 0x56)", 8'h12, 8'h56, 1'b0);

        // Test 37: Chaining with carry-in (0x80 + 0x80 produces Cout=1)
        run_test("Chain test lower (0x80 + 0x80)", 8'h80, 8'h80, 1'b0);

        // Test 38: Upper byte receiving carry from lower
        run_test("Chain test upper with Cin (0x00 + 0x00 + 1)", 8'h00, 8'h00, 1'b1);

        // =====================================================================
        // Final Summary
        // =====================================================================
        $display("=============================================================================");
        $display("Test Summary");
        $display("=============================================================================");
        $display("Total Tests:  %0d", test_count);
        $display("Passed:       %0d", pass_count);
        $display("Failed:       %0d", fail_count);
        $display("Pass Rate:    %0.2f%%", (pass_count * 100.0) / test_count);
        $display("=============================================================================");

        if (fail_count == 0) begin
            $display("✓ ALL TESTS PASSED!");
        end else begin
            $display("✗ SOME TESTS FAILED - Review results above");
        end
        $display("=============================================================================");

        // End simulation
        $finish;
    end

    // =========================================================================
    // Timeout Watchdog
    // =========================================================================
    // Safety mechanism to prevent infinite simulation
    initial begin
        #100000;  // 100 microseconds timeout
        $display("ERROR: Simulation timeout!");
        $finish;
    end

    // =========================================================================
    // Waveform Dump (for viewing in waveform viewers)
    // =========================================================================
    // Uncomment the following lines to generate VCD waveform file
    // initial begin
    //     $dumpfile("ripple_carry_adder_tb.vcd");
    //     $dumpvars(0, ripple_carry_adder_tb);
    // end

endmodule


// =============================================================================
// Testbench Design Notes
// =============================================================================
// 1. Comprehensive Coverage:
//    - Corner cases (all 0s, all 1s)
//    - Carry propagation scenarios
//    - Pattern-based tests (alternating bits)
//    - Random value testing
//    - Multi-precision chaining simulation
//
// 2. Self-Checking:
//    - Automatic calculation of expected results
//    - Comparison of actual vs expected outputs
//    - Clear PASS/FAIL reporting
//
// 3. Readability:
//    - Organized into test categories
//    - Descriptive test names
//    - Detailed output showing both hex and decimal values
//    - Summary statistics at the end
//
// 4. Robustness:
//    - Timeout watchdog to prevent hangs
//    - Proper initialization and settling time
//    - 10ns delay for combinational logic propagation
//
// 5. Extensibility:
//    - Easy to add more test cases
//    - Parameterized random testing
//    - VCD dump capability for waveform analysis
//
// 6. Expected Results:
//    - All 38+ tests should PASS
//    - 100% pass rate expected for correct implementation
//    - Any failures indicate design or implementation bugs
// =============================================================================
