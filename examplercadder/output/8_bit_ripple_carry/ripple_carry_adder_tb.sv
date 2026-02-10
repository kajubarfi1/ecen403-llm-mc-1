// ============================================================================
// 8-Bit Ripple Carry Adder - Comprehensive Testbench
// ============================================================================
// This testbench verifies the functionality of the 8-bit ripple carry adder
// with comprehensive test cases including:
// - All zeros, all ones, alternating bit patterns
// - Carry propagation tests
// - Random value testing
// - Edge cases and overflow scenarios
//
// Date: 2026-02-10
// ============================================================================

`timescale 1ns/1ps

module ripple_carry_adder_tb;

    // ------------------------------------------------------------------------
    // Testbench Signals
    // ------------------------------------------------------------------------
    logic [7:0] A;           // First operand
    logic [7:0] B;           // Second operand
    logic       Cin;         // Carry input
    logic [7:0] S;           // Sum output
    logic       Cout;        // Carry output

    // Expected values for verification
    logic [8:0] expected;    // 9-bit expected result (includes carry)
    logic [7:0] expected_sum;
    logic       expected_cout;

    // Test statistics
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // ------------------------------------------------------------------------
    // DUT Instantiation
    // ------------------------------------------------------------------------
    ripple_carry_adder DUT (
        .A    (A),
        .B    (B),
        .Cin  (Cin),
        .S    (S),
        .Cout (Cout)
    );

    // ------------------------------------------------------------------------
    // Task: Check Result
    // ------------------------------------------------------------------------
    // Compares actual output with expected result and reports PASS/FAIL
    // ------------------------------------------------------------------------
    task check_result(
        input string test_name,
        input logic [7:0] a_val,
        input logic [7:0] b_val,
        input logic cin_val,
        input logic [7:0] exp_sum,
        input logic exp_cout
    );
        test_count++;

        if (S === exp_sum && Cout === exp_cout) begin
            $display("[PASS] %s: %0d + %0d + %0d = {%b, %08b} (decimal: %0d)",
                     test_name, a_val, b_val, cin_val, Cout, S, {Cout, S});
            pass_count++;
        end else begin
            $display("[FAIL] %s: %0d + %0d + %0d", test_name, a_val, b_val, cin_val);
            $display("       Expected: {%b, %08b} (decimal: %0d)",
                     exp_cout, exp_sum, {exp_cout, exp_sum});
            $display("       Got:      {%b, %08b} (decimal: %0d)",
                     Cout, S, {Cout, S});
            fail_count++;
        end
    endtask

    // ------------------------------------------------------------------------
    // Task: Apply Test Vector
    // ------------------------------------------------------------------------
    task apply_test(
        input string test_name,
        input logic [7:0] a_val,
        input logic [7:0] b_val,
        input logic cin_val
    );
        A = a_val;
        B = b_val;
        Cin = cin_val;
        #10;  // Wait for combinational logic to settle

        // Calculate expected result
        expected = a_val + b_val + cin_val;
        expected_sum = expected[7:0];
        expected_cout = expected[8];

        check_result(test_name, a_val, b_val, cin_val, expected_sum, expected_cout);
    endtask

    // ------------------------------------------------------------------------
    // Main Test Sequence
    // ------------------------------------------------------------------------
    initial begin
        $display("============================================================================");
        $display("8-Bit Ripple Carry Adder Testbench");
        $display("============================================================================");
        $display("");

        // Initialize signals
        A = 8'b0;
        B = 8'b0;
        Cin = 1'b0;
        #5;

        // ====================================================================
        // Test Category 1: Basic Edge Cases
        // ====================================================================
        $display("--------------------------------------------------------------------");
        $display("Test Category 1: Basic Edge Cases");
        $display("--------------------------------------------------------------------");

        // Test 1.1: All zeros
        apply_test("All zeros (no carry-in)", 8'd0, 8'd0, 1'b0);

        // Test 1.2: All zeros with carry-in
        apply_test("All zeros (with carry-in)", 8'd0, 8'd0, 1'b1);

        // Test 1.3: All ones
        apply_test("All ones (no carry-in)", 8'd255, 8'd255, 1'b0);

        // Test 1.4: All ones with carry-in
        apply_test("All ones (with carry-in)", 8'd255, 8'd255, 1'b1);

        // ====================================================================
        // Test Category 2: Simple Addition
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 2: Simple Addition");
        $display("--------------------------------------------------------------------");

        apply_test("1 + 1", 8'd1, 8'd1, 1'b0);
        apply_test("1 + 1 + 1", 8'd1, 8'd1, 1'b1);
        apply_test("10 + 20", 8'd10, 8'd20, 1'b0);
        apply_test("100 + 50", 8'd100, 8'd50, 1'b0);
        apply_test("127 + 127", 8'd127, 8'd127, 1'b0);

        // ====================================================================
        // Test Category 3: Carry Propagation Tests
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 3: Carry Propagation Tests");
        $display("--------------------------------------------------------------------");

        // Test 3.1: Maximum carry propagation (all 1s + 1)
        apply_test("0xFF + 0x01 (full carry)", 8'hFF, 8'h01, 1'b0);

        // Test 3.2: 0xFF + 0x00 + 1 (carry-in triggers propagation)
        apply_test("0xFF + 0x00 + 1 (carry-in propagation)", 8'hFF, 8'h00, 1'b1);

        // Test 3.3: Half-adder carry chain
        apply_test("0x0F + 0x01 (4-bit carry)", 8'h0F, 8'h01, 1'b0);

        // Test 3.4: Upper nibble carry
        apply_test("0xF0 + 0x10 (upper nibble carry)", 8'hF0, 8'h10, 1'b0);

        // Test 3.5: 128 + 128 (MSB carry out)
        apply_test("128 + 128 (overflow)", 8'd128, 8'd128, 1'b0);

        // Test 3.6: 200 + 100 (overflow with carry out)
        apply_test("200 + 100 (overflow)", 8'd200, 8'd100, 1'b0);

        // ====================================================================
        // Test Category 4: Alternating Bit Patterns
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 4: Alternating Bit Patterns");
        $display("--------------------------------------------------------------------");

        // Test 4.1: Alternating 01010101 + 10101010
        apply_test("0x55 + 0xAA (alternating)", 8'b01010101, 8'b10101010, 1'b0);

        // Test 4.2: Alternating with carry-in
        apply_test("0x55 + 0xAA + 1 (alternating)", 8'b01010101, 8'b10101010, 1'b1);

        // Test 4.3: 0xAA + 0xAA
        apply_test("0xAA + 0xAA", 8'hAA, 8'hAA, 1'b0);

        // Test 4.4: 0x55 + 0x55
        apply_test("0x55 + 0x55", 8'h55, 8'h55, 1'b0);

        // ====================================================================
        // Test Category 5: Boundary Tests
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 5: Boundary Tests");
        $display("--------------------------------------------------------------------");

        // Test 5.1: Maximum value (no overflow)
        apply_test("254 + 0", 8'd254, 8'd0, 1'b0);

        // Test 5.2: Maximum value + 1 (no overflow)
        apply_test("254 + 1", 8'd254, 8'd1, 1'b0);

        // Test 5.3: Maximum value + 1 (overflow)
        apply_test("255 + 1", 8'd255, 8'd1, 1'b0);

        // Test 5.4: Minimum overflow
        apply_test("255 + 0 + 1", 8'd255, 8'd0, 1'b1);

        // ====================================================================
        // Test Category 6: Power-of-2 Tests
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 6: Power-of-2 Tests");
        $display("--------------------------------------------------------------------");

        apply_test("1 + 1 (2^0 + 2^0)", 8'd1, 8'd1, 1'b0);
        apply_test("2 + 2 (2^1 + 2^1)", 8'd2, 8'd2, 1'b0);
        apply_test("4 + 4 (2^2 + 2^2)", 8'd4, 8'd4, 1'b0);
        apply_test("8 + 8 (2^3 + 2^3)", 8'd8, 8'd8, 1'b0);
        apply_test("16 + 16 (2^4 + 2^4)", 8'd16, 8'd16, 1'b0);
        apply_test("32 + 32 (2^5 + 2^5)", 8'd32, 8'd32, 1'b0);
        apply_test("64 + 64 (2^6 + 2^6)", 8'd64, 8'd64, 1'b0);
        apply_test("128 + 128 (2^7 + 2^7)", 8'd128, 8'd128, 1'b0);

        // ====================================================================
        // Test Category 7: Random Tests
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 7: Random Tests");
        $display("--------------------------------------------------------------------");

        // Seed random number generator for reproducibility
        // Run 20 random tests
        for (int i = 0; i < 20; i++) begin
            automatic logic [7:0] rand_a = $urandom_range(0, 255);
            automatic logic [7:0] rand_b = $urandom_range(0, 255);
            automatic logic rand_cin = $urandom_range(0, 1);

            apply_test($sformatf("Random test %0d", i+1), rand_a, rand_b, rand_cin);
        end

        // ====================================================================
        // Test Category 8: Increment Operations
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 8: Increment Operations (B=0, Cin=1)");
        $display("--------------------------------------------------------------------");

        apply_test("Increment 0", 8'd0, 8'd0, 1'b1);
        apply_test("Increment 1", 8'd1, 8'd0, 1'b1);
        apply_test("Increment 127", 8'd127, 8'd0, 1'b1);
        apply_test("Increment 254", 8'd254, 8'd0, 1'b1);
        apply_test("Increment 255 (wraparound)", 8'd255, 8'd0, 1'b1);

        // ====================================================================
        // Test Category 9: Nibble-specific Tests
        // ====================================================================
        $display("");
        $display("--------------------------------------------------------------------");
        $display("Test Category 9: Nibble-specific Tests");
        $display("--------------------------------------------------------------------");

        apply_test("Lower nibble only (0x0F + 0x01)", 8'h0F, 8'h01, 1'b0);
        apply_test("Upper nibble only (0xF0 + 0x10)", 8'hF0, 8'h10, 1'b0);
        apply_test("Both nibbles (0xFF + 0xFF)", 8'hFF, 8'hFF, 1'b0);
        apply_test("Cross nibble (0x08 + 0x08)", 8'h08, 8'h08, 1'b0);

        // ====================================================================
        // Final Summary
        // ====================================================================
        $display("");
        $display("============================================================================");
        $display("Test Summary");
        $display("============================================================================");
        $display("Total Tests:  %0d", test_count);
        $display("Passed:       %0d", pass_count);
        $display("Failed:       %0d", fail_count);
        $display("Pass Rate:    %0.2f%%", (100.0 * pass_count) / test_count);
        $display("============================================================================");

        if (fail_count == 0) begin
            $display("ALL TESTS PASSED! ✓");
        end else begin
            $display("SOME TESTS FAILED! ✗");
        end

        $display("============================================================================");
        $display("");

        $finish;
    end

endmodule : ripple_carry_adder_tb


// ============================================================================
// End of File
// ============================================================================
