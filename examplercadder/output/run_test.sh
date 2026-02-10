#!/bin/bash

echo "============================================================================="
echo "8-Bit Ripple Carry Adder - Compilation and Testing"
echo "============================================================================="
echo ""

# Check if iverilog is available
if command -v iverilog &> /dev/null; then
    echo "Step 1: Compiling with Icarus Verilog..."
    iverilog -g2012 -o ripple_carry_adder_sim ripple_carry_adder.sv ripple_carry_adder_tb.sv
    
    if [ $? -eq 0 ]; then
        echo "✓ Compilation successful!"
        echo ""
        echo "Step 2: Running simulation..."
        echo "============================================================================="
        vvp ripple_carry_adder_sim
    else
        echo "✗ Compilation failed!"
        exit 1
    fi
else
    echo "Note: Icarus Verilog (iverilog) not found."
    echo "To run simulation, install iverilog and execute:"
    echo "  iverilog -g2012 -o ripple_carry_adder_sim ripple_carry_adder.sv ripple_carry_adder_tb.sv"
    echo "  vvp ripple_carry_adder_sim"
fi
