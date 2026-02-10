"""
Ripple Carry Adder Multi-Agent System
======================================
Three agents work together:
1. Architecture Agent - Designs microarchitecture based on user specs, outputs block diagram
2. I/O Agent - Defines inputs/outputs and creates a SystemVerilog skeleton
3. SystemVerilog Agent - Fully implements the ripple carry adder

Usage:
    export ANTHROPIC_API_KEY=your-key-here
    uv run agent.py
"""

import asyncio
import json
import os
import sys
from claude_agent_sdk import query, ClaudeAgentOptions, AssistantMessage, ResultMessage


# ─────────────────────────────────────────────
#  Utility: Run an agent and collect its output
# ─────────────────────────────────────────────
async def run_agent(name: str, prompt: str, system_prompt: str, cwd: str) -> str:
    """Run a single agent and return its full text output."""
    print(f"\n{'='*60}")
    print(f"  🤖 Running: {name}")
    print(f"{'='*60}\n")

    collected_text = []

    async for message in query(
        prompt=prompt,
        options=ClaudeAgentOptions(
            system_prompt=system_prompt,
            allowed_tools=["Read", "Write", "Edit", "Bash", "Glob", "Grep"],
            permission_mode="acceptEdits",
            cwd=cwd,
        ),
    ):
        if isinstance(message, AssistantMessage):
            for block in message.content:
                if hasattr(block, "text"):
                    print(block.text)
                    collected_text.append(block.text)
                elif hasattr(block, "name"):
                    print(f"  [Tool: {block.name}]")
        elif isinstance(message, ResultMessage):
            print(f"\n✅ {name} finished: {message.subtype}")

    return "\n".join(collected_text)


# ─────────────────────────────────────────────
#  Get user specifications
# ─────────────────────────────────────────────
def get_user_specs() -> dict:
    """Prompt the user for ripple carry adder specifications."""
    print("\n" + "=" * 60)
    print("  ⚡ Ripple Carry Adder Design System")
    print("=" * 60)
    print("\nEnter your specifications (press Enter for defaults):\n")

    bit_width = input("  Bit width [default: 4]: ").strip()
    bit_width = int(bit_width) if bit_width else 4

    carry_in = input("  Include carry-in? (y/n) [default: y]: ").strip().lower()
    carry_in = carry_in != "n"

    carry_out = input("  Include carry-out? (y/n) [default: y]: ").strip().lower()
    carry_out = carry_out != "n"

    overflow = input("  Include overflow detection? (y/n) [default: n]: ").strip().lower()
    overflow = overflow == "y"

    testbench = input("  Generate testbench? (y/n) [default: y]: ").strip().lower()
    testbench = testbench != "n"

    specs = {
        "bit_width": bit_width,
        "carry_in": carry_in,
        "carry_out": carry_out,
        "overflow_detection": overflow,
        "generate_testbench": testbench,
    }

    print(f"\n📋 Specifications: {json.dumps(specs, indent=2)}")
    return specs


# ─────────────────────────────────────────────
#  Agent 1: Architecture Agent
# ─────────────────────────────────────────────
ARCHITECTURE_SYSTEM_PROMPT = """\
You are the Architecture Agent for digital circuit design. Your job is to:

1. Analyze the user's ripple carry adder specifications
2. Design the microarchitecture (how full adders chain together)
3. Create a DETAILED block diagram as an SVG file called `block_diagram.svg`
4. Write a design document called `architecture.md`

For the block diagram SVG:
- Show each full adder as a labeled box with A, B, Cin inputs and S, Cout outputs
- Show the carry chain connections between full adders
- Show the top-level inputs (A[n:0], B[n:0], Cin) and outputs (S[n:0], Cout)
- Use clean, professional styling with colors
- Make it clear and readable

For the architecture document:
- Describe the overall design approach
- List all modules needed (full_adder, ripple_carry_adder)
- Describe the carry propagation path
- Note any special features (overflow detection, etc.)
- Include a signal list with bit widths

Write these files directly to the current directory.
"""


async def run_architecture_agent(specs: dict, cwd: str) -> str:
    prompt = f"""Design a {specs['bit_width']}-bit ripple carry adder with these specifications:
- Bit width: {specs['bit_width']}
- Carry-in: {specs['carry_in']}
- Carry-out: {specs['carry_out']}
- Overflow detection: {specs['overflow_detection']}

Create two files:
1. `block_diagram.svg` - A detailed, professional SVG block diagram showing the full microarchitecture
2. `architecture.md` - A design document describing the architecture

Make the SVG block diagram visually clear with:
- Each full adder as a distinct box
- Labeled signal connections
- The carry chain clearly shown
- Top-level I/O labeled with bit widths
- Professional color scheme (use blues and grays)
"""
    return await run_agent("Architecture Agent", prompt, ARCHITECTURE_SYSTEM_PROMPT, cwd)


# ─────────────────────────────────────────────
#  Agent 2: I/O Agent
# ─────────────────────────────────────────────
IO_SYSTEM_PROMPT = """\
You are the I/O Definition Agent for digital circuit design. Your job is to:

1. Read the architecture document (`architecture.md`) and block diagram to understand the design
2. Define all inputs and outputs precisely with correct bit widths
3. Create a SystemVerilog skeleton file with:
   - Module declarations with proper port lists
   - Parameter definitions
   - All input/output declarations with correct widths
   - Internal signal/wire declarations
   - Placeholder comments where logic should be filled in
   - A separate full_adder module skeleton

Write the skeleton to `ripple_carry_adder_skeleton.sv`.
Also write an I/O specification to `io_spec.md`.

The skeleton should compile without errors (no undriven signals - use placeholder assignments).
Use SystemVerilog conventions: logic type, always_comb, etc.
"""


async def run_io_agent(specs: dict, cwd: str) -> str:
    prompt = f"""Read the `architecture.md` file in the current directory to understand the 
{specs['bit_width']}-bit ripple carry adder design.

Then create two files:

1. `io_spec.md` - Detailed I/O specification listing every port and internal signal
2. `ripple_carry_adder_skeleton.sv` - A SystemVerilog skeleton with:
   - A `full_adder` module with ports defined but logic marked as TODO
   - A `ripple_carry_adder` module with:
     - All ports declared (A[{specs['bit_width']-1}:0], B[{specs['bit_width']-1}:0], etc.)
     - Internal carry wires declared  
     - Instantiation of full_adder modules with correct connections marked as TODO
     {"- Overflow detection logic marked as TODO" if specs['overflow_detection'] else ""}
   - The file should be valid SystemVerilog that compiles (use placeholder assigns)

Specifications:
- Bit width: {specs['bit_width']}
- Carry-in: {specs['carry_in']}
- Carry-out: {specs['carry_out']}
- Overflow detection: {specs['overflow_detection']}
"""
    return await run_agent("I/O Agent", prompt, IO_SYSTEM_PROMPT, cwd)


# ─────────────────────────────────────────────
#  Agent 3: SystemVerilog Agent
# ─────────────────────────────────────────────
SV_SYSTEM_PROMPT = """\
You are the SystemVerilog Implementation Agent. Your job is to:

1. Read the architecture document (`architecture.md`), I/O spec (`io_spec.md`), 
   and skeleton (`ripple_carry_adder_skeleton.sv`)
2. Create the COMPLETE, WORKING SystemVerilog implementation
3. Replace all TODO placeholders with actual logic
4. Ensure correct carry chain connections
5. Follow SystemVerilog best practices

Write the final implementation to `ripple_carry_adder.sv`.
If a testbench is requested, write it to `ripple_carry_adder_tb.sv`.

Requirements:
- Use `logic` type (not `wire`/`reg`)
- Use `always_comb` for combinational logic
- Use generate blocks for full adder instantiation
- Include proper comments
- The code MUST be synthesizable
- The testbench should verify all edge cases (all 0s, all 1s, alternating, random)
"""


async def run_sv_agent(specs: dict, cwd: str) -> str:
    prompt = f"""Read all the design files in the current directory:
- `architecture.md` (design document)
- `io_spec.md` (I/O specification)  
- `ripple_carry_adder_skeleton.sv` (skeleton code)

Now create the COMPLETE, FULLY WORKING SystemVerilog implementation.

Write to `ripple_carry_adder.sv`:
- Implement the `full_adder` module with XOR/AND gate logic
- Implement the `ripple_carry_adder` module with:
  - Generate block to instantiate {specs['bit_width']} full adders
  - Correct carry chain: carry[0] = Cin, carry[i+1] = Cout of FA[i]
  - Final sum and carry-out assignments
  {"- Overflow = carry[N] XOR carry[N-1]" if specs['overflow_detection'] else ""}

{"Also write `ripple_carry_adder_tb.sv` with a comprehensive testbench that:" if specs['generate_testbench'] else ""}
{"- Tests all zeros, all ones, alternating bits" if specs['generate_testbench'] else ""}
{"- Tests carry propagation (e.g., 0xF + 0x1 for 4-bit)" if specs['generate_testbench'] else ""}
{"- Tests random values" if specs['generate_testbench'] else ""}
{"- Prints PASS/FAIL for each test" if specs['generate_testbench'] else ""}
{"- Uses $display for readable output" if specs['generate_testbench'] else ""}

The implementation must be synthesizable and correct.
"""
    return await run_agent("SystemVerilog Agent", prompt, SV_SYSTEM_PROMPT, cwd)


# ─────────────────────────────────────────────
#  Main: Orchestrate all three agents
# ─────────────────────────────────────────────
async def main():
    # Get user specs
    specs = get_user_specs()

    # Create output directory
    output_dir = os.path.join(os.getcwd(), "output")
    os.makedirs(output_dir, exist_ok=True)
    print(f"\n📁 Output directory: {output_dir}\n")

    # Agent 1: Architecture
    print("\n" + "🔷" * 30)
    print("  PHASE 1: Architecture Design")
    print("🔷" * 30)
    await run_architecture_agent(specs, output_dir)

    # Agent 2: I/O Definition
    print("\n" + "🔶" * 30)
    print("  PHASE 2: I/O Definition & Skeleton")
    print("🔶" * 30)
    await run_io_agent(specs, output_dir)

    # Agent 3: SystemVerilog Implementation
    print("\n" + "🟢" * 30)
    print("  PHASE 3: SystemVerilog Implementation")
    print("🟢" * 30)
    await run_sv_agent(specs, output_dir)

    # Summary
    print("\n" + "=" * 60)
    print("  ✅ All agents complete! Files generated:")
    print("=" * 60)
    for f in sorted(os.listdir(output_dir)):
        filepath = os.path.join(output_dir, f)
        size = os.path.getsize(filepath)
        print(f"  📄 output/{f} ({size} bytes)")
    print(f"\n  📂 All files in: {output_dir}")
    print("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())