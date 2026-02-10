# Ripple Carry Adder Multi-Agent System

Three AI agents collaborate to design and implement a ripple carry adder in SystemVerilog.

## Agents

| Agent | Role | Output Files |
|-------|------|-------------|
| **Architecture Agent** | Designs microarchitecture, creates block diagram | `block_diagram.svg`, `architecture.md` |
| **I/O Agent** | Defines all ports and signals, creates code skeleton | `io_spec.md`, `ripple_carry_adder_skeleton.sv` |
| **SystemVerilog Agent** | Implements full working RTL and testbench | `ripple_carry_adder.sv`, `ripple_carry_adder_tb.sv` |

## Setup

```bash
cd ~/my-project        # or wherever you want the project
cp agent.py .          # copy agent.py here
echo "3.12" > .python-version
uv init                # skip if already initialized
uv add claude-agent-sdk
```

## Run

```bash
export ANTHROPIC_API_KEY=your-key-here
uv run agent.py
```

You'll be prompted for specifications:

```
  Bit width [default: 4]: 8
  Include carry-in? (y/n) [default: y]: y
  Include carry-out? (y/n) [default: y]: y
  Include overflow detection? (y/n) [default: n]: y
  Generate testbench? (y/n) [default: y]: y
```

## Output

All generated files appear in the `output/` folder:

```
output/
├── architecture.md                  # Design document
├── block_diagram.svg                # Visual block diagram
├── io_spec.md                       # I/O specification
├── ripple_carry_adder_skeleton.sv   # Code skeleton (intermediate)
├── ripple_carry_adder.sv            # Final implementation
└── ripple_carry_adder_tb.sv         # Testbench
```

## Simulating the Output

With Icarus Verilog:
```bash
cd output
iverilog -g2012 -o rca_tb ripple_carry_adder.sv ripple_carry_adder_tb.sv
vvp rca_tb
```

With ModelSim/QuestaSim:
```bash
cd output
vlog ripple_carry_adder.sv ripple_carry_adder_tb.sv
vsim -run -all ripple_carry_adder_tb
```