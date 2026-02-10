# I/O Specification: 8-Bit Ripple Carry Adder

## Document Information
- **Design**: 8-bit Ripple Carry Adder
- **Version**: 1.0
- **Date**: 2026-02-10

---

## 1. Top-Level Module: `ripple_carry_adder`

### 1.1 Module Ports

| Port Name | Direction | Type   | Width | Description |
|-----------|-----------|--------|-------|-------------|
| `A`       | Input     | logic  | [7:0] | First 8-bit operand for addition |
| `B`       | Input     | logic  | [7:0] | Second 8-bit operand for addition |
| `Cin`     | Input     | logic  | [0:0] | Carry input (allows chaining with other adders or increment operations) |
| `S`       | Output    | logic  | [7:0] | 8-bit sum result (S = A + B + Cin) |
| `Cout`    | Output    | logic  | [0:0] | Carry output from MSB (indicates unsigned overflow) |

### 1.2 Internal Signals

| Signal Name | Type   | Width | Description |
|-------------|--------|-------|-------------|
| `carry`     | logic  | [7:0] | Internal carry chain signals connecting full adders |

#### Carry Signal Mapping:
- `carry[0]` = Connected to top-level `Cin` input
- `carry[1]` = Carry output from FA0, carry input to FA1
- `carry[2]` = Carry output from FA1, carry input to FA2
- `carry[3]` = Carry output from FA2, carry input to FA3
- `carry[4]` = Carry output from FA3, carry input to FA4
- `carry[5]` = Carry output from FA4, carry input to FA5
- `carry[6]` = Carry output from FA5, carry input to FA6
- `carry[7]` = Carry output from FA6, carry input to FA7

**Note**: The carry output from FA7 is connected directly to the top-level `Cout` port.

---

## 2. Sub-Module: `full_adder`

### 2.1 Module Ports

| Port Name | Direction | Type   | Width | Description |
|-----------|-----------|--------|-------|-------------|
| `a`       | Input     | logic  | [0:0] | First input bit |
| `b`       | Input     | logic  | [0:0] | Second input bit |
| `cin`     | Input     | logic  | [0:0] | Carry input from previous stage |
| `sum`     | Output    | logic  | [0:0] | Sum output bit (a ⊕ b ⊕ cin) |
| `cout`    | Output    | logic  | [0:0] | Carry output bit to next stage |

### 2.2 Logic Equations

**Sum Output**:
```
sum = a ⊕ b ⊕ cin
```

**Carry Output** (two equivalent forms):
```
cout = (a · b) + (cin · (a ⊕ b))
```
or
```
cout = (a · b) + (a · cin) + (b · cin)
```

---

## 3. Module Instantiation Hierarchy

```
ripple_carry_adder (Top-level)
├── full_adder FA0 (LSB - Bit 0)
├── full_adder FA1 (Bit 1)
├── full_adder FA2 (Bit 2)
├── full_adder FA3 (Bit 3)
├── full_adder FA4 (Bit 4)
├── full_adder FA5 (Bit 5)
├── full_adder FA6 (Bit 6)
└── full_adder FA7 (MSB - Bit 7)
```

---

## 4. Signal Connectivity

### 4.1 Full Adder Instantiation Pattern

| Instance | a port | b port | cin port   | sum port | cout port  |
|----------|--------|--------|------------|----------|------------|
| FA0      | A[0]   | B[0]   | Cin        | S[0]     | carry[1]   |
| FA1      | A[1]   | B[1]   | carry[1]   | S[1]     | carry[2]   |
| FA2      | A[2]   | B[2]   | carry[2]   | S[2]     | carry[3]   |
| FA3      | A[3]   | B[3]   | carry[3]   | S[3]     | carry[4]   |
| FA4      | A[4]   | B[4]   | carry[4]   | S[4]     | carry[5]   |
| FA5      | A[5]   | B[5]   | carry[5]   | S[5]     | carry[6]   |
| FA6      | A[6]   | B[6]   | carry[6]   | S[6]     | carry[7]   |
| FA7      | A[7]   | B[7]   | carry[7]   | S[7]     | Cout       |

### 4.2 Carry Chain Data Flow

```
Cin (external) → carry[0] → FA0 → carry[1] → FA1 → carry[2] → FA2 →
carry[3] → FA3 → carry[4] → FA4 → carry[5] → FA5 → carry[6] →
FA6 → carry[7] → FA7 → Cout (external)
```

---

## 5. Bit Width Parameters

| Parameter         | Value | Notes |
|-------------------|-------|-------|
| `WIDTH`           | 8     | Number of bits in operands and result |
| Input bit width   | 8     | A[7:0], B[7:0] |
| Output bit width  | 8     | S[7:0] |
| Carry bits        | 1     | Cin, Cout |
| Internal carries  | 7     | carry[7:1] (carry[0] is assigned from Cin) |

---

## 6. Timing Characteristics

### 6.1 Critical Path
The critical path runs through the entire carry chain from Cin through all 8 full adders to Cout:

```
Cin → FA0.cout → FA1.cout → FA2.cout → FA3.cout →
FA4.cout → FA5.cout → FA6.cout → FA7.cout → Cout
```

**Estimated Delay**: 8 × (Full Adder Delay) ≈ 16-24 gate delays

### 6.2 Propagation Delay
- **Worst Case**: Input change at LSB with full carry propagation to MSB
- **Best Case**: Input change with no carry propagation (single FA delay)

---

## 7. Functional Behavior

### 7.1 Addition Operation
```
S[7:0] = A[7:0] + B[7:0] + Cin
{Cout, S[7:0]} = A[7:0] + B[7:0] + Cin  (9-bit result)
```

### 7.2 Carry Out Interpretation
- **Cout = 1**: Indicates unsigned overflow (result > 255)
- **Cout = 0**: Result fits in 8 bits (result ≤ 255)

### 7.3 Use Cases
1. **Simple Addition**: A + B (set Cin = 0)
2. **Addition with Carry**: A + B + Cin (for multi-precision arithmetic)
3. **Increment**: A + 1 (set B = 0, Cin = 1)
4. **Chained Adders**: Cout of one adder feeds Cin of next for 16-bit, 32-bit, etc.

---

## 8. Design Specifications Summary

| Specification        | Value | Notes |
|---------------------|-------|-------|
| Bit Width           | 8     | Fixed width design |
| Carry-In Support    | Yes   | Cin input provided |
| Carry-Out Support   | Yes   | Cout output provided |
| Overflow Detection  | No    | Not implemented (can be derived from Cin/Cout of MSB) |
| Architecture Type   | Ripple Carry | Sequential carry propagation |
| Number of FA Cells  | 8     | One per bit position |

---

## 9. Signal Convention

- **Naming**: lowercase for internal signals, PascalCase for ports (per architecture doc)
- **Type**: `logic` type used throughout (SystemVerilog)
- **Indexing**: [MSB:LSB] format, e.g., [7:0]
- **Bit Numbering**: Bit 0 = LSB, Bit 7 = MSB

---

**End of I/O Specification**
