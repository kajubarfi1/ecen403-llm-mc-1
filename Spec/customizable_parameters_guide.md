# DDR3 Memory Controller — Customizable Parameters Guide

## Overview

This document classifies every parameter in the microarchitecture schema into three categories:

- **🔒 Fixed by JEDEC** — determined by the DDR3 spec and device choice; not user-tunable
- **⚙️ Derived** — automatically computed from other selections; changed indirectly
- **🎛️ User-Customizable** — the knobs a user should be able to adjust for performance/cost tradeoffs

---

## User-Customizable Parameters

### Tier 1: High-Impact (Expose First)

These have the largest effect on performance, area, and cost. They should be the primary user-facing controls.

| Parameter | Section | Tradeoff | Range |
|-----------|---------|----------|-------|
| **Speed grade** (DDR3-800/1066/1333/1600) | `clocking_model` | Higher speed = more bandwidth but tighter timing margins, harder PHY design, higher power | Drives `ddr_clock_period_ps`, all timing parameters |
| **Device density** (1Gb/2Gb/4Gb/8Gb) | `memory_geometry` | Larger density = more capacity per chip but longer tRFC (refresh penalty) | Changes `row_bits`, `tRFC` |
| **Ranks** | `memory_geometry` | More ranks = more capacity but higher power, ODT complexity, rank-switching latency | 1–4 |
| **Byte lanes** | `memory_geometry` | More lanes = wider data bus = more bandwidth but more pins, area, power | 1–8 |
| **ECC mode** | `controller_architecture` | ECC adds reliability but costs an extra byte lane, reduces usable bandwidth ~12%, increases latency | 0 (off), 1 (SEC-DED), 2, 3 |
| **Scheduler policy** | `controller_architecture` | FR-FCFS gives ~20–40% better bandwidth utilization than in-order, but costs more area (comparators, reorder logic) | `in_order`, `fr_fcfs` |
| **Row policy** | `controller_architecture` | Open-page is faster for sequential/locality workloads; close-page is better for random access and saves power | `open_page`, `close_page` |

### Tier 2: Medium-Impact (Advanced Options)

These affect performance meaningfully but have interdependencies users should understand.

| Parameter | Section | Tradeoff | Range |
|-----------|---------|----------|-------|
| **Command queue depth** | `controller_architecture` | Deeper queue = more reordering opportunity = better bandwidth, but more area (flip-flops, comparators) and latency for lightly-loaded scenarios | 4–32 |
| **Lookahead depth** | `controller_architecture` | Higher lookahead = smarter scheduling but more combinational logic, longer critical path | 0–16 |
| **Address mapping** | `memory_geometry` | Row-bank-column is better for sequential; bank-row-column better for interleaving across banks with random access | 2 options |
| **Burst length** | `memory_geometry` | BL8 is standard and higher bandwidth; BL4 (burst chop) reduces latency for small transfers at the cost of bus efficiency | 4, 8 |
| **Host bus data width** | `host_interface` | Wider bus = higher throughput from host but more routing area, potentially harder timing closure | 32, 64, 128 |
| **Read/write buffer depth** | `host_interface` | Deeper buffers absorb burst traffic better but cost SRAM area | 4–64 |
| **Interface type** | `host_interface` | Pipelined Wishbone gives ~2× throughput over classic but is more complex | 2 options |
| **Self-refresh mode** | `controller_architecture` | Auto self-refresh saves power in idle but adds wake-up latency | `disabled`, `manual`, `auto` |

### Tier 3: Implementation Tuning

These matter for physical implementation and are typically set by the backend team.

| Parameter | Section | Tradeoff | Range |
|-----------|---------|----------|-------|
| **Target frequency** | `implementation_targets` | Higher controller frequency = more throughput but harder timing closure, more power | 100–300 MHz |
| **Area optimization** | `implementation_targets` | Area-optimized = smaller die, cheaper; performance-optimized = faster, larger | 3 options |
| **Power optimization** | `implementation_targets` | Low-power = clock gating, fewer buffers; performance = always-on, deeper pipelines | 3 options |
| **Pipeline latency** | `clocking_model` | More pipeline stages = easier timing closure at high freq but adds fixed latency to every transaction | 1–4 |

---

## Fixed / Derived Parameters (Not User-Tunable)

These are automatically set based on Tier 1 choices and JEDEC spec. The agent should compute them.

### Fixed by Device Choice (density + speed grade)

| Parameter | Determined By | Example (2Gb DDR3-1600K) |
|-----------|--------------|--------------------------|
| `tRCD` | Speed bin + JEDEC table | 11 nCK (13.75ns) |
| `tRP` | Speed bin + JEDEC table | 11 nCK |
| `tRAS` | Speed bin + JEDEC table | 28 nCK (35ns) |
| `tRC` | tRAS + tRP | 39 nCK |
| `tRFC` | Device density | 128 nCK (160ns for 2Gb) |
| `tFAW` | Page size + speed | 32 nCK (40ns for 1KB page) |
| `tRRD` | Page size + speed | 6 nCK |
| `tWR` | JEDEC fixed | 12 nCK (15ns) |
| `tWTR` | JEDEC fixed | 6 nCK |
| `tRTP` | JEDEC fixed | 6 nCK |
| `tCCD` | Always 4 for BL8 | 4 nCK |
| `tREFI` | JEDEC: 7.8μs/tCK | 6240 nCK |
| `CAS_latency` | Speed bin | 11 (for -1600K) |
| `CAS_write_latency` | Speed bin + JEDEC CWL table | 8 |

### Fixed by JEDEC Init Spec

| Parameter | Value | Source |
|-----------|-------|--------|
| `reset_hold_us` | ≥ 200 | JEDEC init sequence |
| `cke_delay_us` | ≥ 500 | JEDEC init sequence |
| `tXPR_cycles` | max(5, tRFC + ceil(10ns/tCK)) | JEDEC |
| `tZQinit_cycles` | ≥ 512 | JEDEC |
| All MR0/MR1/MR2/MR3 fields | Must match timing model | Cross-checked |

### Derived from Geometry

| Parameter | Formula |
|-----------|---------|
| `column_bits` | 10 (x8, 1KB page) or 11 (x16, 2KB page) |
| `bank_bits` | Always 3 (DDR3 = 8 banks) |
| `device_width_bits` | Follows from device selection |
| `ddr_clock_period_ps` | 1e6 / (data_rate / 2) |
| `controller_clock_period_ps` | ddr_clock_period_ps × clock_ratio |
| `address_width_bits` | row_bits + column_bits + bank_bits + log2(ranks) + log2(byte_lanes) |

---

## Recommended Agent Workflow

When a user provides input, the microarchitecture agent should:

1. **Accept Tier 1 choices** from the user (speed grade, density, ranks, byte lanes, ECC, scheduler, row policy)
2. **Offer Tier 2 defaults** with override capability
3. **Auto-derive** all timing parameters from JEDEC tables using the speed grade and density
4. **Cross-validate** mode registers against timing model (CL↔MR0, CWL↔MR2, tWR↔MR0)
5. **Run the compliance checker** to verify all JEDEC rules and internal consistency
6. **Emit the complete JSON instance** ready for RTL generation

### Example: Cost vs Performance Presets

| Preset | Speed | Density | Ranks | Lanes | ECC | Scheduler | Queue | Row Policy |
|--------|-------|---------|-------|-------|-----|-----------|-------|------------|
| **Low-cost embedded** | DDR3-800 | 2Gb | 1 | 1 | Off | In-order | 4 | Close-page |
| **Balanced** | DDR3-1333 | 2Gb | 1 | 2 | Off | FR-FCFS | 16 | Open-page |
| **Default (this file)** | DDR3-1600 | 2Gb | 1 | 2 | Off | FR-FCFS | 16 | Open-page |
| **High-performance** | DDR3-1600 | 4Gb | 2 | 4 | SEC-DED | FR-FCFS | 32 | Open-page |
| **Server-grade** | DDR3-1600 | 4Gb | 4 | 8 | SEC-DED | FR-FCFS | 32 | Open-page |

### tRFC Scaling by Density (Critical Cost Driver)

| Density | tRFC (ns) | tRFC at 800MHz (nCK) | Refresh overhead at JEDEC tREFI |
|---------|-----------|----------------------|----------------------------------|
| 1Gb | 110 | 88 | 1.41% |
| 2Gb | 160 | 128 | 2.05% |
| 4Gb | 260 | 208 | 3.33% |
| 8Gb | 350 | 280 | 4.49% |

Larger devices spend proportionally more time refreshing, which directly reduces usable bandwidth.
