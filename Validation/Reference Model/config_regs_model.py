"""
Config Registers Reference Model
=================================
Golden behavioral model of the DDR3 memory controller CSR register file.
Derived entirely from the microarchitecture spec JSON — no RTL knowledge.

Usage:
    model = ConfigRegsModel()
    model.write(0x08, 0xDEADBEEF)   # write TIMING_0
    val = model.read(0x08)            # read it back
    model.reset()                     # return to power-on state

Access types per field:
    RO   — read-only, writes are silently ignored
    RW   — read-write, full read/write access
    RW1C — read, write-1-to-clear (writing 1 clears the bit)
    WO   — write-only, reads return 0, value self-clears after write

Author: Validation Subsystem (Reference Model/Checker Agent)
Source of truth: llmmc_microarchitecturespec_filled (1).json → csr_register_map
"""

import json
import os


# ---------------------------------------------------------------------------
# Register / field definitions — directly from the spec JSON
# ---------------------------------------------------------------------------

class Field:
    """One bitfield inside a register."""
    __slots__ = ("name", "hi", "lo", "access", "reset_value")

    def __init__(self, name: str, bits: str, access: str, reset_value: int):
        self.name = name
        self.access = access.upper()
        self.reset_value = reset_value

        # Parse bit range: "31:8" → hi=31,lo=8  or "4" → hi=4,lo=4
        if ":" in bits:
            parts = bits.split(":")
            self.hi = int(parts[0])
            self.lo = int(parts[1])
        else:
            self.hi = int(bits)
            self.lo = int(bits)

    @property
    def width(self):
        return self.hi - self.lo + 1

    @property
    def mask(self):
        """Bitmask for this field, shifted to its position."""
        return ((1 << self.width) - 1) << self.lo


class Register:
    """One 32-bit CSR register."""
    __slots__ = ("name", "offset", "access", "reset_value", "fields", "value")

    def __init__(self, name: str, offset: int, access: str,
                 reset_value: int, fields: list[Field]):
        self.name = name
        self.offset = offset
        self.access = access.upper()
        self.reset_value = reset_value
        self.fields = fields
        self.value = reset_value

    def reset(self):
        self.value = self.reset_value

    def read(self) -> int:
        """Return register value. WO fields read as 0."""
        result = self.value
        for f in self.fields:
            if f.access == "WO":
                result &= ~f.mask  # WO bits read as 0
        return result & 0xFFFFFFFF

    def write(self, wdata: int):
        """Apply write with per-field access semantics."""
        new_val = self.value
        for f in self.fields:
            field_wbits = (wdata >> f.lo) & ((1 << f.width) - 1)
            field_wbits_shifted = field_wbits << f.lo

            if f.access == "RO":
                # Ignore writes to RO fields
                pass
            elif f.access == "RW":
                # Overwrite field with new data
                new_val = (new_val & ~f.mask) | field_wbits_shifted
            elif f.access == "RW1C":
                # Writing 1 clears the bit(s)
                new_val &= ~field_wbits_shifted
            elif f.access == "WO":
                # Accept the write (for side-effect), then self-clear
                # The pulse value is captured here for one "cycle",
                # but reads return 0 and the field clears.
                # For modeling purposes, we store it then immediately clear.
                new_val = (new_val & ~f.mask) | field_wbits_shifted
                # Self-clear after the write takes effect
                new_val &= ~f.mask

        self.value = new_val & 0xFFFFFFFF

    # --- Status injection (for signals feeding INTO status registers) ---

    def inject_status(self, field_name: str, value: int):
        """
        Set an RO or RW1C field from external hardware signals.
        Used by higher-level models to update status bits
        (e.g., init_done, cal_done, ref_pending_cnt) and error flags.
        """
        for f in self.fields:
            if f.name == field_name and f.access in ("RO", "RW1C"):
                clamped = value & ((1 << f.width) - 1)
                self.value = (self.value & ~f.mask) | (clamped << f.lo)
                return
        raise ValueError(f"No RO/RW1C field '{field_name}' in register '{self.name}'")


# ---------------------------------------------------------------------------
# The full CSR register file model
# ---------------------------------------------------------------------------

class ConfigRegsModel:
    """
    Golden reference model for the DDR3 MC config register block.
    
    Mirrors the 11 CSR registers defined in the microarchitecture spec.
    All behavioral rules (RO/RW/RW1C/WO) are enforced per-field.
    """

    # Register definitions from the spec
    REGISTER_DEFS = [
        {
            "name": "CTRL_STATUS", "offset": 0x00, "access": "RO",
            "reset_value": 0x00000000,
            "fields": [
                {"name": "init_done",          "bits": "0",    "access": "RO", "reset_value": 0},
                {"name": "cal_done",           "bits": "1",    "access": "RO", "reset_value": 0},
                {"name": "cal_fail",           "bits": "2",    "access": "RO", "reset_value": 0},
                {"name": "bist_done",          "bits": "3",    "access": "RO", "reset_value": 0},
                {"name": "bist_fail",          "bits": "4",    "access": "RO", "reset_value": 0},
                {"name": "ref_pending_cnt",    "bits": "7:5",  "access": "RO", "reset_value": 0},
                {"name": "self_refresh_active","bits": "8",    "access": "RO", "reset_value": 0},
                {"name": "reserved",           "bits": "31:9", "access": "RO", "reset_value": 0},
            ],
        },
        {
            "name": "CTRL_CONFIG", "offset": 0x04, "access": "RW",
            "reset_value": 0x00000009,
            # NOTE: spec JSON says 0x00000012 — that's WRONG.
            # Field reset values: sched_policy=1(bit0) + row_policy=0(bit1)
            #   + self_ref_mode=2(bits3:2) + ecc_enable=0(bit4)
            # = 1 + 0 + (2<<2) + 0 = 1 + 8 = 9 = 0x09
            # The spec value 0x12=0b10010 would mean sched_policy=0, row_policy=1,
            # ecc_enable=1, contradicting the field defs and controller_architecture.
            # Trust the field definitions → 0x09.
            "fields": [
                {"name": "sched_policy",   "bits": "0",    "access": "RW", "reset_value": 1},
                {"name": "row_policy",     "bits": "1",    "access": "RW", "reset_value": 0},
                {"name": "self_ref_mode",  "bits": "3:2",  "access": "RW", "reset_value": 2},
                {"name": "ecc_enable",     "bits": "4",    "access": "RW", "reset_value": 0},
                {"name": "bist_start",     "bits": "5",    "access": "WO", "reset_value": 0},
                {"name": "force_refresh",  "bits": "6",    "access": "WO", "reset_value": 0},
                {"name": "force_self_ref", "bits": "7",    "access": "WO", "reset_value": 0},
                {"name": "reserved",       "bits": "31:8", "access": "RO", "reset_value": 0},
            ],
        },
        {
            "name": "TIMING_0", "offset": 0x08, "access": "RW",
            "reset_value": 0x271C0B0B,  # NOTE: spec JSON says 0x0B0B1C27 — that's REVERSED.
            # Fields: tRCD=11 in bits[7:0], tRP=11 in bits[15:8],
            #         tRAS=28 in bits[23:16], tRC=39 in bits[31:24]
            # Correct: (39<<24)|(28<<16)|(11<<8)|11 = 0x271C0B0B
            "fields": [
                {"name": "tRCD_nCK", "bits": "7:0",   "access": "RW", "reset_value": 11},
                {"name": "tRP_nCK",  "bits": "15:8",  "access": "RW", "reset_value": 11},
                {"name": "tRAS_nCK", "bits": "23:16", "access": "RW", "reset_value": 28},
                {"name": "tRC_nCK",  "bits": "31:24", "access": "RW", "reset_value": 39},
            ],
        },
        {
            "name": "TIMING_1", "offset": 0x0C, "access": "RW",
            "reset_value": 0x80200606,
            "fields": [
                {"name": "tRRD_nCK", "bits": "7:0",   "access": "RW", "reset_value": 6},
                {"name": "tWTR_nCK", "bits": "15:8",  "access": "RW", "reset_value": 6},
                {"name": "tFAW_nCK", "bits": "23:16", "access": "RW", "reset_value": 32},
                {"name": "tRFC_nCK", "bits": "31:24", "access": "RW", "reset_value": 128},
            ],
        },
        {
            "name": "TIMING_2", "offset": 0x10, "access": "RW",
            "reset_value": 0x080B060C,
            "fields": [
                {"name": "tWR_nCK",  "bits": "7:0",   "access": "RW", "reset_value": 12},
                {"name": "tRTP_nCK", "bits": "15:8",  "access": "RW", "reset_value": 6},
                {"name": "CL_nCK",   "bits": "23:16", "access": "RW", "reset_value": 11},
                {"name": "CWL_nCK",  "bits": "31:24", "access": "RW", "reset_value": 8},
            ],
        },
        {
            "name": "TIMING_3", "offset": 0x14, "access": "RW",
            "reset_value": 0x00186004,  # NOTE: spec JSON says 0x00041860 — that's wrong.
            # Correct: tCCD=4 in bits[7:0] = 0x04, tREFI=6240 in bits[31:8] = 0x1860<<8
            # So reset = 0x00186004. The spec has a byte-swap bug. See note below.
            "fields": [
                {"name": "tCCD_nCK",  "bits": "7:0",  "access": "RW", "reset_value": 4},
                {"name": "tREFI_nCK", "bits": "31:8", "access": "RW", "reset_value": 6240},
            ],
        },
        {
            "name": "REFRESH_CONFIG", "offset": 0x18, "access": "RW",
            "reset_value": 0x00000168,
            # NOTE: spec says 0x00060608. Let's verify:
            # max_postpone=8 in bits[3:0] = 0x8
            # urgent_threshold=6 in bits[7:4] = 0x6 << 4 = 0x60
            # ref_priority=1 in bit[8] = 0x100
            # reserved=0 in bits[31:9]
            # Total = 0x100 + 0x60 + 0x8 = 0x168
            # Spec says 0x00060608 which doesn't match field layout.
            "fields": [
                {"name": "max_postpone",     "bits": "3:0", "access": "RW", "reset_value": 8},
                {"name": "urgent_threshold", "bits": "7:4", "access": "RW", "reset_value": 6},
                {"name": "ref_priority",     "bits": "8",   "access": "RW", "reset_value": 1},
                {"name": "reserved",         "bits": "31:9","access": "RO", "reset_value": 0},
            ],
        },
        {
            "name": "ERROR_STATUS", "offset": 0x1C, "access": "RW1C",
            "reset_value": 0x00000000,
            "fields": [
                {"name": "ecc_ce_count",  "bits": "15:0",  "access": "RO",   "reset_value": 0},
                {"name": "ecc_ue_flag",   "bits": "16",    "access": "RW1C", "reset_value": 0},
                {"name": "ref_starve_flag","bits": "17",    "access": "RW1C", "reset_value": 0},
                {"name": "init_fail_flag","bits": "18",     "access": "RW1C", "reset_value": 0},
                {"name": "bist_fail_addr","bits": "31:19",  "access": "RO",   "reset_value": 0},
            ],
        },
        {
            "name": "BIST_CONFIG", "offset": 0x20, "access": "RW",
            "reset_value": 0x00000000,
            "fields": [
                {"name": "bist_pattern",  "bits": "2:0", "access": "RW", "reset_value": 0},
                {"name": "bist_addr_mode","bits": "3",   "access": "RW", "reset_value": 0},
                {"name": "reserved",      "bits": "31:4","access": "RO", "reset_value": 0},
            ],
        },
        {
            "name": "BIST_ADDR_START", "offset": 0x24, "access": "RW",
            "reset_value": 0x00000000,
            "fields": [
                {"name": "start_addr", "bits": "28:0",  "access": "RW", "reset_value": 0},
                {"name": "reserved",   "bits": "31:29", "access": "RO", "reset_value": 0},
            ],
        },
        {
            "name": "BIST_ADDR_END", "offset": 0x28, "access": "RW",
            "reset_value": 0x1FFFFFFF,
            "fields": [
                {"name": "end_addr", "bits": "28:0",  "access": "RW", "reset_value": 536870911},
                {"name": "reserved", "bits": "31:29", "access": "RO", "reset_value": 0},
            ],
        },
    ]

    def __init__(self):
        self.registers: dict[int, Register] = {}
        self._build_registers()

    def _build_registers(self):
        for rdef in self.REGISTER_DEFS:
            fields = [
                Field(f["name"], f["bits"], f["access"], f["reset_value"])
                for f in rdef["fields"]
            ]
            reg = Register(
                name=rdef["name"],
                offset=rdef["offset"],
                access=rdef["access"],
                reset_value=rdef["reset_value"],
                fields=fields,
            )
            self.registers[rdef["offset"]] = reg

    def reset(self):
        """Reset all registers to power-on values."""
        for reg in self.registers.values():
            reg.reset()

    def write(self, addr: int, data: int) -> bool:
        """
        Write to a CSR register. Returns True if address is valid.
        Access rules enforced per-field.
        """
        reg = self.registers.get(addr)
        if reg is None:
            return False  # unmapped address
        reg.write(data)
        return True

    def read(self, addr: int) -> tuple[bool, int]:
        """
        Read a CSR register. Returns (valid, data).
        WO fields read as 0.
        """
        reg = self.registers.get(addr)
        if reg is None:
            return False, 0  # unmapped address
        return True, reg.read()

    def inject_status(self, reg_name: str, field_name: str, value: int):
        """Update an RO status field from external hardware signals."""
        for reg in self.registers.values():
            if reg.name == reg_name:
                reg.inject_status(field_name, value)
                return
        raise ValueError(f"No register named '{reg_name}'")

    def get_field(self, reg_name: str, field_name: str) -> int:
        """Read a specific field value (for test assertions)."""
        for reg in self.registers.values():
            if reg.name == reg_name:
                for f in reg.fields:
                    if f.name == field_name:
                        return (reg.value >> f.lo) & ((1 << f.width) - 1)
                raise ValueError(f"No field '{field_name}' in '{reg_name}'")
        raise ValueError(f"No register '{reg_name}'")

    def dump(self) -> dict:
        """Dump all register values for debug."""
        return {
            reg.name: {
                "offset": f"0x{reg.offset:02X}",
                "value": f"0x{reg.value:08X}",
                "read_value": f"0x{reg.read():08X}",
            }
            for reg in self.registers.values()
        }


# ---------------------------------------------------------------------------
# Vector generation helper
# ---------------------------------------------------------------------------

def generate_config_regs_vectors(model: ConfigRegsModel) -> list[dict]:
    """
    Generate a systematic vector suite for config_regs scope.
    
    Each vector is: {cycle, op, addr, wdata, expected_rdata}
    op: 'R' = read, 'W' = write, 'RST' = reset
    
    Returns a list of vectors that can be serialized to CSV
    for consumption by the SystemVerilog testbench.
    """
    vectors = []
    cycle = 0

    def add(op, addr=0, wdata=0, expected=0, comment=""):
        nonlocal cycle
        vectors.append({
            "cycle": cycle,
            "op": op,
            "addr": f"0x{addr:02X}",
            "wdata": f"0x{wdata:08X}",
            "expected_rdata": f"0x{expected:08X}",
            "comment": comment,
        })
        cycle += 1

    # --- TEST 1: Reset values ---
    model.reset()
    add("RST", comment="Assert reset")
    for reg in model.registers.values():
        _, rdata = model.read(reg.offset)
        add("R", reg.offset, 0, rdata,
            f"Read {reg.name} after reset → expect 0x{rdata:08X}")

    # --- TEST 2: Write all-ones to every register, verify access rules ---
    for reg in model.registers.values():
        model.write(reg.offset, 0xFFFFFFFF)
        _, rdata = model.read(reg.offset)
        add("W", reg.offset, 0xFFFFFFFF, 0,
            f"Write 0xFFFFFFFF to {reg.name}")
        add("R", reg.offset, 0, rdata,
            f"Read {reg.name} → expect 0x{rdata:08X} (access rules applied)")

    # --- TEST 3: Reset and verify clean state ---
    model.reset()
    add("RST", comment="Assert reset again")
    for reg in model.registers.values():
        _, rdata = model.read(reg.offset)
        add("R", reg.offset, 0, rdata,
            f"Read {reg.name} after 2nd reset → expect 0x{rdata:08X}")

    # --- TEST 4: Write all-zeros to every register ---
    for reg in model.registers.values():
        model.write(reg.offset, 0x00000000)
        _, rdata = model.read(reg.offset)
        add("W", reg.offset, 0x00000000, 0,
            f"Write 0x00000000 to {reg.name}")
        add("R", reg.offset, 0, rdata,
            f"Read {reg.name} → expect 0x{rdata:08X}")

    # --- TEST 5: RW1C behavior on ERROR_STATUS ---
    model.reset()
    add("RST", comment="Reset for RW1C test")

    # Inject error flags (simulating hardware setting them)
    model.inject_status("ERROR_STATUS", "ecc_ue_flag", 1)
    model.inject_status("ERROR_STATUS", "ref_starve_flag", 1)
    model.inject_status("ERROR_STATUS", "init_fail_flag", 1)
    _, rdata = model.read(0x1C)
    add("R", 0x1C, 0, rdata,
        f"Read ERROR_STATUS with flags set → 0x{rdata:08X}")

    # Clear only ecc_ue_flag by writing 1 to bit 16
    model.write(0x1C, 0x00010000)
    _, rdata = model.read(0x1C)
    add("W", 0x1C, 0x00010000, 0, "Write 1 to ecc_ue_flag (clear it)")
    add("R", 0x1C, 0, rdata,
        f"Read ERROR_STATUS → ecc_ue cleared, others remain: 0x{rdata:08X}")

    # Clear remaining flags
    model.write(0x1C, 0x00060000)
    _, rdata = model.read(0x1C)
    add("W", 0x1C, 0x00060000, 0, "Write 1 to ref_starve + init_fail (clear)")
    add("R", 0x1C, 0, rdata,
        f"Read ERROR_STATUS → all cleared: 0x{rdata:08X}")

    # --- TEST 6: WO self-clear on CTRL_CONFIG ---
    model.reset()
    add("RST", comment="Reset for WO test")

    # Write bist_start (bit 5) and force_refresh (bit 6)
    model.write(0x04, 0x00000060)
    _, rdata = model.read(0x04)
    add("W", 0x04, 0x00000060, 0, "Write bist_start + force_refresh (WO)")
    add("R", 0x04, 0, rdata,
        f"Read CTRL_CONFIG → WO bits self-cleared: 0x{rdata:08X}")

    # --- TEST 7: Partial field writes (TIMING registers) ---
    model.reset()
    add("RST", comment="Reset for partial write test")

    # Write only tRCD field (bits 7:0) to a new value, keep others at reset
    model.write(0x08, 0x0B0B1C0F)  # change tRCD from 11 to 15
    _, rdata = model.read(0x08)
    add("W", 0x08, 0x0B0B1C0F, 0, "Write TIMING_0: tRCD=15, rest same")
    add("R", 0x08, 0, rdata, f"Read TIMING_0 → 0x{rdata:08X}")

    # --- TEST 8: Unmapped address ---
    # Address 0x2C is beyond our register map
    valid = model.write(0x2C, 0xDEADBEEF)
    add("W", 0x2C, 0xDEADBEEF, 0,
        f"Write unmapped addr 0x2C → valid={valid}")
    rvalid, rdata = model.read(0x2C)
    add("R", 0x2C, 0, rdata,
        f"Read unmapped addr 0x2C → valid={rvalid}, data=0x{rdata:08X}")

    return vectors


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def run_self_test():
    """Verify the reference model against known-good expected values."""
    model = ConfigRegsModel()
    passed = 0
    failed = 0

    def check(desc, got, expected):
        nonlocal passed, failed
        if got == expected:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {desc}: got 0x{got:08X}, expected 0x{expected:08X}")

    print("=" * 60)
    print("Config Regs Reference Model — Self-Test")
    print("=" * 60)

    # 1. Reset values
    print("\n[1] Reset values...")
    check("CTRL_STATUS reset",  model.read(0x00)[1], 0x00000000)
    check("CTRL_CONFIG reset",  model.read(0x04)[1], 0x00000009)
    # CTRL_CONFIG: sched_policy=1(bit0) + self_ref_mode=2(bits3:2)=0b10<<2=0x08
    # Wait: 1 + (2<<2) = 1 + 8 = 9? But spec says 0x12 = 18 = 0b10010
    # bit0=0, bit1=1, bits3:2=00, bit4=1 → row_policy=1, ecc_enable=1?
    # Actually 0x12 = 0b00010010: bit0=0,bit1=1,bit2=0,bit3=0,bit4=1
    # That would be sched_policy=0, row_policy=1, self_ref_mode=0, ecc_enable=1
    # But the spec field reset values say: sched_policy=1, row_policy=0, self_ref_mode=2, ecc_enable=0
    # 1 + (0<<1) + (2<<2) + (0<<4) = 1 + 0 + 8 + 0 = 9 = 0x09
    # 0x12 ≠ 0x09. This is ANOTHER spec inconsistency.
    # The field reset values compute to 0x09, but the register reset is listed as 0x12.
    # We trust the field definitions → computed reset = 0x09.

    check("TIMING_0 reset",     model.read(0x08)[1], 0x271C0B0B)
    check("TIMING_1 reset",     model.read(0x0C)[1], 0x80200606)
    check("TIMING_2 reset",     model.read(0x10)[1], 0x080B060C)
    check("TIMING_3 reset",     model.read(0x14)[1], 0x00186004)
    check("REFRESH_CONFIG reset", model.read(0x18)[1], 0x00000168)
    check("ERROR_STATUS reset", model.read(0x1C)[1], 0x00000000)
    check("BIST_CONFIG reset",  model.read(0x20)[1], 0x00000000)
    check("BIST_ADDR_START reset", model.read(0x24)[1], 0x00000000)
    check("BIST_ADDR_END reset",   model.read(0x28)[1], 0x1FFFFFFF)

    # 2. RO register ignores writes
    print("\n[2] CTRL_STATUS (RO) ignores writes...")
    model.write(0x00, 0xFFFFFFFF)
    check("CTRL_STATUS after write 0xFFFFFFFF", model.read(0x00)[1], 0x00000000)

    # 3. RW register accepts writes
    print("\n[3] TIMING_0 (RW) full write...")
    model.write(0x08, 0xAABBCCDD)
    check("TIMING_0 after write", model.read(0x08)[1], 0xAABBCCDD)
    model.reset()

    # 4. RW1C behavior
    print("\n[4] ERROR_STATUS (RW1C)...")
    model.inject_status("ERROR_STATUS", "ecc_ue_flag", 1)
    model.inject_status("ERROR_STATUS", "ref_starve_flag", 1)
    check("ERROR_STATUS flags set", model.read(0x1C)[1], 0x00030000)

    model.write(0x1C, 0x00010000)  # clear only ecc_ue
    check("After clearing ecc_ue", model.read(0x1C)[1], 0x00020000)

    model.write(0x1C, 0x00020000)  # clear ref_starve
    check("After clearing ref_starve", model.read(0x1C)[1], 0x00000000)
    model.reset()

    # 5. WO self-clear
    print("\n[5] CTRL_CONFIG WO fields self-clear...")
    model.write(0x04, 0x00000060)  # bist_start + force_refresh
    rdata = model.read(0x04)[1]
    # WO bits self-clear to 0, and the RW fields (bits 4:0) were overwritten to 0
    # because 0x60 has bits 4:0 = 0. So entire register reads as 0.
    check("CTRL_CONFIG WO self-cleared", rdata, 0x00000000)
    model.reset()

    # 6. Reserved/RO fields in mixed register
    print("\n[6] BIST_ADDR_START reserved bits...")
    model.write(0x24, 0xFFFFFFFF)
    check("BIST_ADDR_START (29-bit addr, reserved upper)",
          model.read(0x24)[1], 0x1FFFFFFF)  # bits 31:29 are RO=0
    model.reset()

    # 7. Unmapped address
    print("\n[7] Unmapped address...")
    valid = model.write(0x2C, 0x12345678)
    check("Write unmapped returns False", int(valid), 0)
    rvalid, rdata = model.read(0x2C)
    check("Read unmapped returns False", int(rvalid), 0)

    # 8. Status injection
    print("\n[8] Status injection...")
    model.inject_status("CTRL_STATUS", "init_done", 1)
    model.inject_status("CTRL_STATUS", "cal_done", 1)
    model.inject_status("CTRL_STATUS", "ref_pending_cnt", 5)
    rdata = model.read(0x00)[1]
    # bit0=1 (init_done) + bit1=1 (cal_done) + bits7:5=5 (ref_pending_cnt)=5<<5=0xA0
    check("CTRL_STATUS with injected status", rdata, 0x000000A3)

    # Summary
    print("\n" + "=" * 60)
    total = passed + failed
    print(f"Results: {passed}/{total} passed, {failed} failed")
    if failed == 0:
        print("ALL TESTS PASSED ✓")
    else:
        print(f"*** {failed} TESTS FAILED ***")
    print("=" * 60)

    return failed == 0


if __name__ == "__main__":
    if run_self_test():
        print("\nGenerating vector suite...")
        model = ConfigRegsModel()
        vectors = generate_config_regs_vectors(model)
        print(f"Generated {len(vectors)} vectors")
        for v in vectors[:10]:
            print(f"  [{v['cycle']:3d}] {v['op']:3s} addr={v['addr']} "
                  f"wdata={v['wdata']} exp={v['expected_rdata']}  // {v['comment']}")
        print(f"  ... ({len(vectors) - 10} more)")