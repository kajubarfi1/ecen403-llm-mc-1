#!/usr/bin/env python3
"""
+======================================================================+
|                  DDR3 JEDEC LOOKUP TABLES                            |
|                                                                      |
|  Deterministic. No LLM. No I/O. Pure functions + data.               |
|                                                                      |
|  This is the "device knowledge base" the microarchitecture compiler  |
|  uses to turn Tier-1 user choices (speed grade, density, device      |
|  width) into JEDEC-correct timing/geometry numbers. It formalizes    |
|  the tables written in prose in Spec/customizable_parameters_guide.md |
|                                                                      |
|  NOTE ON PRECISION: the speed-bin CL/tRCD/tRP/tRAS and tFAW values   |
|  below are the canonical representative bins. Cross-check against     |
|  JEDEC JESD79-3 (and the specific Micron/Samsung/Hynix datasheet)    |
|  before taping anything out. The golden config (DDR3-1600K / 2Gb /   |
|  x8) is verified to reproduce Spec/llmmc_microarchitecturespec_      |
|  filled.json exactly -- see microarch_compiler.py --selftest.        |
+======================================================================+
"""
from __future__ import annotations
import math

# ----------------------------------------------------------------------
# Speed grades -- one canonical JEDEC bin per grade.
#   tCK_ns          : clock period at the rated data rate
#   data_rate_MTps  : DDR transfer rate
#   CL              : CAS latency in nCK (from the speed bin)
#   tRCD_ns/tRP_ns  : RAS-to-CAS / row precharge (absolute ns, from bin)
#   tRAS_ns         : row active time (absolute ns, from bin)
#   speed_bin_label : human label matching the datasheet bin
# ----------------------------------------------------------------------
SPEED_GRADES: dict[str, dict] = {
    "DDR3-800": {
        "tCK_ns": 2.5, "data_rate_MTps": 800.0, "CL": 6,
        "tRCD_ns": 15.0, "tRP_ns": 15.0, "tRAS_ns": 37.5,
        "speed_bin_label": "DDR3-800E (6-6-6)",
    },
    "DDR3-1066": {
        "tCK_ns": 1.875, "data_rate_MTps": 1066.0, "CL": 8,
        "tRCD_ns": 15.0, "tRP_ns": 15.0, "tRAS_ns": 37.5,
        "speed_bin_label": "DDR3-1066G (8-8-8)",
    },
    "DDR3-1333": {
        "tCK_ns": 1.5, "data_rate_MTps": 1333.0, "CL": 9,
        "tRCD_ns": 13.5, "tRP_ns": 13.5, "tRAS_ns": 36.0,
        "speed_bin_label": "DDR3-1333H (9-9-9)",
    },
    "DDR3-1600": {
        "tCK_ns": 1.25, "data_rate_MTps": 1600.0, "CL": 11,
        "tRCD_ns": 13.75, "tRP_ns": 13.75, "tRAS_ns": 35.0,
        "speed_bin_label": "DDR3-1600K (11-11-11)",
    },
}

# Refresh cycle time by device density (ns) -- JEDEC JESD79-3, normal temp.
TRFC_NS_BY_DENSITY: dict[str, float] = {
    "1Gb": 110.0,
    "2Gb": 160.0,
    "4Gb": 260.0,
    "8Gb": 350.0,
}

# Total device density in bits.
DENSITY_BITS: dict[str, int] = {
    "1Gb": 2 ** 30,
    "2Gb": 2 ** 31,
    "4Gb": 2 ** 32,
    "8Gb": 2 ** 33,
}

# JEDEC fixed / grade-independent constants.
TWR_NS = 15.0        # write recovery -- fixed across all DDR3 speed grades
TREFI_NS = 7800.0    # average refresh interval, 7.8 us for Tcase <= 85 C
BANK_BITS = 3        # DDR3 is always 8 banks
CLOCK_RATIO_DDR_TO_CTRL = 4   # this design is a 4:1 controller

DDR3_SPEED_GRADE_CHOICES = tuple(SPEED_GRADES.keys())
DDR3_DENSITY_CHOICES = tuple(DENSITY_BITS.keys())
DDR3_DEVICE_WIDTH_CHOICES = ("x8", "x16")


# ----------------------------------------------------------------------
# Conversion helper -- the one rule the whole spec is built on:
#     nCK = ceil(param_ns / tCK_ns)      (conversion_rules.rounding_rule)
# The round() guards against floating-point noise (e.g. 11.00000002)
# tipping a clean integer up to the next cycle.
# ----------------------------------------------------------------------
def ns_to_nck(ns: float, tCK_ns: float) -> int:
    return math.ceil(round(ns / tCK_ns, 6))


def device_width_bits(device_width: str) -> int:
    return {"x4": 4, "x8": 8, "x16": 16}[device_width]


def page_size_bytes_per_device(device_width: str) -> int:
    """DDR3 page size: x4/x8 -> 1 KB, x16 -> 2 KB."""
    return 2048 if device_width == "x16" else 1024


def column_bits(device_width: str) -> int:
    dw = device_width_bits(device_width)
    cols = page_size_bytes_per_device(device_width) * 8 // dw
    return int(round(math.log2(cols)))


def row_bits(density: str, device_width: str) -> int:
    """Rows implied by density once banks, columns and device width are fixed."""
    total = DENSITY_BITS[density]
    dw = device_width_bits(device_width)
    rows = total // dw // (2 ** BANK_BITS) // (2 ** column_bits(device_width))
    return int(round(math.log2(rows)))


def cwl_cycles(tCK_ns: float) -> int:
    """JEDEC DDR3 CAS write latency table, keyed by tCK."""
    if tCK_ns >= 2.5:
        return 5
    if tCK_ns >= 1.875:
        return 6
    if tCK_ns >= 1.5:
        return 7
    if tCK_ns >= 1.25:
        return 8
    if tCK_ns >= 1.071:
        return 9
    return 10


def trrd_ns(tCK_ns: float, device_width: str) -> float:
    """ACTIVATE-to-ACTIVATE (different bank). Floor is page-size dependent."""
    floor = 10.0 if device_width == "x16" else 7.5
    return max(4.0 * tCK_ns, floor)


def tccd_ns(tCK_ns: float) -> float:
    """CAS-to-CAS: always 4 nCK for BL8."""
    return 4.0 * tCK_ns


def twtr_ns(tCK_ns: float) -> float:
    return max(4.0 * tCK_ns, 7.5)


def trtp_ns(tCK_ns: float) -> float:
    return max(4.0 * tCK_ns, 7.5)


def tfaw_ns(speed_grade: str, device_width: str) -> float:
    """Four-ACTIVATE window -- JEDEC table, page-size dependent."""
    table_1kb = {"DDR3-800": 40.0, "DDR3-1066": 50.0, "DDR3-1333": 45.0, "DDR3-1600": 40.0}
    table_2kb = {"DDR3-800": 50.0, "DDR3-1066": 50.0, "DDR3-1333": 45.0, "DDR3-1600": 40.0}
    table = table_2kb if device_width == "x16" else table_1kb
    return table[speed_grade]


def timing_model_ns(speed_grade: str, density: str, device_width: str) -> dict:
    """
    Full absolute-ns timing set for a (speed grade, density, device width).
    Mirrors the shape of Spec/*.json -> timing_model (the non-$ keys).
    """
    g = SPEED_GRADES[speed_grade]
    tCK = g["tCK_ns"]
    tRP = g["tRP_ns"]
    tRAS = g["tRAS_ns"]
    return {
        "units": "ns",
        "tCK_ns": tCK,
        "speed_bin": g["speed_bin_label"],
        "tRCD": g["tRCD_ns"],
        "tRP": tRP,
        "tRAS": tRAS,
        "tRC": round(tRAS + tRP, 6),
        "tRFC": TRFC_NS_BY_DENSITY[density],
        "tFAW": tfaw_ns(speed_grade, device_width),
        "tRRD": trrd_ns(tCK, device_width),
        "tWR": TWR_NS,
        "tWTR": twtr_ns(tCK),
        "tRTP": trtp_ns(tCK),
        "tCCD": tccd_ns(tCK),
        "tREFI": TREFI_NS,
        "CL_cycles": g["CL"],
        "CWL_cycles": cwl_cycles(tCK),
    }


def derived_cycles(tm_ns: dict) -> dict:
    """timing_model.$derived_cycles -- the load-bearing block every agent reads."""
    tCK = tm_ns["tCK_ns"]
    keys = ["tRCD", "tRP", "tRAS", "tRC", "tRFC", "tFAW", "tRRD",
            "tWR", "tWTR", "tRTP", "tCCD", "tREFI"]
    out = {f"{k}_nCK": ns_to_nck(tm_ns[k], tCK) for k in keys}
    out["CL_ns"] = round(tm_ns["CL_cycles"] * tCK, 6)
    out["CWL_ns"] = round(tm_ns["CWL_cycles"] * tCK, 6)
    out["$comment"] = f"All computed via ceil(param_ns / {tCK})."
    return out


if __name__ == "__main__":
    # Sanity dump for the golden config.
    tm = timing_model_ns("DDR3-1600", "2Gb", "x8")
    dc = derived_cycles(tm)
    print("timing_model (ns):")
    for k, v in tm.items():
        print(f"  {k:14s} {v}")
    print("\n$derived_cycles:")
    for k, v in dc.items():
        print(f"  {k:14s} {v}")
    print(f"\nrow_bits(2Gb,x8)   = {row_bits('2Gb', 'x8')}   (golden: 15)")
    print(f"column_bits(x8)    = {column_bits('x8')}   (golden: 10)")
