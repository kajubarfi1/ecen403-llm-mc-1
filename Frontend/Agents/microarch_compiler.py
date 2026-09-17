#!/usr/bin/env python3
"""
+======================================================================+
|              MICROARCHITECTURE SPEC COMPILER                         |
|                                                                      |
|  Deterministic. No LLM.                                              |
|                                                                      |
|  compile_spec(choices) -> {                                          |
|      ok, errors, warnings, resolved_choices,                         |
|      spec, consistency_checks, consistency_ok                        |
|  }                                                                   |
|                                                                      |
|  Takes a resolved Tier-1/2/3 choice dict and produces a complete,    |
|  schema-shaped microarchitecture spec with every $derived /          |
|  $derived_cycles block the Phase 1-4 agents index into directly      |
|  (see the earlier "how agents use the spec" audit -- those blocks    |
|  are load-bearing, not documentation).                               |
|                                                                      |
|  Three jobs:                                                         |
|    1. VALIDITY MATRIX  -- reject Tier-1 combos the design can't       |
|       actually build (like Xilinx MIG's picker), with a reason.      |
|    2. DERIVE + ASSEMBLE -- JEDEC lookup (microarch_jedec) + geometry  |
|       math -> full spec, CSR reset values repacked from the numbers. |
|    3. CONSISTENCY CHECKS -- executable version of the golden spec's   |
|       $consistency_checks / $cross_checks comments.                  |
|                                                                      |
|  Plus modifiability_report(): which spec fields a user can change     |
|  without rippling through every module (blast-radius classification). |
|                                                                      |
|  CLI:                                                                 |
|    python microarch_compiler.py --selftest                           |
|    python microarch_compiler.py --preset balanced --out ./builds/bal |
|    python microarch_compiler.py --from-choices choices.json --out ... |
|    python microarch_compiler.py --list-modifiable                     |
+======================================================================+
"""
from __future__ import annotations

import argparse
import copy
import json
import math
import sys
from pathlib import Path

import microarch_jedec as jd


# ======================================================================
# CHOICE SPACE
# ======================================================================
# Tier-1: high blast radius. A user must pick these (or accept a preset).
TIER1_CHOICES = {
    "speed_grade": list(jd.DDR3_SPEED_GRADE_CHOICES),
    "density": list(jd.DDR3_DENSITY_CHOICES),
    "device_width": list(jd.DDR3_DEVICE_WIDTH_CHOICES),
    "ranks": [1, 2, 3, 4],
    "byte_lanes": [1, 2, 3, 4, 5, 6, 7, 8],
    "ecc_mode": [0, 1, 2, 3],
    "scheduler_policy": ["in_order", "fr_fcfs"],
    "row_policy": ["open_page", "close_page"],
}

# Tier-2: medium blast radius. Defaulted; user may override.
TIER2_DEFAULTS = {
    "command_queue_depth": 16,      # power of 2, 4..32
    "lookahead_depth": 8,           # 0..16, <= queue depth
    "address_mapping": "row-bank-column",
    "burst_length": 8,             # 4 or 8
    "host_data_width": 32,          # 32 / 64 / 128
    "read_buffer_depth": 16,        # 4..64
    "write_buffer_depth": 16,       # 4..64
    "interface_type": "wishbone_pipelined",
    "self_refresh_mode": "auto",   # disabled / manual / auto
}

# Tier-3: implementation tuning. Backend-facing; mostly ignored by the
# frontend RTL agents today.
TIER3_DEFAULTS = {
    "target_frequency_mhz": None,   # None -> derived controller frequency
    "area_optimization_goal": "balanced",     # area / balanced / performance
    "power_optimization_goal": "balanced",    # low_power / balanced / performance
    "pipeline_latency_cycles": 2,   # 1..4
}

PRESETS = {
    # From Spec/customizable_parameters_guide.md, "Cost vs Performance Presets".
    "low-cost-embedded": dict(
        speed_grade="DDR3-800", density="2Gb", device_width="x8", ranks=1,
        byte_lanes=1, ecc_mode=0, scheduler_policy="in_order",
        row_policy="close_page", command_queue_depth=4, lookahead_depth=0,
    ),
    "balanced": dict(
        speed_grade="DDR3-1333", density="2Gb", device_width="x8", ranks=1,
        byte_lanes=2, ecc_mode=0, scheduler_policy="fr_fcfs",
        row_policy="open_page", command_queue_depth=16, lookahead_depth=8,
    ),
    "default": dict(
        speed_grade="DDR3-1600", density="2Gb", device_width="x8", ranks=1,
        byte_lanes=2, ecc_mode=0, scheduler_policy="fr_fcfs",
        row_policy="open_page", command_queue_depth=16, lookahead_depth=8,
    ),
    "high-performance": dict(
        speed_grade="DDR3-1600", density="4Gb", device_width="x8", ranks=2,
        byte_lanes=4, ecc_mode=1, scheduler_policy="fr_fcfs",
        row_policy="open_page", command_queue_depth=32, lookahead_depth=16,
    ),
    "server-grade": dict(
        speed_grade="DDR3-1600", density="4Gb", device_width="x8", ranks=4,
        byte_lanes=8, ecc_mode=1, scheduler_policy="fr_fcfs",
        row_policy="open_page", command_queue_depth=32, lookahead_depth=16,
    ),
}


# ======================================================================
# BLAST-RADIUS CLASSIFICATION
#   "isolated"    -- change the value, RTL structure / ports / widths are
#                    untouched; at most a constant, a CSR reset value, or
#                    a backend hint changes. Cheapest to vary.
#   "regen_local" -- a few modules' *parameters* (widths, FIFO depths)
#                    change and those modules regenerate, but port NAMES
#                    and the cross-module interface stay stable.
#   "structural"  -- bus widths / address widths / geometry / port lists
#                    change; ripples across most modules and the
#                    cross-phase lint must re-pass. Most expensive.
#   "unsupported" -- current RTL agents do not implement this axis;
#                    compiler rejects it outright.
# ======================================================================
BLAST_RADIUS = {
    # ---- isolated -------------------------------------------------------
    "area_optimization_goal": ("isolated",
        "Backend synthesis hint only. Frontend RTL agents ignore it."),
    "power_optimization_goal": ("isolated",
        "Backend synthesis hint only. Frontend RTL agents ignore it."),
    "target_frequency_mhz": ("isolated",
        "Backend timing-closure goal. No RTL change as long as it stays "
        ">= the controller clock the speed grade needs."),
    "max_postpone_count": ("isolated",
        "Refresh policy constant + REFRESH_CONFIG reset value. Fits the "
        "existing 4-bit CSR field; no port change."),
    "urgent_threshold": ("isolated",
        "Refresh policy constant + REFRESH_CONFIG reset value. Existing "
        "4-bit field."),
    "bist_config": ("isolated",
        "BIST pattern / address range. Existing CSR fields, no port change."),
    "error_handling": ("isolated",
        "Behavioural selectors in refresh_ctrl / data_path; no interface "
        "change."),
    "reset_hold_us": ("isolated",
        "Counter compare value in init_fsm. No port change while it fits "
        "the counter width."),
    "cke_delay_us": ("isolated",
        "Counter compare value in init_fsm."),
    "periodic_zqcs_interval": ("isolated",
        "Counter compare value in calibration / scheduler."),
    # ---- regen_local -------------------------------------------------
    "command_queue_depth": ("regen_local",
        "Drives queue_index_bits -> cmd_queue + scheduler parameter widths. "
        "Port names stable. Must be a power of 2."),
    "lookahead_depth": ("regen_local",
        "Drives lookahead_index_bits -> scheduler. Port names stable."),
    "read_buffer_depth": ("regen_local",
        "wb_port / data_path read-return FIFO depth. Local parameter."),
    "write_buffer_depth": ("regen_local",
        "wb_port / data_path write FIFO depth. Local parameter."),
    "scheduler_policy": ("regen_local",
        "scheduler behaviour + CTRL_CONFIG.sched_policy reset bit (bit "
        "already exists). No port change."),
    "row_policy": ("regen_local",
        "scheduler / bank_tracker behaviour + CTRL_CONFIG.row_policy reset "
        "bit. No port change."),
    "self_refresh_mode": ("regen_local",
        "refresh_ctrl behaviour + CTRL_CONFIG.self_ref_mode reset field. "
        "No port change."),
    "address_mapping": ("regen_local",
        "addr_decoder bit-slicing logic changes; its port list stays the "
        "same."),
    "pipeline_latency_cycles": ("regen_local",
        "Adds/removes pipeline registers -> latency_model + data_path. "
        "Interface stable."),
    # ---- structural -------------------------------------------------
    "speed_grade": ("structural",
        "Every timing constant, tCK, all clock periods, CL/CWL, mode "
        "registers, TIMING_* CSR reset values, latency model. Touches "
        "timing / init_fsm / config_regs / scheduler / bank_tracker / "
        "data_path."),
    "density": ("structural",
        "Changes row_bits -> address_width_bits -> addr_decoder, "
        "bank_tracker, every module carrying a row-address port, and the "
        "BIST address range. tRFC also changes."),
    "byte_lanes": ("structural",
        "Changes channel_data_width -> data_path packing, phy_interface, "
        "addr_decoder, host burst sizing, capacity/address width."),
    "device_width": ("structural",
        "x8 vs x16 changes page size -> column_bits, row_bits, "
        "channel width. Ripples like density."),
    "burst_length": ("structural",
        "BL4 vs BL8 changes tCCD, data-beat count, data_path packing and "
        "the latency model."),
    "host_data_width": ("structural",
        "wb_port bus width, wb_sel width, data_path pack_mode, and every "
        "host-facing port."),
    "interface_type": ("structural",
        "wishbone_classic vs _pipelined changes the wb_port protocol FSM "
        "and stall semantics."),
    "ecc_mode": ("structural",
        "ECC on consumes a byte lane and widens the data_path with "
        "SEC-DED logic; changes channel data width and ERROR_STATUS use."),
    # ---- unsupported ----------------------------------------------
    "ranks": ("unsupported",
        "ranks > 1: current RTL agents assume a single rank "
        "(bank_tracker / addr_decoder have no rank dimension, no ODT / "
        "rank-switch handling)."),
    "num_ports": ("unsupported",
        "num_ports > 1: only a single Wishbone host port is implemented "
        "(no arbiter instancing in wb_port)."),
}


# ======================================================================
# VALIDITY MATRIX
# ======================================================================
def _is_pow2(n: int) -> bool:
    return isinstance(n, int) and n > 0 and (n & (n - 1)) == 0


def validate_choices(choices: dict) -> tuple[list[str], list[str], dict]:
    """
    Returns (errors, warnings, resolved).

    errors   -> blocking. compile_spec will refuse; the intake agent
                should revise or re-prompt the user.
    warnings -> non-blocking; surfaced in the report.
    resolved -> choices with Tier-2/3 defaults filled in.
    """
    errors: list[str] = []
    warnings: list[str] = []

    r = {}
    r.update(TIER2_DEFAULTS)
    r.update(TIER3_DEFAULTS)
    r.update({k: v for k, v in choices.items() if v is not None})

    # ---- required Tier-1 present + in range --------------------------
    for key, allowed in TIER1_CHOICES.items():
        if key not in r:
            errors.append(f"missing Tier-1 choice: {key} (one of {allowed})")
        elif r[key] not in allowed:
            errors.append(f"{key}={r[key]!r} invalid; must be one of {allowed}")

    # Bail early if Tier-1 is malformed -- later checks would KeyError.
    if errors:
        return errors, warnings, r

    # ---- unsupported axes -------------------------------------------
    if r["ranks"] > 1:
        errors.append(BLAST_RADIUS["ranks"][1])
    if int(r.get("num_ports", 1)) > 1:
        errors.append(BLAST_RADIUS["num_ports"][1])

    # ---- ECC ------------------------------------------------------
    if r["ecc_mode"] > 0:
        if r["byte_lanes"] < 2:
            errors.append(
                "ecc_mode>0 needs a dedicated ECC lane: byte_lanes must be >= 2")
        elif not _is_pow2(r["byte_lanes"] - 1):
            errors.append(
                f"ecc_mode>0: data lanes after the ECC lane "
                f"(byte_lanes-1={r['byte_lanes']-1}) must be a power of 2")
        warnings.append(
            "ecc_mode>0: SEC-DED datapath widening is only partially wired "
            "in data_path_agent -- verify generated RTL before trusting it")

    # ---- byte lanes --------------------------------------------------
    if r["byte_lanes"] not in (1, 2, 4, 8):
        warnings.append(
            f"byte_lanes={r['byte_lanes']} is unusual (expected 1/2/4/8); "
            "channel width will not be a power of 2")

    # ---- queue / lookahead ----------------------------------------
    q = r["command_queue_depth"]
    if not (_is_pow2(q) and 4 <= q <= 32):
        errors.append(
            f"command_queue_depth={q} must be a power of 2 in [4, 32] "
            "(queue_index_bits = log2 of it)")
    la = r["lookahead_depth"]
    if not (isinstance(la, int) and 0 <= la <= 16):
        errors.append(f"lookahead_depth={la} must be an integer in [0, 16]")
    elif _is_pow2(q) and la > q:
        errors.append(
            f"lookahead_depth={la} cannot exceed command_queue_depth={q}")

    if r["scheduler_policy"] == "in_order" and _is_pow2(q) and q > 8:
        warnings.append(
            f"in_order scheduler with command_queue_depth={q}: the extra "
            "queue entries can't be reordered -- wasted area")
    if r["scheduler_policy"] == "fr_fcfs" and la == 0:
        warnings.append(
            "fr_fcfs scheduler with lookahead_depth=0: the scheduler has "
            "nothing to look ahead into -- behaves close to in_order")
    if r["row_policy"] == "close_page" and la > 4:
        warnings.append(
            "close_page with a deep lookahead: row-hit reordering has "
            "limited benefit when every access auto-precharges")

    # ---- burst length ------------------------------------------------
    if r["burst_length"] not in (4, 8):
        errors.append(f"burst_length={r['burst_length']} must be 4 or 8")
    elif r["burst_length"] == 4:
        warnings.append(
            "burst_length=4 (burst chop): changes tCCD accounting and "
            "data-beat handling -- verify data_path supports BL4")

    # ---- host bus --------------------------------------------------
    if r["host_data_width"] not in (32, 64, 128):
        errors.append(
            f"host_data_width={r['host_data_width']} must be 32, 64 or 128")
    if r["interface_type"] not in ("wishbone_classic", "wishbone_pipelined"):
        errors.append(
            f"interface_type={r['interface_type']!r} must be "
            "'wishbone_classic' or 'wishbone_pipelined'")
    if r["self_refresh_mode"] not in ("disabled", "manual", "auto"):
        errors.append(
            f"self_refresh_mode={r['self_refresh_mode']!r} must be "
            "'disabled', 'manual' or 'auto'")
    if r["address_mapping"] not in ("row-bank-column", "bank-row-column"):
        errors.append(
            f"address_mapping={r['address_mapping']!r} must be "
            "'row-bank-column' or 'bank-row-column'")

    # ---- host width vs channel width packing ------------------------
    if not errors:
        data_lanes = r["byte_lanes"] - (1 if r["ecc_mode"] > 0 else 0)
        chan_w = data_lanes * jd.device_width_bits(r["device_width"])
        hw = r["host_data_width"]
        if chan_w <= 0:
            errors.append("computed channel data width <= 0")
        elif not (hw % chan_w == 0 or chan_w % hw == 0):
            errors.append(
                f"host_data_width={hw} and channel_data_width={chan_w} are "
                "not an integer ratio -- data_path packing is undefined")

    # ---- Tier-3 --------------------------------------------------
    pl = r["pipeline_latency_cycles"]
    if not (isinstance(pl, int) and 1 <= pl <= 4):
        errors.append(f"pipeline_latency_cycles={pl} must be in [1, 4]")

    ctrl_freq = jd.SPEED_GRADES[r["speed_grade"]]["data_rate_MTps"] / 2.0 \
        / jd.CLOCK_RATIO_DDR_TO_CTRL
    tf = r["target_frequency_mhz"]
    if tf is None:
        r["target_frequency_mhz"] = int(round(ctrl_freq))
    else:
        if not (100 <= tf <= 300):
            errors.append(f"target_frequency_mhz={tf} must be in [100, 300]")
        if tf < ctrl_freq:
            warnings.append(
                f"target_frequency_mhz={tf} is below the controller clock "
                f"this speed grade needs ({ctrl_freq:.0f} MHz) -- timing "
                "closure will fail")

    for key in ("area_optimization_goal", "power_optimization_goal"):
        pass  # free-form-ish backend hints; not range-checked

    if r["density"] == "8Gb":
        warnings.append(
            "density=8Gb: tRFC is 350 ns -> ~4.5% of bandwidth lost to "
            "refresh at JEDEC tREFI")

    return errors, warnings, r


# ======================================================================
# DERIVE + ASSEMBLE
# ======================================================================
def _bits_for(n: int) -> int:
    """Minimum bits to index n entries (n>=1)."""
    return max(1, math.ceil(math.log2(n))) if n > 1 else 1


def _pack_le_bytes(*vals: int) -> str:
    """Pack up to 4 values as little-endian bytes into a 0xXXXXXXXX string."""
    word = 0
    for i, v in enumerate(vals):
        word |= (int(v) & 0xFF) << (8 * i)
    return f"0x{word:08X}"


def _geometry(choices: dict) -> dict:
    sg, dens, dw = choices["speed_grade"], choices["density"], choices["device_width"]
    bl = choices["burst_length"]
    ecc = choices["ecc_mode"]
    total_lanes = choices["byte_lanes"]
    data_lanes = total_lanes - (1 if ecc > 0 else 0)

    dw_bits = jd.device_width_bits(dw)
    rb = jd.row_bits(dens, dw)
    cb = jd.column_bits(dw)
    chan_w = data_lanes * dw_bits
    page_dev = jd.page_size_bytes_per_device(dw)
    data_rate = jd.SPEED_GRADES[sg]["data_rate_MTps"]

    density_bits = jd.DENSITY_BITS[dens]
    chan_capacity = density_bits * data_lanes // 8

    return {
        "row_bits": rb,
        "column_bits": cb,
        "bank_bits": jd.BANK_BITS,
        "ranks": choices["ranks"],
        "burst_length": bl,
        "device_width_bits": dw_bits,
        "byte_lanes": total_lanes,
        "address_mapping": choices["address_mapping"],
        "$derived": {
            "device_density_bits": density_bits,
            "device_density_label": dens,
            "channel_data_width_bits": chan_w,
            "data_byte_lanes": data_lanes,
            "ecc_byte_lanes": total_lanes - data_lanes,
            "page_size_bytes_per_device": page_dev,
            "page_size_bytes_channel": page_dev * data_lanes,
            "channel_capacity_bytes": chan_capacity,
            "channel_capacity_MB": chan_capacity // (1024 * 1024),
            "burst_transfer_bytes_on_dq": bl * chan_w // 8,
            "peak_channel_bandwidth_MBps": int(data_rate * chan_w // 8),
        },
    }


def _clocking(choices: dict) -> dict:
    sg = choices["speed_grade"]
    tCK = jd.SPEED_GRADES[sg]["tCK_ns"]
    ratio = jd.CLOCK_RATIO_DDR_TO_CTRL
    ctrl_period = round(tCK * ratio, 6)
    data_rate = jd.SPEED_GRADES[sg]["data_rate_MTps"]
    return {
        "controller_clock_period_ns": ctrl_period,
        "ddr_clock_period_ns": tCK,
        "clock_ratio_ddr_to_controller": ratio,
        "pipeline_latency_cycles": choices["pipeline_latency_cycles"],
        "$derived": {
            "controller_frequency_MHz": round(1000.0 / ctrl_period, 4),
            "ddr_clock_frequency_MHz": round(1000.0 / tCK, 4),
            "data_rate_MTps": data_rate,
            "tCK_ns": tCK,
            "period_ratio_check": f"{ctrl_period} / {tCK} = {ratio}",
        },
    }


def _init_sequence(tm_ns: dict) -> dict:
    tCK = tm_ns["tCK_ns"]
    tRFC = tm_ns["tRFC"]
    tXPR_ns = max(5.0 * tCK, tRFC + 10.0)
    tZQinit_nCK = 512
    tZQinit_ns = round(tZQinit_nCK * tCK, 6)
    CL = tm_ns["CL_cycles"]
    CWL = tm_ns["CWL_cycles"]
    return {
        "reset_hold_us": 200,
        "cke_delay_us": 500,
        "tXPR_ns": round(tXPR_ns, 6),
        "zq_calibration_on_init": True,
        "tZQinit_ns": tZQinit_ns,
        "mode_registers": {
            "MR0": {
                "burst_length": "fixed_8" if tm_ns["_bl"] == 8 else "on_the_fly",
                "cas_latency_cycles": CL,
                "dll_reset": True,
                "write_recovery_ns": tm_ns["tWR"],
                "precharge_pd_mode": "fast_exit",
            },
            "MR1": {
                "dll_enable": True,
                "output_drive_strength": "RZQ_6",
                "rtt_nom": "RZQ_4",
                "additive_latency": "disabled",
                "write_leveling_enable": False,
            },
            "MR2": {
                "cas_write_latency_cycles": CWL,
                "rtt_wr": "RZQ_4",
                "self_refresh_temperature": "normal",
                "auto_self_refresh": False,
            },
            "MR3": {"mpr_enable": False, "mpr_read_function": 0},
        },
        "$derived": {
            "tXPR_reason": f"max(5*tCK, tRFC+10ns) = max({5*tCK}, {tRFC+10.0}) "
                           f"= {round(tXPR_ns,6)}ns",
            "tZQinit_reason": f"512*tCK = 512*{tCK} = {tZQinit_ns}ns",
            "tXPR_nCK": jd.ns_to_nck(tXPR_ns, tCK),
            "tZQinit_nCK": tZQinit_nCK,
            "init_sequence_order": (
                "RESET# low -> wait 200us -> RESET# high -> wait 500us -> "
                "CKE high -> wait tXPR -> MR2 -> MR3 -> MR1 -> MR0(DLL reset) "
                "-> ZQCL -> init_done"),
        },
    }


def _csr_map(dc: dict, geom: dict, choices: dict, host: dict,
             CL_nCK: int, CWL_nCK: int) -> dict:
    """CSR register map. Structure is fixed; the TIMING_*, REFRESH_CONFIG,
    CTRL_CONFIG and BIST_ADDR_END reset values are repacked from the
    derived numbers so a non-golden config is self-consistent."""
    sched_bit = 1 if choices["scheduler_policy"] == "fr_fcfs" else 0
    row_bit = 1 if choices["row_policy"] == "close_page" else 0
    srm = {"disabled": 0, "manual": 1, "auto": 2}[choices["self_refresh_mode"]]
    ecc_bit = 1 if choices["ecc_mode"] > 0 else 0
    ctrl_config_reset = (sched_bit
                         | (row_bit << 1)
                         | (srm << 2)
                         | (ecc_bit << 4))

    max_postpone = 8
    urgent_threshold = 6
    ref_priority = 1
    refresh_cfg_reset = (max_postpone & 0xF) \
        | ((urgent_threshold & 0xF) << 4) \
        | ((ref_priority & 0x1) << 8)

    addr_space = host["$derived"]["addressable_space_bytes"]
    end_addr = addr_space - 1
    aw = host["address_width_bits"]

    tim0 = _pack_le_bytes(dc["tRCD_nCK"], dc["tRP_nCK"], dc["tRAS_nCK"], dc["tRC_nCK"])
    tim1 = _pack_le_bytes(dc["tRRD_nCK"], dc["tWTR_nCK"], dc["tFAW_nCK"], dc["tRFC_nCK"])
    tim2 = _pack_le_bytes(dc["tWR_nCK"], dc["tRTP_nCK"], CL_nCK, CWL_nCK)
    tim3_word = (dc["tCCD_nCK"] & 0xFF) | ((dc["tREFI_nCK"] & 0xFFFFFF) << 8)
    tim3 = f"0x{tim3_word:08X}"

    return {
        "base_address": "0x00000000",
        "address_width_bits": 8,
        "data_width_bits": 32,
        "registers": [
            {"name": "CTRL_STATUS", "offset": "0x00", "access": "RO",
             "reset_value": "0x00000000", "fields": [
                {"name": "init_done", "bits": "0", "access": "RO", "reset_value": 0,
                 "description": "1 when init sequence complete"},
                {"name": "cal_done", "bits": "1", "access": "RO", "reset_value": 0,
                 "description": "1 when calibration complete"},
                {"name": "cal_fail", "bits": "2", "access": "RO", "reset_value": 0,
                 "description": "1 if calibration failed"},
                {"name": "bist_done", "bits": "3", "access": "RO", "reset_value": 0,
                 "description": "1 when BIST complete"},
                {"name": "bist_fail", "bits": "4", "access": "RO", "reset_value": 0,
                 "description": "1 if BIST failed"},
                {"name": "ref_pending_cnt", "bits": "7:5", "access": "RO",
                 "reset_value": 0, "description": "Pending refresh count (0-8)"},
                {"name": "self_refresh_active", "bits": "8", "access": "RO",
                 "reset_value": 0, "description": "1 when in self-refresh"},
                {"name": "reserved", "bits": "31:9", "access": "RO",
                 "reset_value": 0, "description": "Reserved"},
             ]},
            {"name": "CTRL_CONFIG", "offset": "0x04", "access": "RW",
             "reset_value": f"0x{ctrl_config_reset:08X}", "fields": [
                {"name": "sched_policy", "bits": "0", "access": "RW",
                 "reset_value": sched_bit, "description": "0=in_order, 1=fr_fcfs"},
                {"name": "row_policy", "bits": "1", "access": "RW",
                 "reset_value": row_bit, "description": "0=open_page, 1=close_page"},
                {"name": "self_ref_mode", "bits": "3:2", "access": "RW",
                 "reset_value": srm, "description": "0=disabled, 1=manual, 2=auto"},
                {"name": "ecc_enable", "bits": "4", "access": "RW",
                 "reset_value": ecc_bit, "description": "ECC mode enable"},
                {"name": "bist_start", "bits": "5", "access": "WO",
                 "reset_value": 0, "description": "Write 1 to start BIST"},
                {"name": "force_refresh", "bits": "6", "access": "WO",
                 "reset_value": 0, "description": "Write 1 to force refresh"},
                {"name": "force_self_ref", "bits": "7", "access": "WO",
                 "reset_value": 0, "description": "Write 1 to enter self-refresh"},
                {"name": "reserved", "bits": "31:8", "access": "RO",
                 "reset_value": 0, "description": "Reserved"},
             ]},
            {"name": "TIMING_0", "offset": "0x08", "access": "RW",
             "reset_value": tim0, "fields": [
                {"name": "tRCD_nCK", "bits": "7:0", "access": "RW",
                 "reset_value": dc["tRCD_nCK"], "description": "RAS-to-CAS delay"},
                {"name": "tRP_nCK", "bits": "15:8", "access": "RW",
                 "reset_value": dc["tRP_nCK"], "description": "Row precharge"},
                {"name": "tRAS_nCK", "bits": "23:16", "access": "RW",
                 "reset_value": dc["tRAS_nCK"], "description": "Row active time"},
                {"name": "tRC_nCK", "bits": "31:24", "access": "RW",
                 "reset_value": dc["tRC_nCK"], "description": "Row cycle time"},
             ]},
            {"name": "TIMING_1", "offset": "0x0C", "access": "RW",
             "reset_value": tim1, "fields": [
                {"name": "tRRD_nCK", "bits": "7:0", "access": "RW",
                 "reset_value": dc["tRRD_nCK"], "description": "Row-to-row delay"},
                {"name": "tWTR_nCK", "bits": "15:8", "access": "RW",
                 "reset_value": dc["tWTR_nCK"], "description": "Write-to-read"},
                {"name": "tFAW_nCK", "bits": "23:16", "access": "RW",
                 "reset_value": dc["tFAW_nCK"], "description": "Four-activate window"},
                {"name": "tRFC_nCK", "bits": "31:24", "access": "RW",
                 "reset_value": dc["tRFC_nCK"], "description": "Refresh cycle time"},
             ]},
            {"name": "TIMING_2", "offset": "0x10", "access": "RW",
             "reset_value": tim2, "fields": [
                {"name": "tWR_nCK", "bits": "7:0", "access": "RW",
                 "reset_value": dc["tWR_nCK"], "description": "Write recovery"},
                {"name": "tRTP_nCK", "bits": "15:8", "access": "RW",
                 "reset_value": dc["tRTP_nCK"], "description": "Read-to-precharge"},
                {"name": "CL_nCK", "bits": "23:16", "access": "RW",
                 "reset_value": CL_nCK, "description": "CAS latency"},
                {"name": "CWL_nCK", "bits": "31:24", "access": "RW",
                 "reset_value": CWL_nCK, "description": "CAS write latency"},
             ]},
            {"name": "TIMING_3", "offset": "0x14", "access": "RW",
             "reset_value": tim3, "fields": [
                {"name": "tCCD_nCK", "bits": "7:0", "access": "RW",
                 "reset_value": dc["tCCD_nCK"], "description": "CAS-to-CAS delay"},
                {"name": "tREFI_nCK", "bits": "31:8", "access": "RW",
                 "reset_value": dc["tREFI_nCK"], "description": "Refresh interval"},
             ]},
            {"name": "REFRESH_CONFIG", "offset": "0x18", "access": "RW",
             "reset_value": f"0x{refresh_cfg_reset:08X}", "fields": [
                {"name": "max_postpone", "bits": "3:0", "access": "RW",
                 "reset_value": max_postpone, "description": "Max postponed refreshes"},
                {"name": "urgent_threshold", "bits": "7:4", "access": "RW",
                 "reset_value": urgent_threshold,
                 "description": "Postpone count to trigger urgent refresh"},
                {"name": "ref_priority", "bits": "8", "access": "RW",
                 "reset_value": ref_priority,
                 "description": "0=normal, 1=urgent_preempt"},
                {"name": "reserved", "bits": "31:9", "access": "RO",
                 "reset_value": 0, "description": "Reserved"},
             ]},
            {"name": "ERROR_STATUS", "offset": "0x1C", "access": "RW1C",
             "reset_value": "0x00000000", "fields": [
                {"name": "ecc_ce_count", "bits": "15:0", "access": "RO",
                 "reset_value": 0, "description": "Correctable ECC error count"},
                {"name": "ecc_ue_flag", "bits": "16", "access": "RW1C",
                 "reset_value": 0, "description": "Uncorrectable ECC error"},
                {"name": "ref_starve_flag", "bits": "17", "access": "RW1C",
                 "reset_value": 0, "description": "Refresh starvation occurred"},
                {"name": "init_fail_flag", "bits": "18", "access": "RW1C",
                 "reset_value": 0, "description": "Init/cal failure occurred"},
                {"name": "bist_fail_addr", "bits": "31:19", "access": "RO",
                 "reset_value": 0, "description": "Upper bits of first BIST fail addr"},
             ]},
            {"name": "BIST_CONFIG", "offset": "0x20", "access": "RW",
             "reset_value": "0x00000000", "fields": [
                {"name": "bist_pattern", "bits": "2:0", "access": "RW",
                 "reset_value": 0, "description": "0=w1s,1=w0s,2=cb,3=lfsr,4=all"},
                {"name": "bist_addr_mode", "bits": "3", "access": "RW",
                 "reset_value": 0, "description": "0=sequential, 1=random_lfsr"},
                {"name": "reserved", "bits": "31:4", "access": "RO",
                 "reset_value": 0, "description": "Reserved"},
             ]},
            {"name": "BIST_ADDR_START", "offset": "0x24", "access": "RW",
             "reset_value": "0x00000000", "fields": [
                {"name": "start_addr", "bits": f"{aw-1}:0", "access": "RW",
                 "reset_value": 0, "description": f"BIST start byte address ({aw} bits)"},
                {"name": "reserved", "bits": f"31:{aw}", "access": "RO",
                 "reset_value": 0, "description": "Reserved"},
             ]},
            {"name": "BIST_ADDR_END", "offset": "0x28", "access": "RW",
             "reset_value": f"0x{end_addr:08X}", "fields": [
                {"name": "end_addr", "bits": f"{aw-1}:0", "access": "RW",
                 "reset_value": end_addr,
                 "description": f"BIST end byte address ({aw} bits)"},
                {"name": "reserved", "bits": f"31:{aw}", "access": "RO",
                 "reset_value": 0, "description": "Reserved"},
             ]},
        ],
    }


def _latency_model(dc: dict, choices: dict, tm_ns: dict) -> dict:
    pl = choices["pipeline_latency_cycles"]
    ratio = jd.CLOCK_RATIO_DDR_TO_CTRL
    BL = choices["burst_length"]
    CL = tm_ns["CL_cycles"]
    CWL = tm_ns["CWL_cycles"]
    tRCD = dc["tRCD_nCK"]
    tRP = dc["tRP_nCK"]
    tWR = dc["tWR_nCK"]
    tWTR = dc["tWTR_nCK"]
    tCCD = dc["tCCD_nCK"]
    half_bl = BL // 2
    rd_hit = pl * ratio + CL + half_bl + 2
    rd_empty = pl * ratio + tRCD + CL + half_bl + 2
    rd_miss = pl * ratio + tRP + tRCD + CL + half_bl + 2
    wr_hit = pl * ratio + CWL + half_bl + tWR
    w2r = CWL + half_bl + tWTR
    r2w = CL + tCCD + 2 - CWL
    return {
        "$comment": "Formulas in DDR clock cycles (nCK). pipeline_latency is "
                    "in controller cycles; multiply by clock_ratio for nCK.",
        "read_hit_latency_nCK": rd_hit,
        "read_empty_latency_nCK": rd_empty,
        "read_miss_latency_nCK": rd_miss,
        "write_hit_latency_nCK": wr_hit,
        "write_to_read_turnaround_nCK": w2r,
        "read_to_write_turnaround_nCK": r2w,
    }


# Static sections that don't depend on Tier-1 choices.
_STATIC_SECTIONS = {
    "conversion_rules": {
        "timing_ns_to_nCK": "ceil(param_ns / tCK_ns)",
        "conversion_owner": "microarchitecture_agent",
        "rounding_rule": "ceiling",
    },
    "validation_scopes": [
        "config_regs", "arbiter", "scheduler", "timing", "init_sequence",
        "calibration", "refresh", "data_path", "full_controller",
    ],
    "memory_model_boundary": {
        "boundary_type": "abstract_cmd_data",
        "phy_modeled": False,
        "supports_training": False,
        "supports_mpr": False,
        "read_data_model": "fixed_latency_from_CL",
        "notes": "No pin-accurate PHY. Validation is at host+controller "
                 "command layer with abstract DRAM command/data boundary.",
    },
    "observability": {
        "debug_interface_name": "mc_debug_if",
        "required_signals_by_scope": {
            "config_regs": ["csr_addr", "csr_we", "csr_re", "csr_wdata",
                            "csr_rdata", "csr_ack"],
            "arbiter": ["port_req_vec", "port_grant_vec", "port_sel_id"],
            "scheduler": ["cmd_valid", "cmd_type", "cmd_rank", "cmd_bank",
                          "cmd_row", "cmd_col", "cmd_auto_precharge",
                          "queue_occupancy"],
            "timing": ["bank_state", "bank_open_row", "act_allowed",
                       "rd_allowed", "wr_allowed", "pre_allowed", "faw_count"],
            "init_sequence": ["init_state", "mrs_issue", "zq_issue",
                              "init_done", "init_fail"],
            "refresh": ["ref_pending", "ref_urgent", "ref_count", "ref_ack"],
            "data_path": ["wr_valid", "wr_data", "rd_valid", "rd_data",
                          "rd_latency_cnt"],
            "calibration": ["cal_state", "cal_done", "cal_fail", "zqcs_issued"],
        },
    },
}


def _load_failure_taxonomy() -> dict:
    """The failure taxonomy is config-independent; reuse the golden file's
    copy verbatim if it is available, else fall back to a minimal set."""
    golden = Path(__file__).resolve().parents[2] / "Spec" \
        / "llmmc_microarchitecturespec_filled.json"
    try:
        g = json.loads(golden.read_text())
        return g["failure_taxonomy"]
    except Exception:
        return {"categories": []}


def compile_spec(choices: dict) -> dict:
    """Main entry. See module docstring for the return shape."""
    errors, warnings, r = validate_choices(choices)
    if errors:
        return {
            "ok": False, "errors": errors, "warnings": warnings,
            "resolved_choices": r, "spec": None,
            "consistency_checks": [], "consistency_ok": False,
        }

    sg = r["speed_grade"]
    tm_ns = jd.timing_model_ns(sg, r["density"], r["device_width"])
    tm_ns["_bl"] = r["burst_length"]        # scratch for _init_sequence
    dc = jd.derived_cycles(tm_ns)
    tm_ns.pop("_bl")

    geom = _geometry(r)
    clk = _clocking(r)

    data_lanes = geom["$derived"]["data_byte_lanes"]
    chan_w = geom["$derived"]["channel_data_width_bits"]
    addr_space = geom["$derived"]["channel_capacity_bytes"]
    aw = int(round(math.log2(addr_space)))

    host = {
        "interface_type": r["interface_type"],
        "addressing": "byte",
        "data_width_bits": r["host_data_width"],
        "address_width_bits": aw,
        "granularity_bits": 8,
        "burst_type": "linear",
        "max_burst_length": r["burst_length"],
        "read_buffer_depth": r["read_buffer_depth"],
        "write_buffer_depth": r["write_buffer_depth"],
        "enable_data_mask": True,
        "$derived": {
            "addressable_space_bytes": addr_space,
            "addressable_space_MB": addr_space // (1024 * 1024),
            "host_burst_transfer_bytes": r["burst_length"] * r["host_data_width"] // 8,
            "sel_width_bits": r["host_data_width"] // 8,
        },
    }

    tm_full = dict(tm_ns)
    tm_full["$derived_cycles"] = dc

    arch = {
        "num_ports": 1,
        "arbiter_policy": "round_robin",
        "scheduler_policy": r["scheduler_policy"],
        "row_policy": r["row_policy"],
        "command_queue_depth": r["command_queue_depth"],
        "lookahead_depth": r["lookahead_depth"],
        "ecc_mode": r["ecc_mode"],
        "self_refresh_mode": r["self_refresh_mode"],
        "refresh_policy": {
            "max_postpone_count": 8,
            "refresh_priority": "urgent_preempt",
            "urgent_threshold": 6,
        },
        "bist_config": {
            "enable": True, "pattern": "all_patterns",
            "address_mode": "sequential",
            "address_range": {"start": 0, "end": addr_space - 1},
        },
        "error_handling": {
            "on_ecc_correctable": "correct_and_continue",
            "on_ecc_uncorrectable": "poison_data",
            "on_refresh_starvation": "force_precharge_all",
            "on_init_failure": "halt_and_signal",
        },
        "enable_second_wishbone": False,
        "aux_width": 4,
        "$derived": {
            "bank_count": 2 ** jd.BANK_BITS,
            "queue_index_bits": int(round(math.log2(r["command_queue_depth"]))),
            "lookahead_index_bits": (int(math.ceil(math.log2(r["lookahead_depth"])))
                                     if r["lookahead_depth"] > 1 else
                                     (1 if r["lookahead_depth"] == 1 else 0)),
        },
    }

    init_seq = _init_sequence({**tm_ns, "_bl": r["burst_length"]})
    zqcs_nCK = 512000
    calib = {
        "enable_write_leveling": False,
        "enable_read_leveling": False,
        "enable_bitslip_training": False,
        "calibration_retry_count": 0,
        "periodic_recalibration_enable": True,
        "periodic_zqcs_interval_ns": round(zqcs_nCK * clk["$derived"]["tCK_ns"], 6),
        "$comment": "PHY not modeled; periodic ZQCS is a scheduling "
                    "requirement only.",
        "$derived": {"periodic_zqcs_interval_nCK": zqcs_nCK},
    }

    spec = {
        "$comment": f"Compiled by microarch_compiler from choices: "
                    f"{sg} / {r['density']} / {r['device_width']} / "
                    f"{r['byte_lanes']}lane / {r['ranks']}rank",
        "$schema": "https://example.com/ddr3_microarchitecture.schema.json",
        "schema_version": "2.0.0",
        "design_id": f"ddr3_mc_{sg.split('-')[1]}_{r['device_width']}_"
                     f"{r['byte_lanes']}lane_{r['ranks']}rank",
        "revision": f"compiled_{sg.lower().replace('-', '')}_"
                    f"{r['device_width']}_{r['byte_lanes']}lane_{r['ranks']}rank",
        **_STATIC_SECTIONS,
        "memory_geometry": geom,
        "clocking_model": clk,
        "timing_model": tm_full,
        "controller_architecture": arch,
        "initialization_sequence": init_seq,
        "calibration": calib,
        "host_interface": host,
        "data_path_mapping": {
            "ddr_channel_width_bits": chan_w,
            "host_width_bits": r["host_data_width"],
            "pack_mode": f"pack_{r['host_data_width']}_to_{chan_w}"
                         if r["host_data_width"] >= chan_w
                         else f"unpack_{r['host_data_width']}_to_{chan_w}",
            "alignment_bytes_required": max(1, chan_w // 8),
            "endianness": "little",
            "byte_enable_semantics": "wishbone_sel_per_byte",
        },
        "phy_interface": {
            "mode": "abstract",
            "dq_width_bits": r["byte_lanes"] * geom["device_width_bits"],
            "dqs_count": r["byte_lanes"],
            "dm_enabled": True,
            "ck_pair_present": True,
            "notes": "Abstracted DRAM boundary. Command/data semantics only.",
        },
        "csr_register_map": _csr_map(dc, geom, r, host,
                                     tm_ns["CL_cycles"], tm_ns["CWL_cycles"]),
        "latency_model": _latency_model(dc, r, tm_ns),
        "failure_taxonomy": _load_failure_taxonomy(),
        "implementation_targets": {
            "target_frequency_mhz": r["target_frequency_mhz"],
            "area_optimization_goal": r["area_optimization_goal"],
            "power_optimization_goal": r["power_optimization_goal"],
            "clock_name": "clk_ctrl",
            "reset_name": "rst_n",
            "reset_polarity": "active_low",
        },
    }

    checks = run_consistency_checks(spec)
    consistency_ok = all(c["pass"] for c in checks)
    return {
        "ok": consistency_ok,
        "errors": ([] if consistency_ok
                   else [f"consistency check failed: {c['name']}"
                         for c in checks if not c["pass"]]),
        "warnings": warnings,
        "resolved_choices": r,
        "spec": spec,
        "consistency_checks": checks,
        "consistency_ok": consistency_ok,
    }


# ======================================================================
# CONSISTENCY CHECKS  (executable $consistency_checks / $cross_checks)
# ======================================================================
def run_consistency_checks(spec: dict) -> list[dict]:
    out: list[dict] = []

    def chk(name, ok, detail=""):
        out.append({"name": name, "pass": bool(ok), "detail": detail})

    tm = spec["timing_model"]
    dc = tm["$derived_cycles"]
    cl = spec["clocking_model"]
    tCK = cl["$derived"]["tCK_ns"]
    geom = spec["memory_geometry"]
    host = spec["host_interface"]
    arch = spec["controller_architecture"]
    ini = spec["initialization_sequence"]

    chk("tRC == tRAS + tRP",
        abs(tm["tRC"] - (tm["tRAS"] + tm["tRP"])) < 1e-6,
        f'{tm["tRC"]} == {tm["tRAS"]} + {tm["tRP"]}')

    chk("tRRD >= max(4*tCK, page floor)",
        tm["tRRD"] >= max(4 * tCK, 7.5 if geom["device_width_bits"] < 16 else 10.0) - 1e-6,
        f'{tm["tRRD"]} vs {max(4*tCK, 7.5 if geom["device_width_bits"]<16 else 10.0)}')

    chk("tWTR >= max(4*tCK, 7.5ns)", tm["tWTR"] >= max(4 * tCK, 7.5) - 1e-6)
    chk("tRTP >= max(4*tCK, 7.5ns)", tm["tRTP"] >= max(4 * tCK, 7.5) - 1e-6)
    chk("tFAW >= 4*tRRD", tm["tFAW"] >= 4 * tm["tRRD"] - 1e-6,
        f'{tm["tFAW"]} >= {4*tm["tRRD"]}')
    chk("tCCD == 4*tCK", abs(tm["tCCD"] - 4 * tCK) < 1e-6)
    chk("timing.tCK_ns == clocking.ddr_clock_period_ns",
        abs(tm["tCK_ns"] - cl["ddr_clock_period_ns"]) < 1e-6)
    chk("controller_period / ddr_period == clock_ratio",
        abs(cl["controller_clock_period_ns"] / cl["ddr_clock_period_ns"]
            - cl["clock_ratio_ddr_to_controller"]) < 1e-6)

    # every $derived_cycles == ceil(ns / tCK)
    for k, ck_key in [("tRCD", "tRCD_nCK"), ("tRP", "tRP_nCK"), ("tRAS", "tRAS_nCK"),
                      ("tRC", "tRC_nCK"), ("tRFC", "tRFC_nCK"), ("tFAW", "tFAW_nCK"),
                      ("tRRD", "tRRD_nCK"), ("tWR", "tWR_nCK"), ("tWTR", "tWTR_nCK"),
                      ("tRTP", "tRTP_nCK"), ("tCCD", "tCCD_nCK"), ("tREFI", "tREFI_nCK")]:
        want = jd.ns_to_nck(tm[k], tCK)
        chk(f"{ck_key} == ceil({k}/tCK)", dc[ck_key] == want,
            f'{dc[ck_key]} == {want}')

    # mode-register cross-checks
    mr = ini["mode_registers"]
    chk("MR0.cas_latency_cycles == timing.CL_cycles",
        mr["MR0"]["cas_latency_cycles"] == tm["CL_cycles"])
    chk("MR2.cas_write_latency_cycles == timing.CWL_cycles",
        mr["MR2"]["cas_write_latency_cycles"] == tm["CWL_cycles"])
    chk("MR0.write_recovery_ns == timing.tWR",
        abs(mr["MR0"]["write_recovery_ns"] - tm["tWR"]) < 1e-6)

    # geometry / address width
    dw_bits = geom["device_width_bits"]
    data_lanes = geom["$derived"]["data_byte_lanes"]
    sum_bits = (geom["row_bits"] + geom["column_bits"] + geom["bank_bits"]
                + int(round(math.log2(geom["ranks"])))
                + int(round(math.log2(max(1, data_lanes * dw_bits // 8)))))
    chk("host.address_width_bits == geometry sum",
        host["address_width_bits"] == sum_bits,
        f'{host["address_width_bits"]} == {sum_bits}')
    chk("address_width_bits == log2(channel_capacity_bytes)",
        host["address_width_bits"]
        == int(round(math.log2(geom["$derived"]["channel_capacity_bytes"]))))

    # queue index bits
    chk("queue_index_bits == log2(command_queue_depth)",
        arch["$derived"]["queue_index_bits"]
        == int(round(math.log2(arch["command_queue_depth"]))))

    # tXPR
    want_txpr = max(5 * tCK, tm["tRFC"] + 10.0)
    chk("tXPR_ns == max(5*tCK, tRFC+10ns)",
        abs(ini["tXPR_ns"] - want_txpr) < 1e-6,
        f'{ini["tXPR_ns"]} == {round(want_txpr,6)}')

    return out


# ======================================================================
# MODIFIABILITY REPORT  (blast-radius classification)
# ======================================================================
def modifiability_report() -> dict:
    buckets: dict[str, list[dict]] = {
        "isolated": [], "regen_local": [], "structural": [], "unsupported": [],
    }
    for param, (level, why) in BLAST_RADIUS.items():
        buckets[level].append({"parameter": param, "effect": why})
    return {
        "legend": {
            "isolated": "Change the value freely. No RTL structure/port/width "
                        "change -- at most a constant, a CSR reset value, or a "
                        "backend hint. Safe to sweep.",
            "regen_local": "A few modules' parameters (widths, depths) change "
                           "and those modules regenerate, but port names and "
                           "the cross-module interface stay stable.",
            "structural": "Bus/address widths, geometry or port lists change; "
                          "ripples across most modules and the cross-phase "
                          "lint must re-pass.",
            "unsupported": "Current RTL agents do not implement this axis; the "
                           "compiler rejects it.",
        },
        "buckets": buckets,
    }


# ======================================================================
# CLI
# ======================================================================
def _selftest() -> int:
    """Compile the 'default' preset and diff its derived blocks against the
    committed golden spec."""
    golden_path = Path(__file__).resolve().parents[2] / "Spec" \
        / "llmmc_microarchitecturespec_filled.json"
    golden = json.loads(golden_path.read_text())
    res = compile_spec(PRESETS["default"])
    if not res["ok"]:
        print("SELFTEST FAIL: compile errors:", res["errors"])
        return 1
    spec = res["spec"]

    diffs = []

    def cmp(path, a, b):
        if a != b:
            diffs.append(f"  {path}: compiled={a!r}  golden={b!r}")

    g_tm = golden["timing_model"]
    c_tm = spec["timing_model"]
    for k in ["tRCD", "tRP", "tRAS", "tRC", "tRFC", "tFAW", "tRRD", "tWR",
              "tWTR", "tRTP", "tCCD", "tREFI", "CL_cycles", "CWL_cycles", "tCK_ns"]:
        cmp(f"timing_model.{k}", c_tm[k], g_tm[k])
    for k, v in g_tm["$derived_cycles"].items():
        if k.startswith("$"):
            continue
        cmp(f"timing_model.$derived_cycles.{k}", c_tm["$derived_cycles"].get(k), v)

    g_ge = golden["memory_geometry"]
    c_ge = spec["memory_geometry"]
    for k in ["row_bits", "column_bits", "bank_bits", "device_width_bits"]:
        cmp(f"memory_geometry.{k}", c_ge[k], g_ge[k])
    for k in ["device_density_bits", "channel_data_width_bits",
              "channel_capacity_bytes", "burst_transfer_bytes_on_dq",
              "peak_channel_bandwidth_MBps"]:
        cmp(f"memory_geometry.$derived.{k}", c_ge["$derived"].get(k),
            g_ge["$derived"][k])

    g_cl = golden["clocking_model"]
    c_cl = spec["clocking_model"]
    for k in ["controller_clock_period_ns", "ddr_clock_period_ns"]:
        cmp(f"clocking_model.{k}", c_cl[k], g_cl[k])
    for k in ["controller_frequency_MHz", "ddr_clock_frequency_MHz",
              "data_rate_MTps", "tCK_ns"]:
        cmp(f"clocking_model.$derived.{k}", c_cl["$derived"][k], g_cl["$derived"][k])

    g_ar = golden["controller_architecture"]["$derived"]
    c_ar = spec["controller_architecture"]["$derived"]
    for k in ["bank_count", "queue_index_bits", "lookahead_index_bits"]:
        cmp(f"controller_architecture.$derived.{k}", c_ar[k], g_ar[k])

    g_ini = golden["initialization_sequence"]["$derived"]
    c_ini = spec["initialization_sequence"]["$derived"]
    for k in ["tXPR_nCK", "tZQinit_nCK"]:
        cmp(f"initialization_sequence.$derived.{k}", c_ini[k], g_ini[k])

    g_ho = golden["host_interface"]["$derived"]
    c_ho = spec["host_interface"]["$derived"]
    for k in ["addressable_space_bytes", "host_burst_transfer_bytes",
              "sel_width_bits"]:
        cmp(f"host_interface.$derived.{k}", c_ho[k], g_ho[k])

    for rg in golden["csr_register_map"]["registers"]:
        cg = next((x for x in spec["csr_register_map"]["registers"]
                   if x["name"] == rg["name"]), None)
        if cg is None:
            diffs.append(f"  csr.{rg['name']}: missing in compiled")
            continue
        cmp(f"csr.{rg['name']}.reset_value", cg["reset_value"], rg["reset_value"])

    print(f"consistency checks: "
          f"{sum(c['pass'] for c in res['consistency_checks'])}"
          f"/{len(res['consistency_checks'])} pass")
    if diffs:
        print(f"SELFTEST: {len(diffs)} field(s) differ from golden:")
        print("\n".join(diffs))
        return 1
    print("SELFTEST PASS -- 'default' preset reproduces the golden spec's "
          "derived blocks and CSR reset values exactly.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="DDR3 microarchitecture spec compiler")
    ap.add_argument("--selftest", action="store_true",
                    help="compile 'default' preset and diff against golden spec")
    ap.add_argument("--preset", choices=sorted(PRESETS),
                    help="compile a named preset")
    ap.add_argument("--from-choices", metavar="FILE",
                    help="compile a JSON choices file")
    ap.add_argument("--out", metavar="DIR",
                    help="write compiled spec to DIR/microarch_spec.json")
    ap.add_argument("--list-modifiable", action="store_true",
                    help="print the blast-radius classification and exit")
    args = ap.parse_args()

    if args.list_modifiable:
        print(json.dumps(modifiability_report(), indent=2))
        return 0
    if args.selftest:
        return _selftest()

    if args.preset:
        choices = dict(PRESETS[args.preset])
    elif args.from_choices:
        choices = json.loads(Path(args.from_choices).read_text())
    else:
        ap.error("need --selftest, --preset, --from-choices, or --list-modifiable")

    res = compile_spec(choices)
    print(f"ok={res['ok']}  errors={len(res['errors'])}  "
          f"warnings={len(res['warnings'])}")
    for e in res["errors"]:
        print(f"  ERROR   {e}")
    for w in res["warnings"]:
        print(f"  WARNING {w}")
    if res["spec"] is None:
        return 2
    bad = [c for c in res["consistency_checks"] if not c["pass"]]
    print(f"consistency: {len(res['consistency_checks']) - len(bad)}"
          f"/{len(res['consistency_checks'])} pass")
    for c in bad:
        print(f"  CHECK FAIL {c['name']}  ({c['detail']})")
    if args.out:
        d = Path(args.out)
        d.mkdir(parents=True, exist_ok=True)
        p = d / "microarch_spec.json"
        p.write_text(json.dumps(res["spec"], indent=2))
        print(f"wrote {p}")
    else:
        print(json.dumps(res["spec"], indent=2))
    return 0 if res["ok"] else 2


if __name__ == "__main__":
    sys.exit(main())
