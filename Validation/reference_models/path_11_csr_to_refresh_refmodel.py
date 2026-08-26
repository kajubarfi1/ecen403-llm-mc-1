#!/usr/bin/env python3
"""
Reference model for CSR → Refresh Controller Configuration path (path_11).

Models the integration path: config_regs -> refresh_ctrl

Signals flowing between blocks:
  config_regs -> refresh_ctrl:
    cfg_max_postpone    -> cfg_max_postpone
    cfg_urgent_threshold -> cfg_urgent_threshold
    cfg_force_refresh   -> cfg_force_refresh
    cfg_ref_priority    -> cfg_ref_priority
    cfg_tREFI_nCK       -> cfg_tREFI_nCK

The refresh controller uses a down-counter for tREFI. When init_done goes high,
the counter is at 0, which fires refi_tick immediately, incrementing postpone_cnt
to 1 and reloading the counter. ref_ack decrements postpone_cnt.
"""

import json
import os
import math

# =============================================================================
# CSR Register Map (relevant registers for this path)
# =============================================================================
# Addresses are byte addresses (Wishbone byte addressing).

REG_CTRL         = 0x00  # Control register
REG_TIMING_0     = 0x04  # tRCD, tRP (packed)
REG_TIMING_1     = 0x08  # tRAS, tRC (packed)
REG_TIMING_2     = 0x0C  # tRRD, tWTR, tFAW (packed)
REG_TIMING_3     = 0x10  # tRFC, tWR, tRTP (packed)
REG_TIMING_4     = 0x14  # CL, CWL, tCCD (packed)
REG_TIMING_5     = 0x18  # tREFI (packed)
REG_SCHED        = 0x1C  # Scheduler config
REG_REFRESH      = 0x20  # Refresh config: max_postpone, urgent_threshold, force_refresh, ref_priority
REG_SELF_REF     = 0x24  # Self-refresh config
REG_ECC          = 0x28  # ECC config
REG_BIST_CTRL    = 0x2C  # BIST control
REG_BIST_PAT     = 0x30  # BIST pattern
REG_BIST_ASTART  = 0x34  # BIST address start
REG_BIST_AEND    = 0x38  # BIST address end
REG_STATUS       = 0x3C  # Status register (read-only)
REG_ERR_STATUS   = 0x40  # Error status (read-only)
REG_ECC_CE_CNT   = 0x44  # ECC correctable error count (read-only)
REG_BIST_FADDR   = 0x48  # BIST fail address (read-only)
REG_REF_PEND_CNT = 0x4C  # Refresh pending count (read-only)

# Default timing values from spec (DDR3-1600K at tCK=1.25ns)
DEFAULT_tRCD_nCK  = 11
DEFAULT_tRP_nCK   = 11
DEFAULT_tRAS_nCK  = 28
DEFAULT_tRC_nCK   = 39
DEFAULT_tRRD_nCK  = 6
DEFAULT_tWTR_nCK  = 6
DEFAULT_tFAW_nCK  = 32
DEFAULT_tRFC_nCK  = 128
DEFAULT_tWR_nCK   = 12
DEFAULT_tRTP_nCK  = 6
DEFAULT_CL_nCK    = 11
DEFAULT_CWL_nCK   = 8
DEFAULT_tCCD_nCK  = 4
DEFAULT_tREFI_nCK = 6240

# Refresh config defaults from spec
DEFAULT_MAX_POSTPONE     = 8
DEFAULT_URGENT_THRESHOLD = 6
DEFAULT_REF_PRIORITY     = 1  # 1 = urgent_preempt

# Scheduler/row policy encoding
SCHED_FR_FCFS = 0
SCHED_FCFS    = 1

ROW_OPEN_PAGE  = 0
ROW_CLOSE_PAGE = 1

SELF_REF_AUTO    = 0
SELF_REF_MANUAL  = 1
SELF_REF_DISABLE = 2


class PathModel:
    """
    Models the CSR -> Refresh Controller configuration path.

    The CSR block accepts Wishbone transactions to configure refresh parameters.
    The refresh controller receives these configuration signals and manages
    the refresh timing/state machine.
    """

    # All output signal names
    OUTPUT_SIGNALS = [
        "csr_ack_o", "csr_dat_o", "csr_err_o",
        "cfg_tRCD_nCK", "cfg_tRP_nCK", "cfg_tRAS_nCK", "cfg_tRC_nCK",
        "cfg_tRRD_nCK", "cfg_tWTR_nCK", "cfg_tFAW_nCK", "cfg_tRFC_nCK",
        "cfg_tWR_nCK", "cfg_tRTP_nCK", "cfg_CL_nCK", "cfg_CWL_nCK",
        "cfg_tCCD_nCK", "cfg_sched_policy", "cfg_row_policy",
        "cfg_self_ref_mode", "cfg_ecc_enable", "cfg_bist_start",
        "cfg_force_self_ref", "cfg_bist_pattern", "cfg_bist_addr_mode",
        "cfg_bist_addr_start", "cfg_bist_addr_end",
        "ref_required", "ref_urgent", "ref_pending_cnt", "ref_starve_flag"
    ]

    def __init__(self):
        self.reset()

    def reset(self):
        """Reset all internal state to power-on defaults."""
        # =====================================================================
        # CSR Block State
        # =====================================================================
        # Wishbone pipeline state
        self._wb_ack_pending = False
        self._wb_dat_pending = 0
        self._wb_err_pending = False

        # Configuration registers (defaults from spec)
        self._cfg_tRCD_nCK  = DEFAULT_tRCD_nCK
        self._cfg_tRP_nCK   = DEFAULT_tRP_nCK
        self._cfg_tRAS_nCK  = DEFAULT_tRAS_nCK
        self._cfg_tRC_nCK   = DEFAULT_tRC_nCK
        self._cfg_tRRD_nCK  = DEFAULT_tRRD_nCK
        self._cfg_tWTR_nCK  = DEFAULT_tWTR_nCK
        self._cfg_tFAW_nCK  = DEFAULT_tFAW_nCK
        self._cfg_tRFC_nCK  = DEFAULT_tRFC_nCK
        self._cfg_tWR_nCK   = DEFAULT_tWR_nCK
        self._cfg_tRTP_nCK  = DEFAULT_tRTP_nCK
        self._cfg_CL_nCK    = DEFAULT_CL_nCK
        self._cfg_CWL_nCK   = DEFAULT_CWL_nCK
        self._cfg_tCCD_nCK  = DEFAULT_tCCD_nCK
        self._cfg_tREFI_nCK = DEFAULT_tREFI_nCK

        self._cfg_sched_policy   = SCHED_FR_FCFS
        self._cfg_row_policy     = ROW_OPEN_PAGE
        self._cfg_self_ref_mode  = SELF_REF_AUTO
        self._cfg_ecc_enable     = 0
        self._cfg_bist_start     = 0
        self._cfg_force_self_ref = 0
        self._cfg_bist_pattern   = 0  # all_patterns encoded
        self._cfg_bist_addr_mode = 0  # sequential
        self._cfg_bist_addr_start = 0
        self._cfg_bist_addr_end   = 536870911

        # Refresh-specific config signals (CSR -> refresh_ctrl path)
        self._cfg_max_postpone     = DEFAULT_MAX_POSTPONE
        self._cfg_urgent_threshold = DEFAULT_URGENT_THRESHOLD
        self._cfg_force_refresh    = 0
        self._cfg_ref_priority     = DEFAULT_REF_PRIORITY

        # =====================================================================
        # Refresh Controller State
        # =====================================================================
        self._refi_counter = 0       # Down-counter for tREFI interval
        self._postpone_cnt = 0       # Number of pending (postponed) refreshes
        self._ref_required = 0       # Refresh needed flag
        self._ref_urgent   = 0       # Urgent refresh flag
        self._ref_starve_flag = 0    # Starvation flag
        self._init_done_prev = 0     # Previous init_done for edge detection
        self._init_done_curr = 0     # Current init_done

        # Status inputs (directly from external signals)
        self._sts_init_done           = 0
        self._sts_cal_done            = 0
        self._sts_cal_fail            = 0
        self._sts_bist_done           = 0
        self._sts_bist_fail           = 0
        self._sts_ref_pending_cnt     = 0
        self._sts_self_refresh_active = 0
        self._sts_ecc_ce_count        = 0
        self._sts_ecc_ue_event        = 0
        self._sts_ref_starve_event    = 0
        self._sts_init_fail_event     = 0
        self._sts_bist_fail_addr      = 0

    def _read_csr(self, addr):
        """Read a CSR register and return (data, error)."""
        addr = addr & 0xFFFFFFFC  # Word-align

        if addr == REG_CTRL:
            val = (self._cfg_force_self_ref & 1) | ((self._cfg_bist_start & 1) << 1)
            return (val, False)
        elif addr == REG_TIMING_0:
            val = (self._cfg_tRCD_nCK & 0xFFFF) | ((self._cfg_tRP_nCK & 0xFFFF) << 16)
            return (val, False)
        elif addr == REG_TIMING_1:
            val = (self._cfg_tRAS_nCK & 0xFFFF) | ((self._cfg_tRC_nCK & 0xFFFF) << 16)
            return (val, False)
        elif addr == REG_TIMING_2:
            val = ((self._cfg_tRRD_nCK & 0xFF) |
                   ((self._cfg_tWTR_nCK & 0xFF) << 8) |
                   ((self._cfg_tFAW_nCK & 0xFFFF) << 16))
            return (val, False)
        elif addr == REG_TIMING_3:
            val = ((self._cfg_tRFC_nCK & 0xFFFF) |
                   ((self._cfg_tWR_nCK & 0xFF) << 16) |
                   ((self._cfg_tRTP_nCK & 0xFF) << 24))
            return (val, False)
        elif addr == REG_TIMING_4:
            val = ((self._cfg_CL_nCK & 0xFF) |
                   ((self._cfg_CWL_nCK & 0xFF) << 8) |
                   ((self._cfg_tCCD_nCK & 0xFF) << 16))
            return (val, False)
        elif addr == REG_TIMING_5:
            val = self._cfg_tREFI_nCK & 0xFFFFFFFF
            return (val, False)
        elif addr == REG_SCHED:
            val = ((self._cfg_sched_policy & 0xF) |
                   ((self._cfg_row_policy & 0xF) << 4))
            return (val, False)
        elif addr == REG_REFRESH:
            val = ((self._cfg_max_postpone & 0xFF) |
                   ((self._cfg_urgent_threshold & 0xFF) << 8) |
                   ((self._cfg_force_refresh & 1) << 16) |
                   ((self._cfg_ref_priority & 0xF) << 20))
            return (val, False)
        elif addr == REG_SELF_REF:
            val = self._cfg_self_ref_mode & 0xF
            return (val, False)
        elif addr == REG_ECC:
            val = self._cfg_ecc_enable & 1
            return (val, False)
        elif addr == REG_BIST_CTRL:
            val = self._cfg_bist_start & 1
            return (val, False)
        elif addr == REG_BIST_PAT:
            val = self._cfg_bist_pattern & 0xFFFFFFFF
            return (val, False)
        elif addr == REG_BIST_ASTART:
            val = self._cfg_bist_addr_start & 0xFFFFFFFF
            return (val, False)
        elif addr == REG_BIST_AEND:
            val = self._cfg_bist_addr_end & 0xFFFFFFFF
            return (val, False)
        elif addr == REG_STATUS:
            val = ((self._sts_init_done & 1) |
                   ((self._sts_cal_done & 1) << 1) |
                   ((self._sts_cal_fail & 1) << 2) |
                   ((self._sts_bist_done & 1) << 3) |
                   ((self._sts_bist_fail & 1) << 4) |
                   ((self._sts_self_refresh_active & 1) << 5))
            return (val, False)
        elif addr == REG_ERR_STATUS:
            val = ((self._sts_ecc_ue_event & 1) |
                   ((self._sts_ref_starve_event & 1) << 1) |
                   ((self._sts_init_fail_event & 1) << 2))
            return (val, False)
        elif addr == REG_ECC_CE_CNT:
            val = self._sts_ecc_ce_count & 0xFFFFFFFF
            return (val, False)
        elif addr == REG_BIST_FADDR:
            val = self._sts_bist_fail_addr & 0xFFFFFFFF
            return (val, False)
        elif addr == REG_REF_PEND_CNT:
            val = self._postpone_cnt & 0xFFFFFFFF
            return (val, False)
        else:
            # Unmapped address -> error
            return (0, True)

    def _write_csr(self, addr, data, sel):
        """Write a CSR register. sel is byte-enable mask (4 bits)."""
        addr = addr & 0xFFFFFFFC  # Word-align
        data = data & 0xFFFFFFFF

        if addr == REG_CTRL:
            if sel & 0x1:
                self._cfg_force_self_ref = (data >> 0) & 1
                self._cfg_bist_start = (data >> 1) & 1
            return False
        elif addr == REG_TIMING_0:
            if sel & 0x3:
                self._cfg_tRCD_nCK = data & 0xFFFF
            if sel & 0xC:
                self._cfg_tRP_nCK = (data >> 16) & 0xFFFF
            return False
        elif addr == REG_TIMING_1:
            if sel & 0x3:
                self._cfg_tRAS_nCK = data & 0xFFFF
            if sel & 0xC:
                self._cfg_tRC_nCK = (data >> 16) & 0xFFFF
            return False
        elif addr == REG_TIMING_2:
            if sel & 0x1:
                self._cfg_tRRD_nCK = data & 0xFF
            if sel & 0x2:
                self._cfg_tWTR_nCK = (data >> 8) & 0xFF
            if sel & 0xC:
                self._cfg_tFAW_nCK = (data >> 16) & 0xFFFF
            return False
        elif addr == REG_TIMING_3:
            if sel & 0x3:
                self._cfg_tRFC_nCK = data & 0xFFFF
            if sel & 0x4:
                self._cfg_tWR_nCK = (data >> 16) & 0xFF
            if sel & 0x8:
                self._cfg_tRTP_nCK = (data >> 24) & 0xFF
            return False
        elif addr == REG_TIMING_4:
            if sel & 0x1:
                self._cfg_CL_nCK = data & 0xFF
            if sel & 0x2:
                self._cfg_CWL_nCK = (data >> 8) & 0xFF
            if sel & 0x4:
                self._cfg_tCCD_nCK = (data >> 16) & 0xFF
            return False
        elif addr == REG_TIMING_5:
            self._cfg_tREFI_nCK = data & 0xFFFFFFFF
            return False
        elif addr == REG_SCHED:
            if sel & 0x1:
                self._cfg_sched_policy = data & 0xF
                self._cfg_row_policy = (data >> 4) & 0xF
            return False
        elif addr == REG_REFRESH:
            if sel & 0x1:
                self._cfg_max_postpone = data & 0xFF
            if sel & 0x2:
                self._cfg_urgent_threshold = (data >> 8) & 0xFF
            if sel & 0x4:
                self._cfg_force_refresh = (data >> 16) & 1
            if sel & 0x8:
                self._cfg_ref_priority = (data >> 20) & 0xF
            return False
        elif addr == REG_SELF_REF:
            if sel & 0x1:
                self._cfg_self_ref_mode = data & 0xF
            return False
        elif addr == REG_ECC:
            if sel & 0x1:
                self._cfg_ecc_enable = data & 1
            return False
        elif addr == REG_BIST_CTRL:
            if sel & 0x1:
                self._cfg_bist_start = data & 1
            return False
        elif addr == REG_BIST_PAT:
            self._cfg_bist_pattern = data & 0xFFFFFFFF
            return False
        elif addr == REG_BIST_ASTART:
            self._cfg_bist_addr_start = data & 0xFFFFFFFF
            return False
        elif addr == REG_BIST_AEND:
            self._cfg_bist_addr_end = data & 0xFFFFFFFF
            return False
        elif addr in (REG_STATUS, REG_ERR_STATUS, REG_ECC_CE_CNT,
                       REG_BIST_FADDR, REG_REF_PEND_CNT):
            # Read-only registers: write has no effect, but no error
            return False
        else:
            return True  # error for unmapped address

    def step(self, **inputs):
        """
        Advance the model by one clock cycle.

        Accepts input signals as keyword arguments, ignores unknown ones.
        Returns a dict with ALL output signal names and their current integer values.
        """
        # Extract known inputs with defaults
        csr_cyc_i = inputs.get("csr_cyc_i", 0)
        csr_stb_i = inputs.get("csr_stb_i", 0)
        csr_we_i  = inputs.get("csr_we_i", 0)
        csr_adr_i = inputs.get("csr_adr_i", 0)
        csr_dat_i = inputs.get("csr_dat_i", 0)
        csr_sel_i = inputs.get("csr_sel_i", 0xF)
        init_done = inputs.get("init_done", 0)
        ref_ack   = inputs.get("ref_ack", 0)

        # Status inputs
        self._sts_init_done           = inputs.get("sts_init_done", self._sts_init_done)
        self._sts_cal_done            = inputs.get("sts_cal_done", self._sts_cal_done)
        self._sts_cal_fail            = inputs.get("sts_cal_fail", self._sts_cal_fail)
        self._sts_bist_done           = inputs.get("sts_bist_done", self._sts_bist_done)
        self._sts_bist_fail           = inputs.get("sts_bist_fail", self._sts_bist_fail)
        self._sts_ref_pending_cnt     = inputs.get("sts_ref_pending_cnt", self._sts_ref_pending_cnt)
        self._sts_self_refresh_active = inputs.get("sts_self_refresh_active", self._sts_self_refresh_active)
        self._sts_ecc_ce_count        = inputs.get("sts_ecc_ce_count", self._sts_ecc_ce_count)
        self._sts_ecc_ue_event        = inputs.get("sts_ecc_ue_event", self._sts_ecc_ue_event)
        self._sts_ref_starve_event    = inputs.get("sts_ref_starve_event", self._sts_ref_starve_event)
        self._sts_init_fail_event     = inputs.get("sts_init_fail_event", self._sts_init_fail_event)
        self._sts_bist_fail_addr      = inputs.get("sts_bist_fail_addr", self._sts_bist_fail_addr)

        # =================================================================
        # 1. CSR Wishbone Interface (pipelined: 1 cycle ack latency)
        # =================================================================
        csr_ack_o = 0
        csr_dat_o = 0
        csr_err_o = 0

        if self._wb_ack_pending:
            csr_ack_o = 1
            csr_dat_o = self._wb_dat_pending
            csr_err_o = 1 if self._wb_err_pending else 0
            self._wb_ack_pending = False
            self._wb_dat_pending = 0
            self._wb_err_pending = False

        # Process new Wishbone transaction
        if csr_cyc_i and csr_stb_i and not self._wb_ack_pending:
            if csr_we_i:
                # Write transaction
                err = self._write_csr(csr_adr_i, csr_dat_i, csr_sel_i)
                self._wb_ack_pending = True
                self._wb_dat_pending = 0
                self._wb_err_pending = err
            else:
                # Read transaction
                data, err = self._read_csr(csr_adr_i)
                self._wb_ack_pending = True
                self._wb_dat_pending = data
                self._wb_err_pending = err

        # =================================================================
        # 2. Refresh Controller State Machine
        # =================================================================
        # Track init_done transitions
        self._init_done_prev = self._init_done_curr
        self._init_done_curr = init_done

        if not init_done:
            # While init_done=0, hold counters at 0
            self._refi_counter = 0
            self._postpone_cnt = 0
            self._ref_required = 0
            self._ref_urgent = 0
            self._ref_starve_flag = 0
        else:
            # init_done is active

            # Handle ref_ack: decrement postpone_cnt
            if ref_ack and self._postpone_cnt > 0:
                self._postpone_cnt -= 1

            # Handle force_refresh from CSR
            if self._cfg_force_refresh:
                if self._postpone_cnt < self._cfg_max_postpone:
                    self._postpone_cnt += 1
                # Force refresh is a one-shot; auto-clear
                self._cfg_force_refresh = 0

            # tREFI down-counter logic
            #
            # The counter starts at 0 after reset/init. When we see counter==0,
            # a refi_tick fires: postpone_cnt increments, and the counter reloads
            # to cfg_tREFI_nCK - 1. This gives exactly cfg_tREFI_nCK cycles
            # between consecutive ticks:
            #   - Tick fires (counter==0), reload to N-1
            #   - N-1 decrement cycles: N-1 -> N-2 -> ... -> 1 -> 0
            #   - That's N-1 cycles of decrementing, plus the tick cycle = N cycles total
            #
            # On the very first cycle after init_done, counter is 0 (from reset),
            # so a tick fires immediately.
            if self._refi_counter == 0:
                # refi_tick fires: increment postpone_cnt (capped at max_postpone)
                if self._postpone_cnt < self._cfg_max_postpone:
                    self._postpone_cnt += 1
                # Reload counter
                if self._cfg_tREFI_nCK > 1:
                    self._refi_counter = self._cfg_tREFI_nCK - 1
                else:
                    # tREFI of 0 or 1: tick every cycle
                    self._refi_counter = 0
            else:
                self._refi_counter -= 1

            # Compute refresh flags
            self._ref_required = 1 if self._postpone_cnt > 0 else 0
            self._ref_urgent = 1 if self._postpone_cnt >= self._cfg_urgent_threshold else 0
            self._ref_starve_flag = 1 if self._postpone_cnt >= self._cfg_max_postpone else 0

        # =================================================================
        # 3. Build output dict
        # =================================================================
        outputs = {
            "csr_ack_o": csr_ack_o,
            "csr_dat_o": csr_dat_o & 0xFFFFFFFF,
            "csr_err_o": csr_err_o,

            # Timing configuration outputs
            "cfg_tRCD_nCK": self._cfg_tRCD_nCK,
            "cfg_tRP_nCK": self._cfg_tRP_nCK,
            "cfg_tRAS_nCK": self._cfg_tRAS_nCK,
            "cfg_tRC_nCK": self._cfg_tRC_nCK,
            "cfg_tRRD_nCK": self._cfg_tRRD_nCK,
            "cfg_tWTR_nCK": self._cfg_tWTR_nCK,
            "cfg_tFAW_nCK": self._cfg_tFAW_nCK,
            "cfg_tRFC_nCK": self._cfg_tRFC_nCK,
            "cfg_tWR_nCK": self._cfg_tWR_nCK,
            "cfg_tRTP_nCK": self._cfg_tRTP_nCK,
            "cfg_CL_nCK": self._cfg_CL_nCK,
            "cfg_CWL_nCK": self._cfg_CWL_nCK,
            "cfg_tCCD_nCK": self._cfg_tCCD_nCK,

            # Scheduler/policy configuration outputs
            "cfg_sched_policy": self._cfg_sched_policy,
            "cfg_row_policy": self._cfg_row_policy,
            "cfg_self_ref_mode": self._cfg_self_ref_mode,
            "cfg_ecc_enable": self._cfg_ecc_enable,
            "cfg_bist_start": self._cfg_bist_start,
            "cfg_force_self_ref": self._cfg_force_self_ref,
            "cfg_bist_pattern": self._cfg_bist_pattern,
            "cfg_bist_addr_mode": self._cfg_bist_addr_mode,
            "cfg_bist_addr_start": self._cfg_bist_addr_start,
            "cfg_bist_addr_end": self._cfg_bist_addr_end,

            # Refresh controller outputs
            "ref_required": self._ref_required,
            "ref_urgent": self._ref_urgent,
            "ref_pending_cnt": self._postpone_cnt,
            "ref_starve_flag": self._ref_starve_flag,
        }

        return outputs

    def get_state(self) -> dict:
        """Return a dict with the full internal state for debugging."""
        return {
            # CSR WB state
            "wb_ack_pending": self._wb_ack_pending,
            "wb_dat_pending": self._wb_dat_pending,
            "wb_err_pending": self._wb_err_pending,

            # Timing config
            "cfg_tRCD_nCK": self._cfg_tRCD_nCK,
            "cfg_tRP_nCK": self._cfg_tRP_nCK,
            "cfg_tRAS_nCK": self._cfg_tRAS_nCK,
            "cfg_tRC_nCK": self._cfg_tRC_nCK,
            "cfg_tRRD_nCK": self._cfg_tRRD_nCK,
            "cfg_tWTR_nCK": self._cfg_tWTR_nCK,
            "cfg_tFAW_nCK": self._cfg_tFAW_nCK,
            "cfg_tRFC_nCK": self._cfg_tRFC_nCK,
            "cfg_tWR_nCK": self._cfg_tWR_nCK,
            "cfg_tRTP_nCK": self._cfg_tRTP_nCK,
            "cfg_CL_nCK": self._cfg_CL_nCK,
            "cfg_CWL_nCK": self._cfg_CWL_nCK,
            "cfg_tCCD_nCK": self._cfg_tCCD_nCK,
            "cfg_tREFI_nCK": self._cfg_tREFI_nCK,

            # Refresh config
            "cfg_max_postpone": self._cfg_max_postpone,
            "cfg_urgent_threshold": self._cfg_urgent_threshold,
            "cfg_force_refresh": self._cfg_force_refresh,
            "cfg_ref_priority": self._cfg_ref_priority,

            # Scheduler config
            "cfg_sched_policy": self._cfg_sched_policy,
            "cfg_row_policy": self._cfg_row_policy,
            "cfg_self_ref_mode": self._cfg_self_ref_mode,
            "cfg_ecc_enable": self._cfg_ecc_enable,
            "cfg_bist_start": self._cfg_bist_start,
            "cfg_force_self_ref": self._cfg_force_self_ref,
            "cfg_bist_pattern": self._cfg_bist_pattern,
            "cfg_bist_addr_mode": self._cfg_bist_addr_mode,
            "cfg_bist_addr_start": self._cfg_bist_addr_start,
            "cfg_bist_addr_end": self._cfg_bist_addr_end,

            # Refresh controller state
            "refi_counter": self._refi_counter,
            "postpone_cnt": self._postpone_cnt,
            "ref_required": self._ref_required,
            "ref_urgent": self._ref_urgent,
            "ref_starve_flag": self._ref_starve_flag,
            "init_done_curr": self._init_done_curr,
            "init_done_prev": self._init_done_prev,
        }


def run_self_test():
    """Run self-test and print per-test PASS/FAIL."""
    results = []

    def check(test_name, condition):
        status = "PASS" if condition else "FAIL"
        results.append((test_name, condition))
        print(f"  {status}: {test_name}")

    # =========================================================================
    # Test 1: After reset, all outputs are at their reset values
    # =========================================================================
    print("Test 1: Reset values")
    m = PathModel()
    out = m.step()

    check("csr_ack_o == 0 after reset",          out["csr_ack_o"] == 0)
    check("csr_dat_o == 0 after reset",           out["csr_dat_o"] == 0)
    check("csr_err_o == 0 after reset",           out["csr_err_o"] == 0)
    check("cfg_tRCD_nCK == 11 after reset",       out["cfg_tRCD_nCK"] == 11)
    check("cfg_tRP_nCK == 11 after reset",        out["cfg_tRP_nCK"] == 11)
    check("cfg_tRAS_nCK == 28 after reset",       out["cfg_tRAS_nCK"] == 28)
    check("cfg_tRC_nCK == 39 after reset",        out["cfg_tRC_nCK"] == 39)
    check("cfg_tRRD_nCK == 6 after reset",        out["cfg_tRRD_nCK"] == 6)
    check("cfg_tWTR_nCK == 6 after reset",        out["cfg_tWTR_nCK"] == 6)
    check("cfg_tFAW_nCK == 32 after reset",       out["cfg_tFAW_nCK"] == 32)
    check("cfg_tRFC_nCK == 128 after reset",      out["cfg_tRFC_nCK"] == 128)
    check("cfg_tWR_nCK == 12 after reset",        out["cfg_tWR_nCK"] == 12)
    check("cfg_tRTP_nCK == 6 after reset",        out["cfg_tRTP_nCK"] == 6)
    check("cfg_CL_nCK == 11 after reset",         out["cfg_CL_nCK"] == 11)
    check("cfg_CWL_nCK == 8 after reset",         out["cfg_CWL_nCK"] == 8)
    check("cfg_tCCD_nCK == 4 after reset",        out["cfg_tCCD_nCK"] == 4)
    check("cfg_sched_policy == 0 after reset",    out["cfg_sched_policy"] == 0)
    check("cfg_row_policy == 0 after reset",      out["cfg_row_policy"] == 0)
    check("cfg_self_ref_mode == 0 after reset",   out["cfg_self_ref_mode"] == 0)
    check("cfg_ecc_enable == 0 after reset",      out["cfg_ecc_enable"] == 0)
    check("cfg_bist_start == 0 after reset",      out["cfg_bist_start"] == 0)
    check("cfg_force_self_ref == 0 after reset",  out["cfg_force_self_ref"] == 0)
    check("cfg_bist_pattern == 0 after reset",    out["cfg_bist_pattern"] == 0)
    check("cfg_bist_addr_mode == 0 after reset",  out["cfg_bist_addr_mode"] == 0)
    check("cfg_bist_addr_start == 0 after reset", out["cfg_bist_addr_start"] == 0)
    check("cfg_bist_addr_end == 536870911 after reset", out["cfg_bist_addr_end"] == 536870911)
    check("ref_required == 0 after reset",        out["ref_required"] == 0)
    check("ref_urgent == 0 after reset",          out["ref_urgent"] == 0)
    check("ref_pending_cnt == 0 after reset",     out["ref_pending_cnt"] == 0)
    check("ref_starve_flag == 0 after reset",     out["ref_starve_flag"] == 0)

    # =========================================================================
    # Test 2: step() returns all expected output keys
    # =========================================================================
    print("\nTest 2: Output keys completeness")
    m.reset()
    out = m.step()
    all_keys_present = all(k in out for k in PathModel.OUTPUT_SIGNALS)
    check("All output signal keys present", all_keys_present)
    if not all_keys_present:
        missing = [k for k in PathModel.OUTPUT_SIGNALS if k not in out]
        print(f"    Missing keys: {missing}")

    # =========================================================================
    # Test 3: step() accepts and ignores unknown kwargs
    # =========================================================================
    print("\nTest 3: Unknown kwargs handling")
    m.reset()
    try:
        out = m.step(unknown_signal_xyz=42, another_bogus=99)
        check("step() ignores unknown kwargs", True)
    except Exception as e:
        check(f"step() ignores unknown kwargs (raised {e})", False)

    # =========================================================================
    # Test 4: CSR Write then Read (refresh config register)
    # =========================================================================
    print("\nTest 4: CSR Write/Read refresh config")
    m.reset()

    # Write to REG_REFRESH: max_postpone=4, urgent_threshold=3, force_refresh=0, ref_priority=2
    write_data = (4 & 0xFF) | ((3 & 0xFF) << 8) | ((0 & 1) << 16) | ((2 & 0xF) << 20)
    out = m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
                 csr_adr_i=REG_REFRESH, csr_dat_i=write_data, csr_sel_i=0xF)
    check("Write cycle: no immediate ack", out["csr_ack_o"] == 0)

    out = m.step(csr_cyc_i=1, csr_stb_i=0)  # Wait for ack
    check("Write ack in next cycle", out["csr_ack_o"] == 1)

    # Now read back
    out = m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=0,
                 csr_adr_i=REG_REFRESH, csr_sel_i=0xF)
    check("Read cycle: no immediate ack", out["csr_ack_o"] == 0)

    out = m.step(csr_cyc_i=1, csr_stb_i=0)
    check("Read ack in next cycle", out["csr_ack_o"] == 1)
    expected_read = (4 & 0xFF) | ((3 & 0xFF) << 8) | ((0 & 1) << 16) | ((2 & 0xF) << 20)
    check(f"Read data matches written ({out['csr_dat_o']} == {expected_read})",
          out["csr_dat_o"] == expected_read)

    # Verify config signals updated
    state = m.get_state()
    check("cfg_max_postpone updated to 4", state["cfg_max_postpone"] == 4)
    check("cfg_urgent_threshold updated to 3", state["cfg_urgent_threshold"] == 3)
    check("cfg_ref_priority updated to 2", state["cfg_ref_priority"] == 2)

    # =========================================================================
    # Test 5: Refresh controller - init_done triggers immediate refi_tick
    # =========================================================================
    print("\nTest 5: Refresh counter immediate tick on init_done")
    m.reset()

    # Run a cycle with init_done=0
    out = m.step(init_done=0)
    check("ref_pending_cnt == 0 while init_done=0", out["ref_pending_cnt"] == 0)
    check("ref_required == 0 while init_done=0", out["ref_required"] == 0)

    # Set init_done=1 -> immediate refi_tick because counter is 0
    out = m.step(init_done=1)
    check("ref_pending_cnt == 1 on first cycle after init_done", out["ref_pending_cnt"] == 1)
    check("ref_required == 1 on first cycle after init_done", out["ref_required"] == 1)
    check("ref_urgent == 0 (1 < 6 threshold)", out["ref_urgent"] == 0)

    # Verify refi_counter was reloaded
    state = m.get_state()
    check(f"refi_counter reloaded to {DEFAULT_tREFI_nCK - 1}", state["refi_counter"] == DEFAULT_tREFI_nCK - 1)

    # =========================================================================
    # Test 6: Refresh controller - ref_ack decrements postpone_cnt
    # =========================================================================
    print("\nTest 6: ref_ack decrements postpone_cnt")
    # Continue from Test 5 state (postpone_cnt=1)
    out = m.step(init_done=1, ref_ack=1)
    check("ref_pending_cnt == 0 after ref_ack", out["ref_pending_cnt"] == 0)
    check("ref_required == 0 after ref_ack", out["ref_required"] == 0)

    # =========================================================================
    # Test 7: Refresh urgent threshold
    # =========================================================================
    print("\nTest 7: Urgent threshold and starvation")
    m.reset()

    # Configure with small tREFI so we can accumulate postponed refreshes quickly
    # Write tREFI = 2 (very short for testing)
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_TIMING_5, csr_dat_i=2, csr_sel_i=0xF)
    m.step(csr_cyc_i=1, csr_stb_i=0)  # wait for ack

    # init_done=1 -> first tick (postpone=1, counter reloads to 1)
    out = m.step(init_done=1)
    check("After init: postpone_cnt=1", out["ref_pending_cnt"] == 1)

    # With tREFI=2, counter reloads to 1 (tREFI-1). So:
    # Next cycle: counter 1->0 (decrement), no tick on this cycle
    # Cycle after: counter==0 -> tick fires -> postpone increments, reload to 1
    # So each tick happens every 2 cycles after the initial one.

    # counter=1 -> decrement to 0
    out = m.step(init_done=1)
    check("After 1 cycle: postpone_cnt still 1", out["ref_pending_cnt"] == 1)

    # Next step: counter==0 -> tick fires -> postpone=2, reload counter to 1
    out = m.step(init_done=1)
    check("After 2 more cycles: postpone_cnt=2", out["ref_pending_cnt"] == 2)

    # Keep running to accumulate more
    for i in range(2):
        out = m.step(init_done=1)
    check("After 2 more: postpone_cnt=3", out["ref_pending_cnt"] == 3)

    for i in range(2):
        out = m.step(init_done=1)
    check("After 2 more: postpone_cnt=4", out["ref_pending_cnt"] == 4)

    for i in range(2):
        out = m.step(init_done=1)
    check("After 2 more: postpone_cnt=5", out["ref_pending_cnt"] == 5)

    for i in range(2):
        out = m.step(init_done=1)
    check("After 2 more: postpone_cnt=6 (urgent)", out["ref_pending_cnt"] == 6)
    check("ref_urgent asserted at threshold", out["ref_urgent"] == 1)

    for i in range(2):
        out = m.step(init_done=1)
    check("After 2 more: postpone_cnt=7", out["ref_pending_cnt"] == 7)

    for i in range(2):
        out = m.step(init_done=1)
    # max_postpone=8, so should be capped at 8
    check("postpone_cnt capped at max_postpone=8", out["ref_pending_cnt"] == 8)
    check("ref_starve_flag asserted at max_postpone", out["ref_starve_flag"] == 1)

    # One more tREFI interval should not go above 8
    for i in range(2):
        out = m.step(init_done=1)
    check("postpone_cnt stays at 8 (capped)", out["ref_pending_cnt"] == 8)

    # =========================================================================
    # Test 8: CSR write to tREFI propagates to refresh controller
    # =========================================================================
    print("\nTest 8: tREFI CSR write propagation")
    m.reset()

    # Write tREFI = 100
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_TIMING_5, csr_dat_i=100, csr_sel_i=0xF)
    m.step(csr_cyc_i=1, csr_stb_i=0)

    # Enable init_done -> immediate tick, reload to 99
    out = m.step(init_done=1)
    state = m.get_state()
    check("tREFI written as 100, refi_counter=99 after init", state["refi_counter"] == 99)
    check("postpone_cnt=1 after init", out["ref_pending_cnt"] == 1)

    # Run 98 more cycles -> counter goes from 99 down to 1
    for i in range(98):
        out = m.step(init_done=1)
    check("postpone_cnt=1 after 98 cycles (counter=1)", out["ref_pending_cnt"] == 1)

    # One more cycle -> counter goes from 1 to 0 (decrement, no tick yet)
    out = m.step(init_done=1)
    check("postpone_cnt=1 after 99 cycles (counter=0)", out["ref_pending_cnt"] == 1)

    # One more cycle -> counter==0 -> tick -> postpone=2
    out = m.step(init_done=1)
    check("postpone_cnt=2 after tREFI expires", out["ref_pending_cnt"] == 2)

    # =========================================================================
    # Test 9: CSR refresh config write changes urgent threshold, max_postpone
    # =========================================================================
    print("\nTest 9: Changing urgent_threshold via CSR")
    m.reset()

    # Set urgent_threshold to 2, max_postpone to 3, tREFI to 2
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_TIMING_5, csr_dat_i=2, csr_sel_i=0xF)
    m.step(csr_cyc_i=1, csr_stb_i=0)

    refresh_val = (3 & 0xFF) | ((2 & 0xFF) << 8) | ((0 & 1) << 16) | ((1 & 0xF) << 20)
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_REFRESH, csr_dat_i=refresh_val, csr_sel_i=0xF)
    m.step(csr_cyc_i=1, csr_stb_i=0)

    # init_done -> postpone=1
    out = m.step(init_done=1)
    check("postpone=1, not urgent yet", out["ref_urgent"] == 0)

    # 2 more cycles -> postpone=2 (hits urgent threshold of 2)
    m.step(init_done=1)
    out = m.step(init_done=1)
    check("postpone=2, ref_urgent=1 (threshold=2)", out["ref_urgent"] == 1)

    # 2 more cycles -> postpone=3 (hits max_postpone of 3)
    m.step(init_done=1)
    out = m.step(init_done=1)
    check("postpone=3, ref_starve_flag=1 (max=3)", out["ref_starve_flag"] == 1)

    # =========================================================================
    # Test 10: CSR error on unmapped address
    # =========================================================================
    print("\nTest 10: CSR error on unmapped address")
    m.reset()
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=0,
           csr_adr_i=0x100, csr_sel_i=0xF)
    out = m.step(csr_cyc_i=1, csr_stb_i=0)
    check("Error on unmapped read", out["csr_err_o"] == 1)

    # =========================================================================
    # Test 11: Refresh counter held at 0 while init_done=0
    # =========================================================================
    print("\nTest 11: Counter held at 0 while init_done=0")
    m.reset()
    for _ in range(10):
        out = m.step(init_done=0)
    check("ref_pending_cnt stays 0 with init_done=0", out["ref_pending_cnt"] == 0)
    check("ref_required stays 0 with init_done=0", out["ref_required"] == 0)

    # =========================================================================
    # Test 12: init_done going back to 0 resets refresh state
    # =========================================================================
    print("\nTest 12: init_done deassert resets refresh state")
    m.reset()
    # Set short tREFI
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_TIMING_5, csr_dat_i=2, csr_sel_i=0xF)
    m.step(csr_cyc_i=1, csr_stb_i=0)

    # Accumulate some refreshes
    m.step(init_done=1)  # postpone=1
    m.step(init_done=1)
    out = m.step(init_done=1)  # postpone=2
    check("Accumulated postpone > 0", out["ref_pending_cnt"] > 0)

    # Deassert init_done
    out = m.step(init_done=0)
    check("Deassert init_done: postpone_cnt=0", out["ref_pending_cnt"] == 0)
    check("Deassert init_done: ref_required=0", out["ref_required"] == 0)

    # =========================================================================
    # Test 13: Force refresh via CSR
    # =========================================================================
    print("\nTest 13: Force refresh via CSR")
    m.reset()

    # Set init_done, get initial tick (postpone=1)
    out = m.step(init_done=1)
    check("Initial postpone=1", out["ref_pending_cnt"] == 1)

    # Ack the initial refresh
    out = m.step(init_done=1, ref_ack=1)
    check("After ack: postpone=0", out["ref_pending_cnt"] == 0)

    # Write force_refresh=1 to CSR
    refresh_val = ((8 & 0xFF) | ((6 & 0xFF) << 8) |
                   ((1 & 1) << 16) | ((1 & 0xF) << 20))
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_REFRESH, csr_dat_i=refresh_val, csr_sel_i=0xF,
           init_done=1)
    out = m.step(csr_cyc_i=1, csr_stb_i=0, init_done=1)
    # The force_refresh is processed in the step where it is set
    # It auto-clears, so next step it should be 0
    # The postpone_cnt should have been incremented by force_refresh
    # Note: force refresh increments during the step where cfg_force_refresh is first seen
    # Let's check by running another step
    out = m.step(init_done=1)
    # At this point, force_refresh was consumed. Let's check state
    state = m.get_state()
    check("Force refresh auto-cleared", state["cfg_force_refresh"] == 0)

    # =========================================================================
    # Test 14: Timing register write/read roundtrip
    # =========================================================================
    print("\nTest 14: Timing register write/read roundtrip")
    m.reset()

    # Write tRCD=5, tRP=7
    write_data = (5 & 0xFFFF) | ((7 & 0xFFFF) << 16)
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=REG_TIMING_0, csr_dat_i=write_data, csr_sel_i=0xF)
    m.step(csr_cyc_i=1, csr_stb_i=0)

    out = m.step()
    check("cfg_tRCD_nCK updated to 5", out["cfg_tRCD_nCK"] == 5)
    check("cfg_tRP_nCK updated to 7", out["cfg_tRP_nCK"] == 7)

    # Read back
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=0,
           csr_adr_i=REG_TIMING_0, csr_sel_i=0xF)
    out = m.step(csr_cyc_i=1, csr_stb_i=0)
    expected = (5 & 0xFFFF) | ((7 & 0xFFFF) << 16)
    check(f"Timing readback matches ({out['csr_dat_o']} == {expected})", out["csr_dat_o"] == expected)

    # =========================================================================
    # Test 15: Multiple output signals all present every cycle
    # =========================================================================
    print("\nTest 15: All output signals present on every step")
    m.reset()
    for cycle in range(5):
        out = m.step(init_done=(cycle > 2))
        all_present = all(k in out for k in PathModel.OUTPUT_SIGNALS)
        if not all_present:
            missing = [k for k in PathModel.OUTPUT_SIGNALS if k not in out]
            check(f"Cycle {cycle}: all keys present (missing: {missing})", False)
            break
    else:
        check("All keys present across 5 cycles", True)

    # =========================================================================
    # Summary
    # =========================================================================
    print()
    total = len(results)
    passed = sum(1 for _, ok in results if ok)
    failed = total - passed
    print(f"Results: {passed}/{total} passed, {failed} failed")
    if failed == 0:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        for name, ok in results:
            if not ok:
                print(f"  FAILED: {name}")


if __name__ == "__main__":
    run_self_test()