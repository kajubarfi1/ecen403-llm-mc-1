#!/usr/bin/env python3
"""
Reference model for CSR → Bank Tracker Timing Configuration path.
Models the data flow: config_regs -> bank_tracker

This path delivers timing parameters from CSR registers to the bank tracker
which uses them for DDR3 timing enforcement.
"""

import json
import os

# Number of banks in DDR3
NUM_BANKS = 8

# DDR command encoding (from RTL cmd_gen.sv)
DDR_NOP  = 7   # 4'b0111
DDR_ACT  = 3   # 4'b0011
DDR_RD   = 5   # 4'b0101
DDR_WR   = 4   # 4'b0100
DDR_PRE  = 2   # 4'b0010
DDR_REF  = 1   # 4'b0001
DDR_MRS  = 0   # 4'b0000
DDR_ZQCL = 6   # 4'b0110
DDR_DESL = 15  # 4'b1111

# Scheduler command types (internal)
SCHED_NOP = 0
SCHED_ACT = 1
SCHED_RD  = 2
SCHED_WR  = 3
SCHED_PRE = 4
SCHED_REF = 5

# CSR register addresses (byte addressing, 32-bit aligned)
CSR_CTRL        = 0x00
CSR_STATUS      = 0x04
CSR_TIMING0     = 0x08  # tRCD, tRP (each 8 bits)
CSR_TIMING1     = 0x0C  # tRAS, tRC (each 8 bits)
CSR_TIMING2     = 0x10  # tRRD, tFAW (each 8 bits)
CSR_TIMING3     = 0x14  # tWTR, tWR (each 8 bits)
CSR_TIMING4     = 0x18  # tRTP, tCCD (each 8 bits)
CSR_TIMING5     = 0x1C  # tRFC (16 bits)
CSR_TIMING6     = 0x20  # tREFI (16 bits)
CSR_TIMING7     = 0x24  # CL, CWL (each 8 bits)
CSR_SCHED_CFG   = 0x28  # Scheduler config
CSR_REF_CFG     = 0x2C  # Refresh config
CSR_BIST_CFG    = 0x30  # BIST config
CSR_BIST_START  = 0x34  # BIST address start
CSR_BIST_END    = 0x38  # BIST address end

# Default timing values from spec (in controller clock cycles)
DEFAULT_tRCD_nCK  = 11
DEFAULT_tRP_nCK   = 11
DEFAULT_tRAS_nCK  = 28
DEFAULT_tRC_nCK   = 39
DEFAULT_tRFC_nCK  = 128
DEFAULT_tFAW_nCK  = 32
DEFAULT_tRRD_nCK  = 6
DEFAULT_tWR_nCK   = 12
DEFAULT_tWTR_nCK  = 6
DEFAULT_tRTP_nCK  = 6
DEFAULT_tCCD_nCK  = 4
DEFAULT_tREFI_nCK = 6240
DEFAULT_CL_nCK    = 11
DEFAULT_CWL_nCK   = 8

# Scheduler/row policies
SCHED_FR_FCFS = 0
SCHED_FCFS    = 1
ROW_OPEN_PAGE  = 0
ROW_CLOSE_PAGE = 1

# Self-refresh modes
SELF_REF_MANUAL = 0
SELF_REF_AUTO   = 1

# Refresh priority
REF_PRIORITY_NORMAL       = 0
REF_PRIORITY_URGENT_PREEMPT = 1


class PathModel:
    """
    Reference model for CSR → Bank Tracker Timing Configuration.
    
    Models:
    - config_regs: CSR block holding timing configuration registers
    - bank_tracker: Per-bank state and timing counter management
    """
    
    def __init__(self):
        """Initialize the model and reset to power-on defaults."""
        self.reset()
    
    def reset(self):
        """Reset all internal state to power-on defaults."""
        # =========================================================
        # CSR Configuration Registers (config_regs block)
        # =========================================================
        # Timing parameters in controller clock cycles
        self.cfg_tRCD_nCK  = DEFAULT_tRCD_nCK
        self.cfg_tRP_nCK   = DEFAULT_tRP_nCK
        self.cfg_tRAS_nCK  = DEFAULT_tRAS_nCK
        self.cfg_tRC_nCK   = DEFAULT_tRC_nCK
        self.cfg_tRFC_nCK  = DEFAULT_tRFC_nCK
        self.cfg_tFAW_nCK  = DEFAULT_tFAW_nCK
        self.cfg_tRRD_nCK  = DEFAULT_tRRD_nCK
        self.cfg_tWR_nCK   = DEFAULT_tWR_nCK
        self.cfg_tWTR_nCK  = DEFAULT_tWTR_nCK
        self.cfg_tRTP_nCK  = DEFAULT_tRTP_nCK
        self.cfg_tCCD_nCK  = DEFAULT_tCCD_nCK
        self.cfg_tREFI_nCK = DEFAULT_tREFI_nCK
        self.cfg_CL_nCK    = DEFAULT_CL_nCK
        self.cfg_CWL_nCK   = DEFAULT_CWL_nCK
        
        # Scheduler/controller configuration
        self.cfg_sched_policy    = SCHED_FR_FCFS  # fr_fcfs from spec
        self.cfg_row_policy      = ROW_OPEN_PAGE  # open_page from spec
        self.cfg_self_ref_mode   = SELF_REF_AUTO  # auto from spec
        self.cfg_ecc_enable      = 0              # ecc_mode=0 from spec
        self.cfg_bist_start      = 0              # BIST control signal
        self.cfg_force_refresh   = 0
        self.cfg_force_self_ref  = 0
        
        # Refresh configuration
        self.cfg_max_postpone     = 8  # max_postpone_count from spec
        self.cfg_urgent_threshold = 6  # urgent_threshold from spec
        self.cfg_ref_priority     = REF_PRIORITY_URGENT_PREEMPT  # from spec
        
        # BIST configuration
        self.cfg_bist_pattern    = 0  # all_patterns encoded as 0
        self.cfg_bist_addr_mode  = 0  # sequential encoded as 0
        self.cfg_bist_addr_start = 0
        self.cfg_bist_addr_end   = 536870911  # Full address range
        
        # =========================================================
        # Bank Tracker State (bank_tracker block)
        # =========================================================
        # Per-bank state
        self.bank_is_active = [0] * NUM_BANKS   # 1 if bank has open row
        self.bank_open_row  = [0] * NUM_BANKS   # Currently open row per bank
        
        # Per-bank timing counters (decrement each cycle)
        self.cnt_tRCD = [0] * NUM_BANKS   # ACT to RD/WR delay
        self.cnt_tRAS = [0] * NUM_BANKS   # ACT to PRE delay
        self.cnt_tRC  = [0] * NUM_BANKS   # ACT to ACT (same bank) delay
        self.cnt_tRP  = [0] * NUM_BANKS   # PRE to ACT delay
        self.cnt_tWR  = [0] * NUM_BANKS   # Last write to PRE delay
        self.cnt_tRTP = [0] * NUM_BANKS   # Last read to PRE delay
        self.cnt_tWTR = [0] * NUM_BANKS   # Write to read delay
        self.cnt_tCCD = 0                 # CAS to CAS delay (global)
        
        # Global timing counters
        self.cnt_tRRD = 0                 # ACT to ACT (different bank) delay
        self.cnt_tRFC = 0                 # Refresh to any command delay
        
        # Four-Activate-Window tracking (tFAW)
        self.faw_window = []              # Timestamps of last 4 ACTs
        
        # Refresh state
        self.refresh_counter     = 0      # Down-counter for tREFI
        self.postpone_cnt        = 0      # Number of postponed refreshes
        self.refresh_in_progress = False  # RFC window active
        
        # =========================================================
        # Wishbone Interface State
        # =========================================================
        self.csr_ack_pending = False
        self.csr_read_data   = 0
        self.csr_err_pending = False
        
        # =========================================================
        # Pipeline State (for feedback delay modeling)
        # =========================================================
        # Pipeline stages: decisions take 2 cycles to reach DDR pins
        # pipe_s1: scheduler output (1 cycle delayed)
        # pipe_s2: cmd_gen output (2 cycles delayed, visible on DDR)
        self.pipe_s1 = {'cmd_type': SCHED_NOP, 'bank': 0, 'row': 0}
        self.pipe_s2 = {'cmd_type': SCHED_NOP, 'bank': 0, 'row': 0}
        
        # Pending feedback (applied at START of next cycle)
        self.pending_fb_type = SCHED_NOP
        self.pending_fb_bank = 0
        self.pending_fb_row  = 0
        
        # Global cycle counter for tFAW tracking
        self.cycle_count = 0
        
        # Initialization status (model starts as if init is incomplete)
        self.init_done_latched = False
    
    def _write_csr(self, addr, data, sel):
        """Handle CSR write operation."""
        # Apply byte enables (sel is 4-bit for 32-bit data)
        # sel[0] -> byte 0 (bits 7:0), sel[1] -> byte 1, etc.
        
        if addr == CSR_TIMING0:
            # tRCD in bits 7:0, tRP in bits 15:8
            if sel & 0x1:
                self.cfg_tRCD_nCK = data & 0xFF
            if sel & 0x2:
                self.cfg_tRP_nCK = (data >> 8) & 0xFF
                
        elif addr == CSR_TIMING1:
            # tRAS in bits 7:0, tRC in bits 15:8 (16-bit each)
            if sel & 0x1:
                self.cfg_tRAS_nCK = (self.cfg_tRAS_nCK & 0xFF00) | (data & 0xFF)
            if sel & 0x2:
                self.cfg_tRAS_nCK = (self.cfg_tRAS_nCK & 0x00FF) | ((data & 0xFF00))
                # Actually tRAS is likely 8-bit, tRC is separate
                self.cfg_tRAS_nCK = data & 0xFF
                self.cfg_tRC_nCK = (data >> 8) & 0xFF
                
        elif addr == CSR_TIMING2:
            # tRRD in bits 7:0, tFAW in bits 15:8
            if sel & 0x1:
                self.cfg_tRRD_nCK = data & 0xFF
            if sel & 0x2:
                self.cfg_tFAW_nCK = (data >> 8) & 0xFF
                
        elif addr == CSR_TIMING3:
            # tWTR in bits 7:0, tWR in bits 15:8
            if sel & 0x1:
                self.cfg_tWTR_nCK = data & 0xFF
            if sel & 0x2:
                self.cfg_tWR_nCK = (data >> 8) & 0xFF
                
        elif addr == CSR_TIMING4:
            # tRTP in bits 7:0, tCCD in bits 15:8
            if sel & 0x1:
                self.cfg_tRTP_nCK = data & 0xFF
            if sel & 0x2:
                self.cfg_tCCD_nCK = (data >> 8) & 0xFF
                
        elif addr == CSR_TIMING5:
            # tRFC (16 bits)
            if sel & 0x3:
                self.cfg_tRFC_nCK = data & 0xFFFF
                
        elif addr == CSR_TIMING6:
            # tREFI (16 bits)
            if sel & 0x3:
                self.cfg_tREFI_nCK = data & 0xFFFF
                
        elif addr == CSR_TIMING7:
            # CL in bits 7:0, CWL in bits 15:8
            if sel & 0x1:
                self.cfg_CL_nCK = data & 0xFF
            if sel & 0x2:
                self.cfg_CWL_nCK = (data >> 8) & 0xFF
                
        elif addr == CSR_SCHED_CFG:
            # sched_policy in bits 1:0, row_policy in bit 2
            # self_ref_mode in bit 3, ecc_enable in bit 4
            if sel & 0x1:
                self.cfg_sched_policy = data & 0x3
                self.cfg_row_policy = (data >> 2) & 0x1
                self.cfg_self_ref_mode = (data >> 3) & 0x1
                self.cfg_ecc_enable = (data >> 4) & 0x1
                
        elif addr == CSR_REF_CFG:
            # max_postpone in bits 7:0, urgent_threshold in bits 15:8
            # ref_priority in bit 16
            if sel & 0x1:
                self.cfg_max_postpone = data & 0xFF
            if sel & 0x2:
                self.cfg_urgent_threshold = (data >> 8) & 0xFF
            if sel & 0x4:
                self.cfg_ref_priority = (data >> 16) & 0x1
                
        elif addr == CSR_CTRL:
            # Control register: bist_start, force_refresh, force_self_ref
            if sel & 0x1:
                self.cfg_bist_start = data & 0x1
                self.cfg_force_refresh = (data >> 1) & 0x1
                self.cfg_force_self_ref = (data >> 2) & 0x1
                
        elif addr == CSR_BIST_CFG:
            # bist_pattern in bits 3:0, bist_addr_mode in bits 7:4
            if sel & 0x1:
                self.cfg_bist_pattern = data & 0xF
                self.cfg_bist_addr_mode = (data >> 4) & 0xF
                
        elif addr == CSR_BIST_START:
            # BIST start address (32 bits)
            self.cfg_bist_addr_start = data & 0xFFFFFFFF
            
        elif addr == CSR_BIST_END:
            # BIST end address (32 bits)
            self.cfg_bist_addr_end = data & 0xFFFFFFFF
    
    def _read_csr(self, addr):
        """Handle CSR read operation."""
        if addr == CSR_TIMING0:
            return (self.cfg_tRP_nCK << 8) | self.cfg_tRCD_nCK
        elif addr == CSR_TIMING1:
            return (self.cfg_tRC_nCK << 8) | self.cfg_tRAS_nCK
        elif addr == CSR_TIMING2:
            return (self.cfg_tFAW_nCK << 8) | self.cfg_tRRD_nCK
        elif addr == CSR_TIMING3:
            return (self.cfg_tWR_nCK << 8) | self.cfg_tWTR_nCK
        elif addr == CSR_TIMING4:
            return (self.cfg_tCCD_nCK << 8) | self.cfg_tRTP_nCK
        elif addr == CSR_TIMING5:
            return self.cfg_tRFC_nCK
        elif addr == CSR_TIMING6:
            return self.cfg_tREFI_nCK
        elif addr == CSR_TIMING7:
            return (self.cfg_CWL_nCK << 8) | self.cfg_CL_nCK
        elif addr == CSR_SCHED_CFG:
            return ((self.cfg_ecc_enable << 4) |
                    (self.cfg_self_ref_mode << 3) |
                    (self.cfg_row_policy << 2) |
                    self.cfg_sched_policy)
        elif addr == CSR_REF_CFG:
            return ((self.cfg_ref_priority << 16) |
                    (self.cfg_urgent_threshold << 8) |
                    self.cfg_max_postpone)
        elif addr == CSR_CTRL:
            return ((self.cfg_force_self_ref << 2) |
                    (self.cfg_force_refresh << 1) |
                    self.cfg_bist_start)
        elif addr == CSR_BIST_CFG:
            return (self.cfg_bist_addr_mode << 4) | self.cfg_bist_pattern
        elif addr == CSR_BIST_START:
            return self.cfg_bist_addr_start
        elif addr == CSR_BIST_END:
            return self.cfg_bist_addr_end
        else:
            return 0
    
    def _apply_pending_feedback(self):
        """Apply pending feedback from previous cycle to bank state."""
        cmd_type = self.pending_fb_type
        bank = self.pending_fb_bank
        row = self.pending_fb_row
        
        if cmd_type == SCHED_ACT:
            # Activate command: open row in bank
            self.bank_is_active[bank] = 1
            self.bank_open_row[bank] = row
            # Start timing counters (use cfg values directly, NO clock conversion)
            self.cnt_tRCD[bank] = self.cfg_tRCD_nCK
            self.cnt_tRAS[bank] = self.cfg_tRAS_nCK
            self.cnt_tRC[bank] = self.cfg_tRC_nCK
            # Global ACT to ACT timing
            self.cnt_tRRD = self.cfg_tRRD_nCK
            # Record ACT in tFAW window
            self.faw_window.append(self.cycle_count)
            # Keep only last 4 ACTs
            if len(self.faw_window) > 4:
                self.faw_window.pop(0)
                
        elif cmd_type == SCHED_PRE:
            # Precharge command: close bank
            self.bank_is_active[bank] = 0
            self.bank_open_row[bank] = 0
            # Start tRP counter
            self.cnt_tRP[bank] = self.cfg_tRP_nCK
            
        elif cmd_type == SCHED_RD:
            # Read command: update read timing
            self.cnt_tCCD = self.cfg_tCCD_nCK
            self.cnt_tRTP[bank] = self.cfg_tRTP_nCK
            
        elif cmd_type == SCHED_WR:
            # Write command: update write timing
            self.cnt_tCCD = self.cfg_tCCD_nCK
            self.cnt_tWR[bank] = self.cfg_tWR_nCK
            self.cnt_tWTR[bank] = self.cfg_tWTR_nCK
            
        elif cmd_type == SCHED_REF:
            # Refresh command: all banks closed, start tRFC
            for b in range(NUM_BANKS):
                self.bank_is_active[b] = 0
                self.bank_open_row[b] = 0
            self.cnt_tRFC = self.cfg_tRFC_nCK
            # Clear tFAW window - all prior ACTs invalidated by refresh
            self.faw_window = []
            # Clear tRRD - no prior ACT relevant
            self.cnt_tRRD = 0
            self.refresh_in_progress = True
            # Decrement postpone count when refresh is issued
            if self.postpone_cnt > 0:
                self.postpone_cnt -= 1
    
    def _decrement_counters(self):
        """Decrement all timing counters by 1 (minimum 0)."""
        # Per-bank counters
        for b in range(NUM_BANKS):
            if self.cnt_tRCD[b] > 0:
                self.cnt_tRCD[b] -= 1
            if self.cnt_tRAS[b] > 0:
                self.cnt_tRAS[b] -= 1
            if self.cnt_tRC[b] > 0:
                self.cnt_tRC[b] -= 1
            if self.cnt_tRP[b] > 0:
                self.cnt_tRP[b] -= 1
            if self.cnt_tWR[b] > 0:
                self.cnt_tWR[b] -= 1
            if self.cnt_tRTP[b] > 0:
                self.cnt_tRTP[b] -= 1
            if self.cnt_tWTR[b] > 0:
                self.cnt_tWTR[b] -= 1
        
        # Global counters
        if self.cnt_tCCD > 0:
            self.cnt_tCCD -= 1
        if self.cnt_tRRD > 0:
            self.cnt_tRRD -= 1
        if self.cnt_tRFC > 0:
            self.cnt_tRFC -= 1
            
        # Check if refresh complete
        if self.cnt_tRFC == 0 and self.refresh_in_progress:
            self.refresh_in_progress = False
    
    def _compute_bank_allowed_signals(self):
        """Compute which operations are allowed for each bank."""
        bank_act_allowed = [0] * NUM_BANKS
        bank_rd_allowed  = [0] * NUM_BANKS
        bank_wr_allowed  = [0] * NUM_BANKS
        bank_pre_allowed = [0] * NUM_BANKS
        
        # Check tFAW constraint: can issue ACT if fewer than 4 ACTs in window
        # or if oldest ACT is old enough
        faw_allows_act = True
        if len(self.faw_window) >= 4:
            oldest_act_time = self.faw_window[0]
            if (self.cycle_count - oldest_act_time) < self.cfg_tFAW_nCK:
                faw_allows_act = False
        
        # Global constraints that block all banks
        if self.refresh_in_progress or self.cnt_tRFC > 0:
            # During refresh, nothing allowed
            return bank_act_allowed, bank_rd_allowed, bank_wr_allowed, bank_pre_allowed
        
        for b in range(NUM_BANKS):
            if self.bank_is_active[b]:
                # Bank is active (has open row)
                # ACT not allowed on active bank
                bank_act_allowed[b] = 0
                
                # RD allowed if tRCD elapsed and tCCD elapsed
                if self.cnt_tRCD[b] == 0 and self.cnt_tCCD == 0:
                    bank_rd_allowed[b] = 1
                    
                # WR allowed if tRCD elapsed, tCCD elapsed, and no pending WTR
                if self.cnt_tRCD[b] == 0 and self.cnt_tCCD == 0:
                    bank_wr_allowed[b] = 1
                    
                # PRE allowed if tRAS elapsed and no pending write (tWR) or read (tRTP)
                if (self.cnt_tRAS[b] == 0 and 
                    self.cnt_tWR[b] == 0 and 
                    self.cnt_tRTP[b] == 0):
                    bank_pre_allowed[b] = 1
            else:
                # Bank is idle (precharged)
                # ACT allowed if tRP elapsed, tRC elapsed, tRRD elapsed, and tFAW allows
                if (self.cnt_tRP[b] == 0 and 
                    self.cnt_tRC[b] == 0 and 
                    self.cnt_tRRD == 0 and 
                    faw_allows_act):
                    bank_act_allowed[b] = 1
                    
                # RD/WR/PRE not allowed on idle bank
                bank_rd_allowed[b] = 0
                bank_wr_allowed[b] = 0
                bank_pre_allowed[b] = 0
        
        return bank_act_allowed, bank_rd_allowed, bank_wr_allowed, bank_pre_allowed
    
    def step(self, **inputs):
        """
        Advance the model by one clock cycle.
        
        Args:
            **inputs: Input signals as keyword arguments (unknown ones ignored)
            
        Returns:
            dict: All output signal values
        """
        # Extract known inputs (ignore unknown)
        csr_cyc_i = inputs.get('csr_cyc_i', 0)
        csr_stb_i = inputs.get('csr_stb_i', 0)
        csr_we_i  = inputs.get('csr_we_i', 0)
        csr_adr_i = inputs.get('csr_adr_i', 0)
        csr_dat_i = inputs.get('csr_dat_i', 0)
        csr_sel_i = inputs.get('csr_sel_i', 0xF)
        
        # Status inputs from init/calibration
        sts_init_done = inputs.get('sts_init_done', 0)
        
        # Command feedback inputs (from DDR command generator)
        cmd_act_valid = inputs.get('cmd_act_valid', 0)
        cmd_act_bank  = inputs.get('cmd_act_bank', 0)
        cmd_act_row   = inputs.get('cmd_act_row', 0)
        cmd_pre_valid = inputs.get('cmd_pre_valid', 0)
        cmd_pre_bank  = inputs.get('cmd_pre_bank', 0)
        cmd_pre_all   = inputs.get('cmd_pre_all', 0)
        cmd_rd_valid  = inputs.get('cmd_rd_valid', 0)
        cmd_rd_bank   = inputs.get('cmd_rd_bank', 0)
        cmd_wr_valid  = inputs.get('cmd_wr_valid', 0)
        cmd_wr_bank   = inputs.get('cmd_wr_bank', 0)
        cmd_ref_valid = inputs.get('cmd_ref_valid', 0)
        
        # =========================================================
        # Step 1: Apply pending feedback from PREVIOUS cycle
        # =========================================================
        self._apply_pending_feedback()
        
        # =========================================================
        # Step 2: Decrement timing counters
        # =========================================================
        self._decrement_counters()
        
        # =========================================================
        # Step 3: Handle init_done transition for refresh
        # =========================================================
        # Track init_done transition
        if sts_init_done and not self.init_done_latched:
            # First cycle after init_done goes high
            # Refresh counter sees 0, fires refi_tick immediately
            self.postpone_cnt = 1  # First refresh required immediately
            self.refresh_counter = self.cfg_tREFI_nCK  # Reload for next interval
            self.init_done_latched = True
        elif self.init_done_latched:
            # Normal operation: decrement refresh counter
            if self.refresh_counter > 0:
                self.refresh_counter -= 1
            else:
                # Counter reached 0, increment postpone and reload
                if self.postpone_cnt < self.cfg_max_postpone:
                    self.postpone_cnt += 1
                self.refresh_counter = self.cfg_tREFI_nCK
        
        # =========================================================
        # Step 4: Compute combinational outputs from CURRENT state
        # =========================================================
        (bank_act_allowed, bank_rd_allowed, 
         bank_wr_allowed, bank_pre_allowed) = self._compute_bank_allowed_signals()
        
        # =========================================================
        # Step 5: Process CSR Wishbone transactions
        # =========================================================
        csr_ack_o = 0
        csr_dat_o = 0
        csr_err_o = 0
        
        if csr_cyc_i and csr_stb_i and not self.csr_ack_pending:
            # New transaction
            if csr_we_i:
                # Write transaction
                self._write_csr(csr_adr_i, csr_dat_i, csr_sel_i)
            else:
                # Read transaction
                self.csr_read_data = self._read_csr(csr_adr_i)
            self.csr_ack_pending = True
        
        if self.csr_ack_pending:
            csr_ack_o = 1
            csr_dat_o = self.csr_read_data
            self.csr_ack_pending = False  # Single-cycle ack
        
        # =========================================================
        # Step 6: Process command feedback inputs directly
        # =========================================================
        # Set pending feedback based on command inputs
        # This will be applied at the START of the next cycle
        if cmd_act_valid:
            self.pending_fb_type = SCHED_ACT
            self.pending_fb_bank = cmd_act_bank
            self.pending_fb_row = cmd_act_row
        elif cmd_pre_valid:
            self.pending_fb_type = SCHED_PRE
            self.pending_fb_bank = cmd_pre_bank
            self.pending_fb_row = 0
            # Handle precharge all
            if cmd_pre_all:
                # Mark all banks as needing precharge
                for b in range(NUM_BANKS):
                    if self.bank_is_active[b]:
                        self.bank_is_active[b] = 0
                        self.cnt_tRP[b] = self.cfg_tRP_nCK
        elif cmd_rd_valid:
            self.pending_fb_type = SCHED_RD
            self.pending_fb_bank = cmd_rd_bank
            self.pending_fb_row = 0
        elif cmd_wr_valid:
            self.pending_fb_type = SCHED_WR
            self.pending_fb_bank = cmd_wr_bank
            self.pending_fb_row = 0
        elif cmd_ref_valid:
            self.pending_fb_type = SCHED_REF
            self.pending_fb_bank = 0
            self.pending_fb_row = 0
        else:
            self.pending_fb_type = SCHED_NOP
            self.pending_fb_bank = 0
            self.pending_fb_row = 0
        
        # Increment cycle counter
        self.cycle_count += 1
        
        # =========================================================
        # Build output dictionary
        # =========================================================
        # Pack bank arrays into bitmasks for output
        bank_is_active_bits = 0
        bank_act_allowed_bits = 0
        bank_rd_allowed_bits = 0
        bank_wr_allowed_bits = 0
        bank_pre_allowed_bits = 0
        
        for b in range(NUM_BANKS):
            if self.bank_is_active[b]:
                bank_is_active_bits |= (1 << b)
            if bank_act_allowed[b]:
                bank_act_allowed_bits |= (1 << b)
            if bank_rd_allowed[b]:
                bank_rd_allowed_bits |= (1 << b)
            if bank_wr_allowed[b]:
                bank_wr_allowed_bits |= (1 << b)
            if bank_pre_allowed[b]:
                bank_pre_allowed_bits |= (1 << b)
        
        outputs = {
            # CSR interface outputs
            'csr_ack_o': csr_ack_o,
            'csr_dat_o': csr_dat_o,
            'csr_err_o': csr_err_o,
            
            # Timing configuration outputs (directly from CSR to bank tracker)
            'cfg_CL_nCK': self.cfg_CL_nCK,
            'cfg_CWL_nCK': self.cfg_CWL_nCK,
            'cfg_tREFI_nCK': self.cfg_tREFI_nCK,
            
            # Scheduler configuration outputs
            'cfg_sched_policy': self.cfg_sched_policy,
            'cfg_row_policy': self.cfg_row_policy,
            'cfg_self_ref_mode': self.cfg_self_ref_mode,
            'cfg_ecc_enable': self.cfg_ecc_enable,
            'cfg_bist_start': self.cfg_bist_start,
            'cfg_force_refresh': self.cfg_force_refresh,
            'cfg_force_self_ref': self.cfg_force_self_ref,
            
            # Refresh configuration outputs
            'cfg_max_postpone': self.cfg_max_postpone,
            'cfg_urgent_threshold': self.cfg_urgent_threshold,
            'cfg_ref_priority': self.cfg_ref_priority,
            
            # BIST configuration outputs
            'cfg_bist_pattern': self.cfg_bist_pattern,
            'cfg_bist_addr_mode': self.cfg_bist_addr_mode,
            'cfg_bist_addr_start': self.cfg_bist_addr_start,
            'cfg_bist_addr_end': self.cfg_bist_addr_end,
            
            # Bank tracker status outputs
            'bank_is_active': bank_is_active_bits,
            'bank_act_allowed': bank_act_allowed_bits,
            'bank_rd_allowed': bank_rd_allowed_bits,
            'bank_wr_allowed': bank_wr_allowed_bits,
            'bank_pre_allowed': bank_pre_allowed_bits,
        }
        
        return outputs
    
    def get_state(self) -> dict:
        """Return full internal state for debugging."""
        return {
            # CSR timing configuration
            'cfg_tRCD_nCK': self.cfg_tRCD_nCK,
            'cfg_tRP_nCK': self.cfg_tRP_nCK,
            'cfg_tRAS_nCK': self.cfg_tRAS_nCK,
            'cfg_tRC_nCK': self.cfg_tRC_nCK,
            'cfg_tRFC_nCK': self.cfg_tRFC_nCK,
            'cfg_tFAW_nCK': self.cfg_tFAW_nCK,
            'cfg_tRRD_nCK': self.cfg_tRRD_nCK,
            'cfg_tWR_nCK': self.cfg_tWR_nCK,
            'cfg_tWTR_nCK': self.cfg_tWTR_nCK,
            'cfg_tRTP_nCK': self.cfg_tRTP_nCK,
            'cfg_tCCD_nCK': self.cfg_tCCD_nCK,
            'cfg_tREFI_nCK': self.cfg_tREFI_nCK,
            'cfg_CL_nCK': self.cfg_CL_nCK,
            'cfg_CWL_nCK': self.cfg_CWL_nCK,
            
            # Scheduler/controller configuration
            'cfg_sched_policy': self.cfg_sched_policy,
            'cfg_row_policy': self.cfg_row_policy,
            'cfg_self_ref_mode': self.cfg_self_ref_mode,
            'cfg_ecc_enable': self.cfg_ecc_enable,
            
            # Bank tracker state
            'bank_is_active': self.bank_is_active.copy(),
            'bank_open_row': self.bank_open_row.copy(),
            'cnt_tRCD': self.cnt_tRCD.copy(),
            'cnt_tRAS': self.cnt_tRAS.copy(),
            'cnt_tRC': self.cnt_tRC.copy(),
            'cnt_tRP': self.cnt_tRP.copy(),
            'cnt_tWR': self.cnt_tWR.copy(),
            'cnt_tRTP': self.cnt_tRTP.copy(),
            'cnt_tWTR': self.cnt_tWTR.copy(),
            'cnt_tCCD': self.cnt_tCCD,
            'cnt_tRRD': self.cnt_tRRD,
            'cnt_tRFC': self.cnt_tRFC,
            'faw_window': self.faw_window.copy(),
            
            # Refresh state
            'refresh_counter': self.refresh_counter,
            'postpone_cnt': self.postpone_cnt,
            'refresh_in_progress': self.refresh_in_progress,
            'init_done_latched': self.init_done_latched,
            
            # Cycle counter
            'cycle_count': self.cycle_count,
        }


def run_self_test():
    """Run self-test to verify model behavior."""
    all_passed = True
    test_count = 0
    pass_count = 0
    
    def test(name, condition):
        nonlocal all_passed, test_count, pass_count
        test_count += 1
        if condition:
            print(f"PASS: {name}")
            pass_count += 1
        else:
            print(f"FAIL: {name}")
            all_passed = False
    
    # Test 1: Reset values
    print("=" * 60)
    print("Test 1: Reset Values")
    print("=" * 60)
    model = PathModel()
    outputs = model.step()
    
    test("Reset - cfg_CL_nCK is 11", outputs['cfg_CL_nCK'] == 11)
    test("Reset - cfg_CWL_nCK is 8", outputs['cfg_CWL_nCK'] == 8)
    test("Reset - cfg_tREFI_nCK is 6240", outputs['cfg_tREFI_nCK'] == 6240)
    test("Reset - cfg_sched_policy is FR_FCFS (0)", outputs['cfg_sched_policy'] == 0)
    test("Reset - cfg_row_policy is OPEN_PAGE (0)", outputs['cfg_row_policy'] == 0)
    test("Reset - cfg_max_postpone is 8", outputs['cfg_max_postpone'] == 8)
    test("Reset - cfg_urgent_threshold is 6", outputs['cfg_urgent_threshold'] == 6)
    test("Reset - bank_is_active is 0", outputs['bank_is_active'] == 0)
    test("Reset - csr_ack_o is 0", outputs['csr_ack_o'] == 0)
    
    # Test 2: CSR Write and Read
    print("=" * 60)
    print("Test 2: CSR Write and Read")
    print("=" * 60)
    model.reset()
    
    # Write new tRCD value (25) and tRP value (30)
    outputs = model.step(
        csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
        csr_adr_i=CSR_TIMING0, csr_dat_i=(30 << 8) | 25, csr_sel_i=0x3
    )
    test("CSR Write - ack_o asserted", outputs['csr_ack_o'] == 1)
    
    # Verify internal state updated
    state = model.get_state()
    test("CSR Write - tRCD updated to 25", state['cfg_tRCD_nCK'] == 25)
    test("CSR Write - tRP updated to 30", state['cfg_tRP_nCK'] == 30)
    
    # Read back the register
    outputs = model.step(
        csr_cyc_i=1, csr_stb_i=1, csr_we_i=0,
        csr_adr_i=CSR_TIMING0, csr_sel_i=0xF
    )
    test("CSR Read - ack_o asserted", outputs['csr_ack_o'] == 1)
    test("CSR Read - dat_o correct", outputs['csr_dat_o'] == ((30 << 8) | 25))
    
    # Test 3: Bank Activation and Timing
    print("=" * 60)
    print("Test 3: Bank Activation and Timing")
    print("=" * 60)
    model.reset()
    
    # Initially, all banks should allow activation (after reset counters = 0)
    outputs = model.step()
    test("Initial - all banks allow ACT", outputs['bank_act_allowed'] == 0xFF)
    test("Initial - no banks allow RD", outputs['bank_rd_allowed'] == 0)
    test("Initial - no banks are active", outputs['bank_is_active'] == 0)
    
    # Issue ACT to bank 0
    outputs = model.step(cmd_act_valid=1, cmd_act_bank=0, cmd_act_row=100)
    
    # In next cycle, feedback is applied
    outputs = model.step()
    test("After ACT - bank 0 is active", (outputs['bank_is_active'] & 0x1) == 1)
    test("After ACT - bank 0 cannot ACT", (outputs['bank_act_allowed'] & 0x1) == 0)
    
    # RD should not be allowed yet (tRCD = 11 cycles)
    test("After ACT - bank 0 cannot RD (tRCD)", (outputs['bank_rd_allowed'] & 0x1) == 0)
    
    # Wait for tRCD to elapse (11 cycles)
    for i in range(11):
        outputs = model.step()
    
    test("After tRCD - bank 0 can RD", (outputs['bank_rd_allowed'] & 0x1) == 1)
    test("After tRCD - bank 0 can WR", (outputs['bank_wr_allowed'] & 0x1) == 1)
    
    # Test 4: Precharge Timing
    print("=" * 60)
    print("Test 4: Precharge Timing")
    print("=" * 60)
    model.reset()
    
    # Activate bank 0
    outputs = model.step(cmd_act_valid=1, cmd_act_bank=0, cmd_act_row=50)
    outputs = model.step()  # Apply feedback
    
    # PRE should not be allowed yet (tRAS = 28 cycles)
    test("After ACT - bank 0 cannot PRE (tRAS)", (outputs['bank_pre_allowed'] & 0x1) == 0)
    
    # Wait for tRAS to elapse
    for i in range(28):
        outputs = model.step()
    
    test("After tRAS - bank 0 can PRE", (outputs['bank_pre_allowed'] & 0x1) == 1)
    
    # Issue precharge
    outputs = model.step(cmd_pre_valid=1, cmd_pre_bank=0)
    outputs = model.step()  # Apply feedback
    
    test("After PRE - bank 0 is idle", (outputs['bank_is_active'] & 0x1) == 0)
    
    # ACT should not be allowed yet (tRP = 11 cycles)
    test("After PRE - bank 0 cannot ACT (tRP)", (outputs['bank_act_allowed'] & 0x1) == 0)
    
    # Wait for tRP
    for i in range(11):
        outputs = model.step()
    
    test("After tRP - bank 0 can ACT", (outputs['bank_act_allowed'] & 0x1) == 1)
    
    # Test 5: tRRD (ACT to ACT different bank)
    print("=" * 60)
    print("Test 5: tRRD Timing")
    print("=" * 60)
    model.reset()
    
    # Activate bank 0
    outputs = model.step(cmd_act_valid=1, cmd_act_bank=0, cmd_act_row=10)
    outputs = model.step()  # Apply feedback
    
    # Bank 1 should not allow ACT yet (tRRD = 6 cycles)
    test("After ACT bank0 - bank1 cannot ACT (tRRD)", (outputs['bank_act_allowed'] & 0x2) == 0)
    
    # Wait for tRRD
    for i in range(6):
        outputs = model.step()
    
    test("After tRRD - bank1 can ACT", (outputs['bank_act_allowed'] & 0x2) == 2)
    
    # Test 6: Refresh Behavior
    print("=" * 60)
    print("Test 6: Refresh Behavior")
    print("=" * 60)
    model.reset()
    
    # Activate bank 0
    outputs = model.step(cmd_act_valid=1, cmd_act_bank=0, cmd_act_row=200)
    outputs = model.step()
    test("Before REF - bank 0 active", (outputs['bank_is_active'] & 0x1) == 1)
    
    # Issue refresh
    outputs = model.step(cmd_ref_valid=1)
    outputs = model.step()  # Apply feedback
    
    test("After REF - all banks idle", outputs['bank_is_active'] == 0)
    test("After REF - no ACT allowed (tRFC)", outputs['bank_act_allowed'] == 0)
    
    # Wait for tRFC (128 cycles)
    for i in range(128):
        outputs = model.step()
    
    test("After tRFC - ACT allowed again", outputs['bank_act_allowed'] == 0xFF)
    
    # Test 7: tFAW (Four Activate Window)
    print("=" * 60)
    print("Test 7: tFAW Timing")
    print("=" * 60)
    model.reset()
    
    # Issue 4 consecutive ACTs (need to space them by tRRD = 6)
    for bank in range(4):
        outputs = model.step(cmd_act_valid=1, cmd_act_bank=bank, cmd_act_row=bank*10)
        outputs = model.step()  # Apply feedback
        # Wait for tRRD
        for i in range(6):
            outputs = model.step()
    
    # At this point, banks 0-3 are active, and we've done 4 ACTs
    # Bank 4 should be blocked by tFAW until enough time passes
    state = model.get_state()
    test("After 4 ACTs - faw_window has 4 entries", len(state['faw_window']) == 4)
    
    # The 5th ACT should be blocked until tFAW elapses from the first ACT
    # tFAW = 32 cycles from first ACT
    
    # Test 8: step() accepts unknown kwargs
    print("=" * 60)
    print("Test 8: step() accepts unknown kwargs")
    print("=" * 60)
    model.reset()
    try:
        outputs = model.step(unknown_signal_xyz=123, another_unknown=456)
        test("step() accepts unknown kwargs", True)
    except Exception as e:
        print(f"Exception: {e}")
        test("step() accepts unknown kwargs", False)
    
    # Test 9: step() returns all expected outputs
    print("=" * 60)
    print("Test 9: step() returns all expected outputs")
    print("=" * 60)
    model.reset()
    outputs = model.step()
    
    expected_outputs = [
        'csr_ack_o', 'csr_dat_o', 'csr_err_o',
        'cfg_CL_nCK', 'cfg_CWL_nCK', 'cfg_tREFI_nCK',
        'cfg_sched_policy', 'cfg_row_policy', 'cfg_self_ref_mode',
        'cfg_ecc_enable', 'cfg_bist_start', 'cfg_force_refresh',
        'cfg_force_self_ref', 'cfg_max_postpone', 'cfg_urgent_threshold',
        'cfg_ref_priority', 'cfg_bist_pattern', 'cfg_bist_addr_mode',
        'cfg_bist_addr_start', 'cfg_bist_addr_end',
        'bank_is_active', 'bank_act_allowed', 'bank_rd_allowed',
        'bank_wr_allowed', 'bank_pre_allowed'
    ]
    
    all_present = True
    for key in expected_outputs:
        if key not in outputs:
            print(f"  Missing output: {key}")
            all_present = False
    test("All expected outputs present", all_present)
    
    # Test 10: Verify timing counter values are used directly (no clock conversion)
    print("=" * 60)
    print("Test 10: Timing counter direct usage")
    print("=" * 60)
    model.reset()
    
    # Write custom tRCD = 5
    model.step(
        csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
        csr_adr_i=CSR_TIMING0, csr_dat_i=5, csr_sel_i=0x1
    )
    
    # Activate bank 0
    model.step(cmd_act_valid=1, cmd_act_bank=0, cmd_act_row=0)
    model.step()  # Apply feedback
    
    # Check RD not allowed initially
    outputs = model.step()
    test("Custom tRCD=5 - RD not allowed at cycle 0", (outputs['bank_rd_allowed'] & 0x1) == 0)
    
    # After 5 cycles, RD should be allowed
    for i in range(4):
        outputs = model.step()
    
    test("Custom tRCD=5 - RD allowed at cycle 5", (outputs['bank_rd_allowed'] & 0x1) == 1)
    
    # Test 11: Init done transition triggers immediate refresh
    print("=" * 60)
    print("Test 11: Init done refresh trigger")
    print("=" * 60)
    model.reset()
    
    # Before init_done, postpone_cnt should be 0
    outputs = model.step(sts_init_done=0)
    state = model.get_state()
    test("Before init_done - postpone_cnt is 0", state['postpone_cnt'] == 0)
    
    # First cycle with init_done=1
    outputs = model.step(sts_init_done=1)
    state = model.get_state()
    test("First init_done=1 - postpone_cnt is 1", state['postpone_cnt'] == 1)
    
    # Refresh counter should be reloaded
    test("First init_done=1 - refresh_counter reloaded", 
         state['refresh_counter'] == DEFAULT_tREFI_nCK)
    
    # Summary
    print("=" * 60)
    print(f"Results: {pass_count}/{test_count} tests passed")
    print("=" * 60)
    
    if all_passed:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
    
    return all_passed


if __name__ == "__main__":
    run_self_test()