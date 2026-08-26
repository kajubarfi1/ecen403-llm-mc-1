#!/usr/bin/env python3
"""
Reference model for DDR3 Full Write Transaction Path
Path: wb_port -> addr_decoder -> cmd_queue -> scheduler -> cmd_gen

Models the complete write transaction flow from Wishbone interface to DDR3 commands.
"""

import json
import os
from typing import Dict, Any, List, Optional

# =============================================================================
# CONSTANTS FROM SPEC
# =============================================================================

# DDR Command Encoding (from RTL cmd_gen.sv)
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

# Memory geometry from spec
ROW_BITS = 15
COL_BITS = 10
BANK_BITS = 3
NUM_BANKS = 8  # 2^3

# Timing parameters (in controller clock cycles - use directly, no division!)
CFG_tRCD_nCK  = 11
CFG_tRP_nCK   = 11
CFG_tRAS_nCK  = 28
CFG_tRC_nCK   = 39
CFG_tRFC_nCK  = 128
CFG_tFAW_nCK  = 32
CFG_tRRD_nCK  = 6
CFG_tWR_nCK   = 12
CFG_tWTR_nCK  = 6
CFG_tRTP_nCK  = 6
CFG_tCCD_nCK  = 4
CFG_tREFI_nCK = 6240
CFG_CL        = 11
CFG_CWL       = 8

# Controller architecture
CMD_QUEUE_DEPTH = 16
LOOKAHEAD_DEPTH = 8
MAX_POSTPONE_COUNT = 8
URGENT_THRESHOLD = 6

# Host interface
DATA_WIDTH_BITS = 32
ADDR_WIDTH_BITS = 29
SEL_WIDTH = 4
MAX_BURST_LENGTH = 8


class PathModel:
    """
    Reference model for DDR3 Full Write Transaction Path.
    Models: wb_port -> addr_decoder -> cmd_queue -> scheduler -> cmd_gen
    """
    
    def __init__(self):
        """Initialize the path model."""
        self.reset()
    
    def reset(self):
        """Reset all internal state to power-on defaults."""
        # =====================================================================
        # Wishbone Port State
        # =====================================================================
        self.wb_stall = 0
        self.wb_ack = 0
        self.wb_err = 0
        self.wb_dat_o = 0
        
        # Pending request from Wishbone
        self.req_pending = False
        self.req_addr = 0
        self.req_we = 0
        self.req_wdata = 0
        self.req_wmask = 0
        self.req_aux = 0
        
        # =====================================================================
        # Address Decoder State (combinational, but track outputs)
        # =====================================================================
        self.dec_row = 0
        self.dec_col = 0
        self.dec_bank = 0
        self.dec_rank = 0
        
        # =====================================================================
        # Command Queue State (single entry mode)
        # =====================================================================
        self.queue_valid = False
        self.queue_row = 0
        self.queue_col = 0
        self.queue_bank = 0
        self.queue_we = 0
        self.queue_aux = 0
        self.queue_wdata = 0
        self.queue_wmask = 0
        
        # Queue status
        self.enq_ready = 1  # Ready when queue not full
        self.queue_full = 0
        self.queue_empty = 1
        self.queue_count = 0
        
        # =====================================================================
        # Bank Tracker State
        # =====================================================================
        self.bank_is_active = [0] * NUM_BANKS
        self.bank_open_row = [0] * NUM_BANKS
        
        # Per-bank timing counters
        self.cnt_rcd = [0] * NUM_BANKS   # RCD countdown after ACT
        self.cnt_ras = [0] * NUM_BANKS   # RAS countdown after ACT (min active time)
        self.cnt_rp = [0] * NUM_BANKS    # RP countdown after PRE
        self.cnt_wr = [0] * NUM_BANKS    # Write recovery
        self.cnt_rtp = [0] * NUM_BANKS   # Read to precharge
        self.cnt_wtr = [0] * NUM_BANKS   # Write to read
        
        # Global timing counters
        self.cnt_rrd = 0      # RRD countdown (ACT to ACT different banks)
        self.cnt_rfc = 0      # RFC countdown after REF
        self.cnt_ccd = 0      # CCD countdown (CAS to CAS)
        
        # FAW tracking (sliding window of last 4 ACT timestamps)
        self.faw_window = []  # List of cycle numbers when ACT was issued
        self.cycle_count = 0  # Global cycle counter for FAW
        
        # Refresh state
        self.refresh_in_progress = False
        
        # =====================================================================
        # Refresh Controller State
        # =====================================================================
        self.init_done = False
        self.refi_counter = 0
        self.postpone_cnt = 0
        self.ref_required = 0
        self.ref_urgent = 0
        self.ref_ack = 0
        
        # =====================================================================
        # Scheduler Pipeline State
        # =====================================================================
        # Pipeline stages for 2-cycle latency to DDR output
        # pipe_s1: scheduler decision (registered)
        # pipe_s2: cmd_gen output (registered)
        self.pipe_s1 = {'cmd_type': SCHED_NOP, 'bank': 0, 'row': 0, 'col': 0, 
                        'we': 0, 'aux': 0, 'valid': False, 'deq_grant': 0, 'ref_ack': 0}
        self.pipe_s2 = {'cmd_type': SCHED_NOP, 'bank': 0, 'row': 0, 'col': 0,
                        'we': 0, 'aux': 0, 'valid': False, 'deq_grant': 0, 'ref_ack': 0}
        
        # Pending feedback (applied next cycle)
        self.pending_fb_type = SCHED_NOP
        self.pending_fb_bank = 0
        self.pending_fb_row = 0
        self.pending_fb_valid = False
        
        # =====================================================================
        # DDR Output State
        # =====================================================================
        self.ddr_cmd = DDR_NOP
        self.ddr_addr = 0
        self.ddr_bank = 0
        self.ddr_cke = 1
        self.ddr_reset_n = 1
        self.ddr_odt = 0
        
        # Feedback signals to bank tracker
        self.fb_act_valid = 0
        self.fb_act_bank = 0
        self.fb_act_row = 0
        self.fb_pre_valid = 0
        self.fb_rd_valid = 0
        self.fb_wr_valid = 0
        self.fb_ref_valid = 0
    
    def _decode_address(self, byte_addr: int) -> tuple:
        """
        Decode byte address to row/col/bank using row-bank-column mapping.
        Address format (29 bits): [row:15][bank:3][col:10][byte_offset:1]
        
        Note: byte_offset accounts for 16-bit channel width (2 bytes per access)
        """
        # Remove byte offset within burst (DDR3 BL8 = 8 beats of 16 bits = 16 bytes)
        # Column addresses the 16-byte burst-aligned location
        # With 10 column bits and 16-bit data width:
        # - Bits [0]: byte select within 16-bit word (ignored at DDR level)
        # - Bits [3:1]: beat within burst (handled by DRAM)
        # - Bits [12:4]: column address bits [9:1] mapped from address
        
        # For row-bank-column mapping with 16-bit channel:
        # addr[0] = byte within 16-bit word
        # addr[3:1] = burst beat (implicit in BL8)
        # addr[12:4] = column[9:1] (col bit 0 tied low for BL8)
        # addr[15:13] = bank[2:0]
        # addr[30:16] = row[14:0]
        
        # Actually, let's be more precise based on spec:
        # - burst_transfer_bytes_on_dq = 16 (BL8 * 16-bit = 16 bytes)
        # - page_size_bytes_channel = 2048 (1024 columns * 2 bytes)
        
        # Byte address breakdown for row-bank-column:
        # [28:14] = row (15 bits)
        # [13:11] = bank (3 bits) 
        # [10:1]  = column (10 bits, but lower bits handle burst)
        # [0]     = byte within 16-bit word
        
        # Simplified: treat lower 4 bits as burst offset (16 bytes = 2^4)
        burst_addr = byte_addr >> 4  # Remove 16-byte burst offset
        
        col = (burst_addr >> 0) & ((1 << (COL_BITS - 3)) - 1)  # Column bits above burst
        col = col << 3  # Shift back (lower 3 bits are burst-internal)
        bank = (burst_addr >> (COL_BITS - 3)) & ((1 << BANK_BITS) - 1)
        row = (burst_addr >> (COL_BITS - 3 + BANK_BITS)) & ((1 << ROW_BITS) - 1)
        
        return row, col, bank
    
    def _apply_feedback(self):
        """Apply pending feedback from previous cycle to bank state."""
        if not self.pending_fb_valid:
            return
        
        cmd_type = self.pending_fb_type
        bank = self.pending_fb_bank
        row = self.pending_fb_row
        
        if cmd_type == SCHED_ACT:
            self.bank_is_active[bank] = 1
            self.bank_open_row[bank] = row
            self.cnt_rcd[bank] = CFG_tRCD_nCK
            self.cnt_ras[bank] = CFG_tRAS_nCK
            self.cnt_rrd = CFG_tRRD_nCK
            # Add to FAW window
            self.faw_window.append(self.cycle_count)
            # Keep only last 4 ACTs in window
            while len(self.faw_window) > 4:
                self.faw_window.pop(0)
                
        elif cmd_type == SCHED_PRE:
            self.bank_is_active[bank] = 0
            self.bank_open_row[bank] = 0
            self.cnt_rp[bank] = CFG_tRP_nCK
            
        elif cmd_type == SCHED_RD:
            self.cnt_rtp[bank] = CFG_tRTP_nCK
            self.cnt_ccd = CFG_tCCD_nCK
            
        elif cmd_type == SCHED_WR:
            self.cnt_wr[bank] = CFG_tWR_nCK + CFG_CWL + 4  # WR + CWL + BL/2
            self.cnt_wtr[bank] = CFG_tWTR_nCK
            self.cnt_ccd = CFG_tCCD_nCK
            
        elif cmd_type == SCHED_REF:
            # Refresh closes all banks and clears timing state
            for b in range(NUM_BANKS):
                self.bank_is_active[b] = 0
                self.bank_open_row[b] = 0
            self.cnt_rfc = CFG_tRFC_nCK
            self.faw_window = []  # Clear FAW window
            self.cnt_rrd = 0
            self.refresh_in_progress = True
        
        self.pending_fb_valid = False
    
    def _decrement_counters(self):
        """Decrement all timing counters by 1 each cycle."""
        # Per-bank counters
        for b in range(NUM_BANKS):
            if self.cnt_rcd[b] > 0:
                self.cnt_rcd[b] -= 1
            if self.cnt_ras[b] > 0:
                self.cnt_ras[b] -= 1
            if self.cnt_rp[b] > 0:
                self.cnt_rp[b] -= 1
            if self.cnt_wr[b] > 0:
                self.cnt_wr[b] -= 1
            if self.cnt_rtp[b] > 0:
                self.cnt_rtp[b] -= 1
            if self.cnt_wtr[b] > 0:
                self.cnt_wtr[b] -= 1
        
        # Global counters
        if self.cnt_rrd > 0:
            self.cnt_rrd -= 1
        if self.cnt_ccd > 0:
            self.cnt_ccd -= 1
        if self.cnt_rfc > 0:
            self.cnt_rfc -= 1
            if self.cnt_rfc == 0 and self.refresh_in_progress:
                self.refresh_in_progress = False
    
    def _check_bank_timing(self, bank: int) -> dict:
        """Check timing constraints for a specific bank."""
        return {
            'act_allowed': (not self.bank_is_active[bank] and 
                           self.cnt_rp[bank] == 0 and
                           self.cnt_rrd == 0 and
                           self._faw_allows_act()),
            'rd_allowed': (self.bank_is_active[bank] and 
                          self.cnt_rcd[bank] == 0 and
                          self.cnt_ccd == 0),
            'wr_allowed': (self.bank_is_active[bank] and 
                          self.cnt_rcd[bank] == 0 and
                          self.cnt_ccd == 0),
            'pre_allowed': (self.bank_is_active[bank] and 
                           self.cnt_ras[bank] == 0 and
                           self.cnt_rtp[bank] == 0 and
                           self.cnt_wr[bank] == 0)
        }
    
    def _faw_allows_act(self) -> bool:
        """Check if FAW constraint allows another ACT."""
        if len(self.faw_window) < 4:
            return True
        # Check if oldest ACT in window is old enough
        oldest_act = self.faw_window[0]
        return (self.cycle_count - oldest_act) >= CFG_tFAW_nCK
    
    def _all_banks_idle(self) -> bool:
        """Check if all banks are idle (required for refresh)."""
        return all(not active for active in self.bank_is_active)
    
    def _scheduler_decision(self, bank_open_row_0: int) -> dict:
        """
        Make scheduler decision based on FR-FCFS with open page policy.
        Returns dict with cmd_type, bank, row, col, valid, deq_grant, ref_ack.
        """
        result = {
            'cmd_type': SCHED_NOP,
            'bank': 0,
            'row': 0,
            'col': 0,
            'we': 0,
            'aux': 0,
            'valid': False,
            'deq_grant': 0,
            'ref_ack': 0
        }
        
        # If refresh in progress, no scheduling
        if self.refresh_in_progress or self.cnt_rfc > 0:
            return result
        
        # Priority 1: ref_urgent preempts everything
        if self.ref_urgent and self._all_banks_idle():
            result['cmd_type'] = SCHED_REF
            result['valid'] = True
            result['ref_ack'] = 1
            return result
        
        # Check queue entry
        if self.queue_valid:
            bank = self.queue_bank
            row = self.queue_row
            col = self.queue_col
            we = self.queue_we
            aux = self.queue_aux
            
            timing = self._check_bank_timing(bank)
            
            # Use bank_open_row_0 input for bank 0, otherwise use internal state
            if bank == 0:
                current_open_row = bank_open_row_0
            else:
                current_open_row = self.bank_open_row[bank]
            
            is_active = self.bank_is_active[bank]
            is_row_hit = is_active and (current_open_row == row)
            is_row_miss = not is_active or (current_open_row != row)
            
            # Priority 2: Row-hit CAS (is_cas_ready)
            if is_row_hit:
                if we and timing['wr_allowed']:
                    result['cmd_type'] = SCHED_WR
                    result['bank'] = bank
                    result['row'] = row
                    result['col'] = col
                    result['we'] = we
                    result['aux'] = aux
                    result['valid'] = True
                    result['deq_grant'] = 1  # CAS commands dequeue
                    return result
                elif not we and timing['rd_allowed']:
                    result['cmd_type'] = SCHED_RD
                    result['bank'] = bank
                    result['row'] = row
                    result['col'] = col
                    result['we'] = we
                    result['aux'] = aux
                    result['valid'] = True
                    result['deq_grant'] = 1  # CAS commands dequeue
                    return result
            
            # Priority 3: Row-miss handling (is_act_needed)
            if is_row_miss:
                # If bank active with wrong row, precharge first
                if is_active and timing['pre_allowed']:
                    result['cmd_type'] = SCHED_PRE
                    result['bank'] = bank
                    result['row'] = row
                    result['col'] = col
                    result['we'] = we
                    result['aux'] = aux
                    result['valid'] = True
                    return result
                # If bank idle, activate
                elif not is_active and timing['act_allowed']:
                    result['cmd_type'] = SCHED_ACT
                    result['bank'] = bank
                    result['row'] = row
                    result['col'] = col
                    result['we'] = we
                    result['aux'] = aux
                    result['valid'] = True
                    return result
        
        # Priority 4: Normal (non-urgent) refresh when all banks idle
        if self.ref_required and self._all_banks_idle():
            result['cmd_type'] = SCHED_REF
            result['valid'] = True
            result['ref_ack'] = 1
            return result
        
        # Priority 5: NOP
        return result
    
    def _cmd_to_ddr(self, cmd_type: int, bank: int, row: int, col: int) -> tuple:
        """Convert scheduler command to DDR command encoding."""
        ddr_cmd = DDR_NOP
        ddr_addr = 0
        ddr_bank = bank
        
        if cmd_type == SCHED_ACT:
            ddr_cmd = DDR_ACT
            ddr_addr = row  # Row address on ACT
        elif cmd_type == SCHED_RD:
            ddr_cmd = DDR_RD
            ddr_addr = col  # Column address on RD, with A10 for auto-precharge
        elif cmd_type == SCHED_WR:
            ddr_cmd = DDR_WR
            ddr_addr = col  # Column address on WR
        elif cmd_type == SCHED_PRE:
            ddr_cmd = DDR_PRE
            ddr_addr = 0  # A10=0 for single bank, bank in ddr_bank
        elif cmd_type == SCHED_REF:
            ddr_cmd = DDR_REF
            ddr_addr = 0
            ddr_bank = 0
        
        return ddr_cmd, ddr_addr, ddr_bank
    
    def _update_refresh_controller(self):
        """Update refresh controller state."""
        if not self.init_done:
            # Hold counters at 0 while not initialized
            self.refi_counter = 0
            self.postpone_cnt = 0
            self.ref_required = 0
            self.ref_urgent = 0
            return
        
        # Down-counter for tREFI
        if self.refi_counter == 0:
            # Timer expired - refresh tick
            self.refi_counter = CFG_tREFI_nCK
            if self.postpone_cnt < MAX_POSTPONE_COUNT:
                self.postpone_cnt += 1
        else:
            self.refi_counter -= 1
        
        # Update refresh request signals
        self.ref_required = 1 if self.postpone_cnt > 0 else 0
        self.ref_urgent = 1 if self.postpone_cnt >= URGENT_THRESHOLD else 0
    
    def step(self, **inputs) -> dict:
        """
        Advance the model by one clock cycle.
        
        Args:
            **inputs: Input signals (unknown ones are ignored)
        
        Returns:
            dict: All output signals with their current values
        """
        # Extract inputs (with defaults)
        wb_cyc_i = inputs.get('wb_cyc_i', 0)
        wb_stb_i = inputs.get('wb_stb_i', 0)
        wb_we_i = inputs.get('wb_we_i', 0)
        wb_adr_i = inputs.get('wb_adr_i', 0)
        wb_dat_i = inputs.get('wb_dat_i', 0)
        wb_sel_i = inputs.get('wb_sel_i', 0xF)
        wb_bte_i = inputs.get('wb_bte_i', 0)
        wb_cti_i = inputs.get('wb_cti_i', 0)
        req_ready = inputs.get('req_ready', 1)
        
        # Bank state from external (for single-entry mode)
        bank_open_row_0 = inputs.get('bank_open_row_0', 0)
        
        # External init_done signal
        init_done_in = inputs.get('init_done', 0)
        if init_done_in:
            self.init_done = True
        
        # Increment cycle counter
        self.cycle_count += 1
        
        # =====================================================================
        # Step 1: Apply pending feedback from PREVIOUS cycle
        # =====================================================================
        self._apply_feedback()
        
        # =====================================================================
        # Step 2: Decrement timing counters
        # =====================================================================
        self._decrement_counters()
        
        # =====================================================================
        # Step 3: Update refresh controller
        # =====================================================================
        self._update_refresh_controller()
        
        # Handle ref_ack from pipe_s2 (1 cycle delayed from scheduler)
        if self.pipe_s2.get('ref_ack', 0):
            if self.postpone_cnt > 0:
                self.postpone_cnt -= 1
            self.ref_required = 1 if self.postpone_cnt > 0 else 0
            self.ref_urgent = 1 if self.postpone_cnt >= URGENT_THRESHOLD else 0
        
        # =====================================================================
        # Step 4: Capture DDR output from pipe_s2 BEFORE shifting
        # =====================================================================
        old_pipe_s2 = self.pipe_s2.copy()
        
        ddr_cmd, ddr_addr, ddr_bank = self._cmd_to_ddr(
            old_pipe_s2['cmd_type'],
            old_pipe_s2['bank'],
            old_pipe_s2['row'],
            old_pipe_s2['col']
        )
        
        self.ddr_cmd = ddr_cmd
        self.ddr_addr = ddr_addr
        self.ddr_bank = ddr_bank
        
        # Generate feedback signals based on command type
        self.fb_act_valid = 1 if old_pipe_s2['cmd_type'] == SCHED_ACT else 0
        self.fb_act_bank = old_pipe_s2['bank'] if self.fb_act_valid else 0
        self.fb_act_row = old_pipe_s2['row'] if self.fb_act_valid else 0
        self.fb_pre_valid = 1 if old_pipe_s2['cmd_type'] == SCHED_PRE else 0
        self.fb_rd_valid = 1 if old_pipe_s2['cmd_type'] == SCHED_RD else 0
        self.fb_wr_valid = 1 if old_pipe_s2['cmd_type'] == SCHED_WR else 0
        self.fb_ref_valid = 1 if old_pipe_s2['cmd_type'] == SCHED_REF else 0
        
        # =====================================================================
        # Step 5: Wishbone Interface Handling
        # =====================================================================
        wb_valid = wb_cyc_i and wb_stb_i
        
        # Default outputs
        self.wb_ack = 0
        self.wb_err = 0
        
        # Accept new request if queue has space
        if wb_valid and not self.queue_valid and not self.wb_stall:
            # Decode address
            row, col, bank = self._decode_address(wb_adr_i)
            
            # Store in queue
            self.queue_valid = True
            self.queue_row = row
            self.queue_col = col
            self.queue_bank = bank
            self.queue_we = wb_we_i
            self.queue_aux = 0  # AUX field for tracking
            self.queue_wdata = wb_dat_i if wb_we_i else 0
            self.queue_wmask = wb_sel_i if wb_we_i else 0
            
            # Update decoder outputs
            self.dec_row = row
            self.dec_col = col
            self.dec_bank = bank
            
            # ACK the Wishbone transaction
            self.wb_ack = 1
            
            # Store request data for output
            self.req_wdata = wb_dat_i if wb_we_i else 0
            self.req_wmask = wb_sel_i if wb_we_i else 0
        
        # Update queue status
        self.queue_full = 1 if self.queue_valid else 0
        self.queue_empty = 0 if self.queue_valid else 1
        self.queue_count = 1 if self.queue_valid else 0
        self.enq_ready = 0 if self.queue_valid else 1
        self.wb_stall = self.queue_full
        
        # =====================================================================
        # Step 6: Scheduler Decision
        # =====================================================================
        new_decision = self._scheduler_decision(bank_open_row_0)
        
        # =====================================================================
        # Step 7: Shift pipeline
        # =====================================================================
        self.pipe_s2 = self.pipe_s1.copy()
        self.pipe_s1 = new_decision.copy()
        
        # =====================================================================
        # Step 8: Store current pipe_s2 command as pending feedback
        # =====================================================================
        self.pending_fb_type = old_pipe_s2['cmd_type']
        self.pending_fb_bank = old_pipe_s2['bank']
        self.pending_fb_row = old_pipe_s2['row']
        self.pending_fb_valid = old_pipe_s2['valid']
        
        # =====================================================================
        # Step 9: Handle dequeue on CAS completion
        # =====================================================================
        # deq_grant comes from pipe_s2 AFTER shift (1 cycle delay from scheduler)
        if self.pipe_s2.get('deq_grant', 0):
            self.queue_valid = False
            self.queue_full = 0
            self.queue_empty = 1
            self.queue_count = 0
            self.enq_ready = 1
            self.wb_stall = 0
        
        # =====================================================================
        # Step 10: Extract ref_ack from pipe_s2 AFTER shift
        # =====================================================================
        self.ref_ack = self.pipe_s2.get('ref_ack', 0)
        
        # =====================================================================
        # Build output dictionary with ALL signals
        # =====================================================================
        outputs = {
            # Wishbone outputs
            'wb_ack_o': self.wb_ack,
            'wb_dat_o': self.wb_dat_o,
            'wb_stall_o': self.wb_stall,
            'wb_err_o': self.wb_err,
            
            # Request data outputs
            'req_wdata': self.req_wdata,
            'req_wmask': self.req_wmask,
            
            # Address decoder outputs
            'dec_rank': self.dec_rank,
            
            # Queue status outputs
            'enq_ready': self.enq_ready,
            'queue_full': self.queue_full,
            'queue_empty': self.queue_empty,
            'queue_count': self.queue_count,
            
            # Refresh outputs
            'ref_ack': self.ref_ack,
            
            # DDR command outputs
            'ddr_cmd': self.ddr_cmd,
            'ddr_addr': self.ddr_addr,
            'ddr_bank': self.ddr_bank,
            'ddr_cke': self.ddr_cke,
            'ddr_reset_n': self.ddr_reset_n,
            'ddr_odt': self.ddr_odt,
            
            # Feedback signals
            'fb_act_valid': self.fb_act_valid,
            'fb_act_bank': self.fb_act_bank,
            'fb_act_row': self.fb_act_row,
            'fb_pre_valid': self.fb_pre_valid,
            'fb_rd_valid': self.fb_rd_valid,
            'fb_wr_valid': self.fb_wr_valid,
            'fb_ref_valid': self.fb_ref_valid,
        }
        
        return outputs
    
    def get_state(self) -> dict:
        """Return full internal state for debugging."""
        return {
            # Wishbone state
            'wb_stall': self.wb_stall,
            'wb_ack': self.wb_ack,
            
            # Queue state
            'queue_valid': self.queue_valid,
            'queue_row': self.queue_row,
            'queue_col': self.queue_col,
            'queue_bank': self.queue_bank,
            'queue_we': self.queue_we,
            
            # Bank state
            'bank_is_active': self.bank_is_active.copy(),
            'bank_open_row': self.bank_open_row.copy(),
            
            # Timing counters
            'cnt_rcd': self.cnt_rcd.copy(),
            'cnt_ras': self.cnt_ras.copy(),
            'cnt_rp': self.cnt_rp.copy(),
            'cnt_rrd': self.cnt_rrd,
            'cnt_rfc': self.cnt_rfc,
            'cnt_ccd': self.cnt_ccd,
            
            # FAW window
            'faw_window': self.faw_window.copy(),
            'cycle_count': self.cycle_count,
            
            # Refresh state
            'init_done': self.init_done,
            'refi_counter': self.refi_counter,
            'postpone_cnt': self.postpone_cnt,
            'ref_required': self.ref_required,
            'ref_urgent': self.ref_urgent,
            'refresh_in_progress': self.refresh_in_progress,
            
            # Pipeline state
            'pipe_s1': self.pipe_s1.copy(),
            'pipe_s2': self.pipe_s2.copy(),
            'pending_fb_type': self.pending_fb_type,
            'pending_fb_bank': self.pending_fb_bank,
            'pending_fb_row': self.pending_fb_row,
            'pending_fb_valid': self.pending_fb_valid,
            
            # DDR outputs
            'ddr_cmd': self.ddr_cmd,
            'ddr_addr': self.ddr_addr,
            'ddr_bank': self.ddr_bank,
        }


def run_self_test():
    """Run self-tests to verify the reference model."""
    tests_passed = 0
    tests_failed = 0
    
    def test(name: str, condition: bool, msg: str = ""):
        nonlocal tests_passed, tests_failed
        if condition:
            print(f"PASS: {name}")
            tests_passed += 1
        else:
            print(f"FAIL: {name} - {msg}")
            tests_failed += 1
    
    # =========================================================================
    # Test 1: Reset values
    # =========================================================================
    print("\n=== Test 1: Reset Values ===")
    model = PathModel()
    
    test("Reset - ddr_cmd is NOP", model.ddr_cmd == DDR_NOP, f"got {model.ddr_cmd}")
    test("Reset - queue_empty is 1", model.queue_empty == 1, f"got {model.queue_empty}")
    test("Reset - queue_valid is False", model.queue_valid == False, f"got {model.queue_valid}")
    test("Reset - enq_ready is 1", model.enq_ready == 1, f"got {model.enq_ready}")
    test("Reset - wb_stall is 0", model.wb_stall == 0, f"got {model.wb_stall}")
    test("Reset - all banks idle", all(not a for a in model.bank_is_active), 
         f"got {model.bank_is_active}")
    test("Reset - init_done is False", model.init_done == False, f"got {model.init_done}")
    
    # =========================================================================
    # Test 2: step() returns all output signals
    # =========================================================================
    print("\n=== Test 2: step() Output Completeness ===")
    model = PathModel()
    outputs = model.step()
    
    expected_outputs = [
        'wb_ack_o', 'wb_dat_o', 'wb_stall_o', 'wb_err_o',
        'req_wdata', 'req_wmask', 'dec_rank',
        'enq_ready', 'queue_full', 'queue_empty', 'queue_count',
        'ref_ack', 'ddr_cmd', 'ddr_addr', 'ddr_bank',
        'ddr_cke', 'ddr_reset_n', 'ddr_odt',
        'fb_act_valid', 'fb_act_bank', 'fb_act_row',
        'fb_pre_valid', 'fb_rd_valid', 'fb_wr_valid', 'fb_ref_valid'
    ]
    
    for sig in expected_outputs:
        test(f"Output contains {sig}", sig in outputs, f"missing from outputs")
    
    # =========================================================================
    # Test 3: step() accepts unknown kwargs
    # =========================================================================
    print("\n=== Test 3: step() Accepts Unknown Kwargs ===")
    model = PathModel()
    try:
        outputs = model.step(unknown_signal=42, another_unknown=0xDEAD)
        test("step() accepts unknown kwargs", True, "")
    except Exception as e:
        test("step() accepts unknown kwargs", False, str(e))
    
    # =========================================================================
    # Test 4: Wishbone Write Request
    # =========================================================================
    print("\n=== Test 4: Wishbone Write Request ===")
    model = PathModel()
    
    # Issue a write request
    outputs = model.step(
        wb_cyc_i=1,
        wb_stb_i=1,
        wb_we_i=1,
        wb_adr_i=0x1000,  # Some address
        wb_dat_i=0xDEADBEEF,
        wb_sel_i=0xF
    )
    
    test("Write - wb_ack_o asserted", outputs['wb_ack_o'] == 1, f"got {outputs['wb_ack_o']}")
    test("Write - queue not empty", model.queue_valid == True, f"got {model.queue_valid}")
    test("Write - queue_we is 1", model.queue_we == 1, f"got {model.queue_we}")
    test("Write - req_wdata captured", outputs['req_wdata'] == 0xDEADBEEF, 
         f"got {hex(outputs['req_wdata'])}")
    test("Write - req_wmask captured", outputs['req_wmask'] == 0xF, 
         f"got {outputs['req_wmask']}")
    
    # =========================================================================
    # Test 5: Address Decoding
    # =========================================================================
    print("\n=== Test 5: Address Decoding ===")
    model = PathModel()
    
    # Test address decoding with known address
    # For row-bank-column mapping with 16-byte burst offset:
    # Row should be in upper bits, bank in middle, column in lower
    test_addr = 0x00800000  # Should hit a specific row/bank/col
    row, col, bank = model._decode_address(test_addr)
    
    test("Decode - row is integer", isinstance(row, int), f"got {type(row)}")
    test("Decode - col is integer", isinstance(col, int), f"got {type(col)}")
    test("Decode - bank is integer", isinstance(bank, int), f"got {type(bank)}")
    test("Decode - bank in range", 0 <= bank < NUM_BANKS, f"got {bank}")
    test("Decode - row in range", 0 <= row < (1 << ROW_BITS), f"got {row}")
    test("Decode - col in range", 0 <= col < (1 << COL_BITS), f"got {col}")
    
    # =========================================================================
    # Test 6: Pipeline Latency (NOP propagation)
    # =========================================================================
    print("\n=== Test 6: Pipeline Latency ===")
    model = PathModel()
    
    # Without init_done and no requests, should output NOPs
    for i in range(5):
        outputs = model.step()
    
    test("Pipeline - ddr_cmd is NOP when idle", outputs['ddr_cmd'] == DDR_NOP, 
         f"got {outputs['ddr_cmd']}")
    test("Pipeline - fb_act_valid is 0 when idle", outputs['fb_act_valid'] == 0,
         f"got {outputs['fb_act_valid']}")
    
    # =========================================================================
    # Test 7: Refresh Controller Initial Tick
    # =========================================================================
    print("\n=== Test 7: Refresh Controller ===")
    model = PathModel()
    
    # Before init_done, no refresh required
    outputs = model.step()
    test("Refresh - ref_required=0 before init", model.ref_required == 0, 
         f"got {model.ref_required}")
    
    # Set init_done, first cycle should trigger refi_tick
    outputs = model.step(init_done=1)
    test("Refresh - ref_required=1 after init", model.ref_required == 1,
         f"got {model.ref_required}")
    test("Refresh - postpone_cnt=1 after init", model.postpone_cnt == 1,
         f"got {model.postpone_cnt}")
    
    # =========================================================================
    # Test 8: Timing Constraints
    # =========================================================================
    print("\n=== Test 8: Timing Constraints ===")
    model = PathModel()
    
    test("Timing - CFG_tRCD_nCK is 11", CFG_tRCD_nCK == 11, f"got {CFG_tRCD_nCK}")
    test("Timing - CFG_tRP_nCK is 11", CFG_tRP_nCK == 11, f"got {CFG_tRP_nCK}")
    test("Timing - CFG_tRFC_nCK is 128", CFG_tRFC_nCK == 128, f"got {CFG_tRFC_nCK}")
    test("Timing - CFG_tFAW_nCK is 32", CFG_tFAW_nCK == 32, f"got {CFG_tFAW_nCK}")
    
    # =========================================================================
    # Test 9: DDR Command Encoding
    # =========================================================================
    print("\n=== Test 9: DDR Command Encoding ===")
    
    test("DDR - NOP encoding is 7", DDR_NOP == 7, f"got {DDR_NOP}")
    test("DDR - ACT encoding is 3", DDR_ACT == 3, f"got {DDR_ACT}")
    test("DDR - RD encoding is 5", DDR_RD == 5, f"got {DDR_RD}")
    test("DDR - WR encoding is 4", DDR_WR == 4, f"got {DDR_WR}")
    test("DDR - PRE encoding is 2", DDR_PRE == 2, f"got {DDR_PRE}")
    test("DDR - REF encoding is 1", DDR_REF == 1, f"got {DDR_REF}")
    
    # =========================================================================
    # Test 10: Full Write Transaction Flow
    # =========================================================================
    print("\n=== Test 10: Full Write Transaction Flow ===")
    model = PathModel()
    model.init_done = True  # Skip initialization
    
    # Issue write request
    outputs = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x100, wb_dat_i=0x12345678, wb_sel_i=0xF,
        init_done=1
    )
    
    test("Flow - write accepted", outputs['wb_ack_o'] == 1, f"got {outputs['wb_ack_o']}")
    test("Flow - queue has entry", model.queue_valid == True, f"got {model.queue_valid}")
    
    # Run scheduler for several cycles to see command generation
    # Note: Due to pipeline latency, commands appear 2 cycles after decision
    act_seen = False
    wr_seen = False
    cycles_run = 0
    max_cycles = 50  # Enough for ACT + tRCD + WR
    
    while cycles_run < max_cycles and not wr_seen:
        # Provide bank_open_row_0 matching what we track internally
        outputs = model.step(
            wb_cyc_i=0, wb_stb_i=0,
            bank_open_row_0=model.bank_open_row[0],
            init_done=1
        )
        cycles_run += 1
        
        if outputs['ddr_cmd'] == DDR_ACT:
            act_seen = True
        if outputs['ddr_cmd'] == DDR_WR:
            wr_seen = True
    
    test("Flow - ACT command issued", act_seen, f"ACT not seen in {cycles_run} cycles")
    test("Flow - WR command issued", wr_seen, f"WR not seen in {cycles_run} cycles")
    
    # =========================================================================
    # Test 11: get_state() returns dict
    # =========================================================================
    print("\n=== Test 11: get_state() ===")
    model = PathModel()
    state = model.get_state()
    
    test("get_state - returns dict", isinstance(state, dict), f"got {type(state)}")
    test("get_state - contains bank_is_active", 'bank_is_active' in state, "missing")
    test("get_state - contains pipe_s1", 'pipe_s1' in state, "missing")
    test("get_state - contains cycle_count", 'cycle_count' in state, "missing")
    
    # =========================================================================
    # Test 12: Queue Full Behavior
    # =========================================================================
    print("\n=== Test 12: Queue Full Behavior ===")
    model = PathModel()
    
    # First write - should be accepted
    outputs = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x200, wb_dat_i=0xAAAAAAAA, wb_sel_i=0xF
    )
    test("Queue - first write accepted", outputs['wb_ack_o'] == 1, f"got {outputs['wb_ack_o']}")
    
    # Second write immediately - should stall (queue full in single-entry mode)
    outputs = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x300, wb_dat_i=0xBBBBBBBB, wb_sel_i=0xF
    )
    test("Queue - second write stalls", outputs['wb_stall_o'] == 1, 
         f"got stall={outputs['wb_stall_o']}")
    
    # =========================================================================
    # Test 13: FAW Constraint
    # =========================================================================
    print("\n=== Test 13: FAW Window ===")
    model = PathModel()
    
    # Initially FAW should allow ACT
    test("FAW - allows ACT initially", model._faw_allows_act() == True, 
         f"got {model._faw_allows_act()}")
    
    # Simulate 4 ACTs by adding to window
    for i in range(4):
        model.faw_window.append(model.cycle_count)
        model.cycle_count += 1
    
    # FAW should now block (need CFG_tFAW_nCK cycles since first ACT)
    test("FAW - blocks after 4 ACTs", model._faw_allows_act() == False,
         f"got {model._faw_allows_act()}")
    
    # Advance time past FAW
    model.cycle_count += CFG_tFAW_nCK
    test("FAW - allows after tFAW", model._faw_allows_act() == True,
         f"got {model._faw_allows_act()}")
    
    # =========================================================================
    # Summary
    # =========================================================================
    print("\n" + "=" * 60)
    print(f"Tests Passed: {tests_passed}")
    print(f"Tests Failed: {tests_failed}")
    print("=" * 60)
    
    if tests_failed == 0:
        print("ALL TESTS PASSED")
    else:
        print(f"SOME TESTS FAILED ({tests_failed} failures)")
    
    return tests_failed == 0


if __name__ == "__main__":
    run_self_test()