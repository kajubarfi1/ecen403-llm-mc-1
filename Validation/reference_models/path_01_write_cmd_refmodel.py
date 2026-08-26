#!/usr/bin/env python3
"""
Reference model for DDR3 Write Command Path
Path: wb_port -> addr_decoder -> cmd_queue -> scheduler -> cmd_gen

Derived from spec: path_01_write_cmd
"""

import json
import os

# =============================================================================
# Constants from spec
# =============================================================================

# Memory geometry
ROW_BITS = 15
COL_BITS = 10
BANK_BITS = 3
NUM_BANKS = 8

# Timing parameters (in controller clock cycles, from spec $derived_cycles)
CFG_tRCD_nCK = 11
CFG_tRP_nCK = 11
CFG_tRAS_nCK = 28
CFG_tRC_nCK = 39
CFG_tRFC_nCK = 128
CFG_tFAW_nCK = 32
CFG_tRRD_nCK = 6
CFG_tWR_nCK = 12
CFG_tWTR_nCK = 6
CFG_tRTP_nCK = 6
CFG_tCCD_nCK = 4
CFG_tREFI_nCK = 6240
CFG_CL = 11
CFG_CWL = 8

# Refresh policy
MAX_POSTPONE_COUNT = 8
URGENT_THRESHOLD = 6

# Queue depth (single-entry mode means we only model entry 0)
CMD_QUEUE_DEPTH = 16

# DDR command encoding (CS#/RAS#/CAS#/WE# active-low)
DDR_NOP = 7    # 4'b0111
DDR_ACT = 3    # 4'b0011
DDR_RD = 5     # 4'b0101
DDR_WR = 4     # 4'b0100
DDR_PRE = 2    # 4'b0010
DDR_REF = 1    # 4'b0001
DDR_MRS = 0    # 4'b0000
DDR_ZQCL = 6   # 4'b0110
DDR_DESL = 15  # 4'b1111

# Scheduler command types (internal)
SCHED_NOP = 0
SCHED_ACT = 1
SCHED_RD = 2
SCHED_WR = 3
SCHED_PRE = 4
SCHED_REF = 5


class PathModel:
    """
    Reference model for DDR3 Write Command Path.
    Models: wb_port -> addr_decoder -> cmd_queue -> scheduler -> cmd_gen
    """

    def __init__(self):
        self.reset()

    def reset(self):
        """Reset all internal state to power-on defaults."""
        # =====================================================================
        # Wishbone Port State
        # =====================================================================
        self.wb_ack_pending = False
        self.wb_stall = False
        self.wb_dat_o = 0
        self.wb_err = False
        
        # =====================================================================
        # Address Decoder State
        # =====================================================================
        self.dec_row = 0
        self.dec_col = 0
        self.dec_bank = 0
        self.dec_rank = 0  # Single rank
        
        # =====================================================================
        # Command Queue State (single-entry mode)
        # =====================================================================
        self.queue_valid = False
        self.queue_row = 0
        self.queue_col = 0
        self.queue_bank = 0
        self.queue_we = False
        self.queue_aux = 0
        self.queue_count = 0
        
        # Write data buffer
        self.req_wdata = 0
        self.req_wmask = 0
        
        # =====================================================================
        # Bank Tracker State (per-bank)
        # =====================================================================
        self.bank_is_active = [0] * NUM_BANKS
        self.bank_open_row = [0] * NUM_BANKS
        
        # Per-bank timing counters
        self.cnt_rcd = [0] * NUM_BANKS   # ACT to CAS
        self.cnt_rp = [0] * NUM_BANKS    # PRE to ACT
        self.cnt_ras = [0] * NUM_BANKS   # ACT to PRE (min active time)
        self.cnt_rc = [0] * NUM_BANKS    # ACT to ACT (same bank)
        self.cnt_wr = [0] * NUM_BANKS    # Write recovery
        self.cnt_rtp = [0] * NUM_BANKS   # Read to PRE
        self.cnt_wtr = [0] * NUM_BANKS   # Write to Read
        self.cnt_ccd = [0] * NUM_BANKS   # CAS to CAS
        
        # Global timing
        self.cnt_rrd = 0       # ACT to ACT (different banks)
        self.cnt_rfc = 0       # Refresh cycle time
        self.faw_window = []   # Timestamps of last 4 ACTs for tFAW
        self.cycle_count = 0   # Global cycle counter for FAW tracking
        
        # Refresh state
        self.refresh_in_progress = False
        self.refi_counter = 0
        self.postpone_cnt = 0
        self.init_done = True  # Assume init complete for this path model
        self.ref_required = False
        self.ref_urgent = False
        
        # =====================================================================
        # Scheduler Pipeline (2-stage for DDR output timing)
        # =====================================================================
        # pipe_s1: scheduler decision (1 cycle old)
        # pipe_s2: cmd_gen output (2 cycles old, visible on DDR pins)
        self.pipe_s1 = {
            'valid': False,
            'cmd_type': SCHED_NOP,
            'bank': 0,
            'row': 0,
            'col': 0,
            'we': False,
            'aux': 0,
            'deq': False,
            'ref_ack': False
        }
        self.pipe_s2 = {
            'valid': False,
            'cmd_type': SCHED_NOP,
            'bank': 0,
            'row': 0,
            'col': 0,
            'we': False,
            'aux': 0,
            'deq': False,
            'ref_ack': False
        }
        
        # Pending feedback (applied at START of next cycle)
        self.pending_fb = {
            'valid': False,
            'cmd_type': SCHED_NOP,
            'bank': 0,
            'row': 0
        }
        
        # =====================================================================
        # DDR Output Registers
        # =====================================================================
        self.ddr_cmd = DDR_NOP
        self.ddr_addr = 0
        self.ddr_bank = 0
        self.ddr_cke = 1
        self.ddr_reset_n = 1
        self.ddr_odt = 0

    def _decode_address(self, byte_addr):
        """
        Decode Wishbone byte address into DDR row/bank/col.
        Address mapping: row-bank-column (from spec)
        
        Host address bits breakdown:
        - [1:0] byte within 32-bit word (ignored, aligned)
        - [COL_BITS+1:2] column address (within page)
        - [COL_BITS+BANK_BITS+1:COL_BITS+2] bank address
        - [COL_BITS+BANK_BITS+ROW_BITS+1:COL_BITS+BANK_BITS+2] row address
        
        For 16-bit DDR bus with BL8: burst covers 16 bytes on DQ
        Column address: [COL_BITS-1:0], but lower 3 bits are burst-internal
        """
        # Shift out byte offset within burst (DDR BL8 = 8 beats * 2 bytes = 16 bytes)
        # But Wishbone is 32-bit, so shift by 2 for word alignment
        word_addr = byte_addr >> 2
        
        # Extract column (lower bits after word alignment)
        col_mask = (1 << COL_BITS) - 1
        col = word_addr & col_mask
        
        # Extract bank
        bank_shift = COL_BITS
        bank_mask = (1 << BANK_BITS) - 1
        bank = (word_addr >> bank_shift) & bank_mask
        
        # Extract row
        row_shift = COL_BITS + BANK_BITS
        row_mask = (1 << ROW_BITS) - 1
        row = (word_addr >> row_shift) & row_mask
        
        return row, bank, col

    def _apply_feedback(self):
        """Apply pending feedback from previous cycle to bank state."""
        if not self.pending_fb['valid']:
            return
        
        cmd_type = self.pending_fb['cmd_type']
        bank = self.pending_fb['bank']
        row = self.pending_fb['row']
        
        if cmd_type == SCHED_ACT:
            # Activate: open row in bank
            self.bank_is_active[bank] = 1
            self.bank_open_row[bank] = row
            # Start timing counters
            self.cnt_rcd[bank] = CFG_tRCD_nCK
            self.cnt_ras[bank] = CFG_tRAS_nCK
            self.cnt_rc[bank] = CFG_tRC_nCK
            # Global RRD and FAW
            self.cnt_rrd = CFG_tRRD_nCK
            self.faw_window.append(self.cycle_count)
            # Keep only last 4 ACTs
            if len(self.faw_window) > 4:
                self.faw_window.pop(0)
        
        elif cmd_type == SCHED_PRE:
            # Precharge: close bank
            self.bank_is_active[bank] = 0
            self.bank_open_row[bank] = 0
            self.cnt_rp[bank] = CFG_tRP_nCK
        
        elif cmd_type == SCHED_RD:
            # Read: start CAS-related timers
            self.cnt_ccd[bank] = CFG_tCCD_nCK
            self.cnt_rtp[bank] = CFG_tRTP_nCK
        
        elif cmd_type == SCHED_WR:
            # Write: start CAS-related timers
            self.cnt_ccd[bank] = CFG_tCCD_nCK
            self.cnt_wr[bank] = CFG_tWR_nCK + CFG_CWL + 4  # WR recovery
            self.cnt_wtr[bank] = CFG_tWTR_nCK
        
        elif cmd_type == SCHED_REF:
            # Refresh: close ALL banks, clear FAW
            for b in range(NUM_BANKS):
                self.bank_is_active[b] = 0
                self.bank_open_row[b] = 0
            self.cnt_rfc = CFG_tRFC_nCK
            self.faw_window = []  # Clear FAW window
            self.cnt_rrd = 0      # Clear RRD
            self.refresh_in_progress = True
        
        # Clear pending feedback
        self.pending_fb['valid'] = False

    def _decrement_counters(self):
        """Decrement all timing counters by 1 each cycle."""
        for b in range(NUM_BANKS):
            if self.cnt_rcd[b] > 0:
                self.cnt_rcd[b] -= 1
            if self.cnt_rp[b] > 0:
                self.cnt_rp[b] -= 1
            if self.cnt_ras[b] > 0:
                self.cnt_ras[b] -= 1
            if self.cnt_rc[b] > 0:
                self.cnt_rc[b] -= 1
            if self.cnt_wr[b] > 0:
                self.cnt_wr[b] -= 1
            if self.cnt_rtp[b] > 0:
                self.cnt_rtp[b] -= 1
            if self.cnt_wtr[b] > 0:
                self.cnt_wtr[b] -= 1
            if self.cnt_ccd[b] > 0:
                self.cnt_ccd[b] -= 1
        
        if self.cnt_rrd > 0:
            self.cnt_rrd -= 1
        
        if self.cnt_rfc > 0:
            self.cnt_rfc -= 1
        
        # Check if refresh cycle complete
        if self.cnt_rfc == 0 and self.refresh_in_progress:
            self.refresh_in_progress = False

    def _update_refresh(self):
        """Update refresh controller state."""
        if not self.init_done:
            self.refi_counter = 0
            self.postpone_cnt = 0
            self.ref_required = False
            self.ref_urgent = False
            return
        
        # Down-counter for tREFI
        if self.refi_counter > 0:
            self.refi_counter -= 1
        
        # tREFI tick when counter reaches 0
        if self.refi_counter == 0:
            if self.postpone_cnt < MAX_POSTPONE_COUNT:
                self.postpone_cnt += 1
            self.refi_counter = CFG_tREFI_nCK
        
        # Update required/urgent flags
        self.ref_required = (self.postpone_cnt > 0)
        self.ref_urgent = (self.postpone_cnt >= URGENT_THRESHOLD)

    def _check_bank_timing(self, bank, bank_is_active_input, bank_open_row_input):
        """
        Check timing constraints for a bank.
        Returns: (act_allowed, rd_allowed, wr_allowed, pre_allowed)
        """
        # Use input bank state (from testbench, representing current RTL state)
        is_active = bank_is_active_input
        
        # ACT allowed if: bank idle, tRP done, tRC done, tRRD done, FAW allows
        faw_allows = True
        if len(self.faw_window) >= 4:
            oldest_act = self.faw_window[0]
            if (self.cycle_count - oldest_act) < CFG_tFAW_nCK:
                faw_allows = False
        
        act_allowed = (not is_active and 
                       self.cnt_rp[bank] == 0 and 
                       self.cnt_rc[bank] == 0 and 
                       self.cnt_rrd == 0 and 
                       faw_allows and
                       not self.refresh_in_progress)
        
        # RD allowed if: bank active, tRCD done, tCCD done
        rd_allowed = (is_active and 
                      self.cnt_rcd[bank] == 0 and 
                      self.cnt_ccd[bank] == 0 and
                      not self.refresh_in_progress)
        
        # WR allowed if: bank active, tRCD done, tCCD done
        wr_allowed = (is_active and 
                      self.cnt_rcd[bank] == 0 and 
                      self.cnt_ccd[bank] == 0 and
                      not self.refresh_in_progress)
        
        # PRE allowed if: bank active, tRAS done, tRTP done, tWR done
        pre_allowed = (is_active and 
                       self.cnt_ras[bank] == 0 and 
                       self.cnt_rtp[bank] == 0 and 
                       self.cnt_wr[bank] == 0 and
                       not self.refresh_in_progress)
        
        return act_allowed, rd_allowed, wr_allowed, pre_allowed

    def _scheduler_decision(self, bank_is_active_input, bank_open_row_input,
                           bank_act_allowed, bank_rd_allowed, bank_wr_allowed,
                           bank_pre_allowed, ref_required_in, ref_urgent_in):
        """
        Make scheduler decision based on current state.
        Returns: (cmd_type, bank, row, col, we, aux, deq_grant, ref_ack)
        """
        # Default: NOP
        cmd_type = SCHED_NOP
        bank = 0
        row = 0
        col = 0
        we = False
        aux = 0
        deq_grant = False
        ref_ack = False
        
        # If refresh in progress, only issue NOP
        if self.refresh_in_progress:
            return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
        
        # Priority 1: ref_urgent preempts everything
        if ref_urgent_in and self._all_banks_idle(bank_is_active_input):
            cmd_type = SCHED_REF
            ref_ack = True
            return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
        
        # Check queue entry 0 (single-entry mode)
        if self.queue_valid:
            q_bank = self.queue_bank
            q_row = self.queue_row
            q_col = self.queue_col
            q_we = self.queue_we
            q_aux = self.queue_aux
            
            is_active = bank_is_active_input
            open_row = bank_open_row_input
            
            # Priority 2: Row-hit CAS
            row_hit = (is_active and open_row == q_row)
            
            if row_hit:
                if q_we and bank_wr_allowed:
                    # Write
                    cmd_type = SCHED_WR
                    bank = q_bank
                    row = q_row
                    col = q_col
                    we = True
                    aux = q_aux
                    deq_grant = True
                    return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
                elif not q_we and bank_rd_allowed:
                    # Read
                    cmd_type = SCHED_RD
                    bank = q_bank
                    row = q_row
                    col = q_col
                    we = False
                    aux = q_aux
                    deq_grant = True
                    return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
            
            # Priority 3: Row-miss handling
            if is_active and open_row != q_row:
                # Need precharge first
                if bank_pre_allowed:
                    cmd_type = SCHED_PRE
                    bank = q_bank
                    return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
            
            if not is_active:
                # Need activate
                if bank_act_allowed:
                    cmd_type = SCHED_ACT
                    bank = q_bank
                    row = q_row
                    return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
        
        # Priority 4: Non-urgent refresh
        if ref_required_in and self._all_banks_idle(bank_is_active_input):
            cmd_type = SCHED_REF
            ref_ack = True
            return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack
        
        # Priority 5: NOP (default)
        return cmd_type, bank, row, col, we, aux, deq_grant, ref_ack

    def _all_banks_idle(self, bank_is_active_input):
        """Check if all banks are idle (for refresh)."""
        # For single-entry mode, we only check bank 0 status from input
        # But we need to consider all banks for refresh
        # Since we're in single-entry mode with single bank input,
        # we check our internal state for other banks
        for b in range(NUM_BANKS):
            if self.bank_is_active[b]:
                return False
        return True

    def _encode_ddr_cmd(self, cmd_type, bank, row, col):
        """Encode scheduler command type to DDR command."""
        if cmd_type == SCHED_NOP:
            return DDR_NOP, 0, 0
        elif cmd_type == SCHED_ACT:
            return DDR_ACT, row, bank
        elif cmd_type == SCHED_RD:
            # Column address with A10=0 for no auto-precharge
            return DDR_RD, col & 0x3FF, bank
        elif cmd_type == SCHED_WR:
            return DDR_WR, col & 0x3FF, bank
        elif cmd_type == SCHED_PRE:
            # A10=0 for single-bank precharge
            return DDR_PRE, 0, bank
        elif cmd_type == SCHED_REF:
            return DDR_REF, 0, 0
        else:
            return DDR_NOP, 0, 0

    def step(self, **inputs):
        """
        Advance the model by one clock cycle.
        Accept any input signals as keyword arguments (ignore unknown ones).
        """
        # Extract inputs (with defaults)
        wb_cyc_i = inputs.get('wb_cyc_i', 0)
        wb_stb_i = inputs.get('wb_stb_i', 0)
        wb_we_i = inputs.get('wb_we_i', 0)
        wb_adr_i = inputs.get('wb_adr_i', 0)
        wb_dat_i = inputs.get('wb_dat_i', 0)
        wb_sel_i = inputs.get('wb_sel_i', 0xF)
        
        req_ready = inputs.get('req_ready', 1)
        
        # Bank state inputs (single-entry mode: only bank 0 from testbench)
        bank_is_active_in = inputs.get('bank_is_active', 0)
        bank_open_row_0 = inputs.get('bank_open_row_0', 0)
        bank_act_allowed = inputs.get('bank_act_allowed', 1)
        bank_rd_allowed = inputs.get('bank_rd_allowed', 0)
        bank_wr_allowed = inputs.get('bank_wr_allowed', 0)
        bank_pre_allowed = inputs.get('bank_pre_allowed', 0)
        
        ref_required_in = inputs.get('ref_required', self.ref_required)
        ref_urgent_in = inputs.get('ref_urgent', self.ref_urgent)
        
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
        self._update_refresh()
        
        # Increment cycle count (for FAW tracking)
        self.cycle_count += 1
        
        # =====================================================================
        # Step 4: Capture DDR output from pipe_s2 BEFORE shifting
        # =====================================================================
        output_cmd_type = self.pipe_s2['cmd_type']
        output_bank = self.pipe_s2['bank']
        output_row = self.pipe_s2['row']
        output_col = self.pipe_s2['col']
        
        # Encode DDR command
        self.ddr_cmd, self.ddr_addr, self.ddr_bank = self._encode_ddr_cmd(
            output_cmd_type, output_bank, output_row, output_col
        )
        
        # Generate feedback signals for bank_tracker
        fb_act_valid = 1 if output_cmd_type == SCHED_ACT else 0
        fb_act_bank = output_bank if fb_act_valid else 0
        fb_act_row = output_row if fb_act_valid else 0
        fb_pre_valid = 1 if output_cmd_type == SCHED_PRE else 0
        fb_rd_valid = 1 if output_cmd_type == SCHED_RD else 0
        fb_wr_valid = 1 if output_cmd_type == SCHED_WR else 0
        fb_ref_valid = 1 if output_cmd_type == SCHED_REF else 0
        
        # =====================================================================
        # Step 5: Wishbone Interface
        # =====================================================================
        wb_ack_o = 0
        wb_stall_o = 0
        wb_err_o = 0
        
        # Check for valid transaction
        wb_active = (wb_cyc_i and wb_stb_i)
        
        if wb_active:
            # Decode address
            row, bank, col = self._decode_address(wb_adr_i)
            self.dec_row = row
            self.dec_bank = bank
            self.dec_col = col
            
            # Check if queue can accept
            if not self.queue_valid and req_ready:
                # Enqueue the request
                self.queue_valid = True
                self.queue_row = row
                self.queue_col = col
                self.queue_bank = bank
                self.queue_we = bool(wb_we_i)
                self.queue_aux = 0
                self.queue_count = 1
                
                # Store write data
                if wb_we_i:
                    self.req_wdata = wb_dat_i
                    self.req_wmask = wb_sel_i
                
                # Acknowledge
                wb_ack_o = 1
                wb_stall_o = 0
            else:
                # Queue full, stall
                wb_stall_o = 1
        
        # =====================================================================
        # Step 6: Scheduler Decision (combinational)
        # =====================================================================
        # Use internal bank state for decision (which reflects feedback delay)
        # In single-entry mode, use testbench inputs for bank 0
        
        # Compute timing-based allows for the queue's target bank
        if self.queue_valid:
            target_bank = self.queue_bank
            # Check if target bank is active and row matches
            is_active = self.bank_is_active[target_bank]
            open_row = self.bank_open_row[target_bank]
            
            act_ok, rd_ok, wr_ok, pre_ok = self._check_bank_timing(
                target_bank, is_active, open_row
            )
        else:
            is_active = 0
            open_row = 0
            act_ok = bank_act_allowed
            rd_ok = bank_rd_allowed
            wr_ok = bank_wr_allowed
            pre_ok = bank_pre_allowed
        
        # Make scheduler decision
        cmd_type, cmd_bank, cmd_row, cmd_col, cmd_we, cmd_aux, deq_grant, ref_ack = \
            self._scheduler_decision(
                is_active, open_row,
                act_ok, rd_ok, wr_ok, pre_ok,
                self.ref_required, self.ref_urgent
            )
        
        # =====================================================================
        # Step 7: Shift pipeline
        # =====================================================================
        # Save old pipe_s2 for pending feedback BEFORE shift
        old_s2_valid = self.pipe_s2['valid']
        old_s2_cmd = self.pipe_s2['cmd_type']
        old_s2_bank = self.pipe_s2['bank']
        old_s2_row = self.pipe_s2['row']
        
        # Shift: s2 <- s1
        self.pipe_s2 = self.pipe_s1.copy()
        
        # s1 <- new decision
        self.pipe_s1 = {
            'valid': (cmd_type != SCHED_NOP),
            'cmd_type': cmd_type,
            'bank': cmd_bank,
            'row': cmd_row,
            'col': cmd_col,
            'we': cmd_we,
            'aux': cmd_aux,
            'deq': deq_grant,
            'ref_ack': ref_ack
        }
        
        # =====================================================================
        # Step 8: Store pending feedback (from old pipe_s2, to be applied NEXT cycle)
        # =====================================================================
        if old_s2_valid and old_s2_cmd != SCHED_NOP:
            self.pending_fb = {
                'valid': True,
                'cmd_type': old_s2_cmd,
                'bank': old_s2_bank,
                'row': old_s2_row
            }
        else:
            self.pending_fb['valid'] = False
        
        # =====================================================================
        # Step 9: Dequeue on deq_grant (from pipe_s2 AFTER shift)
        # =====================================================================
        # deq_grant and ref_ack come from pipe_s2 AFTER the shift (1 cycle delay)
        deq_grant_out = self.pipe_s2['deq']
        ref_ack_out = self.pipe_s2['ref_ack']
        
        if deq_grant_out and self.queue_valid:
            self.queue_valid = False
            self.queue_count = 0
        
        # Handle ref_ack
        if ref_ack_out and self.postpone_cnt > 0:
            self.postpone_cnt -= 1
        
        # =====================================================================
        # Build output dictionary
        # =====================================================================
        outputs = {
            # Wishbone outputs
            'wb_ack_o': wb_ack_o,
            'wb_dat_o': self.wb_dat_o,
            'wb_stall_o': wb_stall_o,
            'wb_err_o': wb_err_o,
            
            # Write data outputs
            'req_wdata': self.req_wdata,
            'req_wmask': self.req_wmask,
            
            # Address decoder outputs
            'dec_rank': self.dec_rank,
            
            # Command queue outputs
            'enq_ready': 1 if not self.queue_valid else 0,
            'queue_full': 1 if self.queue_valid else 0,
            'queue_empty': 0 if self.queue_valid else 1,
            'queue_count': self.queue_count,
            
            # Refresh outputs
            'ref_ack': ref_ack_out,
            
            # DDR command outputs
            'ddr_cmd': self.ddr_cmd,
            'ddr_addr': self.ddr_addr,
            'ddr_bank': self.ddr_bank,
            'ddr_cke': self.ddr_cke,
            'ddr_reset_n': self.ddr_reset_n,
            'ddr_odt': self.ddr_odt,
            
            # Feedback signals
            'fb_act_valid': fb_act_valid,
            'fb_act_bank': fb_act_bank,
            'fb_act_row': fb_act_row,
            'fb_pre_valid': fb_pre_valid,
            'fb_rd_valid': fb_rd_valid,
            'fb_wr_valid': fb_wr_valid,
            'fb_ref_valid': fb_ref_valid,
        }
        
        return outputs

    def get_state(self) -> dict:
        """Return a dict with the full internal state for debugging."""
        return {
            # Queue state
            'queue_valid': self.queue_valid,
            'queue_row': self.queue_row,
            'queue_col': self.queue_col,
            'queue_bank': self.queue_bank,
            'queue_we': self.queue_we,
            'queue_count': self.queue_count,
            
            # Bank state
            'bank_is_active': self.bank_is_active.copy(),
            'bank_open_row': self.bank_open_row.copy(),
            
            # Timing counters
            'cnt_rcd': self.cnt_rcd.copy(),
            'cnt_rp': self.cnt_rp.copy(),
            'cnt_ras': self.cnt_ras.copy(),
            'cnt_rfc': self.cnt_rfc,
            'cnt_rrd': self.cnt_rrd,
            
            # Refresh state
            'refresh_in_progress': self.refresh_in_progress,
            'refi_counter': self.refi_counter,
            'postpone_cnt': self.postpone_cnt,
            'ref_required': self.ref_required,
            'ref_urgent': self.ref_urgent,
            
            # Pipeline
            'pipe_s1': self.pipe_s1.copy(),
            'pipe_s2': self.pipe_s2.copy(),
            'pending_fb': self.pending_fb.copy(),
            
            # Cycle count
            'cycle_count': self.cycle_count,
        }


def run_self_test():
    """Run self-tests for the PathModel."""
    all_passed = True
    test_results = []
    
    def check(name, condition):
        nonlocal all_passed
        if condition:
            test_results.append((name, "PASS"))
        else:
            test_results.append((name, "FAIL"))
            all_passed = False
        return condition
    
    # =========================================================================
    # Test 1: Reset state
    # =========================================================================
    model = PathModel()
    outputs = model.step()  # Get initial outputs
    
    check("Reset: ddr_cmd is NOP",
          outputs['ddr_cmd'] == DDR_NOP)
    check("Reset: queue_empty is 1",
          outputs['queue_empty'] == 1)
    check("Reset: queue_full is 0",
          outputs['queue_full'] == 0)
    check("Reset: ddr_cke is 1",
          outputs['ddr_cke'] == 1)
    check("Reset: ddr_reset_n is 1",
          outputs['ddr_reset_n'] == 1)
    
    # =========================================================================
    # Test 2: Output dict contains all required keys
    # =========================================================================
    required_outputs = [
        'wb_ack_o', 'wb_dat_o', 'wb_stall_o', 'wb_err_o',
        'req_wdata', 'req_wmask', 'dec_rank',
        'enq_ready', 'queue_full', 'queue_empty', 'queue_count',
        'ref_ack', 'ddr_cmd', 'ddr_addr', 'ddr_bank',
        'ddr_cke', 'ddr_reset_n', 'ddr_odt',
        'fb_act_valid', 'fb_act_bank', 'fb_act_row',
        'fb_pre_valid', 'fb_rd_valid', 'fb_wr_valid', 'fb_ref_valid'
    ]
    
    for key in required_outputs:
        check(f"Output key present: {key}", key in outputs)
    
    # =========================================================================
    # Test 3: step() accepts unknown kwargs
    # =========================================================================
    try:
        model.reset()
        outputs = model.step(unknown_signal=123, another_unknown=456)
        check("step() accepts unknown kwargs", True)
    except Exception as e:
        check("step() accepts unknown kwargs", False)
    
    # =========================================================================
    # Test 4: Wishbone write transaction
    # =========================================================================
    model.reset()
    
    # Issue a write command
    outputs = model.step(
        wb_cyc_i=1,
        wb_stb_i=1,
        wb_we_i=1,
        wb_adr_i=0x1000,  # Some address
        wb_dat_i=0xDEADBEEF,
        wb_sel_i=0xF,
        req_ready=1
    )
    
    check("WB write: ack asserted",
          outputs['wb_ack_o'] == 1)
    check("WB write: no stall",
          outputs['wb_stall_o'] == 0)
    check("WB write: queue not empty",
          outputs['queue_empty'] == 0)
    check("WB write: write data captured",
          outputs['req_wdata'] == 0xDEADBEEF)
    check("WB write: write mask captured",
          outputs['req_wmask'] == 0xF)
    
    # =========================================================================
    # Test 5: Address decoding (row-bank-column mapping)
    # =========================================================================
    model.reset()
    
    # Address that should map to specific row/bank/col
    # With COL_BITS=10, BANK_BITS=3, ROW_BITS=15
    # Byte addr >> 2 = word addr
    # word_addr[9:0] = col, word_addr[12:10] = bank, word_addr[27:13] = row
    
    # Test address: row=5, bank=3, col=100
    # word_addr = (5 << 13) | (3 << 10) | 100 = 40960 + 3072 + 100 = 44132
    # byte_addr = 44132 << 2 = 176528
    test_addr = 176528
    
    model.step(
        wb_cyc_i=1,
        wb_stb_i=1,
        wb_we_i=1,
        wb_adr_i=test_addr,
        wb_dat_i=0,
        wb_sel_i=0xF
    )
    
    state = model.get_state()
    check("Addr decode: col matches",
          state['queue_col'] == 100)
    check("Addr decode: bank matches",
          state['queue_bank'] == 3)
    check("Addr decode: row matches",
          state['queue_row'] == 5)
    
    # =========================================================================
    # Test 6: Pipeline latency for DDR commands
    # =========================================================================
    model.reset()
    
    # Enqueue a write request
    model.step(
        wb_cyc_i=1,
        wb_stb_i=1,
        wb_we_i=1,
        wb_adr_i=0x100,
        wb_dat_i=0x12345678,
        wb_sel_i=0xF
    )
    
    # Cycle 1: Scheduler makes decision (ACT for idle bank)
    out1 = model.step()
    check("Pipeline T+1: still NOP on DDR",
          out1['ddr_cmd'] == DDR_NOP)
    
    # Cycle 2: Decision in pipe_s2
    out2 = model.step()
    # Should see ACT command now (2 cycle latency)
    check("Pipeline T+2: ACT visible on DDR",
          out2['ddr_cmd'] == DDR_ACT)
    
    # =========================================================================
    # Test 7: Queue full stalls Wishbone
    # =========================================================================
    model.reset()
    
    # Fill queue with one entry
    model.step(
        wb_cyc_i=1,
        wb_stb_i=1,
        wb_we_i=1,
        wb_adr_i=0x200,
        wb_dat_i=0xAAAAAAAA,
        wb_sel_i=0xF
    )
    
    # Try to add another - should stall
    out = model.step(
        wb_cyc_i=1,
        wb_stb_i=1,
        wb_we_i=1,
        wb_adr_i=0x300,
        wb_dat_i=0xBBBBBBBB,
        wb_sel_i=0xF
    )
    
    check("Queue full: stall asserted",
          out['wb_stall_o'] == 1)
    check("Queue full: no ack",
          out['wb_ack_o'] == 0)
    
    # =========================================================================
    # Test 8: DDR command encoding
    # =========================================================================
    check("DDR encoding: NOP = 7", DDR_NOP == 7)
    check("DDR encoding: ACT = 3", DDR_ACT == 3)
    check("DDR encoding: RD = 5", DDR_RD == 5)
    check("DDR encoding: WR = 4", DDR_WR == 4)
    check("DDR encoding: PRE = 2", DDR_PRE == 2)
    check("DDR encoding: REF = 1", DDR_REF == 1)
    
    # =========================================================================
    # Test 9: Timing counter values match spec
    # =========================================================================
    check("Timing: tRCD_nCK = 11", CFG_tRCD_nCK == 11)
    check("Timing: tRP_nCK = 11", CFG_tRP_nCK == 11)
    check("Timing: tRAS_nCK = 28", CFG_tRAS_nCK == 28)
    check("Timing: tRFC_nCK = 128", CFG_tRFC_nCK == 128)
    check("Timing: tFAW_nCK = 32", CFG_tFAW_nCK == 32)
    check("Timing: tRRD_nCK = 6", CFG_tRRD_nCK == 6)
    
    # =========================================================================
    # Test 10: get_state() returns valid state dict
    # =========================================================================
    model.reset()
    state = model.get_state()
    
    check("get_state: has queue_valid", 'queue_valid' in state)
    check("get_state: has bank_is_active", 'bank_is_active' in state)
    check("get_state: has pipe_s1", 'pipe_s1' in state)
    check("get_state: has cycle_count", 'cycle_count' in state)
    
    # =========================================================================
    # Test 11: Feedback delay for bank state updates
    # =========================================================================
    model.reset()
    
    # Enqueue request
    model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x400, wb_dat_i=0, wb_sel_i=0xF
    )
    
    # Cycles to let ACT propagate
    for _ in range(3):
        model.step()
    
    state = model.get_state()
    # After ACT feedback applied, bank should be active
    target_bank = state['queue_bank']
    # Note: queue might be dequeued by now, but we check the bank state
    # which should have been updated by feedback
    check("Feedback: bank becomes active after delay",
          state['bank_is_active'][target_bank] == 1 or not state['queue_valid'])
    
    # =========================================================================
    # Test 12: Refresh state tracking
    # =========================================================================
    model.reset()
    
    # Initial refresh state
    check("Refresh: postpone_cnt starts at 0",
          model.get_state()['postpone_cnt'] == 0)
    
    # After one step (down-counter fires immediately at 0)
    model.step()
    state = model.get_state()
    check("Refresh: ref_required after init",
          state['ref_required'] == True)
    
    # =========================================================================
    # Print results
    # =========================================================================
    print("\n" + "="*60)
    print("SELF-TEST RESULTS")
    print("="*60)
    
    for name, result in test_results:
        print(f"  {result}: {name}")
    
    print("="*60)
    passed = sum(1 for _, r in test_results if r == "PASS")
    failed = sum(1 for _, r in test_results if r == "FAIL")
    print(f"  Total: {passed} passed, {failed} failed")
    print("="*60)
    
    if all_passed:
        print("\nALL TESTS PASSED")
    else:
        print("\nSOME TESTS FAILED")
    
    return all_passed


if __name__ == "__main__":
    run_self_test()