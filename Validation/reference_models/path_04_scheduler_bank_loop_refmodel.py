#!/usr/bin/env python3
"""
Reference model for DDR3 Memory Controller Path:
Scheduler → cmd_gen → Bank Tracker → Scheduler Feedback Loop

Models the integration path: scheduler -> cmd_gen -> bank_tracker
with proper pipeline latency and feedback timing.
"""

import json
import os

# === DDR3 Command Encoding (from RTL cmd_gen.sv) ===
DDR_NOP  = 7   # 4'b0111 - CS#/RAS#/CAS#/WE# = 0111
DDR_ACT  = 3   # 4'b0011
DDR_RD   = 5   # 4'b0101
DDR_WR   = 4   # 4'b0100
DDR_PRE  = 2   # 4'b0010
DDR_REF  = 1   # 4'b0001
DDR_MRS  = 0   # 4'b0000
DDR_ZQCL = 6   # 4'b0110
DDR_DESL = 15  # 4'b1111

# === Internal Scheduler Command Types ===
SCHED_NOP = 0
SCHED_ACT = 1
SCHED_RD  = 2
SCHED_WR  = 3
SCHED_PRE = 4
SCHED_REF = 5

# === Constants from spec ===
NUM_BANKS = 8
ROW_BITS = 15
COL_BITS = 10
BANK_BITS = 3
AUX_BITS = 4

# Default timing values (in controller cycles, from spec $derived_cycles)
DEFAULT_tRCD_nCK = 11
DEFAULT_tRP_nCK = 11
DEFAULT_tRAS_nCK = 28
DEFAULT_tRC_nCK = 39
DEFAULT_tRRD_nCK = 6
DEFAULT_tFAW_nCK = 32
DEFAULT_tWTR_nCK = 6
DEFAULT_tWR_nCK = 12
DEFAULT_tRTP_nCK = 6
DEFAULT_tCCD_nCK = 4
DEFAULT_tRFC_nCK = 128


def sched_type_to_ddr_cmd(sched_type):
    """Convert scheduler command type to DDR command encoding."""
    mapping = {
        SCHED_NOP: DDR_NOP,
        SCHED_ACT: DDR_ACT,
        SCHED_RD:  DDR_RD,
        SCHED_WR:  DDR_WR,
        SCHED_PRE: DDR_PRE,
        SCHED_REF: DDR_REF,
    }
    return mapping.get(sched_type, DDR_NOP)


class PathModel:
    """
    Reference model for Scheduler -> cmd_gen -> Bank Tracker feedback loop.
    
    Pipeline structure:
      Cycle N:   Scheduler makes combinational decision
      Cycle N+1: cmd_gen registers output (pipe_s1 -> pipe_s2)
      Cycle N+2: DDR pins visible, feedback captured by bank_tracker
      Cycle N+3: Bank state updated, visible to scheduler
    """
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        """Reset all internal state to power-on defaults."""
        # === Bank Tracker State (per-bank) ===
        self.bank_is_active = [0] * NUM_BANKS
        self.bank_open_row = [0] * NUM_BANKS
        
        # Per-bank timing counters (decrement each cycle, 0 = timing satisfied)
        self.cnt_rcd = [0] * NUM_BANKS   # Counts down after ACT
        self.cnt_ras = [0] * NUM_BANKS   # Minimum active time after ACT
        self.cnt_rp = [0] * NUM_BANKS    # Counts down after PRE
        self.cnt_rc = [0] * NUM_BANKS    # Row cycle time after ACT
        self.cnt_wtp = [0] * NUM_BANKS   # Write-to-precharge (tWR + tWTR)
        self.cnt_rtp = [0] * NUM_BANKS   # Read-to-precharge
        self.cnt_ccd = [0] * NUM_BANKS   # CAS-to-CAS delay
        
        # Global timing counters
        self.cnt_rrd = 0    # ACT-to-ACT different bank delay
        self.cnt_rfc = 0    # Refresh cycle time
        
        # FAW tracking (rolling window of last 4 ACT timestamps)
        self.faw_window = []  # List of cycle counts when ACTs occurred
        
        # Refresh state
        self.refresh_in_progress = False
        
        # === Pipeline Registers ===
        # pipe_s1: scheduler output register (1 cycle delay)
        # pipe_s2: cmd_gen output register (2 cycle delay for DDR, 1 for deq/ref_ack)
        self.pipe_s1 = {'valid': 0, 'type': SCHED_NOP, 'bank': 0, 'row': 0, 'col': 0, 'we': 0, 'aux': 0}
        self.pipe_s2 = {'valid': 0, 'type': SCHED_NOP, 'bank': 0, 'row': 0, 'col': 0, 'we': 0, 'aux': 0}
        
        # Pending feedback (applied at START of next cycle)
        self.pending_fb_valid = 0
        self.pending_fb_type = SCHED_NOP
        self.pending_fb_bank = 0
        self.pending_fb_row = 0
        
        # === Configuration Registers (loaded from inputs) ===
        self.cfg_tRCD_nCK = DEFAULT_tRCD_nCK
        self.cfg_tRP_nCK = DEFAULT_tRP_nCK
        self.cfg_tRAS_nCK = DEFAULT_tRAS_nCK
        self.cfg_tRC_nCK = DEFAULT_tRC_nCK
        self.cfg_tRRD_nCK = DEFAULT_tRRD_nCK
        self.cfg_tFAW_nCK = DEFAULT_tFAW_nCK
        self.cfg_tWTR_nCK = DEFAULT_tWTR_nCK
        self.cfg_tWR_nCK = DEFAULT_tWR_nCK
        self.cfg_tRTP_nCK = DEFAULT_tRTP_nCK
        self.cfg_tCCD_nCK = DEFAULT_tCCD_nCK
        self.cfg_tRFC_nCK = DEFAULT_tRFC_nCK
        
        # Cycle counter for FAW tracking
        self.cycle_count = 0
        
        # Initialization state (assume init_done=1 for this model)
        self.init_done = 1
    
    def _apply_pending_feedback(self):
        """Apply pending feedback from previous cycle to bank state."""
        if not self.pending_fb_valid:
            return
        
        cmd_type = self.pending_fb_type
        bank = self.pending_fb_bank
        row = self.pending_fb_row
        
        if cmd_type == SCHED_ACT:
            # Activate command: open row in bank
            self.bank_is_active[bank] = 1
            self.bank_open_row[bank] = row
            # Start timing counters
            self.cnt_rcd[bank] = self.cfg_tRCD_nCK
            self.cnt_ras[bank] = self.cfg_tRAS_nCK
            self.cnt_rc[bank] = self.cfg_tRC_nCK
            # Global RRD counter
            self.cnt_rrd = self.cfg_tRRD_nCK
            # Add to FAW window
            self.faw_window.append(self.cycle_count)
            
        elif cmd_type == SCHED_RD:
            # Read command: start read-to-precharge timer
            self.cnt_rtp[bank] = self.cfg_tRTP_nCK
            self.cnt_ccd[bank] = self.cfg_tCCD_nCK
            
        elif cmd_type == SCHED_WR:
            # Write command: start write-to-precharge timer
            self.cnt_wtp[bank] = self.cfg_tWR_nCK + self.cfg_tWTR_nCK
            self.cnt_ccd[bank] = self.cfg_tCCD_nCK
            
        elif cmd_type == SCHED_PRE:
            # Precharge command: close bank
            self.bank_is_active[bank] = 0
            self.bank_open_row[bank] = 0
            # Start RP counter
            self.cnt_rp[bank] = self.cfg_tRP_nCK
            
        elif cmd_type == SCHED_REF:
            # Refresh command: all banks become idle, start RFC
            for b in range(NUM_BANKS):
                self.bank_is_active[b] = 0
                self.bank_open_row[b] = 0
            self.cnt_rfc = self.cfg_tRFC_nCK
            # Clear FAW window - all prior ACTs invalidated by refresh
            self.faw_window = []
            # Clear RRD - no prior ACT relevant
            self.cnt_rrd = 0
            self.refresh_in_progress = True
        
        # Clear pending feedback
        self.pending_fb_valid = 0
        self.pending_fb_type = SCHED_NOP
    
    def _decrement_counters(self):
        """Decrement all timing counters by 1 (each call = 1 controller cycle)."""
        # Per-bank counters
        for b in range(NUM_BANKS):
            if self.cnt_rcd[b] > 0:
                self.cnt_rcd[b] -= 1
            if self.cnt_ras[b] > 0:
                self.cnt_ras[b] -= 1
            if self.cnt_rp[b] > 0:
                self.cnt_rp[b] -= 1
            if self.cnt_rc[b] > 0:
                self.cnt_rc[b] -= 1
            if self.cnt_wtp[b] > 0:
                self.cnt_wtp[b] -= 1
            if self.cnt_rtp[b] > 0:
                self.cnt_rtp[b] -= 1
            if self.cnt_ccd[b] > 0:
                self.cnt_ccd[b] -= 1
        
        # Global counters
        if self.cnt_rrd > 0:
            self.cnt_rrd -= 1
        if self.cnt_rfc > 0:
            self.cnt_rfc -= 1
        
        # Check if refresh complete
        if self.cnt_rfc == 0 and self.refresh_in_progress:
            self.refresh_in_progress = False
        
        # Clean up FAW window (remove entries older than tFAW)
        cutoff = self.cycle_count - self.cfg_tFAW_nCK
        self.faw_window = [t for t in self.faw_window if t > cutoff]
    
    def _bank_act_allowed(self, bank):
        """Check if ACT is allowed for this bank."""
        # Bank must be idle
        if self.bank_is_active[bank]:
            return False
        # RP (precharge recovery) must be complete
        if self.cnt_rp[bank] > 0:
            return False
        # RC (row cycle) must be complete
        if self.cnt_rc[bank] > 0:
            return False
        # RRD (ACT-to-ACT different bank) must be complete
        if self.cnt_rrd > 0:
            return False
        # RFC must be complete
        if self.cnt_rfc > 0:
            return False
        # FAW constraint: max 4 ACTs in tFAW window
        if len(self.faw_window) >= 4:
            return False
        return True
    
    def _bank_rd_allowed(self, bank):
        """Check if READ is allowed for this bank."""
        # Bank must be active
        if not self.bank_is_active[bank]:
            return False
        # RCD (row-to-column delay) must be complete
        if self.cnt_rcd[bank] > 0:
            return False
        # CCD (CAS-to-CAS) must be complete
        if self.cnt_ccd[bank] > 0:
            return False
        # RFC must be complete
        if self.cnt_rfc > 0:
            return False
        return True
    
    def _bank_wr_allowed(self, bank):
        """Check if WRITE is allowed for this bank."""
        # Bank must be active
        if not self.bank_is_active[bank]:
            return False
        # RCD must be complete
        if self.cnt_rcd[bank] > 0:
            return False
        # CCD must be complete
        if self.cnt_ccd[bank] > 0:
            return False
        # RFC must be complete
        if self.cnt_rfc > 0:
            return False
        return True
    
    def _bank_pre_allowed(self, bank):
        """Check if PRECHARGE is allowed for this bank."""
        # Bank must be active to precharge
        if not self.bank_is_active[bank]:
            return False
        # RAS (minimum active time) must be met
        if self.cnt_ras[bank] > 0:
            return False
        # WTP (write-to-precharge) must be met
        if self.cnt_wtp[bank] > 0:
            return False
        # RTP (read-to-precharge) must be met
        if self.cnt_rtp[bank] > 0:
            return False
        # RFC must be complete
        if self.cnt_rfc > 0:
            return False
        return True
    
    def _all_banks_idle(self):
        """Check if all banks are idle (required for refresh)."""
        return all(not active for active in self.bank_is_active)
    
    def _all_banks_precharged(self):
        """Check if all banks are precharged and ready for refresh."""
        if not self._all_banks_idle():
            return False
        # All RP counters must be done
        if any(self.cnt_rp[b] > 0 for b in range(NUM_BANKS)):
            return False
        # RFC must be done
        if self.cnt_rfc > 0:
            return False
        return True
    
    def _scheduler_decision(self, q_valid, q_row, q_col, q_bank, q_we, q_aux,
                            ref_required, ref_urgent):
        """
        Make scheduling decision based on current bank state.
        Returns: (cmd_type, cmd_bank, cmd_row, cmd_col, cmd_we, cmd_aux, deq_grant, ref_ack)
        
        Priority order (from RTL):
          1. ref_urgent -> REF (preempts everything, if banks idle)
          2. Row-hit CAS (q_valid and row match and timing ok)
          3. Row-miss handling (PRE if wrong row active, ACT if idle)
          4. ref_required (normal, non-urgent refresh)
          5. NOP
        """
        # During refresh in progress, no commands allowed
        if self.refresh_in_progress:
            return (SCHED_NOP, 0, 0, 0, 0, 0, 0, 0)
        
        # Priority 1: Urgent refresh
        if ref_urgent and self._all_banks_precharged():
            return (SCHED_REF, 0, 0, 0, 0, 0, 0, 1)
        
        # Priority 2: Row-hit CAS
        if q_valid:
            bank = q_bank
            row = q_row
            col = q_col
            we = q_we
            aux = q_aux
            
            if self.bank_is_active[bank] and self.bank_open_row[bank] == row:
                # Row hit - try CAS
                if we and self._bank_wr_allowed(bank):
                    return (SCHED_WR, bank, row, col, we, aux, 1, 0)
                elif not we and self._bank_rd_allowed(bank):
                    return (SCHED_RD, bank, row, col, we, aux, 1, 0)
        
        # Priority 3: Row-miss handling
        if q_valid:
            bank = q_bank
            row = q_row
            col = q_col
            we = q_we
            aux = q_aux
            
            if self.bank_is_active[bank]:
                # Bank active with wrong row - need to precharge first
                if self.bank_open_row[bank] != row:
                    if self._bank_pre_allowed(bank):
                        return (SCHED_PRE, bank, row, col, we, aux, 0, 0)
            else:
                # Bank idle - try to activate
                if self._bank_act_allowed(bank):
                    return (SCHED_ACT, bank, row, col, we, aux, 0, 0)
        
        # Priority 4: Normal refresh
        if ref_required and self._all_banks_precharged():
            return (SCHED_REF, 0, 0, 0, 0, 0, 0, 1)
        
        # Priority 5: NOP
        return (SCHED_NOP, 0, 0, 0, 0, 0, 0, 0)
    
    def step(self, **inputs):
        """
        Advance the model by one clock cycle.
        
        Input signals:
          q_valid_0, q_row_0, q_col_0, q_bank_0, q_we_0, q_aux_0
          ref_required, ref_urgent
          cfg_tRCD_nCK, cfg_tRP_nCK, cfg_tRAS_nCK, cfg_tRC_nCK, cfg_tRRD_nCK
          cfg_tFAW_nCK, cfg_tWTR_nCK, cfg_tWR_nCK, cfg_tRTP_nCK, cfg_tCCD_nCK, cfg_tRFC_nCK
        
        Output signals:
          ref_ack, deq_grant, deq_idx
          ddr_cmd, ddr_addr, ddr_bank, ddr_cke, ddr_reset_n, ddr_odt
        """
        # Extract inputs (with defaults)
        q_valid_0 = inputs.get('q_valid_0', 0)
        q_row_0 = inputs.get('q_row_0', 0)
        q_col_0 = inputs.get('q_col_0', 0)
        q_bank_0 = inputs.get('q_bank_0', 0)
        q_we_0 = inputs.get('q_we_0', 0)
        q_aux_0 = inputs.get('q_aux_0', 0)
        ref_required = inputs.get('ref_required', 0)
        ref_urgent = inputs.get('ref_urgent', 0)
        
        # Update config if provided
        if 'cfg_tRCD_nCK' in inputs:
            self.cfg_tRCD_nCK = inputs['cfg_tRCD_nCK']
        if 'cfg_tRP_nCK' in inputs:
            self.cfg_tRP_nCK = inputs['cfg_tRP_nCK']
        if 'cfg_tRAS_nCK' in inputs:
            self.cfg_tRAS_nCK = inputs['cfg_tRAS_nCK']
        if 'cfg_tRC_nCK' in inputs:
            self.cfg_tRC_nCK = inputs['cfg_tRC_nCK']
        if 'cfg_tRRD_nCK' in inputs:
            self.cfg_tRRD_nCK = inputs['cfg_tRRD_nCK']
        if 'cfg_tFAW_nCK' in inputs:
            self.cfg_tFAW_nCK = inputs['cfg_tFAW_nCK']
        if 'cfg_tWTR_nCK' in inputs:
            self.cfg_tWTR_nCK = inputs['cfg_tWTR_nCK']
        if 'cfg_tWR_nCK' in inputs:
            self.cfg_tWR_nCK = inputs['cfg_tWR_nCK']
        if 'cfg_tRTP_nCK' in inputs:
            self.cfg_tRTP_nCK = inputs['cfg_tRTP_nCK']
        if 'cfg_tCCD_nCK' in inputs:
            self.cfg_tCCD_nCK = inputs['cfg_tCCD_nCK']
        if 'cfg_tRFC_nCK' in inputs:
            self.cfg_tRFC_nCK = inputs['cfg_tRFC_nCK']
        
        # === Step 1: Apply pending feedback from PREVIOUS cycle ===
        self._apply_pending_feedback()
        
        # === Step 2: Decrement timing counters ===
        self._decrement_counters()
        
        # === Step 3: Capture DDR output from pipe_s2 BEFORE shifting ===
        # This is the 2-cycle delayed command that appears on DDR pins
        output_ddr_cmd = sched_type_to_ddr_cmd(self.pipe_s2['type']) if self.pipe_s2['valid'] else DDR_NOP
        output_ddr_bank = self.pipe_s2['bank']
        
        # Address encoding depends on command type
        if self.pipe_s2['type'] == SCHED_ACT:
            output_ddr_addr = self.pipe_s2['row']
        elif self.pipe_s2['type'] in (SCHED_RD, SCHED_WR):
            output_ddr_addr = self.pipe_s2['col']
        elif self.pipe_s2['type'] == SCHED_PRE:
            output_ddr_addr = 0  # A10=0 for single bank precharge
        else:
            output_ddr_addr = 0
        
        # === Step 4: Store pipe_s2 as pending feedback (applied NEXT cycle) ===
        if self.pipe_s2['valid']:
            self.pending_fb_valid = 1
            self.pending_fb_type = self.pipe_s2['type']
            self.pending_fb_bank = self.pipe_s2['bank']
            self.pending_fb_row = self.pipe_s2['row']
        
        # === Step 5: Make new scheduler decision ===
        (cmd_type, cmd_bank, cmd_row, cmd_col, cmd_we, cmd_aux, 
         deq_grant_new, ref_ack_new) = self._scheduler_decision(
            q_valid_0, q_row_0, q_col_0, q_bank_0, q_we_0, q_aux_0,
            ref_required, ref_urgent
        )
        
        # Create new pipeline entry
        new_s1 = {
            'valid': 1 if cmd_type != SCHED_NOP else 0,
            'type': cmd_type,
            'bank': cmd_bank,
            'row': cmd_row,
            'col': cmd_col,
            'we': cmd_we,
            'aux': cmd_aux,
            'deq_grant': deq_grant_new,
            'ref_ack': ref_ack_new,
        }
        
        # === Step 6: Shift pipeline ===
        # pipe_s2 = pipe_s1 (this becomes next cycle's DDR output)
        # pipe_s1 = new decision
        old_s1 = self.pipe_s1.copy()
        self.pipe_s2 = old_s1
        self.pipe_s1 = new_s1
        
        # === Step 7: Get deq_grant and ref_ack from pipe_s2 AFTER shift ===
        # These are 1-cycle delayed (scheduler output register)
        output_deq_grant = self.pipe_s2.get('deq_grant', 0)
        output_ref_ack = self.pipe_s2.get('ref_ack', 0)
        
        # Increment cycle counter
        self.cycle_count += 1
        
        # Build output dict with ALL required signals
        outputs = {
            'ref_ack': output_ref_ack,
            'deq_grant': output_deq_grant,
            'deq_idx': 0,  # Always 0 in single-entry mode
            'ddr_cmd': output_ddr_cmd,
            'ddr_addr': output_ddr_addr,
            'ddr_bank': output_ddr_bank,
            'ddr_cke': 1,     # CKE always high during normal operation
            'ddr_reset_n': 1, # Reset deasserted during normal operation
            'ddr_odt': 0,     # ODT control (simplified)
        }
        
        return outputs
    
    def get_state(self) -> dict:
        """Return full internal state for debugging."""
        return {
            'cycle_count': self.cycle_count,
            'bank_is_active': self.bank_is_active.copy(),
            'bank_open_row': self.bank_open_row.copy(),
            'cnt_rcd': self.cnt_rcd.copy(),
            'cnt_ras': self.cnt_ras.copy(),
            'cnt_rp': self.cnt_rp.copy(),
            'cnt_rc': self.cnt_rc.copy(),
            'cnt_wtp': self.cnt_wtp.copy(),
            'cnt_rtp': self.cnt_rtp.copy(),
            'cnt_ccd': self.cnt_ccd.copy(),
            'cnt_rrd': self.cnt_rrd,
            'cnt_rfc': self.cnt_rfc,
            'faw_window': self.faw_window.copy(),
            'refresh_in_progress': self.refresh_in_progress,
            'pipe_s1': self.pipe_s1.copy(),
            'pipe_s2': self.pipe_s2.copy(),
            'pending_fb_valid': self.pending_fb_valid,
            'pending_fb_type': self.pending_fb_type,
            'pending_fb_bank': self.pending_fb_bank,
            'pending_fb_row': self.pending_fb_row,
            'cfg_tRCD_nCK': self.cfg_tRCD_nCK,
            'cfg_tRP_nCK': self.cfg_tRP_nCK,
            'cfg_tRAS_nCK': self.cfg_tRAS_nCK,
        }


def run_self_test():
    """Run self-tests to verify model behavior."""
    test_results = []
    
    # Test 1: Reset state verification
    print("Test 1: Reset state verification")
    model = PathModel()
    model.reset()
    
    outputs = model.step()  # Step with no inputs
    
    # After reset, first step should produce NOPs
    passed = True
    if outputs['ddr_cmd'] != DDR_NOP:
        print(f"  FAIL: ddr_cmd should be NOP ({DDR_NOP}), got {outputs['ddr_cmd']}")
        passed = False
    if outputs['deq_grant'] != 0:
        print(f"  FAIL: deq_grant should be 0, got {outputs['deq_grant']}")
        passed = False
    if outputs['ref_ack'] != 0:
        print(f"  FAIL: ref_ack should be 0, got {outputs['ref_ack']}")
        passed = False
    if outputs['ddr_cke'] != 1:
        print(f"  FAIL: ddr_cke should be 1, got {outputs['ddr_cke']}")
        passed = False
    if outputs['ddr_reset_n'] != 1:
        print(f"  FAIL: ddr_reset_n should be 1, got {outputs['ddr_reset_n']}")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 2: Output dict contains all required keys
    print("Test 2: Output dict contains all required keys")
    required_keys = ['ref_ack', 'deq_grant', 'deq_idx', 'ddr_cmd', 'ddr_addr', 
                     'ddr_bank', 'ddr_cke', 'ddr_reset_n', 'ddr_odt']
    passed = True
    for key in required_keys:
        if key not in outputs:
            print(f"  FAIL: Missing key '{key}' in outputs")
            passed = False
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 3: step() ignores unknown kwargs
    print("Test 3: step() ignores unknown kwargs")
    try:
        model.reset()
        outputs = model.step(unknown_signal=42, another_unknown="test", q_valid_0=0)
        print("  PASS")
        test_results.append(True)
    except Exception as e:
        print(f"  FAIL: Exception raised: {e}")
        test_results.append(False)
    
    # Test 4: Basic ACT command generation (2-cycle pipeline delay)
    print("Test 4: ACT command with 2-cycle pipeline delay")
    model = PathModel()
    model.reset()
    
    # Cycle 0: Present request for bank 0, row 100
    outputs0 = model.step(q_valid_0=1, q_row_0=100, q_col_0=0, q_bank_0=0, q_we_0=0, q_aux_0=0)
    
    # Cycle 1: Pipeline delay - should still be NOP on DDR
    outputs1 = model.step(q_valid_0=1, q_row_0=100, q_col_0=0, q_bank_0=0, q_we_0=0, q_aux_0=0)
    
    # Cycle 2: ACT should appear on DDR pins
    outputs2 = model.step(q_valid_0=1, q_row_0=100, q_col_0=0, q_bank_0=0, q_we_0=0, q_aux_0=0)
    
    passed = True
    if outputs0['ddr_cmd'] != DDR_NOP:
        print(f"  FAIL: Cycle 0 ddr_cmd should be NOP, got {outputs0['ddr_cmd']}")
        passed = False
    if outputs1['ddr_cmd'] != DDR_NOP:
        print(f"  FAIL: Cycle 1 ddr_cmd should be NOP, got {outputs1['ddr_cmd']}")
        passed = False
    if outputs2['ddr_cmd'] != DDR_ACT:
        print(f"  FAIL: Cycle 2 ddr_cmd should be ACT ({DDR_ACT}), got {outputs2['ddr_cmd']}")
        passed = False
    if outputs2['ddr_bank'] != 0:
        print(f"  FAIL: Cycle 2 ddr_bank should be 0, got {outputs2['ddr_bank']}")
        passed = False
    if outputs2['ddr_addr'] != 100:
        print(f"  FAIL: Cycle 2 ddr_addr should be 100 (row), got {outputs2['ddr_addr']}")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 5: Scheduler re-issues ACT until bank state changes
    print("Test 5: Scheduler re-issues ACT until bank state changes")
    # Continue from test 4 - keep issuing the same request
    # Bank state won't update until cycle 3 after the ACT
    
    # Cycle 3: Another ACT (bank state not updated yet)
    outputs3 = model.step(q_valid_0=1, q_row_0=100, q_col_0=0, q_bank_0=0, q_we_0=0, q_aux_0=0)
    
    # Cycle 4: Another ACT
    outputs4 = model.step(q_valid_0=1, q_row_0=100, q_col_0=0, q_bank_0=0, q_we_0=0, q_aux_0=0)
    
    passed = True
    # Due to re-issue behavior, we should see multiple ACTs
    if outputs3['ddr_cmd'] != DDR_ACT:
        print(f"  FAIL: Cycle 3 should see ACT due to re-issue, got {outputs3['ddr_cmd']}")
        passed = False
    if outputs4['ddr_cmd'] != DDR_ACT:
        print(f"  FAIL: Cycle 4 should see ACT due to re-issue, got {outputs4['ddr_cmd']}")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 6: Refresh command with all banks idle
    print("Test 6: Refresh command generation")
    model = PathModel()
    model.reset()
    
    # Request refresh when all banks idle
    outputs0 = model.step(ref_required=1)
    outputs1 = model.step(ref_required=1)
    outputs2 = model.step(ref_required=0)
    
    passed = True
    # ref_ack should appear 1 cycle after scheduler decision (from pipe_s2)
    if outputs1['ref_ack'] != 1:
        print(f"  FAIL: ref_ack should be 1 in cycle 1, got {outputs1['ref_ack']}")
        passed = False
    # DDR REF command should appear in cycle 2 (2-cycle delay)
    if outputs2['ddr_cmd'] != DDR_REF:
        print(f"  FAIL: ddr_cmd should be REF ({DDR_REF}) in cycle 2, got {outputs2['ddr_cmd']}")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 7: deq_grant only on CAS commands
    print("Test 7: deq_grant only on CAS (RD/WR) commands")
    model = PathModel()
    model.reset()
    
    # Manually set bank 0 as active with row 100
    model.bank_is_active[0] = 1
    model.bank_open_row[0] = 100
    
    # Request read from bank 0, row 100 (row hit)
    outputs = []
    for _ in range(5):
        out = model.step(q_valid_0=1, q_row_0=100, q_col_0=50, q_bank_0=0, q_we_0=0, q_aux_0=0)
        outputs.append(out)
    
    passed = True
    # deq_grant should appear when RD command is scheduled (1-cycle delay)
    # Find cycles where deq_grant=1 and check ddr_cmd 1 cycle later
    deq_cycles = [i for i, o in enumerate(outputs) if o['deq_grant'] == 1]
    if len(deq_cycles) == 0:
        print(f"  FAIL: deq_grant never asserted")
        passed = False
    else:
        # deq_grant is 1-cycle delayed, ddr_cmd is 2-cycle delayed
        # So when deq_grant=1 at cycle i, ddr_cmd shows the corresponding RD at cycle i+1
        for dc in deq_cycles:
            if dc + 1 < len(outputs):
                if outputs[dc + 1]['ddr_cmd'] != DDR_RD:
                    print(f"  FAIL: deq_grant at cycle {dc} but ddr_cmd at {dc+1} is {outputs[dc+1]['ddr_cmd']}, expected RD ({DDR_RD})")
                    passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 8: Timing constraint - tRCD
    print("Test 8: tRCD timing constraint (RD not allowed until tRCD after ACT)")
    model = PathModel()
    model.reset()
    model.cfg_tRCD_nCK = 11  # 11 cycles
    
    # Manually activate bank 0 and set the counter
    model.bank_is_active[0] = 1
    model.bank_open_row[0] = 200
    model.cnt_rcd[0] = 5  # 5 cycles remaining
    
    # Try to read - should not be allowed
    rd_allowed = model._bank_rd_allowed(0)
    passed = True
    if rd_allowed:
        print(f"  FAIL: Read should not be allowed with cnt_rcd > 0")
        passed = False
    
    # Decrement counters 5 times
    for _ in range(5):
        model._decrement_counters()
    
    rd_allowed = model._bank_rd_allowed(0)
    if not rd_allowed:
        print(f"  FAIL: Read should be allowed after tRCD expires")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 9: Precharge before activate on row miss
    print("Test 9: PRE before ACT on row miss")
    model = PathModel()
    model.reset()
    
    # Use short timing values so ACT can appear within test window
    # After PRE, we need to wait for tRP before ACT
    # PRE appears on DDR at cycle 2, feedback at cycle 3, so cnt_rp starts at cycle 3
    # With tRP=2, cnt_rp expires after 2 more cycles (cycle 5)
    # ACT can be scheduled at cycle 5, appears on DDR at cycle 7
    model.cfg_tRP_nCK = 2    # Short precharge recovery time
    model.cfg_tRAS_nCK = 0   # No minimum active time (so PRE is immediate)
    model.cfg_tRC_nCK = 2    # Short row cycle time
    model.cfg_tRRD_nCK = 1   # Short ACT-to-ACT delay
    
    # Set bank 0 active with row 100, all timing counters clear
    model.bank_is_active[0] = 1
    model.bank_open_row[0] = 100
    
    # Request for same bank, different row (row miss)
    collected_cmds = []
    for _ in range(12):  # Run more cycles to allow tRP to expire
        out = model.step(q_valid_0=1, q_row_0=200, q_col_0=50, q_bank_0=0, q_we_0=0, q_aux_0=0)
        collected_cmds.append(out['ddr_cmd'])
    
    passed = True
    # Should see PRE before ACT
    try:
        pre_idx = collected_cmds.index(DDR_PRE)
        # After PRE, should see ACT eventually
        act_found = DDR_ACT in collected_cmds[pre_idx:]
        if not act_found:
            print(f"  FAIL: ACT should follow PRE. Commands: {collected_cmds}")
            passed = False
        else:
            # Verify ACT comes after PRE
            act_idx = collected_cmds.index(DDR_ACT, pre_idx)
            if act_idx <= pre_idx:
                print(f"  FAIL: ACT (idx {act_idx}) should come after PRE (idx {pre_idx})")
                passed = False
    except ValueError:
        print(f"  FAIL: PRE not found in commands: {collected_cmds}")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 10: Refresh blocks scheduling during tRFC
    print("Test 10: Refresh blocks scheduling during tRFC")
    model = PathModel()
    model.reset()
    model.cfg_tRFC_nCK = 10  # Short for testing
    
    # Issue refresh
    model.step(ref_required=1)
    model.step(ref_required=0)
    model.step()  # REF appears on DDR pins, feedback pending
    model.step()  # Feedback applied, refresh_in_progress = True
    
    # Now try to schedule a command - should be blocked
    model.bank_is_active[0] = 0  # Bank should be idle after refresh
    
    # Check if scheduling is blocked
    passed = True
    if not model.refresh_in_progress:
        print(f"  FAIL: refresh_in_progress should be True after REF feedback")
        passed = False
    
    # Check that ACT is not allowed during refresh
    if model._bank_act_allowed(0):
        print(f"  FAIL: ACT should not be allowed during refresh (cnt_rfc > 0)")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 11: FAW constraint
    print("Test 11: FAW constraint (max 4 ACTs in window)")
    model = PathModel()
    model.reset()
    model.cfg_tFAW_nCK = 32
    
    # Simulate 4 ACTs
    model.faw_window = [0, 1, 2, 3]  # 4 ACTs at cycles 0-3
    model.cycle_count = 4
    
    passed = True
    # With 4 ACTs in window, 5th should be blocked
    if model._bank_act_allowed(0):
        print(f"  FAIL: 5th ACT should be blocked by FAW (4 ACTs in window)")
        passed = False
    
    # Advance time past FAW window
    model.cycle_count = 40
    model._decrement_counters()  # This cleans up FAW window
    
    if not model._bank_act_allowed(0):
        print(f"  FAIL: ACT should be allowed after FAW window expires")
        passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Test 12: get_state returns valid dict
    print("Test 12: get_state() returns complete state dict")
    model = PathModel()
    model.reset()
    state = model.get_state()
    
    passed = True
    required_state_keys = ['bank_is_active', 'bank_open_row', 'cnt_rcd', 
                           'cycle_count', 'refresh_in_progress']
    for key in required_state_keys:
        if key not in state:
            print(f"  FAIL: Missing state key '{key}'")
            passed = False
    
    if passed:
        print("  PASS")
    test_results.append(passed)
    
    # Summary
    print("\n" + "="*50)
    total = len(test_results)
    passed_count = sum(test_results)
    failed_count = total - passed_count
    
    for i, result in enumerate(test_results, 1):
        status = "PASS" if result else "FAIL"
        print(f"  Test {i}: {status}")
    
    print(f"\nTotal: {passed_count}/{total} passed, {failed_count} failed")
    
    if all(test_results):
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")


if __name__ == "__main__":
    run_self_test()