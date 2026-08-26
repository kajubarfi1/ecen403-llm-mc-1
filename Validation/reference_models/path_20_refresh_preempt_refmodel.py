import json
import os

# DDR command encoding from RTL cmd_gen.sv
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

# Map scheduler command type to DDR encoding
SCHED_TO_DDR = {
    SCHED_NOP: DDR_NOP,
    SCHED_ACT: DDR_ACT,
    SCHED_RD:  DDR_RD,
    SCHED_WR:  DDR_WR,
    SCHED_PRE: DDR_PRE,
    SCHED_REF: DDR_REF,
}

NUM_BANKS = 8

# Default timing values (in controller clock cycles)
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
DEFAULT_CL        = 11
DEFAULT_CWL       = 8

DEFAULT_MAX_POSTPONE    = 8
DEFAULT_URGENT_THRESHOLD = 6


class PathModel:
    """
    Reference model for Path 20: Transaction Preempted by Urgent Refresh
    Models: wb_port -> addr_decoder -> cmd_queue -> scheduler -> refresh_ctrl -> cmd_gen
    """

    def __init__(self):
        self.reset()

    def reset(self):
        """Reset all internal state to power-on defaults."""
        # ---- Wishbone port state ----
        self.wb_ack_pending = False
        self.wb_stall = False

        # ---- Address decoder outputs ----
        self.dec_row = 0
        self.dec_col = 0
        self.dec_bank = 0
        self.dec_rank = 0

        # ---- Command queue (single-entry mode) ----
        self.q_valid = False
        self.q_row = 0
        self.q_col = 0
        self.q_bank = 0
        self.q_we = 0
        self.q_aux = 0
        self.q_addr = 0  # original address for debug
        self.q_wdata = 0
        self.q_wmask = 0

        # ---- Bank tracker state ----
        self.bank_is_active = [0] * NUM_BANKS
        self.bank_open_row = [0] * NUM_BANKS

        # Per-bank timing counters
        self.cnt_rcd = [0] * NUM_BANKS   # after ACT, wait tRCD before RD/WR
        self.cnt_rp  = [0] * NUM_BANKS   # after PRE, wait tRP before ACT
        self.cnt_ras = [0] * NUM_BANKS   # after ACT, min active time before PRE
        self.cnt_rc  = [0] * NUM_BANKS   # after ACT, min before next ACT to same bank
        self.cnt_wr  = [0] * NUM_BANKS   # after WR, wait tWR+tRP before PRE (simplified: tWR)
        self.cnt_wtr = [0] * NUM_BANKS   # after WR, wait tWTR before RD
        self.cnt_rtp = [0] * NUM_BANKS   # after RD, wait tRTP before PRE
        self.cnt_ccd = 0                 # CAS-to-CAS delay (global)

        # Global timing
        self.cnt_rrd = 0                 # ACT-to-ACT different bank
        self.cnt_rfc = 0                 # refresh cycle time
        self.faw_window = []             # timestamps (cycle numbers) of last 4 ACTs
        self.cycle_count = 0

        # Refresh in progress flag
        self.refresh_in_progress = False

        # ---- Refresh controller state ----
        self.refi_counter = 0
        self.postpone_cnt = 0
        self.ref_required = False
        self.ref_urgent = False
        self.ref_starve_flag = False
        self.init_done_prev = False

        # ---- Pipeline stages (2-stage for cmd_gen latency) ----
        # pipe_s1 = scheduler registered output (1 cycle after decision)
        # pipe_s2 = cmd_gen registered output (2 cycles after decision)
        self.pipe_s1 = {'type': SCHED_NOP, 'bank': 0, 'row': 0, 'col': 0, 'we': 0, 'aux': 0, 'deq': False, 'ref_ack': False}
        self.pipe_s2 = {'type': SCHED_NOP, 'bank': 0, 'row': 0, 'col': 0, 'we': 0, 'aux': 0, 'deq': False, 'ref_ack': False}

        # ---- Pending feedback (applied NEXT cycle) ----
        self.pending_fb_type = SCHED_NOP
        self.pending_fb_bank = 0
        self.pending_fb_row = 0

        # ---- Configuration (defaults) ----
        self.cfg_tRCD_nCK = DEFAULT_tRCD_nCK
        self.cfg_tRP_nCK  = DEFAULT_tRP_nCK
        self.cfg_tRAS_nCK = DEFAULT_tRAS_nCK
        self.cfg_tRC_nCK  = DEFAULT_tRC_nCK
        self.cfg_tRFC_nCK = DEFAULT_tRFC_nCK
        self.cfg_tFAW_nCK = DEFAULT_tFAW_nCK
        self.cfg_tRRD_nCK = DEFAULT_tRRD_nCK
        self.cfg_tWR_nCK  = DEFAULT_tWR_nCK
        self.cfg_tWTR_nCK = DEFAULT_tWTR_nCK
        self.cfg_tRTP_nCK = DEFAULT_tRTP_nCK
        self.cfg_tCCD_nCK = DEFAULT_tCCD_nCK
        self.cfg_tREFI_nCK = DEFAULT_tREFI_nCK
        self.cfg_max_postpone = DEFAULT_MAX_POSTPONE
        self.cfg_urgent_threshold = DEFAULT_URGENT_THRESHOLD

    def _decode_address(self, byte_addr):
        """
        Decode byte address into row, bank, column using row-bank-column mapping.
        Address bits (from LSB):
          [0]     = byte within 16-bit word (ignored for column)
          [1:3]   = burst offset (3 bits for BL8) — part of column
          [4:13]  = column bits [9:0] mapped from addr bits [13:4] → actually:
          
        With 16-bit channel width (2 byte lanes), the LSB of byte address is the
        sub-word byte select. For DDR3 BL8 with 16-bit bus:
          - Bits [0]: sub-word byte (not used in DRAM address)
          - Bits [3:1]: burst offset (3 bits for BL8) — low column bits
          - Bits [10:4]: remaining column bits (total 10 column bits)
            Actually column_bits=10, but 3 bits are burst offset → 10 total col bits in addr
            
        Let me re-derive carefully:
        channel_data_width = 16 bits = 2 bytes
        burst_length = 8
        burst_transfer_bytes = 2 * 8 = 16 bytes
        
        Byte address layout for row-bank-column:
          byte_offset_in_burst = log2(16) = 4 bits → addr[3:0]
          column address (excluding burst bits) = column_bits - log2(BL) = 10 - 3 = 7 bits → addr[10:4]
          bank = bank_bits = 3 bits → addr[13:11]
          row = row_bits = 15 bits → addr[28:14]
        """
        # Number of byte offset bits (within a burst)
        byte_offset_bits = 4  # log2(16) = 4, since burst = 8 * 2 bytes = 16
        col_low_bits = 3      # log2(BL=8)
        col_high_bits = 10 - col_low_bits  # = 7

        addr = byte_addr & 0x1FFFFFFF  # 29-bit address

        # Extract fields
        # byte_offset = addr[3:0] (4 bits) - not sent to DRAM
        col_low = (addr >> 1) & 0x7  # bits [3:1] → 3 bits of column (burst offset)
        # Actually, for DRAM, the full column is 10 bits. The lower 3 bits are the burst
        # offset which the DRAM uses internally. The column address sent is bits [9:3].
        # But the address decoder extracts all column bits:
        
        # Simpler approach: strip byte offset, then extract col, bank, row
        # Word address (16-bit words): addr >> 1
        word_addr = addr >> 1  # 28 bits
        
        # Column = lower 10 bits of word_addr
        col = word_addr & ((1 << 10) - 1)
        
        # Bank = next 3 bits
        bank = (word_addr >> 10) & ((1 << 3) - 1)
        
        # Row = next 15 bits
        row = (word_addr >> (10 + 3)) & ((1 << 15) - 1)

        return row, bank, col

    def _bank_act_allowed(self, bank):
        """Check if ACT is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if self.bank_is_active[bank]:
            return False  # Bank already active
        if self.cnt_rp[bank] > 0:
            return False  # tRP not met
        if self.cnt_rc[bank] > 0:
            return False  # tRC not met
        if self.cnt_rrd > 0:
            return False  # tRRD not met
        # Check tFAW
        if not self._faw_allows_act():
            return False
        return True

    def _bank_rd_allowed(self, bank):
        """Check if RD is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if not self.bank_is_active[bank]:
            return False
        if self.cnt_rcd[bank] > 0:
            return False  # tRCD not met
        if self.cnt_ccd > 0:
            return False  # tCCD not met
        if self.cnt_wtr[bank] > 0:
            return False  # tWTR not met (global would be better, but per-bank approx)
        return True

    def _bank_wr_allowed(self, bank):
        """Check if WR is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if not self.bank_is_active[bank]:
            return False
        if self.cnt_rcd[bank] > 0:
            return False
        if self.cnt_ccd > 0:
            return False
        return True

    def _bank_pre_allowed(self, bank):
        """Check if PRE is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if not self.bank_is_active[bank]:
            return False
        if self.cnt_ras[bank] > 0:
            return False  # tRAS not met
        if self.cnt_rtp[bank] > 0:
            return False  # tRTP not met after RD
        if self.cnt_wr[bank] > 0:
            return False  # tWR not met after WR
        return True

    def _faw_allows_act(self):
        """Check if tFAW window allows another ACT."""
        # Remove old entries
        cutoff = self.cycle_count - self.cfg_tFAW_nCK
        active_acts = [t for t in self.faw_window if t > cutoff]
        return len(active_acts) < 4

    def _all_banks_idle(self):
        """Check if all banks are idle (needed for refresh)."""
        return all(a == 0 for a in self.bank_is_active)

    def _apply_feedback(self, fb_type, fb_bank, fb_row):
        """Apply feedback from a completed command to bank state."""
        if fb_type == SCHED_ACT:
            self.bank_is_active[fb_bank] = 1
            self.bank_open_row[fb_bank] = fb_row
            self.cnt_rcd[fb_bank] = self.cfg_tRCD_nCK
            self.cnt_ras[fb_bank] = self.cfg_tRAS_nCK
            self.cnt_rc[fb_bank] = self.cfg_tRC_nCK
            self.cnt_rrd = self.cfg_tRRD_nCK
            # Record ACT in FAW window
            self.faw_window.append(self.cycle_count)
            # Trim old entries
            cutoff = self.cycle_count - self.cfg_tFAW_nCK
            self.faw_window = [t for t in self.faw_window if t > cutoff]

        elif fb_type == SCHED_RD:
            self.cnt_ccd = self.cfg_tCCD_nCK
            self.cnt_rtp[fb_bank] = self.cfg_tRTP_nCK

        elif fb_type == SCHED_WR:
            self.cnt_ccd = self.cfg_tCCD_nCK
            self.cnt_wr[fb_bank] = self.cfg_tWR_nCK
            self.cnt_wtr[fb_bank] = self.cfg_tWTR_nCK

        elif fb_type == SCHED_PRE:
            self.bank_is_active[fb_bank] = 0
            self.bank_open_row[fb_bank] = 0
            self.cnt_rp[fb_bank] = self.cfg_tRP_nCK

        elif fb_type == SCHED_REF:
            # Refresh closes all banks
            for b in range(NUM_BANKS):
                self.bank_is_active[b] = 0
                self.bank_open_row[b] = 0
            self.cnt_rfc = self.cfg_tRFC_nCK
            self.faw_window = []  # CLEAR — all prior ACTs invalidated
            self.cnt_rrd = 0      # CLEAR — no prior ACT relevant
            self.refresh_in_progress = True

    def _decrement_counters(self):
        """Decrement all timing counters by 1 (clamp to 0)."""
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
            if self.cnt_wtr[b] > 0:
                self.cnt_wtr[b] -= 1
            if self.cnt_rtp[b] > 0:
                self.cnt_rtp[b] -= 1
        if self.cnt_ccd > 0:
            self.cnt_ccd -= 1
        if self.cnt_rrd > 0:
            self.cnt_rrd -= 1
        if self.cnt_rfc > 0:
            self.cnt_rfc -= 1
        if self.cnt_rfc == 0 and self.refresh_in_progress:
            self.refresh_in_progress = False

    def _scheduler_decision(self, init_done, bank_is_active_ext, bank_open_row_0_ext,
                            bank_act_allowed_ext, bank_rd_allowed_ext,
                            bank_wr_allowed_ext, bank_pre_allowed_ext):
        """
        Combinational scheduler decision.
        Returns (cmd_type, cmd_bank, cmd_row, cmd_col, cmd_we, cmd_aux, deq, ref_ack)
        """
        if not init_done:
            return (SCHED_NOP, 0, 0, 0, 0, 0, False, False)

        # Priority 1: Urgent refresh preempts everything
        if self.ref_urgent:
            # For refresh, we need all banks idle. If not, precharge them.
            # But the spec says urgent_preempt: we issue REF if possible,
            # or precharge banks first.
            if self._all_banks_idle() and not self.refresh_in_progress:
                return (SCHED_REF, 0, 0, 0, 0, 0, False, True)
            else:
                # Need to precharge active banks first
                for b in range(NUM_BANKS):
                    if self.bank_is_active[b] and self._bank_pre_allowed(b):
                        return (SCHED_PRE, b, 0, 0, 0, 0, False, False)
                # Can't precharge yet, issue NOP
                return (SCHED_NOP, 0, 0, 0, 0, 0, False, False)

        # Priority 2: Row-hit CAS
        if self.q_valid and not self.refresh_in_progress:
            b = self.q_bank
            if (self.bank_is_active[b] and
                self.bank_open_row[b] == self.q_row):
                # Row hit
                if self.q_we and self._bank_wr_allowed(b):
                    return (SCHED_WR, b, self.q_row, self.q_col, 1, self.q_aux, True, False)
                elif not self.q_we and self._bank_rd_allowed(b):
                    return (SCHED_RD, b, self.q_row, self.q_col, 0, self.q_aux, True, False)

        # Priority 3: Row-miss handling (ACT or PRE needed)
        if self.q_valid and not self.refresh_in_progress:
            b = self.q_bank
            if not self.bank_is_active[b] or self.bank_open_row[b] != self.q_row:
                # Row miss
                if self.bank_is_active[b] and self.bank_open_row[b] != self.q_row:
                    # Wrong row open, need PRE first
                    if self._bank_pre_allowed(b):
                        return (SCHED_PRE, b, 0, 0, 0, 0, False, False)
                elif not self.bank_is_active[b]:
                    # Bank idle, can ACT
                    if self._bank_act_allowed(b):
                        return (SCHED_ACT, b, self.q_row, 0, 0, 0, False, False)

        # Priority 4: Non-urgent refresh
        if self.ref_required and not self.refresh_in_progress:
            if self._all_banks_idle():
                return (SCHED_REF, 0, 0, 0, 0, 0, False, True)

        # Priority 5: NOP
        return (SCHED_NOP, 0, 0, 0, 0, 0, False, False)

    def step(self, **inputs):
        """Advance the model by one clock cycle."""
        # Extract inputs with defaults
        wb_cyc = inputs.get('wb_cyc_i', 0)
        wb_stb = inputs.get('wb_stb_i', 0)
        wb_we  = inputs.get('wb_we_i', 0)
        wb_adr = inputs.get('wb_adr_i', 0)
        wb_dat = inputs.get('wb_dat_i', 0)
        wb_sel = inputs.get('wb_sel_i', 0xF)
        wb_bte = inputs.get('wb_bte_i', 0)
        wb_cti = inputs.get('wb_cti_i', 0)
        req_ready = inputs.get('req_ready', 1)

        init_done = inputs.get('init_done', 0)
        cfg_force_refresh = inputs.get('cfg_force_refresh', 0)
        cfg_tREFI_nCK = inputs.get('cfg_tREFI_nCK', self.cfg_tREFI_nCK)
        cfg_max_postpone = inputs.get('cfg_max_postpone', self.cfg_max_postpone)
        cfg_urgent_threshold = inputs.get('cfg_urgent_threshold', self.cfg_urgent_threshold)
        cfg_ref_priority = inputs.get('cfg_ref_priority', 0)

        # External bank state (from testbench, but we use internal model)
        bank_is_active_ext = inputs.get('bank_is_active', 0)
        bank_open_row_0_ext = inputs.get('bank_open_row_0', 0)
        bank_act_allowed_ext = inputs.get('bank_act_allowed', 0xFF)
        bank_rd_allowed_ext = inputs.get('bank_rd_allowed', 0xFF)
        bank_wr_allowed_ext = inputs.get('bank_wr_allowed', 0xFF)
        bank_pre_allowed_ext = inputs.get('bank_pre_allowed', 0xFF)

        # Update config
        self.cfg_tREFI_nCK = cfg_tREFI_nCK
        self.cfg_max_postpone = cfg_max_postpone
        self.cfg_urgent_threshold = cfg_urgent_threshold

        # ================================================================
        # Step 1: Apply PENDING feedback from previous cycle to bank state
        # ================================================================
        self._apply_feedback(self.pending_fb_type, self.pending_fb_bank, self.pending_fb_row)
        self.pending_fb_type = SCHED_NOP
        self.pending_fb_bank = 0
        self.pending_fb_row = 0

        # ================================================================
        # Step 2: Decrement timing counters
        # ================================================================
        self._decrement_counters()

        # ================================================================
        # Step 3: Refresh controller update
        # ================================================================
        if not init_done:
            self.refi_counter = 0
            self.postpone_cnt = 0
            self.ref_required = False
            self.ref_urgent = False
            self.ref_starve_flag = False
        else:
            # tREFI down-counter
            refi_tick = False
            if self.refi_counter == 0:
                refi_tick = True
                self.refi_counter = self.cfg_tREFI_nCK
            else:
                self.refi_counter -= 1

            if refi_tick:
                self.postpone_cnt += 1

            # Check ref_ack from pipe_s2 (after shift, done below, but we need to
            # check the current pipe_s2 which is about to be output and represents
            # the 1-cycle-delayed scheduler output)
            # Actually, ref_ack decrements postpone_cnt. But we haven't shifted yet.
            # The ref_ack that matters is from the PREVIOUS pipe_s2 shift...
            # Let's handle ref_ack application after pipeline shift.

            self.ref_required = (self.postpone_cnt > 0)
            self.ref_urgent = (self.postpone_cnt >= self.cfg_urgent_threshold)

            if self.postpone_cnt >= self.cfg_max_postpone:
                self.ref_starve_flag = True

        if cfg_force_refresh and init_done:
            self.ref_required = True
            self.ref_urgent = True

        self.init_done_prev = init_done

        # ================================================================
        # Step 3b: Wishbone port / command queue
        # ================================================================
        wb_ack_o = 0
        wb_dat_o = 0
        wb_stall_o = 0
        wb_err_o = 0
        req_wdata = 0
        req_wmask = 0
        enq_ready = 0

        # Queue is full if we have a valid entry and it hasn't been dequeued
        queue_full = 1 if self.q_valid else 0
        queue_empty = 0 if self.q_valid else 1

        # Check if a dequeue happened (from pipe_s2 which is the 1-cycle-delayed output)
        # This will be checked after pipeline shift

        # Accept new Wishbone request if queue is empty
        if wb_cyc and wb_stb and not self.q_valid:
            # Decode address
            row, bank, col = self._decode_address(wb_adr)
            self.dec_row = row
            self.dec_col = col
            self.dec_bank = bank

            # Enqueue
            self.q_valid = True
            self.q_row = row
            self.q_col = col
            self.q_bank = bank
            self.q_we = wb_we
            self.q_aux = 0
            self.q_addr = wb_adr
            if wb_we:
                self.q_wdata = wb_dat
                self.q_wmask = wb_sel
            else:
                self.q_wdata = 0
                self.q_wmask = 0

            wb_ack_o = 1
            enq_ready = 1
            req_wdata = self.q_wdata
            req_wmask = self.q_wmask
        elif wb_cyc and wb_stb and self.q_valid:
            wb_stall_o = 1
            enq_ready = 0

        if not self.q_valid:
            enq_ready = 1

        # ================================================================
        # Step 4: CAPTURE DDR output from pipe_s2 BEFORE shifting
        # ================================================================
        output_cmd = self.pipe_s2.copy()

        ddr_cmd = SCHED_TO_DDR.get(output_cmd['type'], DDR_NOP)

        # Compute DDR address/bank based on command type
        ddr_bank = output_cmd['bank'] & 0x7
        ddr_addr = 0
        if output_cmd['type'] == SCHED_ACT:
            ddr_addr = output_cmd['row'] & 0x7FFF  # 15-bit row
        elif output_cmd['type'] in (SCHED_RD, SCHED_WR):
            # Column address in A[9:0], with A10 = 0 (no auto-precharge)
            ddr_addr = output_cmd['col'] & 0x3FF
        elif output_cmd['type'] == SCHED_PRE:
            # A10 = 0 for single bank precharge
            ddr_addr = 0
        elif output_cmd['type'] == SCHED_REF:
            ddr_addr = 0
            ddr_bank = 0

        # Feedback signals from the output stage
        fb_act_valid = 1 if output_cmd['type'] == SCHED_ACT else 0
        fb_act_bank = output_cmd['bank'] if output_cmd['type'] == SCHED_ACT else 0
        fb_act_row = output_cmd['row'] if output_cmd['type'] == SCHED_ACT else 0
        fb_pre_valid = 1 if output_cmd['type'] == SCHED_PRE else 0
        fb_rd_valid = 1 if output_cmd['type'] == SCHED_RD else 0
        fb_wr_valid = 1 if output_cmd['type'] == SCHED_WR else 0
        fb_ref_valid = 1 if output_cmd['type'] == SCHED_REF else 0

        # ================================================================
        # Step 5: Make scheduler decision (combinational)
        # ================================================================
        decision = self._scheduler_decision(
            init_done,
            bank_is_active_ext, bank_open_row_0_ext,
            bank_act_allowed_ext, bank_rd_allowed_ext,
            bank_wr_allowed_ext, bank_pre_allowed_ext
        )
        cmd_type, cmd_bank, cmd_row, cmd_col, cmd_we, cmd_aux, deq, ref_ack = decision

        new_s1 = {
            'type': cmd_type,
            'bank': cmd_bank,
            'row': cmd_row,
            'col': cmd_col,
            'we': cmd_we,
            'aux': cmd_aux,
            'deq': deq,
            'ref_ack': ref_ack,
        }

        # ================================================================
        # Step 5b: Shift pipeline: pipe_s2 = pipe_s1, pipe_s1 = new_decision
        # ================================================================
        old_pipe_s1 = self.pipe_s1.copy()
        self.pipe_s2 = old_pipe_s1
        self.pipe_s1 = new_s1

        # ================================================================
        # Step 6: Store output_cmd as pending feedback (to be applied NEXT cycle)
        # ================================================================
        self.pending_fb_type = output_cmd['type']
        self.pending_fb_bank = output_cmd['bank']
        self.pending_fb_row = output_cmd['row']

        # ================================================================
        # Step 6b: Process deq_grant and ref_ack from pipe_s2 AFTER shift
        # ================================================================
        # deq_grant comes from self.pipe_s2 after shift (= old_pipe_s1)
        if self.pipe_s2['deq'] and self.q_valid:
            self.q_valid = False

        # ref_ack from pipe_s2 after shift
        if self.pipe_s2['ref_ack'] and init_done:
            if self.postpone_cnt > 0:
                self.postpone_cnt -= 1
            self.ref_required = (self.postpone_cnt > 0)
            self.ref_urgent = (self.postpone_cnt >= self.cfg_urgent_threshold)

        # Update queue status after potential dequeue
        queue_full = 1 if self.q_valid else 0
        queue_empty = 0 if self.q_valid else 1
        queue_count = 1 if self.q_valid else 0

        # ================================================================
        # Increment cycle count
        # ================================================================
        self.cycle_count += 1

        # DDR control signals
        ddr_cke = 1 if init_done else 0
        ddr_reset_n = 1 if init_done else 0
        ddr_odt = 0  # simplified

        # ================================================================
        # Build output dict with ALL required signals
        # ================================================================
        outputs = {
            'wb_ack_o': wb_ack_o,
            'wb_dat_o': wb_dat_o,
            'wb_stall_o': wb_stall_o,
            'wb_err_o': wb_err_o,
            'req_wdata': req_wdata,
            'req_wmask': req_wmask,
            'dec_rank': self.dec_rank,
            'enq_ready': enq_ready,
            'queue_full': queue_full,
            'queue_empty': queue_empty,
            'queue_count': queue_count,
            'ref_pending_cnt': self.postpone_cnt,
            'ref_starve_flag': 1 if self.ref_starve_flag else 0,
            'ddr_cmd': ddr_cmd,
            'ddr_addr': ddr_addr,
            'ddr_bank': ddr_bank,
            'ddr_cke': ddr_cke,
            'ddr_reset_n': ddr_reset_n,
            'ddr_odt': ddr_odt,
            'fb_act_valid': fb_act_valid,
            'fb_act_bank': fb_act_bank,
            'fb_act_row': fb_act_row,
            'fb_pre_valid': fb_pre_valid,
            'fb_rd_valid': fb_rd_valid,
            'fb_wr_valid': fb_wr_valid,
            'fb_ref_valid': fb_ref_valid,
        }

        return outputs

    def get_state(self):
        """Return full internal state for debugging."""
        return {
            'cycle_count': self.cycle_count,
            'q_valid': self.q_valid,
            'q_row': self.q_row,
            'q_col': self.q_col,
            'q_bank': self.q_bank,
            'q_we': self.q_we,
            'bank_is_active': list(self.bank_is_active),
            'bank_open_row': list(self.bank_open_row),
            'cnt_rcd': list(self.cnt_rcd),
            'cnt_rp': list(self.cnt_rp),
            'cnt_ras': list(self.cnt_ras),
            'cnt_rc': list(self.cnt_rc),
            'cnt_rfc': self.cnt_rfc,
            'cnt_rrd': self.cnt_rrd,
            'cnt_ccd': self.cnt_ccd,
            'refresh_in_progress': self.refresh_in_progress,
            'refi_counter': self.refi_counter,
            'postpone_cnt': self.postpone_cnt,
            'ref_required': self.ref_required,
            'ref_urgent': self.ref_urgent,
            'ref_starve_flag': self.ref_starve_flag,
            'pipe_s1': dict(self.pipe_s1),
            'pipe_s2': dict(self.pipe_s2),
            'pending_fb_type': self.pending_fb_type,
            'pending_fb_bank': self.pending_fb_bank,
            'pending_fb_row': self.pending_fb_row,
            'faw_window': list(self.faw_window),
        }


def run_self_test():
    """Run self-tests to validate the reference model."""
    results = []

    def check(name, condition):
        status = "PASS" if condition else "FAIL"
        results.append((name, condition))
        print(f"  {status}: {name}")

    # ================================================================
    # Test 1: Reset values
    # ================================================================
    print("Test 1: Reset values")
    m = PathModel()
    out = m.step()
    check("ddr_cmd is NOP after reset", out['ddr_cmd'] == DDR_NOP)
    check("queue_empty after reset", out['queue_empty'] == 1)
    check("queue_full is 0 after reset", out['queue_full'] == 0)
    check("queue_count is 0 after reset", out['queue_count'] == 0)
    check("ref_pending_cnt is 0 after reset", out['ref_pending_cnt'] == 0)
    check("ref_starve_flag is 0 after reset", out['ref_starve_flag'] == 0)
    check("fb_act_valid is 0 after reset", out['fb_act_valid'] == 0)
    check("fb_ref_valid is 0 after reset", out['fb_ref_valid'] == 0)
    check("ddr_cke is 0 (init_done=0)", out['ddr_cke'] == 0)
    check("ddr_reset_n is 0 (init_done=0)", out['ddr_reset_n'] == 0)

    # ================================================================
    # Test 2: All output keys present
    # ================================================================
    print("\nTest 2: All output keys present")
    expected_keys = [
        'wb_ack_o', 'wb_dat_o', 'wb_stall_o', 'wb_err_o',
        'req_wdata', 'req_wmask', 'dec_rank', 'enq_ready',
        'queue_full', 'queue_empty', 'queue_count',
        'ref_pending_cnt', 'ref_starve_flag',
        'ddr_cmd', 'ddr_addr', 'ddr_bank', 'ddr_cke', 'ddr_reset_n', 'ddr_odt',
        'fb_act_valid', 'fb_act_bank', 'fb_act_row',
        'fb_pre_valid', 'fb_rd_valid', 'fb_wr_valid', 'fb_ref_valid',
    ]
    out = m.step()
    for key in expected_keys:
        check(f"Output key '{key}' present", key in out)

    # ================================================================
    # Test 3: Unknown kwargs ignored
    # ================================================================
    print("\nTest 3: Unknown kwargs ignored")
    try:
        out = m.step(unknown_signal_xyz=42, another_bogus=99)
        check("Unknown kwargs accepted without crash", True)
    except Exception as e:
        check(f"Unknown kwargs accepted without crash (got {e})", False)

    # ================================================================
    # Test 4: Wishbone accept and address decode
    # ================================================================
    print("\nTest 4: Wishbone accept and address decode")
    m = PathModel()
    # Issue a WB read to address 0x00004000
    # byte_addr = 0x4000 = 16384
    # word_addr = 16384 >> 1 = 8192
    # col = 8192 & 0x3FF = 0 (8192 = 0x2000, lower 10 bits = 0)
    # bank = (8192 >> 10) & 0x7 = 8 & 7 = 0
    # row = (8192 >> 13) & 0x7FFF = 1
    out = m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=0x00004000, init_done=1)
    check("WB ack on accept", out['wb_ack_o'] == 1)
    check("Queue not empty after accept", out['queue_empty'] == 0)
    check("Queue count is 1", out['queue_count'] == 1)
    state = m.get_state()
    check("Decoded row = 1", state['q_row'] == 1)
    check("Decoded bank = 0", state['q_bank'] == 0)
    check("Decoded col = 0", state['q_col'] == 0)

    # ================================================================
    # Test 5: Queue stall when full
    # ================================================================
    print("\nTest 5: Queue stall when full")
    out = m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=0x00008000, init_done=1)
    check("WB stall when queue full", out['wb_stall_o'] == 1)
    check("WB ack NOT asserted when stalled", out['wb_ack_o'] == 0)

    # ================================================================
    # Test 6: Refresh counter fires on first cycle after init_done
    # ================================================================
    print("\nTest 6: Refresh counter fires on first init_done")
    m = PathModel()
    # Cycle with init_done=0
    out = m.step(init_done=0)
    check("ref_pending_cnt=0 before init_done", out['ref_pending_cnt'] == 0)
    # First cycle with init_done=1 → refi_counter==0 → tick → postpone_cnt=1
    out = m.step(init_done=1)
    check("ref_pending_cnt=1 on first init_done", out['ref_pending_cnt'] == 1)

    # ================================================================
    # Test 7: Refresh accumulates to urgent threshold
    # ================================================================
    print("\nTest 7: Refresh accumulates to urgent")
    m = PathModel()
    m.cfg_tREFI_nCK = 4  # Very short for testing
    m.cfg_urgent_threshold = 3

    # init_done=0
    m.step(init_done=0, cfg_tREFI_nCK=4, cfg_urgent_threshold=3)
    # init_done=1, first cycle: tick, postpone=1
    m.step(init_done=1, cfg_tREFI_nCK=4, cfg_urgent_threshold=3)
    state = m.get_state()
    check("After first init: postpone_cnt=1", state['postpone_cnt'] == 1)

    # Run 4 more cycles (refi_counter starts at 4, counts to 0 in 4 cycles)
    for i in range(4):
        out = m.step(init_done=1, cfg_tREFI_nCK=4, cfg_urgent_threshold=3)
    state = m.get_state()
    check("After 4 more cycles: postpone_cnt=2", state['postpone_cnt'] == 2)

    # Run 4 more cycles for another tick
    for i in range(4):
        out = m.step(init_done=1, cfg_tREFI_nCK=4, cfg_urgent_threshold=3)
    state = m.get_state()
    check(f"After 8 more cycles: postpone_cnt={state['postpone_cnt']}>=3 → urgent",
          state['postpone_cnt'] >= 3 and state['ref_urgent'])

    # ================================================================
    # Test 8: Basic read transaction through pipeline (ACT then RD)
    # ================================================================
    print("\nTest 8: Basic read transaction (ACT->RD)")
    m = PathModel()
    m.cfg_tREFI_nCK = 100000  # Effectively disable refresh for this test

    # init_done=1, no refresh pressure
    m.step(init_done=1, cfg_tREFI_nCK=100000)
    # postpone_cnt=1 from init tick, but let's force it to 0 for clean test
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    m.refi_counter = 100000

    # Enqueue a read to bank 0, row 5
    # We need addr that decodes to bank=0, row=5, col=0
    # row=5 → bits [28:14] of word_addr → word_addr[27:13] = 5
    # bank=0 → word_addr[12:10] = 0
    # col=0 → word_addr[9:0] = 0
    # word_addr = 5 << 13 = 40960
    # byte_addr = 40960 << 1 = 81920 = 0x14000
    test_addr = 5 << 14  # byte addr: row=5, bank=0, col=0
    out = m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=test_addr,
                 init_done=1, cfg_tREFI_nCK=100000)
    check("WB ack for read request", out['wb_ack_o'] == 1)

    state = m.get_state()
    check("Decoded row=5", state['q_row'] == 5)
    check("Decoded bank=0", state['q_bank'] == 0)
    check("q_valid=True", state['q_valid'] == True)

    # Scheduler should decide ACT on this cycle (bank 0 idle, q_valid)
    # But output comes 2 cycles later via pipeline

    # Run cycles until we see ACT on DDR pins
    saw_act = False
    act_cycle = -1
    for i in range(5):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        m.postpone_cnt = 0
        m.ref_required = False
        m.ref_urgent = False
        if out['ddr_cmd'] == DDR_ACT:
            saw_act = True
            act_cycle = i
            check(f"ACT command seen at cycle offset {i}", True)
            check("ACT bank=0", out['ddr_bank'] == 0)
            check("ACT row=5", out['ddr_addr'] == 5)
            break
    if not saw_act:
        check("ACT command seen within 5 cycles", False)

    # Continue until tRCD expires and we see RD
    saw_rd = False
    for i in range(30):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        m.postpone_cnt = 0
        m.ref_required = False
        m.ref_urgent = False
        if out['ddr_cmd'] == DDR_RD:
            saw_rd = True
            check(f"RD command seen after ACT + tRCD delay", True)
            check("RD bank=0", out['ddr_bank'] == 0)
            break
    if not saw_rd:
        check("RD command seen within 30 cycles after ACT", False)

    # Queue should be dequeued after RD
    # deq happens via pipe_s2 after shift, 1 cycle after scheduler decision
    # Let's run a few more cycles
    for i in range(3):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        m.postpone_cnt = 0
        m.ref_required = False
        m.ref_urgent = False
    state = m.get_state()
    check("Queue empty after RD dequeue", state['q_valid'] == False)

    # ================================================================
    # Test 9: Urgent refresh preempts a pending transaction
    # ================================================================
    print("\nTest 9: Urgent refresh preempts transaction")
    m = PathModel()
    m.cfg_tREFI_nCK = 100000

    # Initialize
    m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    m.refi_counter = 100000

    # Enqueue a read request
    test_addr = 3 << 14  # row=3, bank=0
    out = m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=test_addr,
                 init_done=1, cfg_tREFI_nCK=100000)

    # Now force urgent refresh
    m.postpone_cnt = 6  # >= urgent_threshold(6)
    m.ref_required = True
    m.ref_urgent = True

    # All banks idle, so REF should be issued
    # Run pipeline to see REF on DDR pins
    saw_ref = False
    for i in range(5):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        # Keep refresh urgent
        if m.postpone_cnt < 6:
            m.postpone_cnt = 6
        m.ref_required = True
        m.ref_urgent = True
        if out['ddr_cmd'] == DDR_REF:
            saw_ref = True
            check(f"REF command seen (cycle offset {i}) - preempts transaction", True)
            check("fb_ref_valid asserted", out['fb_ref_valid'] == 1)
            break
    if not saw_ref:
        check("REF command preempts transaction within 5 cycles", False)

    # After REF, request should still be in queue (REF doesn't dequeue)
    state = m.get_state()
    check("Request still valid after REF preemption", state['q_valid'] == True)

    # ================================================================
    # Test 10: Pipeline latency verification
    # ================================================================
    print("\nTest 10: Pipeline latency (2-cycle DDR output delay)")
    m = PathModel()
    m.cfg_tREFI_nCK = 100000

    m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    m.refi_counter = 100000

    # Cycle 0: Enqueue and scheduler makes first decision
    test_addr = 7 << 14  # row=7, bank=0
    out0 = m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=test_addr,
                  init_done=1, cfg_tREFI_nCK=100000)
    check("Cycle 0: DDR still NOP (pipeline empty)", out0['ddr_cmd'] == DDR_NOP)

    # Cycle 1: pipe_s1 has first decision, DDR still from old pipe_s2
    out1 = m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    check("Cycle 1: DDR still NOP (1-cycle pipeline delay)", out1['ddr_cmd'] == DDR_NOP)

    # Cycle 2: First decision reaches DDR output
    out2 = m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    check(f"Cycle 2: DDR shows first command (cmd={out2['ddr_cmd']})",
          out2['ddr_cmd'] != DDR_NOP)

    # ================================================================
    # Test 11: Address decode boundary
    # ================================================================
    print("\nTest 11: Address decode boundaries")
    m = PathModel()
    # Test address with all fields non-zero
    # row=100, bank=5, col=42
    # word_addr = (100 << 13) | (5 << 10) | 42
    word_addr = (100 << 13) | (5 << 10) | 42
    byte_addr = word_addr << 1
    row, bank, col = m._decode_address(byte_addr)
    check("Decode row=100", row == 100)
    check("Decode bank=5", bank == 5)
    check("Decode col=42", col == 42)

    # Max address
    max_byte_addr = 0x1FFFFFFF  # 29-bit max
    row, bank, col = m._decode_address(max_byte_addr)
    check("Max addr: row=32767 (15 bits all 1)", row == 32767)
    check("Max addr: bank=7 (3 bits all 1)", bank == 7)
    check("Max addr: col=1023 (10 bits all 1)", col == 1023)

    # ================================================================
    # Test 12: Write transaction
    # ================================================================
    print("\nTest 12: Write transaction")
    m = PathModel()
    m.cfg_tREFI_nCK = 100000

    m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    m.refi_counter = 100000

    test_addr = 2 << 14  # row=2, bank=0
    out = m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=1, wb_adr_i=test_addr,
                 wb_dat_i=0xDEADBEEF, wb_sel_i=0xF,
                 init_done=1, cfg_tREFI_nCK=100000)
    check("Write req accepted", out['wb_ack_o'] == 1)
    check("req_wdata = 0xDEADBEEF", out['req_wdata'] == 0xDEADBEEF)
    check("req_wmask = 0xF", out['req_wmask'] == 0xF)

    # Run until WR command appears
    saw_wr = False
    for i in range(40):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        m.postpone_cnt = 0
        m.ref_required = False
        m.ref_urgent = False
        if out['ddr_cmd'] == DDR_WR:
            saw_wr = True
            check(f"WR command seen (cycle {i})", True)
            check("fb_wr_valid asserted", out['fb_wr_valid'] == 1)
            break
    if not saw_wr:
        check("WR command seen within 40 cycles", False)

    # ================================================================
    # Test 13: Refresh starvation flag
    # ================================================================
    print("\nTest 13: Refresh starvation flag")
    m = PathModel()
    m.cfg_tREFI_nCK = 100000

    m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 8  # = max_postpone
    m.ref_required = True
    m.ref_urgent = True

    out = m.step(init_done=1, cfg_tREFI_nCK=100000)
    check("ref_starve_flag set at max_postpone", out['ref_starve_flag'] == 1)

    # ================================================================
    # Test 14: get_state returns dict
    # ================================================================
    print("\nTest 14: get_state returns dict")
    m = PathModel()
    state = m.get_state()
    check("get_state returns dict", isinstance(state, dict))
    check("get_state has cycle_count", 'cycle_count' in state)
    check("get_state has bank_is_active", 'bank_is_active' in state)
    check("get_state has postpone_cnt", 'postpone_cnt' in state)

    # ================================================================
    # Test 15: Refresh preempts then transaction completes after tRFC
    # ================================================================
    print("\nTest 15: Transaction completes after refresh tRFC")
    m = PathModel()
    m.cfg_tREFI_nCK = 100000
    m.cfg_tRFC_nCK = 10  # Short for testing

    m.step(init_done=1, cfg_tREFI_nCK=100000)
    m.postpone_cnt = 0
    m.ref_required = False
    m.ref_urgent = False
    m.refi_counter = 100000

    # Enqueue read
    test_addr = 10 << 14  # row=10, bank=0
    m.step(wb_cyc_i=1, wb_stb_i=1, wb_we_i=0, wb_adr_i=test_addr,
           init_done=1, cfg_tREFI_nCK=100000)

    # Force urgent refresh
    m.postpone_cnt = 6
    m.ref_required = True
    m.ref_urgent = True

    # Run until REF
    ref_seen = False
    for i in range(10):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        if m.postpone_cnt < 6:
            m.postpone_cnt = 6
        m.ref_required = True
        m.ref_urgent = True
        if out['fb_ref_valid']:
            ref_seen = True
            # Now allow normal refresh handling (postpone_cnt decremented by ref_ack)
            break

    check("REF seen before transaction", ref_seen)

    # After REF, wait for tRFC, then transaction should proceed
    # Clear urgent state (ref_ack will have decremented)
    m.ref_urgent = False
    m.ref_required = False
    m.postpone_cnt = 0

    saw_act_after_ref = False
    saw_rd_after_ref = False
    for i in range(50):
        out = m.step(init_done=1, cfg_tREFI_nCK=100000)
        m.postpone_cnt = 0
        m.ref_required = False
        m.ref_urgent = False
        if out['ddr_cmd'] == DDR_ACT and not saw_act_after_ref:
            saw_act_after_ref = True
        if out['ddr_cmd'] == DDR_RD and saw_act_after_ref:
            saw_rd_after_ref = True
            break

    check("ACT seen after REF + tRFC", saw_act_after_ref)
    check("RD completes after REF preemption", saw_rd_after_ref)

    # ================================================================
    # Summary
    # ================================================================
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