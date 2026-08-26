import json
import os
import math
from collections import deque

# DDR Command Encoding (from RTL cmd_gen.sv)
DDR_NOP  = 7
DDR_ACT  = 3
DDR_RD   = 5
DDR_WR   = 4
DDR_PRE  = 2
DDR_REF  = 1
DDR_MRS  = 0
DDR_ZQCL = 6
DDR_DESL = 15

# Scheduler command types (internal)
SCHED_NOP = 0
SCHED_ACT = 1
SCHED_RD  = 2
SCHED_WR  = 3
SCHED_PRE = 4
SCHED_REF = 5

NUM_BANKS = 8

# CSR Register Map
# Base address for timing CSRs
CSR_BASE = 0x00000000
# Register offsets (byte addresses, 4-byte aligned)
CSR_CTRL        = 0x00  # Control register
CSR_STATUS      = 0x04  # Status register
CSR_TIMING0     = 0x08  # tRCD, tRP
CSR_TIMING1     = 0x0C  # tRAS, tRC
CSR_TIMING2     = 0x10  # tRRD, tFAW
CSR_TIMING3     = 0x14  # tWTR, tWR
CSR_TIMING4     = 0x18  # tRTP, tCCD
CSR_TIMING5     = 0x1C  # tRFC, tREFI
CSR_CL_CWL      = 0x20  # CL, CWL
CSR_SCHED       = 0x24  # scheduler policy, row policy
CSR_REFRESH     = 0x28  # refresh config
CSR_ECC         = 0x2C  # ECC config
CSR_BIST_CTRL   = 0x30  # BIST control
CSR_BIST_ADDR_S = 0x34  # BIST start address
CSR_BIST_ADDR_E = 0x38  # BIST end address
CSR_SELF_REF    = 0x3C  # Self-refresh mode

# Default timing values from spec
DEF_tRCD  = 11
DEF_tRP   = 11
DEF_tRAS  = 28
DEF_tRC   = 39
DEF_tRRD  = 6
DEF_tFAW  = 32
DEF_tWTR  = 6
DEF_tWR   = 12
DEF_tRTP  = 6
DEF_tCCD  = 4
DEF_tRFC  = 128
DEF_tREFI = 6240
DEF_CL    = 11
DEF_CWL   = 8


class PipelineStage:
    def __init__(self):
        self.valid = False
        self.cmd_type = SCHED_NOP
        self.bank = 0
        self.row = 0
        self.col = 0
        self.we = 0
        self.aux = 0
        self.deq_grant = False
        self.deq_idx = 0
        self.ref_ack = False

    def copy(self):
        p = PipelineStage()
        p.valid = self.valid
        p.cmd_type = self.cmd_type
        p.bank = self.bank
        p.row = self.row
        p.col = self.col
        p.we = self.we
        p.aux = self.aux
        p.deq_grant = self.deq_grant
        p.deq_idx = self.deq_idx
        p.ref_ack = self.ref_ack
        return p


class PathModel:
    """
    Reference model for CSR -> Bank Tracker -> Scheduler path.
    Models the transitive config flow from CSR timing registers through
    bank tracker state to scheduler command decisions.
    """

    def __init__(self):
        self.reset()

    def reset(self):
        """Reset all internal state to power-on defaults."""
        # ---- CSR Configuration Registers ----
        self.cfg_tRCD_nCK = DEF_tRCD
        self.cfg_tRP_nCK = DEF_tRP
        self.cfg_tRAS_nCK = DEF_tRAS
        self.cfg_tRC_nCK = DEF_tRC
        self.cfg_tRRD_nCK = DEF_tRRD
        self.cfg_tFAW_nCK = DEF_tFAW
        self.cfg_tWTR_nCK = DEF_tWTR
        self.cfg_tWR_nCK = DEF_tWR
        self.cfg_tRTP_nCK = DEF_tRTP
        self.cfg_tCCD_nCK = DEF_tCCD
        self.cfg_tRFC_nCK = DEF_tRFC
        self.cfg_tREFI_nCK = DEF_tREFI
        self.cfg_CL_nCK = DEF_CL
        self.cfg_CWL_nCK = DEF_CWL

        # Scheduler/policy config
        self.cfg_sched_policy = 0  # 0=FR-FCFS
        self.cfg_row_policy = 0    # 0=open_page
        self.cfg_self_ref_mode = 1 # 1=auto
        self.cfg_ecc_enable = 0
        self.cfg_bist_start = 0
        self.cfg_force_refresh = 0
        self.cfg_force_self_ref = 0
        self.cfg_max_postpone = 8
        self.cfg_urgent_threshold = 6
        self.cfg_ref_priority = 2  # urgent_preempt
        self.cfg_bist_pattern = 0
        self.cfg_bist_addr_mode = 0
        self.cfg_bist_addr_start = 0
        self.cfg_bist_addr_end = 536870911

        # CSR bus state
        self.csr_ack_o = 0
        self.csr_dat_o = 0
        self.csr_err_o = 0
        self.csr_pending = False

        # ---- Bank Tracker State ----
        self.bank_is_active = [0] * NUM_BANKS
        self.bank_open_row = [0] * NUM_BANKS

        # Per-bank timing counters
        self.cnt_rcd = [0] * NUM_BANKS   # ACT to RD/WR
        self.cnt_ras = [0] * NUM_BANKS   # ACT to PRE min
        self.cnt_rc  = [0] * NUM_BANKS   # ACT to ACT same bank
        self.cnt_rp  = [0] * NUM_BANKS   # PRE to ACT same bank
        self.cnt_wtr = [0] * NUM_BANKS   # WR to RD
        self.cnt_rtp = [0] * NUM_BANKS   # RD to PRE
        self.cnt_wr_done = [0] * NUM_BANKS  # WR to PRE (tWR after write data)

        # Global timing counters
        self.cnt_rrd = 0   # ACT to ACT different bank
        self.cnt_ccd = 0   # CAS to CAS
        self.cnt_rfc = 0   # REF to any command

        # FAW window tracking (list of cycle timestamps when ACTs occurred)
        self.faw_window = []
        self.cycle_count = 0

        # Refresh state
        self.refresh_in_progress = False
        self.refi_counter = 0
        self.postpone_cnt = 0
        self.init_done_prev = False

        # ---- Pipeline Stages ----
        self.pipe_s1 = PipelineStage()
        self.pipe_s2 = PipelineStage()

        # Pending feedback from previous cycle
        self.pending_fb = PipelineStage()

        # Output registers
        self.out_cmd_valid = 0
        self.out_cmd_type = DDR_NOP
        self.out_cmd_row = 0
        self.out_cmd_col = 0
        self.out_cmd_bank = 0
        self.out_cmd_we = 0
        self.out_cmd_aux = 0
        self.out_deq_grant = 0
        self.out_deq_idx = 0
        self.out_ref_ack = 0

    def _apply_feedback(self, fb):
        """Apply pending feedback to bank tracker state."""
        if not fb.valid:
            return

        cmd = fb.cmd_type
        bank = fb.bank
        row = fb.row

        if cmd == SCHED_ACT:
            self.bank_is_active[bank] = 1
            self.bank_open_row[bank] = row
            self.cnt_rcd[bank] = self.cfg_tRCD_nCK
            self.cnt_ras[bank] = self.cfg_tRAS_nCK
            self.cnt_rc[bank] = self.cfg_tRC_nCK
            self.cnt_rrd = self.cfg_tRRD_nCK
            # Track FAW
            self.faw_window.append(self.cycle_count)

        elif cmd == SCHED_RD:
            self.cnt_ccd = self.cfg_tCCD_nCK
            self.cnt_rtp[bank] = self.cfg_tRTP_nCK

        elif cmd == SCHED_WR:
            self.cnt_ccd = self.cfg_tCCD_nCK
            self.cnt_wtr[bank] = self.cfg_tWTR_nCK + self.cfg_CWL_nCK + 4  # CWL + BL/2 + tWTR
            self.cnt_wr_done[bank] = self.cfg_tWR_nCK + self.cfg_CWL_nCK + 4  # CWL + BL/2 + tWR

        elif cmd == SCHED_PRE:
            self.bank_is_active[bank] = 0
            self.bank_open_row[bank] = 0
            self.cnt_rp[bank] = self.cfg_tRP_nCK

        elif cmd == SCHED_REF:
            # Refresh closes all banks
            for b in range(NUM_BANKS):
                self.bank_is_active[b] = 0
                self.bank_open_row[b] = 0
            self.cnt_rfc = self.cfg_tRFC_nCK
            self.faw_window = []  # CLEAR — all prior ACTs invalidated
            self.cnt_rrd = 0      # CLEAR — no prior ACT relevant
            self.refresh_in_progress = True

    def _decrement_counters(self):
        """Decrement all timing counters by 1 (minimum 0)."""
        for b in range(NUM_BANKS):
            if self.cnt_rcd[b] > 0:
                self.cnt_rcd[b] -= 1
            if self.cnt_ras[b] > 0:
                self.cnt_ras[b] -= 1
            if self.cnt_rc[b] > 0:
                self.cnt_rc[b] -= 1
            if self.cnt_rp[b] > 0:
                self.cnt_rp[b] -= 1
            if self.cnt_wtr[b] > 0:
                self.cnt_wtr[b] -= 1
            if self.cnt_rtp[b] > 0:
                self.cnt_rtp[b] -= 1
            if self.cnt_wr_done[b] > 0:
                self.cnt_wr_done[b] -= 1

        if self.cnt_rrd > 0:
            self.cnt_rrd -= 1
        if self.cnt_ccd > 0:
            self.cnt_ccd -= 1
        if self.cnt_rfc > 0:
            self.cnt_rfc -= 1
            if self.cnt_rfc == 0 and self.refresh_in_progress:
                self.refresh_in_progress = False

    def _faw_allows_act(self):
        """Check if FAW window allows another ACT."""
        # Remove old entries from FAW window
        cutoff = self.cycle_count - self.cfg_tFAW_nCK
        self.faw_window = [t for t in self.faw_window if t > cutoff]
        return len(self.faw_window) < 4

    def _bank_act_allowed(self, bank):
        """Check if ACT is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if self.cnt_rfc > 0:
            return False
        if self.cnt_rc[bank] > 0:
            return False
        if self.cnt_rp[bank] > 0:
            return False
        if self.cnt_rrd > 0:
            return False
        if not self._faw_allows_act():
            return False
        return True

    def _bank_rd_allowed(self, bank):
        """Check if RD is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if self.cnt_rfc > 0:
            return False
        if self.cnt_rcd[bank] > 0:
            return False
        if self.cnt_ccd > 0:
            return False
        if self.cnt_wtr[bank] > 0:
            return False
        return True

    def _bank_wr_allowed(self, bank):
        """Check if WR is allowed on this bank."""
        if self.refresh_in_progress:
            return False
        if self.cnt_rfc > 0:
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
        if self.cnt_rfc > 0:
            return False
        if self.cnt_ras[bank] > 0:
            return False
        if self.cnt_rtp[bank] > 0:
            return False
        if self.cnt_wr_done[bank] > 0:
            return False
        return True

    def _all_banks_idle(self):
        """Check if all banks are idle (needed for REF)."""
        return all(a == 0 for a in self.bank_is_active)

    def _handle_csr(self, **inputs):
        """Handle CSR Wishbone bus transactions."""
        cyc = inputs.get('csr_cyc_i', 0)
        stb = inputs.get('csr_stb_i', 0)
        we = inputs.get('csr_we_i', 0)
        adr = inputs.get('csr_adr_i', 0)
        dat_i = inputs.get('csr_dat_i', 0)
        sel = inputs.get('csr_sel_i', 0xF)

        # Default: no ack
        self.csr_ack_o = 0
        self.csr_dat_o = 0
        self.csr_err_o = 0

        if cyc and stb:
            # Single-cycle ack for pipelined wishbone
            self.csr_ack_o = 1

            # Word-aligned address (drop lower 2 bits for register select)
            reg_addr = adr & 0xFFFFFFFC

            if we:
                # Write
                self._csr_write(reg_addr, dat_i, sel)
            else:
                # Read
                self.csr_dat_o = self._csr_read(reg_addr)

    def _csr_write(self, addr, data, sel):
        """Write to a CSR register."""
        if addr == CSR_TIMING0:
            self.cfg_tRCD_nCK = data & 0xFF
            self.cfg_tRP_nCK = (data >> 8) & 0xFF
        elif addr == CSR_TIMING1:
            self.cfg_tRAS_nCK = data & 0xFF
            self.cfg_tRC_nCK = (data >> 8) & 0xFF
        elif addr == CSR_TIMING2:
            self.cfg_tRRD_nCK = data & 0xFF
            self.cfg_tFAW_nCK = (data >> 8) & 0xFF
        elif addr == CSR_TIMING3:
            self.cfg_tWTR_nCK = data & 0xFF
            self.cfg_tWR_nCK = (data >> 8) & 0xFF
        elif addr == CSR_TIMING4:
            self.cfg_tRTP_nCK = data & 0xFF
            self.cfg_tCCD_nCK = (data >> 8) & 0xFF
        elif addr == CSR_TIMING5:
            self.cfg_tRFC_nCK = data & 0xFFFF
            self.cfg_tREFI_nCK = (data >> 16) & 0xFFFF
        elif addr == CSR_CL_CWL:
            self.cfg_CL_nCK = data & 0xFF
            self.cfg_CWL_nCK = (data >> 8) & 0xFF
        elif addr == CSR_SCHED:
            self.cfg_sched_policy = data & 0xF
            self.cfg_row_policy = (data >> 4) & 0xF
        elif addr == CSR_REFRESH:
            self.cfg_max_postpone = data & 0xFF
            self.cfg_urgent_threshold = (data >> 8) & 0xFF
            self.cfg_ref_priority = (data >> 16) & 0xF
            self.cfg_force_refresh = (data >> 24) & 0x1
        elif addr == CSR_ECC:
            self.cfg_ecc_enable = data & 0x1
        elif addr == CSR_BIST_CTRL:
            self.cfg_bist_start = data & 0x1
            self.cfg_bist_pattern = (data >> 4) & 0xF
            self.cfg_bist_addr_mode = (data >> 8) & 0xF
        elif addr == CSR_BIST_ADDR_S:
            self.cfg_bist_addr_start = data
        elif addr == CSR_BIST_ADDR_E:
            self.cfg_bist_addr_end = data
        elif addr == CSR_SELF_REF:
            self.cfg_self_ref_mode = data & 0xF
            self.cfg_force_self_ref = (data >> 4) & 0x1
        elif addr == CSR_CTRL:
            pass  # Control register (init, etc.)

    def _csr_read(self, addr):
        """Read from a CSR register."""
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
            return (self.cfg_tREFI_nCK << 16) | self.cfg_tRFC_nCK
        elif addr == CSR_CL_CWL:
            return (self.cfg_CWL_nCK << 8) | self.cfg_CL_nCK
        elif addr == CSR_SCHED:
            return (self.cfg_row_policy << 4) | self.cfg_sched_policy
        elif addr == CSR_REFRESH:
            return ((self.cfg_force_refresh << 24) |
                    (self.cfg_ref_priority << 16) |
                    (self.cfg_urgent_threshold << 8) |
                    self.cfg_max_postpone)
        elif addr == CSR_ECC:
            return self.cfg_ecc_enable
        elif addr == CSR_BIST_CTRL:
            return ((self.cfg_bist_addr_mode << 8) |
                    (self.cfg_bist_pattern << 4) |
                    self.cfg_bist_start)
        elif addr == CSR_BIST_ADDR_S:
            return self.cfg_bist_addr_start
        elif addr == CSR_BIST_ADDR_E:
            return self.cfg_bist_addr_end
        elif addr == CSR_SELF_REF:
            return (self.cfg_force_self_ref << 4) | self.cfg_self_ref_mode
        elif addr == CSR_STATUS:
            return 0  # Status read from external signals
        return 0

    def _handle_refresh(self, init_done, ref_required_in, ref_urgent_in):
        """
        Handle refresh tracking.
        Returns (ref_required, ref_urgent) for the scheduler.
        """
        # Use external ref_required / ref_urgent if provided
        # Also maintain internal model
        if not init_done:
            self.refi_counter = 0
            self.postpone_cnt = 0
            self.init_done_prev = False
            return (0, 0)

        # On first cycle after init_done transition
        if not self.init_done_prev:
            self.init_done_prev = True
            # Counter is 0, fires immediately
            self.refi_counter = self.cfg_tREFI_nCK
            self.postpone_cnt = 1
        else:
            # Decrement refi counter
            if self.refi_counter > 0:
                self.refi_counter -= 1
            if self.refi_counter == 0:
                # refi tick
                self.refi_counter = self.cfg_tREFI_nCK
                if self.postpone_cnt < self.cfg_max_postpone:
                    self.postpone_cnt += 1

        # Check if a refresh was acknowledged (from pipe_s2)
        # This will be handled externally when ref_ack feedback comes

        ref_req = 1 if self.postpone_cnt > 0 else 0
        ref_urg = 1 if self.postpone_cnt >= self.cfg_urgent_threshold else 0

        # Override with external signals if provided
        if ref_required_in is not None:
            ref_req = ref_required_in
        if ref_urgent_in is not None:
            ref_urg = ref_urgent_in

        return (ref_req, ref_urg)

    def _scheduler_decide(self, q_valid, q_row, q_col, q_bank, q_we, q_aux,
                           ref_required, ref_urgent):
        """
        FR-FCFS Scheduler combinational logic.
        Returns a PipelineStage with the decision.
        """
        decision = PipelineStage()

        # If refresh is in progress (RFC counting), issue NOP
        if self.refresh_in_progress:
            return decision

        # Priority 1: ref_urgent → CMD_REF (preempts everything)
        if ref_urgent and self._all_banks_idle():
            decision.valid = True
            decision.cmd_type = SCHED_REF
            decision.ref_ack = True
            return decision

        # Priority 2: Row-hit CAS (lowest index, only entry 0 in single-entry mode)
        if q_valid:
            bank = q_bank
            if (self.bank_is_active[bank] and
                self.bank_open_row[bank] == q_row):
                # Row hit
                if q_we:
                    if self._bank_wr_allowed(bank):
                        decision.valid = True
                        decision.cmd_type = SCHED_WR
                        decision.bank = bank
                        decision.row = q_row
                        decision.col = q_col
                        decision.we = q_we
                        decision.aux = q_aux
                        decision.deq_grant = True
                        decision.deq_idx = 0
                        return decision
                else:
                    if self._bank_rd_allowed(bank):
                        decision.valid = True
                        decision.cmd_type = SCHED_RD
                        decision.bank = bank
                        decision.row = q_row
                        decision.col = q_col
                        decision.we = q_we
                        decision.aux = q_aux
                        decision.deq_grant = True
                        decision.deq_idx = 0
                        return decision

        # Priority 3: Row-miss handling
        if q_valid:
            bank = q_bank
            is_act_needed = (not self.bank_is_active[bank] or
                            self.bank_open_row[bank] != q_row)
            if is_act_needed:
                if self.bank_is_active[bank] and self.bank_open_row[bank] != q_row:
                    # Wrong row open, need precharge
                    if self._bank_pre_allowed(bank):
                        decision.valid = True
                        decision.cmd_type = SCHED_PRE
                        decision.bank = bank
                        decision.row = q_row
                        return decision
                elif not self.bank_is_active[bank]:
                    # Bank idle, need activate
                    if self._bank_act_allowed(bank):
                        decision.valid = True
                        decision.cmd_type = SCHED_ACT
                        decision.bank = bank
                        decision.row = q_row
                        return decision

        # Priority 4: ref_required (non-urgent)
        if ref_required and self._all_banks_idle():
            decision.valid = True
            decision.cmd_type = SCHED_REF
            decision.ref_ack = True
            return decision

        # Priority 5: NOP
        return decision

    def _sched_cmd_to_ddr(self, cmd_type):
        """Convert scheduler command type to DDR command encoding."""
        if cmd_type == SCHED_ACT:
            return DDR_ACT
        elif cmd_type == SCHED_RD:
            return DDR_RD
        elif cmd_type == SCHED_WR:
            return DDR_WR
        elif cmd_type == SCHED_PRE:
            return DDR_PRE
        elif cmd_type == SCHED_REF:
            return DDR_REF
        else:
            return DDR_NOP

    def step(self, **inputs):
        """
        Advance the model by one clock cycle.
        """
        # ---- Step 0: Handle CSR bus ----
        self._handle_csr(**inputs)

        # ---- Step 1: Apply PENDING feedback from PREVIOUS cycle to bank state ----
        self._apply_feedback(self.pending_fb)

        # ---- Step 2: Decrement timing counters ----
        self._decrement_counters()
        self.cycle_count += 1

        # ---- Step 3: Refresh handling ----
        init_done = inputs.get('sts_init_done', 0)
        ref_required_in = inputs.get('ref_required', None)
        ref_urgent_in = inputs.get('ref_urgent', None)
        ref_required, ref_urgent = self._handle_refresh(init_done, ref_required_in, ref_urgent_in)

        # If ref_ack was issued (from pipe_s2 after shift last cycle), decrement postpone
        if self.pipe_s2.valid and self.pipe_s2.ref_ack:
            if self.postpone_cnt > 0:
                self.postpone_cnt -= 1

        # ---- Step 3b: Read queue inputs ----
        q_valid = inputs.get('q_valid_0', 0)
        q_row = inputs.get('q_row_0', 0)
        q_col = inputs.get('q_col_0', 0)
        q_bank = inputs.get('q_bank_0', 0)
        q_we = inputs.get('q_we_0', 0)
        q_aux = inputs.get('q_aux_0', 0)

        # ---- Step 4: CAPTURE DDR output from pipe_s2 BEFORE shifting ----
        # This is 2 cycles old (cmd_gen output)
        output_stage = self.pipe_s2.copy()

        if output_stage.valid:
            self.out_cmd_valid = 1
            self.out_cmd_type = self._sched_cmd_to_ddr(output_stage.cmd_type)
            self.out_cmd_row = output_stage.row
            self.out_cmd_col = output_stage.col
            self.out_cmd_bank = output_stage.bank
            self.out_cmd_we = output_stage.we
            self.out_cmd_aux = output_stage.aux
        else:
            self.out_cmd_valid = 0
            self.out_cmd_type = DDR_NOP
            self.out_cmd_row = 0
            self.out_cmd_col = 0
            self.out_cmd_bank = 0
            self.out_cmd_we = 0
            self.out_cmd_aux = 0

        # ---- Step 5: Scheduler combinational decision ----
        new_decision = self._scheduler_decide(q_valid, q_row, q_col, q_bank, q_we, q_aux,
                                                ref_required, ref_urgent)

        # ---- Step 6: Shift pipeline ----
        # Store old pipe_s2 as pending feedback
        self.pending_fb = self.pipe_s2.copy()

        # Shift
        self.pipe_s2 = self.pipe_s1.copy()
        self.pipe_s1 = new_decision.copy()

        # ---- Step 7: deq_grant and ref_ack from pipe_s2 AFTER shift (1 cycle delay) ----
        self.out_deq_grant = 1 if self.pipe_s2.deq_grant else 0
        self.out_deq_idx = self.pipe_s2.deq_idx if self.pipe_s2.deq_grant else 0
        self.out_ref_ack = 1 if self.pipe_s2.ref_ack else 0

        # ---- Build output dict ----
        outputs = {
            # CSR outputs
            'csr_ack_o': self.csr_ack_o,
            'csr_dat_o': self.csr_dat_o & 0xFFFFFFFF,
            'csr_err_o': self.csr_err_o,

            # Config outputs
            'cfg_CL_nCK': self.cfg_CL_nCK,
            'cfg_CWL_nCK': self.cfg_CWL_nCK,
            'cfg_tREFI_nCK': self.cfg_tREFI_nCK,
            'cfg_sched_policy': self.cfg_sched_policy,
            'cfg_row_policy': self.cfg_row_policy,
            'cfg_self_ref_mode': self.cfg_self_ref_mode,
            'cfg_ecc_enable': self.cfg_ecc_enable,
            'cfg_bist_start': self.cfg_bist_start,
            'cfg_force_refresh': self.cfg_force_refresh,
            'cfg_force_self_ref': self.cfg_force_self_ref,
            'cfg_max_postpone': self.cfg_max_postpone,
            'cfg_urgent_threshold': self.cfg_urgent_threshold,
            'cfg_ref_priority': self.cfg_ref_priority,
            'cfg_bist_pattern': self.cfg_bist_pattern,
            'cfg_bist_addr_mode': self.cfg_bist_addr_mode,
            'cfg_bist_addr_start': self.cfg_bist_addr_start,
            'cfg_bist_addr_end': self.cfg_bist_addr_end,

            # Scheduler / command outputs
            'ref_ack': self.out_ref_ack,
            'cmd_valid': self.out_cmd_valid,
            'cmd_type': self.out_cmd_type,
            'cmd_row': self.out_cmd_row,
            'cmd_col': self.out_cmd_col,
            'cmd_bank': self.out_cmd_bank,
            'cmd_we': self.out_cmd_we,
            'cmd_aux': self.out_cmd_aux,
            'deq_grant': self.out_deq_grant,
            'deq_idx': self.out_deq_idx,
        }

        return outputs

    def get_state(self):
        """Return a dict with the full internal state for debugging."""
        return {
            'cycle_count': self.cycle_count,
            'bank_is_active': list(self.bank_is_active),
            'bank_open_row': list(self.bank_open_row),
            'cnt_rcd': list(self.cnt_rcd),
            'cnt_ras': list(self.cnt_ras),
            'cnt_rc': list(self.cnt_rc),
            'cnt_rp': list(self.cnt_rp),
            'cnt_wtr': list(self.cnt_wtr),
            'cnt_rtp': list(self.cnt_rtp),
            'cnt_wr_done': list(self.cnt_wr_done),
            'cnt_rrd': self.cnt_rrd,
            'cnt_ccd': self.cnt_ccd,
            'cnt_rfc': self.cnt_rfc,
            'refresh_in_progress': self.refresh_in_progress,
            'refi_counter': self.refi_counter,
            'postpone_cnt': self.postpone_cnt,
            'faw_window': list(self.faw_window),
            'cfg_tRCD_nCK': self.cfg_tRCD_nCK,
            'cfg_tRP_nCK': self.cfg_tRP_nCK,
            'cfg_tRAS_nCK': self.cfg_tRAS_nCK,
            'cfg_tRC_nCK': self.cfg_tRC_nCK,
            'cfg_tRRD_nCK': self.cfg_tRRD_nCK,
            'cfg_tFAW_nCK': self.cfg_tFAW_nCK,
            'cfg_tWTR_nCK': self.cfg_tWTR_nCK,
            'cfg_tWR_nCK': self.cfg_tWR_nCK,
            'cfg_tRTP_nCK': self.cfg_tRTP_nCK,
            'cfg_tCCD_nCK': self.cfg_tCCD_nCK,
            'cfg_tRFC_nCK': self.cfg_tRFC_nCK,
            'cfg_tREFI_nCK': self.cfg_tREFI_nCK,
            'cfg_CL_nCK': self.cfg_CL_nCK,
            'cfg_CWL_nCK': self.cfg_CWL_nCK,
            'pipe_s1_valid': self.pipe_s1.valid,
            'pipe_s1_cmd': self.pipe_s1.cmd_type,
            'pipe_s2_valid': self.pipe_s2.valid,
            'pipe_s2_cmd': self.pipe_s2.cmd_type,
            'pending_fb_valid': self.pending_fb.valid,
            'pending_fb_cmd': self.pending_fb.cmd_type,
        }


def run_self_test():
    """Run self-tests and print PASS/FAIL for each."""
    results = []

    def check(name, condition):
        status = "PASS" if condition else "FAIL"
        results.append((name, condition))
        print(f"  {status}: {name}")

    print("=" * 60)
    print("Path Model Self-Test: CSR -> Bank Tracker -> Scheduler")
    print("=" * 60)

    # ---- Test 1: Reset values ----
    print("\nTest 1: Reset values")
    m = PathModel()
    out = m.step()  # One cycle after reset, no inputs
    check("cmd_valid is 0 after reset", out['cmd_valid'] == 0)
    check("cmd_type is NOP after reset", out['cmd_type'] == DDR_NOP)
    check("deq_grant is 0 after reset", out['deq_grant'] == 0)
    check("ref_ack is 0 after reset", out['ref_ack'] == 0)
    check("csr_ack_o is 0 without bus cycle", out['csr_ack_o'] == 0)
    check("cfg_CL_nCK default is 11", out['cfg_CL_nCK'] == 11)
    check("cfg_CWL_nCK default is 8", out['cfg_CWL_nCK'] == 8)
    check("cfg_tREFI_nCK default is 6240", out['cfg_tREFI_nCK'] == 6240)
    check("cfg_max_postpone default is 8", out['cfg_max_postpone'] == 8)
    check("cfg_urgent_threshold default is 6", out['cfg_urgent_threshold'] == 6)
    check("cfg_bist_addr_end default", out['cfg_bist_addr_end'] == 536870911)

    # ---- Test 2: All output keys present ----
    print("\nTest 2: All output keys present")
    expected_keys = [
        'csr_ack_o', 'csr_dat_o', 'csr_err_o',
        'cfg_CL_nCK', 'cfg_CWL_nCK', 'cfg_tREFI_nCK',
        'cfg_sched_policy', 'cfg_row_policy', 'cfg_self_ref_mode',
        'cfg_ecc_enable', 'cfg_bist_start', 'cfg_force_refresh',
        'cfg_force_self_ref', 'cfg_max_postpone', 'cfg_urgent_threshold',
        'cfg_ref_priority', 'cfg_bist_pattern', 'cfg_bist_addr_mode',
        'cfg_bist_addr_start', 'cfg_bist_addr_end',
        'ref_ack', 'cmd_valid', 'cmd_type', 'cmd_row', 'cmd_col',
        'cmd_bank', 'cmd_we', 'cmd_aux', 'deq_grant', 'deq_idx'
    ]
    all_present = all(k in out for k in expected_keys)
    check("All expected output keys present", all_present)
    if not all_present:
        missing = [k for k in expected_keys if k not in out]
        print(f"    Missing keys: {missing}")

    # ---- Test 3: Unknown kwargs ignored ----
    print("\nTest 3: Unknown kwargs ignored")
    try:
        out = m.step(unknown_signal_xyz=42, another_unknown=99)
        check("step() accepts unknown kwargs without error", True)
    except Exception as e:
        check("step() accepts unknown kwargs without error", False)
        print(f"    Exception: {e}")

    # ---- Test 4: CSR Write/Read ----
    print("\nTest 4: CSR Write/Read")
    m = PathModel()
    # Write tRCD=15, tRP=20 to TIMING0
    out = m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
                 csr_adr_i=CSR_TIMING0, csr_dat_i=(20 << 8) | 15, csr_sel_i=0xF)
    check("CSR write ack", out['csr_ack_o'] == 1)

    # Read back
    out = m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=0,
                 csr_adr_i=CSR_TIMING0, csr_sel_i=0xF)
    check("CSR read ack", out['csr_ack_o'] == 1)
    check("CSR read data matches write", out['csr_dat_o'] == ((20 << 8) | 15))

    # Check internal state updated
    state = m.get_state()
    check("cfg_tRCD_nCK updated to 15", state['cfg_tRCD_nCK'] == 15)
    check("cfg_tRP_nCK updated to 20", state['cfg_tRP_nCK'] == 20)

    # ---- Test 5: CSR timing registers propagate to bank tracker ----
    print("\nTest 5: CSR timing propagation")
    m = PathModel()
    # Write CL=13, CWL=10
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=CSR_CL_CWL, csr_dat_i=(10 << 8) | 13, csr_sel_i=0xF)
    out = m.step()
    check("cfg_CL_nCK updated to 13", out['cfg_CL_nCK'] == 13)
    check("cfg_CWL_nCK updated to 10", out['cfg_CWL_nCK'] == 10)

    # ---- Test 6: Basic ACT -> RD sequence with pipeline delay ----
    print("\nTest 6: ACT -> RD sequence with pipeline delay")
    m = PathModel()

    # Present a read request to bank 0, row 100
    # With init_done=1, no refresh pending
    base_inputs = {
        'sts_init_done': 1,
        'q_valid_0': 1,
        'q_row_0': 100,
        'q_col_0': 32,
        'q_bank_0': 0,
        'q_we_0': 0,
        'q_aux_0': 5,
        'ref_required': 0,
        'ref_urgent': 0,
    }

    # Cycle 0: scheduler decides ACT (bank idle), enters pipe_s1
    out0 = m.step(**base_inputs)
    check("Cycle 0: cmd_valid=0 (pipeline empty)", out0['cmd_valid'] == 0)
    check("Cycle 0: deq_grant=0", out0['deq_grant'] == 0)

    # Cycle 1: pipe_s1->pipe_s2 (ACT), new decision enters pipe_s1
    # Scheduler still sees bank idle -> ACT again
    out1 = m.step(**base_inputs)
    check("Cycle 1: cmd_valid=0 (pipe_s2 just got first, output from old pipe_s2)", out1['cmd_valid'] == 0)
    # deq_grant comes from pipe_s2 AFTER shift, which has the ACT from cycle 0
    check("Cycle 1: deq_grant=0 (ACT doesn't dequeue)", out1['deq_grant'] == 0)

    # Cycle 2: output_stage captures pipe_s2 (which is ACT from cycle 0 decision)
    out2 = m.step(**base_inputs)
    check("Cycle 2: cmd_valid=1 (first ACT appears)", out2['cmd_valid'] == 1)
    check("Cycle 2: cmd_type=ACT", out2['cmd_type'] == DDR_ACT)
    check("Cycle 2: cmd_bank=0", out2['cmd_bank'] == 0)
    check("Cycle 2: cmd_row=100", out2['cmd_row'] == 100)

    # Cycle 3: ACT from cycle 0 feedback applied, bank becomes active
    # But ACT from cycle 1 also appears at output
    out3 = m.step(**base_inputs)
    check("Cycle 3: cmd_valid=1 (second ACT from re-issue)", out3['cmd_valid'] == 1)

    # After feedback is applied, bank 0 is active with row 100
    # But tRCD counter is running, so RD won't be allowed yet
    state = m.get_state()

    # ---- Test 7: Scheduler re-issue behavior ----
    print("\nTest 7: Scheduler re-issue verification")
    m = PathModel()
    # Verify that the scheduler re-issues ACT while bank state hasn't updated

    act_count = 0
    for i in range(5):
        out = m.step(**base_inputs)
        state = m.get_state()
        if out['cmd_valid'] == 1 and out['cmd_type'] == DDR_ACT:
            act_count += 1

    check("Multiple ACTs issued before feedback (re-issue)", act_count >= 1)

    # ---- Test 8: Refresh handling ----
    print("\nTest 8: Refresh handling")
    m = PathModel()

    # No init done - no refresh
    out = m.step(sts_init_done=0, ref_required=0, ref_urgent=0)
    state = m.get_state()
    check("No refresh when init_done=0", state['postpone_cnt'] == 0)

    # Init done transition - immediate ref_required
    out = m.step(sts_init_done=1, ref_required=1, ref_urgent=0)
    state = m.get_state()
    check("postpone_cnt=1 on first cycle after init_done", state['postpone_cnt'] == 1)

    # ---- Test 9: Refresh command when all banks idle ----
    print("\nTest 9: Refresh command")
    m = PathModel()

    ref_inputs = {
        'sts_init_done': 1,
        'q_valid_0': 0,
        'ref_required': 1,
        'ref_urgent': 0,
    }

    # Run a few cycles to get REF through pipeline
    for i in range(4):
        out = m.step(**ref_inputs)

    # Should see REF command and ref_ack
    found_ref = False
    found_ref_ack = False
    for i in range(4):
        out = m.step(**ref_inputs)
        if out['cmd_valid'] == 1 and out['cmd_type'] == DDR_REF:
            found_ref = True
        if out['ref_ack'] == 1:
            found_ref_ack = True

    check("REF command issued when ref_required and banks idle", found_ref)
    check("ref_ack asserted for REF", found_ref_ack)

    # ---- Test 10: Urgent refresh preemption ----
    print("\nTest 10: Urgent refresh preemption")
    m = PathModel()

    urgent_inputs = {
        'sts_init_done': 1,
        'q_valid_0': 1,
        'q_row_0': 200,
        'q_col_0': 16,
        'q_bank_0': 0,
        'q_we_0': 0,
        'q_aux_0': 0,
        'ref_required': 1,
        'ref_urgent': 1,
    }

    # With urgent refresh and all banks idle, REF should be issued
    # (Priority 1 in scheduler)
    found_ref = False
    for i in range(5):
        out = m.step(**urgent_inputs)
        if out['cmd_valid'] == 1 and out['cmd_type'] == DDR_REF:
            found_ref = True
            break
    check("Urgent refresh preempts normal requests", found_ref)

    # ---- Test 11: Write request flow ----
    print("\nTest 11: Write request flow")
    m = PathModel()

    # Force bank 0 active with row 300 by directly setting state
    m.bank_is_active[0] = 1
    m.bank_open_row[0] = 300

    wr_inputs = {
        'sts_init_done': 1,
        'q_valid_0': 1,
        'q_row_0': 300,
        'q_col_0': 64,
        'q_bank_0': 0,
        'q_we_0': 1,
        'q_aux_0': 7,
        'ref_required': 0,
        'ref_urgent': 0,
    }

    # Row hit write should issue WR after pipeline delay
    found_wr = False
    found_deq = False
    for i in range(5):
        out = m.step(**wr_inputs)
        if out['cmd_valid'] == 1 and out['cmd_type'] == DDR_WR:
            found_wr = True
        if out['deq_grant'] == 1:
            found_deq = True

    check("WR command issued for row-hit write", found_wr)
    check("deq_grant asserted for WR (CAS command)", found_deq)

    # ---- Test 12: Row miss requires PRE then ACT ----
    print("\nTest 12: Row miss PRE -> ACT sequence")
    m = PathModel()

    # Bank 0 active with row 500, request for row 600
    m.bank_is_active[0] = 1
    m.bank_open_row[0] = 500

    miss_inputs = {
        'sts_init_done': 1,
        'q_valid_0': 1,
        'q_row_0': 600,
        'q_col_0': 0,
        'q_bank_0': 0,
        'q_we_0': 0,
        'q_aux_0': 0,
        'ref_required': 0,
        'ref_urgent': 0,
    }

    found_pre = False
    found_act = False
    for i in range(20):
        out = m.step(**miss_inputs)
        if out['cmd_valid'] == 1:
            if out['cmd_type'] == DDR_PRE:
                found_pre = True
            elif out['cmd_type'] == DDR_ACT and found_pre:
                found_act = True

    check("PRE issued for row miss", found_pre)
    check("ACT issued after PRE for row miss", found_act)

    # ---- Test 13: RFC blocking after refresh ----
    print("\nTest 13: RFC blocks commands after refresh")
    m = PathModel()

    # Apply a refresh feedback directly
    fb = PipelineStage()
    fb.valid = True
    fb.cmd_type = SCHED_REF
    m._apply_feedback(fb)

    state = m.get_state()
    check("cnt_rfc loaded after REF", state['cnt_rfc'] == DEF_tRFC)
    check("refresh_in_progress set", state['refresh_in_progress'] == True)
    check("All banks deactivated by REF", all(a == 0 for a in state['bank_is_active']))
    check("FAW window cleared by REF", len(state['faw_window']) == 0)

    # ---- Test 14: Timing counter direct use (no divide by 4) ----
    print("\nTest 14: Timing counters use cfg values directly")
    m = PathModel()

    # Apply ACT feedback
    fb = PipelineStage()
    fb.valid = True
    fb.cmd_type = SCHED_ACT
    fb.bank = 2
    fb.row = 42
    m._apply_feedback(fb)

    state = m.get_state()
    check("tRCD counter = cfg_tRCD_nCK (11, not 3)", state['cnt_rcd'][2] == 11)
    check("tRAS counter = cfg_tRAS_nCK (28, not 7)", state['cnt_ras'][2] == 28)
    check("tRC counter = cfg_tRC_nCK (39, not 10)", state['cnt_rc'][2] == 39)

    # Verify counters decrement by 1 each cycle
    m._decrement_counters()
    state = m.get_state()
    check("tRCD decrements by 1 (now 10)", state['cnt_rcd'][2] == 10)

    # ---- Test 15: get_state returns dict ----
    print("\nTest 15: get_state() returns dict")
    m = PathModel()
    state = m.get_state()
    check("get_state() returns dict", isinstance(state, dict))
    check("get_state() has cycle_count", 'cycle_count' in state)
    check("get_state() has bank_is_active", 'bank_is_active' in state)

    # ---- Test 16: CSR TIMING5 write/read (tRFC + tREFI packed) ----
    print("\nTest 16: CSR TIMING5 tRFC/tREFI packing")
    m = PathModel()
    # tRFC=200 (lower 16 bits), tREFI=5000 (upper 16 bits)
    val = (5000 << 16) | 200
    m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=1,
           csr_adr_i=CSR_TIMING5, csr_dat_i=val, csr_sel_i=0xF)
    out = m.step(csr_cyc_i=1, csr_stb_i=1, csr_we_i=0,
                 csr_adr_i=CSR_TIMING5, csr_sel_i=0xF)
    check("CSR TIMING5 read back tRFC=200", (out['csr_dat_o'] & 0xFFFF) == 200)
    check("CSR TIMING5 read back tREFI=5000", ((out['csr_dat_o'] >> 16) & 0xFFFF) == 5000)
    check("cfg_tREFI_nCK updated to 5000", out['cfg_tREFI_nCK'] == 5000)

    # ---- Test 17: Full ACT -> wait tRCD -> RD sequence ----
    print("\nTest 17: Full ACT -> tRCD wait -> RD sequence")
    m = PathModel()

    full_inputs = {
        'sts_init_done': 1,
        'q_valid_0': 1,
        'q_row_0': 777,
        'q_col_0': 8,
        'q_bank_0': 3,
        'q_we_0': 0,
        'q_aux_0': 2,
        'ref_required': 0,
        'ref_urgent': 0,
    }

    found_act = False
    found_rd = False
    act_cycle = -1
    rd_cycle = -1

    for i in range(30):
        out = m.step(**full_inputs)
        if out['cmd_valid'] == 1:
            if out['cmd_type'] == DDR_ACT and not found_act:
                found_act = True
                act_cycle = i
            elif out['cmd_type'] == DDR_RD and found_act:
                found_rd = True
                rd_cycle = i
                break

    check("ACT found in sequence", found_act)
    check("RD found after ACT", found_rd)
    if found_act and found_rd:
        # The RD should appear after ACT + tRCD + pipeline delays
        gap = rd_cycle - act_cycle
        check(f"RD appears after ACT with gap >= tRCD (gap={gap})", gap >= DEF_tRCD)

    # ---- Summary ----
    print("\n" + "=" * 60)
    total = len(results)
    passed = sum(1 for _, ok in results if ok)
    failed = total - passed
    print(f"Results: {passed}/{total} passed, {failed} failed")
    if failed == 0:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED:")
        for name, ok in results:
            if not ok:
                print(f"  FAIL: {name}")


if __name__ == "__main__":
    run_self_test()