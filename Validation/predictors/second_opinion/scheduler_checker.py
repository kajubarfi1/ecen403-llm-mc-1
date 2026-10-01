from txn_contract import LegalityChecker, Txn, Violation
from typing import List, Dict


class SchedulerLegalityChecker(LegalityChecker):
    """
    Legality checker for scheduler invariants.
    
    Detects violations of:
    - SCHED_003: Refresh requests must eventually be serviced
    - REF_001: Refresh postpone count exceeded max_postpone_count
    - REF_002: REFRESH issued while banks are still active
    """
    
    INPUT_IFACES = ('refresh_req',)
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')
    
    # Command type encoding table - derived from schema
    # Per schema: {"NOP": 0, "ACT": 1, "RD": 2, "WR": 3, "PRE": 4, "REF": 5}
    CMD_TYPE_TABLE: Dict[str, int] = {
        'NOP': 0,
        'ACT': 1,
        'RD': 2,
        'WR': 3,
        'PRE': 4,
        'REF': 5,
    }
    
    # Reverse lookup for command names
    CMD_NAME_TABLE: Dict[int, str] = {v: k for k, v in CMD_TYPE_TABLE.items()}
    
    def __init__(self, spec: dict):
        """
        Initialize checker with spec-derived constants.
        
        Per spec: controller_architecture.refresh_policy.max_postpone_count
        determines the maximum allowed postponed refreshes.
        """
        self.spec = spec
        
        # Extract max_postpone_count from spec
        # Spec path: controller_architecture.refresh_policy.max_postpone_count
        self.max_postpone_count: int = (
            spec['controller_architecture']['refresh_policy']['max_postpone_count']
        )
        
        # Extract bank count from memory geometry
        # Spec path: memory_geometry.bank_bits -> 2^bank_bits banks
        bank_bits: int = spec['memory_geometry']['bank_bits']
        self.num_banks: int = 1 << bank_bits
        
        self.reset()
    
    def reset(self) -> None:
        """
        Return all tracked state to power-on.
        
        Per JESD79-3 Section 4.13, all banks are in precharged (idle) state
        after power-on reset sequence completion.
        """
        # Bank state tracking: False = precharged (idle), True = active (row open)
        # Per JESD79-3, banks start precharged after initialization
        self._bank_active: List[bool] = [False] * self.num_banks
        
        # Track the open row per bank (None if precharged)
        # Used for state consistency, though not directly checked here
        self._bank_open_row: List[int | None] = [None] * self.num_banks
        
        # Refresh request tracking for SCHED_003
        # Count of refresh requests seen (rising edges of pending count)
        self._refresh_requests_observed: int = 0
        # Count of REFRESH commands issued
        self._refresh_commands_serviced: int = 0
        # Previous pending count to detect rising edges
        self._prev_pending_count: int = 0
        # Previous starve flag to detect edge
        self._prev_starve_flag: int = 0
        # Transactions associated with unserviced refresh requests
        self._pending_refresh_txns: List[Txn] = []
        
        # Track if we've seen any starve flag assertion for REF_001
        self._starve_flag_violations: List[Txn] = []
    
    def observe(self, txn: Txn) -> List[Violation]:
        """
        Consume one observed transaction and return any violations.
        
        Dispatches to interface-specific handlers based on txn.iface.
        """
        violations: List[Violation] = []
        
        # Dispatch table for interface handling
        handler_table = {
            'refresh_req': self._observe_refresh_req,
            'sched_cmd': self._observe_sched_cmd,
        }
        
        handler = handler_table.get(txn.iface)
        if handler is not None:
            violations.extend(handler(txn))
        
        return violations
    
    def _observe_refresh_req(self, txn: Txn) -> List[Violation]:
        """
        Handle refresh_req transaction.
        
        Fields per schema:
        - pending: ref_pending_cnt, width 3
        - urgent: ref_urgent, width 1  
        - starve: ref_starve_flag, width 1
        
        REF_001 detection: Per spec failure_taxonomy, refresh starvation occurs
        when "Refresh postpone count exceeded max_postpone_count". The
        ref_starve_flag signal indicates this condition.
        
        SCHED_003 tracking: A refresh request rising edge is detected when
        pending count increases. Each such request must eventually be serviced.
        """
        violations: List[Violation] = []
        
        # Extract fields with defaults per schema (width determines valid range)
        current_pending: int = txn.fields.get('pending', 0)
        current_starve: int = txn.fields.get('starve', 0)
        
        # REF_001: Refresh starvation detection
        # Per spec failure_taxonomy REF_001: "Refresh postpone count exceeded
        # max_postpone_count". The starve flag indicates this violation condition.
        # We also check if pending count itself exceeds max_postpone_count
        # (though with 3-bit width it can only reach 7, starve flag catches overflow).
        
        # Check starve flag assertion (rising edge or held high)
        if current_starve == 1:
            # Starve flag is asserted - this indicates REF_001 violation
            # Per spec: controller_architecture.refresh_policy.max_postpone_count
            violations.append(Violation(
                rule='refresh_starvation',
                detail=(
                    f'Refresh starvation flag asserted; pending count {current_pending} '
                    f'indicates max_postpone_count ({self.max_postpone_count}) exceeded'
                ),
                severity='critical',  # Per failure_taxonomy REF_001 severity
                taxonomy_id='REF_001',
                txns=[txn]
            ))
        
        # Also check if pending count directly exceeds max_postpone_count
        # This is a secondary check in case starve flag is not set but count is high
        if current_pending > self.max_postpone_count:
            violations.append(Violation(
                rule='refresh_postpone_exceeded',
                detail=(
                    f'Refresh pending count {current_pending} exceeds '
                    f'max_postpone_count {self.max_postpone_count}'
                ),
                severity='critical',
                taxonomy_id='REF_001',
                txns=[txn]
            ))
        
        # SCHED_003: Track refresh request rising edges
        # A rising edge of the request stream means pending count increased,
        # indicating new refresh request(s) from the refresh controller.
        if current_pending > self._prev_pending_count:
            # New refresh request(s) detected
            new_requests = current_pending - self._prev_pending_count
            self._refresh_requests_observed += new_requests
            # Record transaction for potential end-of-trace violation
            for _ in range(new_requests):
                self._pending_refresh_txns.append(txn)
        
        # Update previous state for next edge detection
        self._prev_pending_count = current_pending
        self._prev_starve_flag = current_starve
        
        return violations
    
    def _observe_sched_cmd(self, txn: Txn) -> List[Violation]:
        """
        Handle sched_cmd transaction.
        
        Fields per schema:
        - type: cmd_type, width 4
        - bank: cmd_bank, width 3
        - row: cmd_row, width 15
        - col: cmd_col, width 10
        - we: cmd_we, width 1
        - aux: cmd_aux, width 4
        
        Updates bank state tracking and checks REF_002.
        """
        violations: List[Violation] = []
        
        # Extract command type
        cmd_type: int = txn.fields.get('type', self.CMD_TYPE_TABLE['NOP'])
        bank: int = txn.fields.get('bank', 0)
        row: int = txn.fields.get('row', 0)
        
        # Command processing table - maps command type to state updates
        # Per JESD79-3:
        # - ACT (Activate): Opens a row in specified bank
        # - PRE (Precharge): Closes the row in specified bank
        # - REF (Refresh): Requires all banks precharged
        
        cmd_act = self.CMD_TYPE_TABLE['ACT']
        cmd_pre = self.CMD_TYPE_TABLE['PRE']
        cmd_ref = self.CMD_TYPE_TABLE['REF']
        cmd_nop = self.CMD_TYPE_TABLE['NOP']
        
        if cmd_type == cmd_act:
            # ACTIVATE command: bank becomes active with specified row
            # Per JESD79-3, bank transitions from precharged to active
            self._bank_active[bank] = True
            self._bank_open_row[bank] = row
            
        elif cmd_type == cmd_pre:
            # PRECHARGE command: bank becomes precharged
            # Per JESD79-3 Section 4.6, PRECHARGE closes the open row
            # Note: Precharge-all (A10 high) would close all banks, but
            # we only have bank field - handle single bank precharge.
            # If aux field bit indicates precharge-all, handle that.
            # Per schema, aux is 4 bits but encoding not specified.
            # Conservative: treat as single-bank precharge per bank field.
            # Per Wishbone B4, unspecified auxiliary fields should not change
            # core behavior - we follow the bank field.
            self._bank_active[bank] = False
            self._bank_open_row[bank] = None
            
        elif cmd_type == cmd_ref:
            # REFRESH command
            
            # REF_002: Check all banks are precharged before REFRESH
            # Per JESD79-3 Section 4.12, REF command requires all banks
            # to be in the precharged (idle) state.
            # Per failure_taxonomy REF_002: "REFRESH issued while one or
            # more banks are still active (not precharged)."
            active_banks = [i for i in range(self.num_banks) if self._bank_active[i]]
            
            if active_banks:
                violations.append(Violation(
                    rule='refresh_during_active_bank',
                    detail=(
                        f'REFRESH issued while bank(s) {active_banks} '
                        f'are still active (not precharged)'
                    ),
                    severity='major',  # Per failure_taxonomy REF_002 severity
                    taxonomy_id='REF_002',
                    txns=[txn]
                ))
            
            # SCHED_003: Track REFRESH servicing
            # Each REFRESH command services one pending refresh request
            self._refresh_commands_serviced += 1
            
            # Remove one pending request transaction if available
            if self._pending_refresh_txns:
                self._pending_refresh_txns.pop(0)
        
        # NOP, RD, WR commands do not change bank active/precharged state
        # (RD/WR operate on already-active banks)
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace rules: check refresh request servicing completeness.
        
        SCHED_003: Every refresh request (rising edge of the request stream)
        must eventually be serviced with a REFRESH command. Outstanding
        requests at end of trace indicate violation.
        """
        violations: List[Violation] = []
        
        # SCHED_003: Check all refresh requests were serviced
        # Per invariant specification: "Every refresh request (rising edge
        # of the request stream) must eventually be serviced with a REFRESH
        # command."
        unserviced_count = (
            self._refresh_requests_observed - self._refresh_commands_serviced
        )
        
        if unserviced_count > 0:
            violations.append(Violation(
                rule='refresh_request_not_serviced',
                detail=(
                    f'{unserviced_count} refresh request(s) not serviced with '
                    f'REFRESH command (observed: {self._refresh_requests_observed}, '
                    f'serviced: {self._refresh_commands_serviced})'
                ),
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=self._pending_refresh_txns[:3]
            ))
        
        return violations
