from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class SchedulerRefreshChecker(LegalityChecker):
    """
    Legality checker for scheduler + refresh_ctrl stage.
    
    Checks invariants over refresh request handling and DDR command issuance.
    """
    
    INPUT_IFACES = ('refresh_req',)
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')
    
    # Command decode table derived from schema encoding
    # Each entry maps integer code to command name
    CMD_DECODE_TABLE = {
        0b0000: 'MRS',
        0b0001: 'REF',
        0b0010: 'PRE',
        0b0011: 'ACT',
        0b0100: 'WR',
        0b0101: 'RD',
        0b0111: 'NOP',
        0b1111: 'DESL',
    }
    
    # Bank state table: maps state name to boolean (True = active row open)
    BANK_STATE_TABLE = {
        'idle': False,       # No row open (precharged)
        'active': True,      # Row is open
    }
    
    # Commands that change bank state, mapped to resulting state
    BANK_STATE_CHANGE_TABLE = {
        'ACT': 'active',     # Activate opens a row
        'PRE': 'idle',       # Precharge closes a row
    }
    
    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract max_postpone_count from spec
        # Spec path: controller_architecture.refresh_policy.max_postpone_count
        self.max_postpone_count = (
            spec['controller_architecture']['refresh_policy']['max_postpone_count']
        )
        
        # Extract bank count from spec
        # Spec path: controller_architecture.$derived.bank_count
        self.num_banks = spec['controller_architecture']['$derived']['bank_count']
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Bank state tracking: each bank starts idle (precharged)
        # Per JESD79-3, after initialization all banks are precharged
        self.bank_active = [self.BANK_STATE_TABLE['idle']] * self.num_banks
        
        # Refresh request tracking for SCHED_003
        # We track the cumulative number of refresh requests made and serviced
        self.refresh_requests_accumulated = 0
        self.refresh_commands_issued = 0
        
        # Track last observed pending count to detect new refresh requests
        self.last_pending_count = 0
        
        # Store refresh request transactions for violation reporting
        self.refresh_req_txns = []
        
        # Track if we've seen any REF_001 violation already to avoid duplicates
        # for the same starvation event
        self.starvation_reported_at_pending = None
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations found."""
        violations = []
        
        # Dispatch based on interface
        if txn.iface == 'refresh_req':
            violations.extend(self._check_refresh_req(txn))
        elif txn.iface == 'ddr_cmd':
            violations.extend(self._check_ddr_cmd(txn))
        
        return violations
    
    def _check_refresh_req(self, txn: Txn) -> List[Violation]:
        """
        Check refresh request transaction for invariant violations.
        
        REF_001: Check if pending count exceeds max_postpone_count.
        SCHED_003: Track refresh requests for end-of-trace check.
        """
        violations = []
        
        # Extract fields from transaction
        pending = txn.fields.get('pending', 0)
        starve = txn.fields.get('starve', 0)
        
        # Store transaction for potential SCHED_003 reporting
        self.refresh_req_txns.append(txn)
        
        # Track new refresh requests: if pending increased, new requests arrived
        # This models the refresh timer firing and incrementing the pending count
        if pending > self.last_pending_count:
            new_requests = pending - self.last_pending_count
            self.refresh_requests_accumulated += new_requests
        
        self.last_pending_count = pending
        
        # REF_001 check: pending count exceeds max_postpone_count
        # Spec: controller_architecture.refresh_policy.max_postpone_count
        # The pending field represents how many refreshes have been postponed
        if pending > self.max_postpone_count:
            # Only report once per starvation event (same pending level)
            if self.starvation_reported_at_pending != pending:
                violations.append(Violation(
                    rule='refresh_postpone_exceeded',
                    detail=(
                        f'Refresh postpone count {pending} exceeds '
                        f'max_postpone_count {self.max_postpone_count}'
                    ),
                    severity='critical',
                    taxonomy_id='REF_001',
                    txns=[txn]
                ))
                self.starvation_reported_at_pending = pending
        
        # REF_001 also detected via starve flag
        # Spec: error_handling.on_refresh_starvation indicates this is a starvation condition
        # The ref_starve_flag in ERROR_STATUS indicates "Refresh starvation occurred"
        if starve:
            # starve flag being set is an explicit indicator of REF_001
            # Report if we haven't already reported for current pending level
            if self.starvation_reported_at_pending != pending:
                violations.append(Violation(
                    rule='refresh_starvation_flag',
                    detail=(
                        f'Refresh starvation flag asserted '
                        f'(pending count={pending}, max={self.max_postpone_count})'
                    ),
                    severity='critical',
                    taxonomy_id='REF_001',
                    txns=[txn]
                ))
                self.starvation_reported_at_pending = pending
        
        # Reset starvation tracking when pending drops (refresh was serviced)
        if pending < self.max_postpone_count:
            self.starvation_reported_at_pending = None
        
        return violations
    
    def _check_ddr_cmd(self, txn: Txn) -> List[Violation]:
        """
        Check DDR command transaction for invariant violations.
        
        REF_002: REFRESH must not be issued while any bank is active.
        Also updates bank state tracking for ACT/PRE commands.
        """
        violations = []
        
        # Extract command code from transaction
        cmd_code = txn.fields.get('cmd', 0b1111)
        bank = txn.fields.get('bank', 0)
        addr = txn.fields.get('addr', 0)
        
        # Decode command using table
        cmd_name = self.CMD_DECODE_TABLE.get(cmd_code, 'UNKNOWN')
        
        # Handle commands that affect bank state
        if cmd_name in self.BANK_STATE_CHANGE_TABLE:
            new_state = self.BANK_STATE_CHANGE_TABLE[cmd_name]
            
            if cmd_name == 'ACT':
                # ACTIVATE: opens a row in the specified bank
                self.bank_active[bank] = self.BANK_STATE_TABLE[new_state]
            
            elif cmd_name == 'PRE':
                # PRECHARGE: closes row(s)
                # Per JESD79-3, A10 high means precharge all banks
                a10_bit = (addr >> 10) & 0x1
                
                if a10_bit:
                    # Precharge all banks
                    for i in range(self.num_banks):
                        self.bank_active[i] = self.BANK_STATE_TABLE[new_state]
                else:
                    # Precharge single bank specified by bank field
                    self.bank_active[bank] = self.BANK_STATE_TABLE[new_state]
        
        elif cmd_name == 'REF':
            # REFRESH command
            # REF_002 check: REFRESH must not be issued while any bank is active
            # Per JESD79-3, all banks must be precharged before REFRESH
            active_banks = [
                i for i in range(self.num_banks) 
                if self.bank_active[i] == self.BANK_STATE_TABLE['active']
            ]
            
            if active_banks:
                violations.append(Violation(
                    rule='refresh_with_active_banks',
                    detail=(
                        f'REFRESH issued while bank(s) {active_banks} '
                        f'still have active rows (not precharged)'
                    ),
                    severity='major',
                    taxonomy_id='REF_002',
                    txns=[txn]
                ))
            
            # Track that a refresh command was issued (for SCHED_003)
            self.refresh_commands_issued += 1
            
            # After valid REFRESH, pending count should decrease
            # Update last_pending_count tracking to reflect serviced refresh
            if self.last_pending_count > 0:
                self.last_pending_count -= 1
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace checks.
        
        SCHED_003: Report if refresh requests were never serviced.
        """
        violations = []
        
        # SCHED_003: Every refresh request must eventually be serviced
        # Compare accumulated requests against issued REFRESH commands
        unserviced = self.refresh_requests_accumulated - self.refresh_commands_issued
        
        if unserviced > 0:
            # Select representative transactions for the violation report
            # Use the most recent refresh_req transactions as they show outstanding state
            representative_txns = self.refresh_req_txns[-min(3, len(self.refresh_req_txns)):]
            
            violations.append(Violation(
                rule='refresh_not_serviced',
                detail=(
                    f'{unserviced} refresh request(s) not serviced by end of trace '
                    f'(total requests={self.refresh_requests_accumulated}, '
                    f'REF commands issued={self.refresh_commands_issued})'
                ),
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=representative_txns
            ))
        
        return violations
