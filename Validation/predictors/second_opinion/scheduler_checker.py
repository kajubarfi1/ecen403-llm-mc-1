from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class SchedulerLegalityChecker(LegalityChecker):
    """
    Legality checker for the scheduler stage.
    
    Detects violations of:
    - SCHED_003: Refresh request must be serviced before end of trace
    - REF_001: Refresh postpone count exceeded max_postpone_count
    - REF_002: REFRESH issued while one or more banks are still active
    """
    
    INPUT_IFACES = ('refresh_req', 'refresh_level')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')
    
    # Command type encoding table derived from schema
    CMD_TYPE_TABLE = {
        'NOP': 0,
        'ACT': 1,
        'RD': 2,
        'WR': 3,
        'PRE': 4,
        'REF': 5,
    }
    
    # Reverse lookup table
    CMD_TYPE_NAME_TABLE = {v: k for k, v in CMD_TYPE_TABLE.items()}
    
    def __init__(self, spec: dict):
        """
        Initialize checker with spec-derived constants.
        
        Per spec: controller_architecture.refresh_policy.max_postpone_count
        Per spec: memory_geometry.bank_bits determines bank_count
        """
        self._spec = spec
        
        # Extract max_postpone_count from spec
        # Spec path: controller_architecture.refresh_policy.max_postpone_count
        refresh_policy = spec['controller_architecture']['refresh_policy']
        self._max_postpone_count = refresh_policy['max_postpone_count']
        
        # Extract bank count from spec
        # Spec path: memory_geometry.bank_bits -> bank_count = 2^bank_bits
        bank_bits = spec['memory_geometry']['bank_bits']
        self._bank_count = 1 << bank_bits
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Bank state tracking: True = active (row open), False = precharged (idle)
        # Per JEDEC DDR3, all banks start precharged after power-on/reset
        self._bank_active = [False] * self._bank_count
        
        # Track which row is active in each bank (only valid when bank is active)
        self._bank_open_row = [None] * self._bank_count
        
        # Track whether a refresh request has been observed
        # Per SCHED_003: count requests only on refresh_req.request
        self._refresh_request_seen = False
        
        # Track whether a REFRESH command has been issued after request
        # Per SCHED_003: count service only on REFRESH commands
        self._refresh_issued_after_request = False
        
        # Store transactions for violation reporting
        self._refresh_request_txn = None
    
    def observe(self, txn: Txn) -> List[Violation]:
        """
        Consume one observed transaction and return any violations.
        
        Dispatches to handler based on interface name.
        """
        violations = []
        
        # Dispatch table for transaction handling
        handler_table = {
            'refresh_req': self._handle_refresh_req,
            'refresh_level': self._handle_refresh_level,
            'sched_cmd': self._handle_sched_cmd,
        }
        
        handler = handler_table.get(txn.iface)
        if handler is not None:
            violations.extend(handler(txn))
        
        return violations
    
    def _handle_refresh_req(self, txn: Txn) -> List[Violation]:
        """
        Handle refresh_req transaction.
        
        Per SCHED_003: refresh_req.request is the event that starts the
        "must be serviced" obligation. This is the rising edge of ref_required.
        """
        # Per schema: refresh_req has kind 'request' with fields urgent, pending, starve
        # The presence of this transaction indicates a refresh request event
        if txn.kind == 'request':
            self._refresh_request_seen = True
            self._refresh_request_txn = txn
            # Reset the serviced flag - a new request needs to be serviced
            self._refresh_issued_after_request = False
        
        return []
    
    def _handle_refresh_level(self, txn: Txn) -> List[Violation]:
        """
        Handle refresh_level transaction.
        
        Per REF_001: Judged on refresh_level.state - violation when
        pending > max_postpone_count, or when starve = 1.
        
        Per spec: "A count equal to max_postpone_count is legal (the design
        saturates there)."
        """
        violations = []
        
        if txn.kind != 'state':
            return violations
        
        # Extract fields from transaction
        pending = txn.fields.get('pending')
        starve = txn.fields.get('starve')
        
        # Check for REF_001 violation conditions
        # Condition 1: pending > max_postpone_count
        if pending is not None and pending > self._max_postpone_count:
            violations.append(Violation(
                rule='refresh_postpone_exceeded',
                detail=(f'refresh pending count ({pending}) exceeds '
                        f'max_postpone_count ({self._max_postpone_count})'),
                severity='critical',
                taxonomy_id='REF_001',
                txns=[txn]
            ))
        
        # Condition 2: starve = 1
        # Per spec: "or when starve = 1" indicates starvation has occurred
        if starve is not None and starve == 1:
            violations.append(Violation(
                rule='refresh_starve_flag_set',
                detail='refresh starve flag is set (starve=1)',
                severity='critical',
                taxonomy_id='REF_001',
                txns=[txn]
            ))
        
        return violations
    
    def _handle_sched_cmd(self, txn: Txn) -> List[Violation]:
        """
        Handle sched_cmd transaction.
        
        Updates bank state model and checks for REF_002 violations.
        
        Per REF_002: REFRESH issued while one or more banks are still active.
        "State convention: after any REFRESH every bank is treated as precharged
        (idle), legal or not -- a REFRESH issued with a bank open is this
        violation and RESYNCHRONISES the bank model"
        """
        violations = []
        
        if txn.kind != 'command':
            return violations
        
        cmd_type = txn.fields.get('type')
        bank = txn.fields.get('bank')
        row = txn.fields.get('row')
        
        # Command handling dispatch table
        # Per JEDEC79-3: command semantics for bank state transitions
        
        if cmd_type == self.CMD_TYPE_TABLE['ACT']:
            # ACTIVATE: opens a row in a bank
            # Per JEDEC: bank transitions from precharged to active
            if bank is not None:
                self._bank_active[bank] = True
                self._bank_open_row[bank] = row
        
        elif cmd_type == self.CMD_TYPE_TABLE['PRE']:
            # PRECHARGE: closes the active row in a bank
            # Per JEDEC: bank transitions from active to precharged
            if bank is not None:
                self._bank_active[bank] = False
                self._bank_open_row[bank] = None
        
        elif cmd_type == self.CMD_TYPE_TABLE['REF']:
            # REFRESH command
            # First check for REF_002: are any banks active?
            active_banks = [i for i in range(self._bank_count) if self._bank_active[i]]
            
            if active_banks:
                # Per REF_002: violation if REFRESH issued while banks are active
                violations.append(Violation(
                    rule='refresh_during_active_bank',
                    detail=(f'REFRESH issued while bank(s) {active_banks} '
                            f'still active (not precharged)'),
                    severity='major',
                    taxonomy_id='REF_002',
                    txns=[txn]
                ))
            
            # Per spec: "after any REFRESH every bank is treated as precharged"
            # This is the RESYNCHRONISATION mentioned in the spec
            for i in range(self._bank_count):
                self._bank_active[i] = False
                self._bank_open_row[i] = None
            
            # Per SCHED_003: track that refresh was issued
            if self._refresh_request_seen:
                self._refresh_issued_after_request = True
        
        elif cmd_type == self.CMD_TYPE_TABLE['RD']:
            # READ: does not change bank active/precharged state
            # Per JEDEC: bank must remain active for read
            pass
        
        elif cmd_type == self.CMD_TYPE_TABLE['WR']:
            # WRITE: does not change bank active/precharged state
            # Per JEDEC: bank must remain active for write
            pass
        
        elif cmd_type == self.CMD_TYPE_TABLE['NOP']:
            # NOP: no operation, no state change
            pass
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace rules.
        
        Per SCHED_003: "Judged at final(): a violation when a request was seen
        and NO REFRESH was ever issued."
        """
        violations = []
        
        # SCHED_003: Check if refresh request was seen but never serviced
        if self._refresh_request_seen and not self._refresh_issued_after_request:
            txns = []
            if self._refresh_request_txn is not None:
                txns = [self._refresh_request_txn]
            
            violations.append(Violation(
                rule='refresh_never_serviced',
                detail=('refresh request was observed but no REFRESH command '
                        'was issued before end of trace'),
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=txns
            ))
        
        return violations
