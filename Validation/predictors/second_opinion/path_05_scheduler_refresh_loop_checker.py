from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class SchedulerRefreshChecker(LegalityChecker):
    """Legality checker for scheduler + refresh_ctrl stage.
    
    Checks invariants:
    - SCHED_003: Refresh requests must be serviced before trace end
    - REF_001: Refresh postpone count must not exceed max_postpone_count
    - REF_002: REFRESH must not be issued while banks are active
    """
    
    INPUT_IFACES = ('refresh_req', 'refresh_level')
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')
    
    # Command encoding table derived from schema
    CMD_ENCODING = {
        0b0000: 'MRS',
        0b0001: 'REF',
        0b0010: 'PRE',
        0b0011: 'ACT',
        0b0100: 'WR',
        0b0101: 'RD',
        0b0111: 'NOP',
        0b1111: 'DESL',
    }
    
    # A10 bit position for PRECHARGE ALL per JESD79-3
    # In DDR3, A10 high during PRECHARGE indicates precharge all banks
    A10_BIT = 10
    
    def __init__(self, spec: dict):
        """Initialize checker with spec-derived constants."""
        # Extract max_postpone_count from spec
        # Path: controller_architecture.refresh_policy.max_postpone_count
        refresh_policy = spec['controller_architecture']['refresh_policy']
        self._max_postpone_count = refresh_policy['max_postpone_count']
        
        # Derived from memory_geometry.bank_bits
        bank_bits = spec['memory_geometry']['bank_bits']
        self._num_banks = 1 << bank_bits  # 2^bank_bits = 8 banks
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Track whether any refresh request has been seen
        # Per SCHED_003: count requests only on refresh_req.request
        self._refresh_request_seen = False
        
        # Track whether any REFRESH command has been issued
        # Per SCHED_003: count service only on REFRESH commands
        self._refresh_issued = False
        
        # Track bank active states for REF_002
        # Per JESD79-3, banks start in idle (precharged) state after reset
        # True = active (row open), False = idle (precharged)
        self._bank_active = [False] * self._num_banks
        
        # Store transactions for violation reporting
        self._last_refresh_req_txn = None
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and check for violations."""
        violations = []
        
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields
        
        if iface == 'refresh_req' and kind == 'request':
            # Per SCHED_003: refresh_req.request indicates a refresh request
            # This is the rising edge of ref_required
            self._refresh_request_seen = True
            self._last_refresh_req_txn = txn
            
        elif iface == 'refresh_level' and kind == 'state':
            # Per REF_001: Check refresh_level.state for violations
            # Fields: required, urgent, pending, starve
            pending = fields.get('pending', 0)
            starve = fields.get('starve', 0)
            
            # REF_001: Violation when pending > max_postpone_count
            # Per spec: "A count equal to max_postpone_count is legal (the design saturates there)"
            if pending > self._max_postpone_count:
                violations.append(Violation(
                    rule='refresh_postpone_exceeded',
                    detail=f'pending count {pending} exceeds max_postpone_count {self._max_postpone_count}',
                    severity='critical',
                    taxonomy_id='REF_001',
                    txns=[txn]
                ))
            
            # REF_001: Violation when starve = 1
            if starve == 1:
                violations.append(Violation(
                    rule='refresh_starvation_flag',
                    detail=f'starve flag asserted (starve={starve})',
                    severity='critical',
                    taxonomy_id='REF_001',
                    txns=[txn]
                ))
                
        elif iface == 'ddr_cmd' and kind == 'command':
            # Parse command
            cmd_val = fields.get('cmd', 0b1111)  # Default to DESL if missing
            addr = fields.get('addr', 0)
            bank = fields.get('bank', 0)
            
            cmd_name = self.CMD_ENCODING.get(cmd_val, 'UNKNOWN')
            
            if cmd_name == 'ACT':
                # ACTIVATE opens a row in the specified bank
                # Per JESD79-3, bank field specifies which bank
                if 0 <= bank < self._num_banks:
                    self._bank_active[bank] = True
                    
            elif cmd_name == 'PRE':
                # PRECHARGE closes bank(s)
                # Per JESD79-3: A10 high = precharge all banks
                a10_set = (addr >> self.A10_BIT) & 1
                if a10_set:
                    # Precharge all banks
                    self._bank_active = [False] * self._num_banks
                else:
                    # Precharge single bank specified by bank field
                    if 0 <= bank < self._num_banks:
                        self._bank_active[bank] = False
                        
            elif cmd_name == 'REF':
                # REFRESH command
                # Per REF_002: Check if any bank is active
                active_banks = [i for i, active in enumerate(self._bank_active) if active]
                
                if active_banks:
                    # Violation: REFRESH issued while banks are active
                    violations.append(Violation(
                        rule='refresh_during_active_bank',
                        detail=f'REFRESH issued while banks {active_banks} are active',
                        severity='major',
                        taxonomy_id='REF_002',
                        txns=[txn]
                    ))
                
                # Per REF_002 state convention: "after any REFRESH every bank is 
                # treated as precharged (idle), legal or not"
                # This resynchronizes the bank model
                self._bank_active = [False] * self._num_banks
                
                # Track that refresh was issued for SCHED_003
                self._refresh_issued = True
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check SCHED_003."""
        violations = []
        
        # SCHED_003: If a refresh request was seen, at least one REFRESH 
        # command must have been issued before end of trace
        # Per spec: "a violation when a request was seen and NO REFRESH was ever issued"
        if self._refresh_request_seen and not self._refresh_issued:
            txns = []
            if self._last_refresh_req_txn is not None:
                txns.append(self._last_refresh_req_txn)
            violations.append(Violation(
                rule='refresh_never_serviced',
                detail='refresh request seen but no REFRESH command was ever issued',
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=txns
            ))
        
        return violations
