from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class BankSchedulerLegalityChecker(LegalityChecker):
    """Legality checker for bank_tracker + scheduler stage.
    
    Validates DDR3 command protocol invariants related to bank state:
    - PROTO_001: READ/WRITE requires active row in target bank
    - PROTO_002: ACTIVATE requires idle (precharged) bank
    - REF_002: REFRESH requires all banks precharged
    """

    INPUT_IFACES = ('cfg_timing', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('PROTO_001', 'PROTO_002', 'REF_002')

    # Bank state constants
    BANK_IDLE = 0
    BANK_ACTIVE = 1

    def __init__(self, spec: dict):
        self._spec = spec
        
        # Extract number of banks from spec memory_geometry.bank_bits
        # Per spec: "bank_bits": 3 means 2^3 = 8 banks
        bank_bits = spec['memory_geometry']['bank_bits']
        self._num_banks = 1 << bank_bits  # 2^bank_bits
        
        # Command type encoding table - derived from provided encoding
        # This is the authoritative mapping from command type field values
        self._cmd_type_table = {
            0: 'NOP',
            1: 'ACT',
            2: 'RD',
            3: 'WR',
            4: 'PRE',
            5: 'REF'
        }
        
        # Table defining which commands require bank to be ACTIVE
        # Per JESD79-3: READ and WRITE commands require an active (open) row
        self._requires_active_bank = {
            'NOP': False,
            'ACT': False,  # ACT requires IDLE, not active
            'RD': True,    # JESD79-3: READ to open row
            'WR': True,    # JESD79-3: WRITE to open row
            'PRE': False,  # PRE can be issued to active or idle bank
            'REF': False   # REF operates on all banks
        }
        
        # Table defining which commands require bank to be IDLE
        # Per JESD79-3: ACTIVATE requires bank to be precharged (idle)
        self._requires_idle_bank = {
            'NOP': False,
            'ACT': True,   # JESD79-3: ACTIVATE to precharged bank only
            'RD': False,
            'WR': False,
            'PRE': False,  # PRE is valid to active bank, NOP to idle per JEDEC
            'REF': False   # REF checks all banks separately
        }
        
        # Table defining bank state transitions
        # Key: (current_state, command) -> new_state or None (no change)
        self._state_transition_table = {
            (self.BANK_IDLE, 'NOP'): None,
            (self.BANK_IDLE, 'ACT'): self.BANK_ACTIVE,
            (self.BANK_IDLE, 'RD'): None,   # Violation case - handled separately
            (self.BANK_IDLE, 'WR'): None,   # Violation case - handled separately
            (self.BANK_IDLE, 'PRE'): self.BANK_IDLE,  # JEDEC: PRE to idle is NOP
            (self.BANK_IDLE, 'REF'): self.BANK_IDLE,
            (self.BANK_ACTIVE, 'NOP'): None,
            (self.BANK_ACTIVE, 'ACT'): None,  # Violation case - handled separately
            (self.BANK_ACTIVE, 'RD'): self.BANK_ACTIVE,
            (self.BANK_ACTIVE, 'WR'): self.BANK_ACTIVE,
            (self.BANK_ACTIVE, 'PRE'): self.BANK_IDLE,
            (self.BANK_ACTIVE, 'REF'): None,  # Violation case - handled separately
        }
        
        # Initialize bank state tracking
        self._bank_state = None
        self._bank_active_row = None
        
        self.reset()

    def reset(self) -> None:
        """Return all tracked state to power-on.
        
        Per JESD79-3 Section 4.1: After power-on and initialization,
        all banks are in the precharged (idle) state.
        """
        # All banks start in IDLE (precharged) state after init
        self._bank_state = [self.BANK_IDLE] * self._num_banks
        # Track which row is active in each bank (None if idle)
        self._bank_active_row = [None] * self._num_banks

    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations.
        
        Only sched_cmd transactions with kind 'command' affect bank state.
        cfg_timing and refresh_req are informational inputs that don't
        directly cause protocol violations in this checker's scope.
        """
        violations = []
        
        # Only process sched_cmd interface with command kind
        if txn.iface != 'sched_cmd':
            # cfg_timing and refresh_req don't directly cause violations
            # per the invariants we're checking
            return violations
        
        if txn.kind != 'command':
            return violations
        
        # Extract command fields from transaction
        cmd_type_val = txn.fields.get('type')
        bank = txn.fields.get('bank')
        row = txn.fields.get('row')
        
        # Validate we have the required fields
        if cmd_type_val is None:
            return violations
        
        # Map command type value to name using table
        cmd_name = self._cmd_type_table.get(cmd_type_val)
        if cmd_name is None:
            # Unknown command type - not a violation we check
            return violations
        
        # NOP commands don't affect bank state and can't violate protocol
        if cmd_name == 'NOP':
            return violations
        
        # REF command - check REF_002 (all banks must be idle)
        if cmd_name == 'REF':
            violations.extend(self._check_refresh(txn))
            # After REF, all banks remain idle (REF only valid when all idle)
            # No state change needed since we only issue REF when all idle
            return violations
        
        # For bank-specific commands, validate bank field
        if bank is None:
            return violations
        
        if bank < 0 or bank >= self._num_banks:
            # Invalid bank number - out of scope for these invariants
            return violations
        
        current_state = self._bank_state[bank]
        
        # Check PROTO_001: RD/WR to idle bank
        if self._requires_active_bank.get(cmd_name, False):
            if current_state == self.BANK_IDLE:
                violations.append(Violation(
                    rule='command_to_idle_bank',
                    detail=f'{cmd_name} issued to bank {bank} which has no active row',
                    severity='major',
                    taxonomy_id='PROTO_001',
                    txns=[txn]
                ))
        
        # Check PROTO_002: ACT to already-active bank
        if self._requires_idle_bank.get(cmd_name, False):
            if current_state == self.BANK_ACTIVE:
                active_row = self._bank_active_row[bank]
                violations.append(Violation(
                    rule='double_activate',
                    detail=f'ACTIVATE issued to bank {bank} which already has row {active_row} active without intervening PRECHARGE',
                    severity='critical',
                    taxonomy_id='PROTO_002',
                    txns=[txn]
                ))
        
        # Apply state transition (even if violation occurred, track intended state)
        # This ensures we track the actual commands issued, not what should have been
        new_state = self._state_transition_table.get((current_state, cmd_name))
        
        if cmd_name == 'ACT':
            # ACT opens a row regardless of prior state (violation already reported)
            self._bank_state[bank] = self.BANK_ACTIVE
            self._bank_active_row[bank] = row
        elif cmd_name == 'PRE':
            # PRE closes the bank
            self._bank_state[bank] = self.BANK_IDLE
            self._bank_active_row[bank] = None
        elif new_state is not None:
            self._bank_state[bank] = new_state
            if new_state == self.BANK_IDLE:
                self._bank_active_row[bank] = None
        
        return violations

    def _check_refresh(self, txn: Txn) -> List[Violation]:
        """Check REF_002: REFRESH requires all banks to be precharged.
        
        Per JESD79-3 Section 4.13: The REFRESH command requires that
        all banks be in the precharged state before it is issued.
        """
        violations = []
        
        # Find all active banks
        active_banks = []
        for bank_idx in range(self._num_banks):
            if self._bank_state[bank_idx] == self.BANK_ACTIVE:
                active_banks.append(bank_idx)
        
        if active_banks:
            # Build detail string listing which banks are active
            if len(active_banks) == 1:
                banks_str = f'bank {active_banks[0]} is still active'
            else:
                banks_list = ', '.join(str(b) for b in active_banks)
                banks_str = f'banks {banks_list} are still active'
            
            violations.append(Violation(
                rule='refresh_during_active',
                detail=f'REFRESH issued while {banks_str} (not precharged)',
                severity='major',
                taxonomy_id='REF_002',
                txns=[txn]
            ))
        
        return violations

    def final(self) -> List[Violation]:
        """End-of-trace rules.
        
        For this checker's scope (PROTO_001, PROTO_002, REF_002),
        there are no end-of-trace invariants. These invariants are
        all checked at command issue time, not at trace completion.
        
        Bank state at end of trace is not constrained by these invariants.
        """
        # No end-of-trace violations for the invariants we're checking
        # PROTO_001, PROTO_002, REF_002 are all checked at command time
        return []
