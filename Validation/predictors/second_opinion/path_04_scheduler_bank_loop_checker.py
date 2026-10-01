from txn_contract import LegalityChecker, Txn, Violation
from typing import List, Dict, Optional


class BankStateLegalityChecker(LegalityChecker):
    """
    Legality checker for DDR3 command stream bank state invariants.
    
    Tracks bank open/closed state from ACT and PRE commands, and validates
    that RD/WR only occur to active banks, ACT only to idle banks, and
    REF only when all banks are precharged.
    """
    
    INPUT_IFACES = ()
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('PROTO_001', 'PROTO_002', 'REF_002')
    
    def __init__(self, spec: dict):
        self._spec = spec
        
        # Extract geometry from spec per memory_geometry section
        self._num_banks = 1 << spec['memory_geometry']['bank_bits']  # 2^3 = 8 banks
        self._row_bits = spec['memory_geometry']['row_bits']  # 15 bits
        
        # Build command encoding table from the provided encoding
        # Per schema: cmd field uses 4-bit encoding
        self._CMD_TABLE: Dict[int, str] = {
            0b0000: 'MRS',
            0b0001: 'REF',
            0b0010: 'PRE',
            0b0011: 'ACT',
            0b0100: 'WR',
            0b0101: 'RD',
            0b0111: 'NOP',
            0b1111: 'DESL',
        }
        
        # Commands that require an active row per JESD79-3: READ and WRITE
        # Section 4.13 (READ) and 4.14 (WRITE) state the bank must be active
        self._REQUIRES_ACTIVE_ROW = {'RD', 'WR'}
        
        # ACTIVATE requires idle bank per JESD79-3 Section 4.10
        self._ACTIVATE_CMD = 'ACT'
        
        # PRECHARGE closes a bank per JESD79-3 Section 4.12
        self._PRECHARGE_CMD = 'PRE'
        
        # REFRESH requires all banks precharged per JESD79-3 Section 4.15
        self._REFRESH_CMD = 'REF'
        
        # Per JESD79-3, A10 high during PRECHARGE = precharge all banks
        # A10 is bit 10 of the address field
        self._A10_BIT = 10
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on.
        
        Per JESD79-3 Section 4.1, after power-up and initialization,
        all banks start in the precharged (idle) state.
        """
        # Bank state: None means idle/precharged, integer means active with that row open
        self._bank_active_row: List[Optional[int]] = [None] * self._num_banks
        
        # Track transactions for violation reporting
        self._txn_count = 0
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Process one DDR command transaction and check invariants."""
        violations: List[Violation] = []
        self._txn_count += 1
        
        # Only process ddr_cmd interface transactions
        if txn.iface != 'ddr_cmd':
            return violations
        
        # Extract command fields from transaction
        cmd_raw = txn.fields.get('cmd')
        if cmd_raw is None:
            # No command field present - cannot validate
            return violations
        
        # Decode command
        cmd_name = self._CMD_TABLE.get(cmd_raw)
        if cmd_name is None:
            # Unknown command encoding - not our concern per spec
            return violations
        
        # Extract bank and address fields
        bank = txn.fields.get('bank', 0)
        addr = txn.fields.get('addr', 0)
        
        # Validate bank index is in range
        if bank < 0 or bank >= self._num_banks:
            # Out of range bank - not covered by our invariants
            return violations
        
        # Check invariants based on command type using table-driven dispatch
        check_fn = self._COMMAND_CHECKS.get(cmd_name)
        if check_fn is not None:
            violation = check_fn(self, cmd_name, bank, addr, txn)
            if violation is not None:
                violations.append(violation)
        
        # Update bank state based on command
        update_fn = self._STATE_UPDATES.get(cmd_name)
        if update_fn is not None:
            update_fn(self, bank, addr)
        
        return violations
    
    def _check_read_write(self, cmd_name: str, bank: int, addr: int, txn: Txn) -> Optional[Violation]:
        """
        PROTO_001: READ/WRITE issued to a bank that has no active row.
        
        Per JESD79-3 Sections 4.13 (READ) and 4.14 (WRITE):
        A READ or WRITE command can only be issued to a bank that has been
        activated (has an open row).
        """
        if self._bank_active_row[bank] is None:
            return Violation(
                rule='read_write_to_idle_bank',
                detail=f'{cmd_name} command issued to bank {bank} which has no active row',
                severity='major',  # Per failure_taxonomy PROTO_001 severity
                taxonomy_id='PROTO_001',
                txns=[txn]
            )
        return None
    
    def _check_activate(self, cmd_name: str, bank: int, addr: int, txn: Txn) -> Optional[Violation]:
        """
        PROTO_002: ACTIVATE issued to a bank that already has an active row
        without intervening PRECHARGE.
        
        Per JESD79-3 Section 4.10 (ACTIVATE):
        Before a new row can be activated, the previously active row must
        be precharged. An ACTIVATE to an already-active bank is illegal.
        """
        if self._bank_active_row[bank] is not None:
            return Violation(
                rule='double_activate',
                detail=f'ACTIVATE issued to bank {bank} which already has row {self._bank_active_row[bank]} active (attempted row from addr={addr})',
                severity='critical',  # Per failure_taxonomy PROTO_002 severity
                taxonomy_id='PROTO_002',
                txns=[txn]
            )
        return None
    
    def _check_refresh(self, cmd_name: str, bank: int, addr: int, txn: Txn) -> Optional[Violation]:
        """
        REF_002: REFRESH issued while one or more banks are still active.
        
        Per JESD79-3 Section 4.15 (REFRESH):
        All banks must be precharged before a REFRESH command can be issued.
        The REFRESH command applies to all banks.
        """
        active_banks = [b for b in range(self._num_banks) if self._bank_active_row[b] is not None]
        if active_banks:
            return Violation(
                rule='refresh_during_active_bank',
                detail=f'REFRESH issued while banks {active_banks} are still active',
                severity='major',  # Per failure_taxonomy REF_002 severity
                taxonomy_id='REF_002',
                txns=[txn]
            )
        return None
    
    def _update_activate(self, bank: int, addr: int) -> None:
        """
        Update state for ACTIVATE command.
        
        Per JESD79-3 Section 4.10: The ACTIVATE command opens a row.
        The row address is provided on the address pins (addr field).
        """
        # Extract row from address - per spec, addr carries the row for ACT
        # Row bits are the full addr field for ACT per JESD79-3
        row = addr & ((1 << self._row_bits) - 1)
        self._bank_active_row[bank] = row
    
    def _update_precharge(self, bank: int, addr: int) -> None:
        """
        Update state for PRECHARGE command.
        
        Per JESD79-3 Section 4.12: PRECHARGE closes the row in a bank.
        If A10 is high, all banks are precharged; otherwise only the
        specified bank is precharged.
        """
        # Check A10 bit for precharge-all per JESD79-3
        a10_high = (addr >> self._A10_BIT) & 1
        
        if a10_high:
            # Precharge all banks
            for b in range(self._num_banks):
                self._bank_active_row[b] = None
        else:
            # Precharge single bank
            self._bank_active_row[bank] = None
    
    def _update_refresh(self, bank: int, addr: int) -> None:
        """
        Update state for REFRESH command.
        
        Per JESD79-3 Section 4.15: After REFRESH, all banks are in
        the precharged state. Note: we already checked that all banks
        were precharged before the REFRESH (REF_002), but we still
        update state to ensure consistency.
        """
        # REFRESH puts all banks into idle/precharged state
        for b in range(self._num_banks):
            self._bank_active_row[b] = None
    
    # Table-driven command check dispatch
    # Maps command name to check function
    _COMMAND_CHECKS: Dict[str, callable] = {
        'RD': _check_read_write,
        'WR': _check_read_write,
        'ACT': _check_activate,
        'REF': _check_refresh,
    }
    
    # Table-driven state update dispatch
    # Maps command name to state update function
    _STATE_UPDATES: Dict[str, callable] = {
        'ACT': _update_activate,
        'PRE': _update_precharge,
        'REF': _update_refresh,
    }
    
    def final(self) -> List[Violation]:
        """
        End-of-trace checks.
        
        For this checker's scope (PROTO_001, PROTO_002, REF_002), there are
        no end-of-trace invariants to check. Bank state at end of trace is
        not constrained by the spec - banks may remain open.
        """
        return []
