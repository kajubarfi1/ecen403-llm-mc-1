from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import field
from typing import List, Dict, Optional


class BankProtocolChecker(LegalityChecker):
    """Checks DDR3 bank state protocol invariants.
    
    Tracks bank open/closed state and active rows to detect:
    - PROTO_001: READ/WRITE to idle bank (no active row)
    - PROTO_002: ACTIVATE to already-active bank (double activate)
    - REF_002: REFRESH while any bank is active
    """
    
    INPUT_IFACES = ()
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('PROTO_001', 'PROTO_002', 'REF_002')
    
    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract bank count from spec
        self.num_banks = 1 << spec['memory_geometry']['bank_bits']
        
        # Command encoding from spec
        self.CMD_MRS = 0b0000
        self.CMD_REF = 0b0001
        self.CMD_PRE = 0b0010
        self.CMD_ACT = 0b0011
        self.CMD_WR = 0b0100
        self.CMD_RD = 0b0101
        self.CMD_NOP = 0b0111
        self.CMD_DESL = 0b1111
        
        # Bank state tracking: None means idle, integer means active row
        self.bank_active_row: Dict[int, Optional[int]] = {}
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # All banks start idle (no active row)
        self.bank_active_row = {b: None for b in range(self.num_banks)}
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and check for violations."""
        violations = []
        
        # Only process ddr_cmd transactions
        if txn.iface != 'ddr_cmd':
            return violations
        
        cmd = txn.fields.get('cmd')
        bank = txn.fields.get('bank')
        addr = txn.fields.get('addr')
        
        if cmd is None:
            return violations
        
        # Handle ACTIVATE command
        if cmd == self.CMD_ACT:
            if bank is not None and 0 <= bank < self.num_banks:
                if self.bank_active_row[bank] is not None:
                    # PROTO_002: Double activate - bank already has active row
                    violations.append(Violation(
                        rule="PROTO_002",
                        detail=f"ACTIVATE to bank {bank} which already has active row {self.bank_active_row[bank]}",
                        severity="critical",
                        taxonomy_id="PROTO_002",
                        txns=[txn]
                    ))
                # Track the new active row (addr carries the row address for ACT)
                self.bank_active_row[bank] = addr
        
        # Handle PRECHARGE command
        elif cmd == self.CMD_PRE:
            if bank is not None:
                # Check if this is precharge all (typically addr[10] == 1)
                # For DDR3, A10 high means precharge all banks
                is_precharge_all = addr is not None and (addr & (1 << 10)) != 0
                
                if is_precharge_all:
                    # Close all banks
                    for b in range(self.num_banks):
                        self.bank_active_row[b] = None
                elif 0 <= bank < self.num_banks:
                    # Close specific bank
                    self.bank_active_row[bank] = None
        
        # Handle READ command
        elif cmd == self.CMD_RD:
            if bank is not None and 0 <= bank < self.num_banks:
                if self.bank_active_row[bank] is None:
                    # PROTO_001: READ to idle bank
                    violations.append(Violation(
                        rule="PROTO_001",
                        detail=f"READ issued to bank {bank} with no active row",
                        severity="major",
                        taxonomy_id="PROTO_001",
                        txns=[txn]
                    ))
        
        # Handle WRITE command
        elif cmd == self.CMD_WR:
            if bank is not None and 0 <= bank < self.num_banks:
                if self.bank_active_row[bank] is None:
                    # PROTO_001: WRITE to idle bank
                    violations.append(Violation(
                        rule="PROTO_001",
                        detail=f"WRITE issued to bank {bank} with no active row",
                        severity="major",
                        taxonomy_id="PROTO_001",
                        txns=[txn]
                    ))
        
        # Handle REFRESH command
        elif cmd == self.CMD_REF:
            # Check if any bank is still active
            active_banks = [b for b, row in self.bank_active_row.items() if row is not None]
            if active_banks:
                # REF_002: Refresh while banks are active
                violations.append(Violation(
                    rule="REF_002",
                    detail=f"REFRESH issued while banks {active_banks} are still active",
                    severity="major",
                    taxonomy_id="REF_002",
                    txns=[txn]
                ))
            # After refresh, all banks are in precharged state
            # (This is implicit in DDR3 - refresh requires all banks precharged)
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace checks. No liveness requirements for this checker."""
        # This checker only validates protocol invariants during command stream
        # No end-of-trace requirements for bank state tracking
        return []
