from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set, Tuple


@dataclass
class PendingRequest:
    """Tracks an enqueued request awaiting CAS."""
    row: int
    col: int
    bank: int
    we: int
    txn: Txn


class SchedulerLegalityChecker(LegalityChecker):
    """
    Legality checker for the full command path from host request to DDR pins.
    
    Checks invariants from spec:
    - SCHED_001: Every enqueued request must eventually issue as matching CAS
    - SCHED_002: No CAS may issue without corresponding enqueued request
    - PROTO_001: RD/WR to bank with no active row
    - PROTO_002: ACT to bank that already has active row
    - SCHED_004: CAS must land on row the request asked for
    """
    
    INPUT_IFACES = ('cq_enq',)
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'SCHED_004')
    
    # Command encoding table derived from schema
    CMD_ENCODING = {
        'MRS': 0b0000,
        'REF': 0b0001,
        'PRE': 0b0010,
        'ACT': 0b0011,
        'WR': 0b0100,
        'RD': 0b0101,
        'NOP': 0b0111,
        'DESL': 0b1111,
    }
    
    # Reverse mapping for lookup
    CMD_DECODE = {v: k for k, v in CMD_ENCODING.items()}
    
    # Commands that are CAS operations (per JESD79-3, READ and WRITE are column access)
    CAS_CMDS = frozenset({CMD_ENCODING['RD'], CMD_ENCODING['WR']})
    
    # A10 bit position for precharge-all detection (JESD79-3 Table 2)
    A10_BIT = 10
    
    def __init__(self, spec: dict):
        """Initialize checker from spec."""
        # Extract geometry from spec for validation bounds
        geometry = spec.get('memory_geometry', {})
        self._row_bits = geometry.get('row_bits', 15)
        self._col_bits = geometry.get('column_bits', 10)
        self._bank_bits = geometry.get('bank_bits', 3)
        
        # Derived bank count from spec
        arch = spec.get('controller_architecture', {})
        derived = arch.get('$derived', {})
        self._num_banks = derived.get('bank_count', 1 << self._bank_bits)
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Bank state: None means idle (no active row), int means row number open
        # Per JESD79-3, banks start in idle (precharged) state after power-on
        self._bank_open_row: Dict[int, Optional[int]] = {
            b: None for b in range(self._num_banks)
        }
        
        # Pending requests: list of requests awaiting CAS
        # Keyed by (bank, col, we) for matching, but row matters for SCHED_004
        self._pending_requests: List[PendingRequest] = []
        
        # Track all observed transactions for violation reporting
        self._txn_count = 0
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any rule violations."""
        self._txn_count += 1
        violations = []
        
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields
        
        if iface == 'cq_enq' and kind == 'enqueue':
            # Input: request entering command queue
            violations.extend(self._handle_enqueue(txn, fields))
        elif iface == 'ddr_cmd' and kind == 'command':
            # Output: DDR command on pins
            violations.extend(self._handle_ddr_cmd(txn, fields))
        
        return violations
    
    def _handle_enqueue(self, txn: Txn, fields: dict) -> List[Violation]:
        """Handle request enqueue - track for later matching."""
        row = fields.get('row', 0)
        col = fields.get('col', 0)
        bank = fields.get('bank', 0)
        we = fields.get('we', 0)
        
        # Record pending request
        req = PendingRequest(row=row, col=col, bank=bank, we=we, txn=txn)
        self._pending_requests.append(req)
        
        return []
    
    def _handle_ddr_cmd(self, txn: Txn, fields: dict) -> List[Violation]:
        """Handle DDR command - check protocol and request matching."""
        violations = []
        
        cmd = fields.get('cmd', self.CMD_ENCODING['NOP'])
        addr = fields.get('addr', 0)
        bank = fields.get('bank', 0)
        
        cmd_name = self.CMD_DECODE.get(cmd, 'UNKNOWN')
        
        if cmd == self.CMD_ENCODING['ACT']:
            violations.extend(self._handle_activate(txn, bank, addr))
        elif cmd == self.CMD_ENCODING['PRE']:
            violations.extend(self._handle_precharge(txn, bank, addr))
        elif cmd == self.CMD_ENCODING['REF']:
            # REFRESH: per JESD79-3, all banks must be precharged
            # This is REF_002 in spec but not in our COVERS, so we don't check it here
            # After refresh all banks remain precharged (JESD79-3 Section 4.11)
            pass
        elif cmd in self.CAS_CMDS:
            violations.extend(self._handle_cas(txn, cmd, bank, addr))
        # NOP, DESL, MRS: no bank state changes relevant to our invariants
        
        return violations
    
    def _handle_activate(self, txn: Txn, bank: int, row_addr: int) -> List[Violation]:
        """
        Handle ACTIVATE command.
        
        PROTO_002: ACTIVATE to bank that already has active row is illegal.
        Per JESD79-3 Table 2, ACT opens row_addr in the specified bank.
        """
        violations = []
        
        current_row = self._bank_open_row.get(bank)
        
        if current_row is not None:
            # Bank already has an active row - PROTO_002 violation
            # Per spec: "ACTIVATE issued to a bank that already has an active row
            # without intervening PRECHARGE"
            violations.append(Violation(
                rule='double_activate',
                detail=f'ACT to bank {bank} which already has row {current_row} active; '
                       f'new row {row_addr}',
                severity='critical',
                taxonomy_id='PROTO_002',
                txns=[txn]
            ))
        
        # Update bank state: row is now open
        # Per JESD79-3, the row address on the address pins becomes the active row
        self._bank_open_row[bank] = row_addr
        
        return violations
    
    def _handle_precharge(self, txn: Txn, bank: int, addr: int) -> List[Violation]:
        """
        Handle PRECHARGE command.
        
        Per JESD79-3 Section 4.10 and Table 2:
        - If A10 is HIGH: precharge all banks (PREA)
        - If A10 is LOW: precharge only the addressed bank
        
        The spec explicitly states: "A PRECHARGE closes only the addressed bank
        unless address bit A10 is set (JESD79-3 precharge-all); the bank number
        never means 'all banks'."
        """
        # Check A10 for precharge-all (JESD79-3 Section 4.10)
        a10_set = (addr >> self.A10_BIT) & 1
        
        if a10_set:
            # Precharge all banks
            for b in range(self._num_banks):
                self._bank_open_row[b] = None
        else:
            # Precharge only specified bank
            self._bank_open_row[bank] = None
        
        return []
    
    def _handle_cas(self, txn: Txn, cmd: int, bank: int, col_addr: int) -> List[Violation]:
        """
        Handle CAS command (READ or WRITE).
        
        PROTO_001: RD/WR to bank with no active row is illegal.
        SCHED_002: CAS with no matching enqueued request is illegal.
        SCHED_004: CAS must land on the row the request asked for.
        
        Per stage note: "A CAS matches an enqueued request when its bank matches,
        the DDR addr carries the request's col, the command direction matches we,
        and the bank's open row (set by the preceding ACT's addr) is the request's row."
        """
        violations = []
        
        is_write = (cmd == self.CMD_ENCODING['WR'])
        cmd_name = 'WR' if is_write else 'RD'
        expected_we = 1 if is_write else 0
        
        current_row = self._bank_open_row.get(bank)
        
        # PROTO_001: Check bank is active
        if current_row is None:
            # Per spec: "READ/WRITE issued to a bank that has no active row"
            violations.append(Violation(
                rule='cas_to_idle_bank',
                detail=f'{cmd_name} to bank {bank} which has no active row',
                severity='major',
                taxonomy_id='PROTO_001',
                txns=[txn]
            ))
            # Cannot match request if bank is idle - also report SCHED_002
            # But we should still try to find a matching request to consume it
        
        # Find matching request
        # Match criteria from stage note:
        # - bank matches
        # - addr carries col
        # - command direction matches we
        # - bank's open row matches request's row (for SCHED_004)
        
        match_idx = None
        wrong_row_match_idx = None
        wrong_row_request = None
        
        for idx, req in enumerate(self._pending_requests):
            if req.bank != bank:
                continue
            if req.col != col_addr:
                continue
            if req.we != expected_we:
                continue
            
            # Found a request matching bank, col, direction
            # Check if row matches what's open
            if current_row is not None and req.row == current_row:
                # Perfect match
                match_idx = idx
                break
            elif current_row is not None:
                # Row mismatch - potential SCHED_004
                # Keep looking for exact match, but remember this
                if wrong_row_match_idx is None:
                    wrong_row_match_idx = idx
                    wrong_row_request = req
            elif current_row is None:
                # Bank is idle (PROTO_001 already reported)
                # Still try to consume the request
                if wrong_row_match_idx is None:
                    wrong_row_match_idx = idx
                    wrong_row_request = req
        
        if match_idx is not None:
            # Perfect match found - consume the request
            self._pending_requests.pop(match_idx)
        elif wrong_row_match_idx is not None:
            # Found request matching bank/col/we but wrong row
            req = wrong_row_request
            
            if current_row is not None:
                # SCHED_004: CAS landed on wrong row
                # Per spec: "when the CAS for a request issues, the row open in
                # that bank (set by the most recent ACTIVATE to it) must be the
                # request's row"
                violations.append(Violation(
                    rule='cas_wrong_row',
                    detail=f'{cmd_name} to bank {bank} col {col_addr}: open row is '
                           f'{current_row} but request asked for row {req.row}',
                    severity='critical',
                    taxonomy_id='SCHED_004',
                    txns=[txn, req.txn]
                ))
            
            # Consume the request even though it violated SCHED_004
            self._pending_requests.pop(wrong_row_match_idx)
        else:
            # SCHED_002: No matching request found at all
            # Per spec: "No CAS may issue that corresponds to no enqueued request"
            violations.append(Violation(
                rule='cas_no_request',
                detail=f'{cmd_name} to bank {bank} col {col_addr} has no matching '
                       f'enqueued request',
                severity='critical',
                taxonomy_id='SCHED_002',
                txns=[txn]
            ))
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace rules.
        
        SCHED_001: Every enqueued request must eventually issue as matching CAS.
        Outstanding requests at end of trace are violations.
        """
        violations = []
        
        # SCHED_001: Check for outstanding requests
        # Per spec: "Outstanding requests at end of trace are dropped"
        # This means they are violations that should be reported
        for req in self._pending_requests:
            direction = 'WRITE' if req.we else 'READ'
            violations.append(Violation(
                rule='request_not_serviced',
                detail=f'{direction} request to bank {req.bank} row {req.row} '
                       f'col {req.col} never issued as CAS',
                severity='critical',
                taxonomy_id='SCHED_001',
                txns=[req.txn]
            ))
        
        return violations
