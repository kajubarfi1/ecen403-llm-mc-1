from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from collections import defaultdict


@dataclass
class PendingRequest:
    """Tracks an enqueued request awaiting CAS completion."""
    row: int
    col: int
    bank: int
    we: int
    txn: Txn


class CmdQueueSchedulerChecker(LegalityChecker):
    """Legality checker for DDR3 command queue + scheduler stage.
    
    Validates invariants over the command stream without predicting
    exact ordering, since FR-FCFS scheduling permits multiple legal orderings.
    """
    
    INPUT_IFACES: tuple = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES: tuple = ('sched_cmd',)
    COVERS: tuple = (
        'SCHED_001',
        'SCHED_002', 
        'PROTO_001',
        'PROTO_002',
        'REF_002',
        'SCHED_004',
    )
    
    # Command type encoding
    CMD_NOP = 0
    CMD_ACT = 1
    CMD_RD = 2
    CMD_WR = 3
    CMD_PRE = 4
    CMD_REF = 5
    
    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract geometry from spec
        geometry = spec.get('memory_geometry', {})
        self.num_banks = 1 << geometry.get('bank_bits', 3)
        self.row_bits = geometry.get('row_bits', 15)
        self.col_bits = geometry.get('column_bits', 10)
        
        # Extract controller architecture settings
        arch = spec.get('controller_architecture', {})
        self.queue_depth = arch.get('command_queue_depth', 16)
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Pending requests: list of PendingRequest objects
        # Multiple requests can target same (bank, row, col) with different we
        self.pending_requests: List[PendingRequest] = []
        
        # Bank state tracking: bank_id -> (is_active, open_row or None)
        self.bank_state: Dict[int, Tuple[bool, Optional[int]]] = {
            b: (False, None) for b in range(self.num_banks)
        }
        
        # Track all CAS commands for SCHED_002 matching
        self.issued_cas_without_match: List[Txn] = []
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []
        
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields
        
        if iface == 'cq_enq' and kind == 'enqueue':
            violations.extend(self._handle_enqueue(txn, fields))
        elif iface == 'refresh_req' and kind == 'request':
            # Refresh requests are informational; no direct violations
            pass
        elif iface == 'sched_cmd' and kind == 'command':
            violations.extend(self._handle_command(txn, fields))
        
        return violations
    
    def _handle_enqueue(self, txn: Txn, fields: dict) -> List[Violation]:
        """Handle a request enqueue into the command queue."""
        row = fields.get('row', 0)
        col = fields.get('col', 0)
        bank = fields.get('bank', 0)
        we = fields.get('we', 0)
        
        # Add to pending requests
        self.pending_requests.append(PendingRequest(
            row=row, col=col, bank=bank, we=we, txn=txn
        ))
        
        return []
    
    def _handle_command(self, txn: Txn, fields: dict) -> List[Violation]:
        """Handle an issued scheduler command."""
        violations = []
        
        cmd_type = fields.get('type', 0)
        bank = fields.get('bank', 0)
        row = fields.get('row', 0)
        col = fields.get('col', 0)
        we = fields.get('we', 0)
        
        if cmd_type == self.CMD_NOP:
            # NOP commands have no protocol implications
            pass
        
        elif cmd_type == self.CMD_ACT:
            # PROTO_002: ACTIVATE to bank that already has active row
            is_active, _ = self.bank_state.get(bank, (False, None))
            if is_active:
                violations.append(Violation(
                    rule='double_activate',
                    detail=f'ACTIVATE to bank {bank} which already has active row',
                    severity='critical',
                    taxonomy_id='PROTO_002',
                    txns=[txn]
                ))
            
            # Update bank state: now active with this row
            self.bank_state[bank] = (True, row)
        
        elif cmd_type == self.CMD_RD or cmd_type == self.CMD_WR:
            # This is a CAS command (column access)
            is_read = (cmd_type == self.CMD_RD)
            expected_we = 0 if is_read else 1
            
            # PROTO_001: CAS to bank with no active row
            is_active, open_row = self.bank_state.get(bank, (False, None))
            if not is_active:
                violations.append(Violation(
                    rule='cas_to_idle_bank',
                    detail=f'{"READ" if is_read else "WRITE"} to bank {bank} with no active row',
                    severity='major',
                    taxonomy_id='PROTO_001',
                    txns=[txn]
                ))
            
            # Find matching pending request
            # Match on bank, col, and we (read vs write)
            matching_req = None
            matching_idx = None
            
            for idx, req in enumerate(self.pending_requests):
                if req.bank == bank and req.col == col and req.we == expected_we:
                    # Found a potential match
                    matching_req = req
                    matching_idx = idx
                    break
            
            if matching_req is None:
                # SCHED_002: CAS with no matching enqueued request
                violations.append(Violation(
                    rule='cas_without_request',
                    detail=f'{"RD" if is_read else "WR"} to bank={bank} col={col} has no matching enqueued request',
                    severity='critical',
                    taxonomy_id='SCHED_002',
                    txns=[txn]
                ))
            else:
                # SCHED_004: CAS must execute against the row the request asked for
                if is_active and open_row is not None:
                    if open_row != matching_req.row:
                        violations.append(Violation(
                            rule='cas_wrong_row',
                            detail=f'{"RD" if is_read else "WR"} issued with open row {open_row} but request asked for row {matching_req.row}',
                            severity='critical',
                            taxonomy_id='SCHED_004',
                            txns=[txn, matching_req.txn]
                        ))
                
                # Remove matched request from pending
                self.pending_requests.pop(matching_idx)
        
        elif cmd_type == self.CMD_PRE:
            # PRECHARGE: close the bank
            # No specific violation checks for precharge itself in our covered list
            self.bank_state[bank] = (False, None)
        
        elif cmd_type == self.CMD_REF:
            # REF_002: REFRESH while banks are active
            active_banks = [b for b, (active, _) in self.bank_state.items() if active]
            if active_banks:
                violations.append(Violation(
                    rule='refresh_during_active',
                    detail=f'REFRESH issued while banks {active_banks} are still active',
                    severity='major',
                    taxonomy_id='REF_002',
                    txns=[txn]
                ))
            
            # After refresh, all banks remain in their precharged state
            # (REFRESH requires all banks precharged per DDR3 protocol)
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check for outstanding requests (starvation)."""
        violations = []
        
        # SCHED_001: Every enqueued request must eventually issue as CAS
        # Outstanding requests at end of trace are dropped requests
        for req in self.pending_requests:
            violations.append(Violation(
                rule='request_not_serviced',
                detail=f'Request to bank={req.bank} row={req.row} col={req.col} we={req.we} was never issued as CAS',
                severity='critical',
                taxonomy_id='SCHED_001',
                txns=[req.txn]
            ))
        
        return violations
