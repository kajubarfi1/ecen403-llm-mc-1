from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Set


class CmdQueueSchedulerChecker(LegalityChecker):
    """Legality checker for cmd_queue + scheduler stage."""
    
    INPUT_IFACES = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'REF_002')
    
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
        self.num_banks = 2 ** geometry.get('bank_bits', 3)
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Track pending requests: list of (row, bank, col, we, txn)
        self.pending_requests: List[Tuple[int, int, int, int, Txn]] = []
        
        # Track bank state: None = idle/precharged, int = active row
        self.bank_active_row: Dict[int, Optional[int]] = {
            b: None for b in range(self.num_banks)
        }
        
        # Track all enqueued request txns for violation reporting
        self.request_txns: List[Txn] = []
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []
        
        if txn.iface == 'cq_enq' and txn.kind == 'enqueue':
            violations.extend(self._handle_enqueue(txn))
        elif txn.iface == 'sched_cmd' and txn.kind == 'command':
            violations.extend(self._handle_command(txn))
        # refresh_req transactions are observed but don't directly cause violations
        
        return violations
    
    def _handle_enqueue(self, txn: Txn) -> List[Violation]:
        """Handle an enqueued request."""
        row = txn.fields.get('row', 0)
        bank = txn.fields.get('bank', 0)
        col = txn.fields.get('col', 0)
        we = txn.fields.get('we', 0)
        
        self.pending_requests.append((row, bank, col, we, txn))
        self.request_txns.append(txn)
        
        return []
    
    def _handle_command(self, txn: Txn) -> List[Violation]:
        """Handle a scheduler command."""
        violations = []
        
        cmd_type = txn.fields.get('type', 0)
        # Handle string or int type
        if isinstance(cmd_type, str):
            type_map = {'NOP': 0, 'ACT': 1, 'RD': 2, 'WR': 3, 'PRE': 4, 'REF': 5}
            cmd_type = type_map.get(cmd_type, 0)
        
        bank = txn.fields.get('bank', 0)
        row = txn.fields.get('row', 0)
        col = txn.fields.get('col', 0)
        we = txn.fields.get('we', 0)
        
        if cmd_type == self.CMD_ACT:
            # PROTO_002: ACTIVATE to bank that already has active row
            if self.bank_active_row.get(bank) is not None:
                violations.append(Violation(
                    rule="PROTO_002",
                    detail=f"ACTIVATE to bank {bank} which already has row {self.bank_active_row[bank]} active",
                    severity="critical",
                    taxonomy_id="PROTO_002",
                    txns=[txn]
                ))
            # Mark bank as active with this row
            self.bank_active_row[bank] = row
            
        elif cmd_type == self.CMD_PRE:
            # Precharge: mark bank as idle
            self.bank_active_row[bank] = None
            
        elif cmd_type == self.CMD_REF:
            # REF_002: REFRESH while banks are active
            active_banks = [b for b, r in self.bank_active_row.items() if r is not None]
            if active_banks:
                violations.append(Violation(
                    rule="REF_002",
                    detail=f"REFRESH issued while banks {active_banks} are still active",
                    severity="major",
                    taxonomy_id="REF_002",
                    txns=[txn]
                ))
            # After refresh, all banks are idle
            for b in self.bank_active_row:
                self.bank_active_row[b] = None
                
        elif cmd_type in (self.CMD_RD, self.CMD_WR):
            # CAS command (READ or WRITE)
            
            # PROTO_001: CAS to bank with no active row
            active_row = self.bank_active_row.get(bank)
            if active_row is None:
                violations.append(Violation(
                    rule="PROTO_001",
                    detail=f"{'RD' if cmd_type == self.CMD_RD else 'WR'} to bank {bank} with no active row",
                    severity="major",
                    taxonomy_id="PROTO_001",
                    txns=[txn]
                ))
            
            # Determine expected we value for this command type
            expected_we = 1 if cmd_type == self.CMD_WR else 0
            
            # SCHED_002: CAS command must match an enqueued request
            # Match by bank, col, we, and the active row must match request's row
            matched_idx = None
            for i, (req_row, req_bank, req_col, req_we, req_txn) in enumerate(self.pending_requests):
                if (req_bank == bank and 
                    req_col == col and 
                    req_we == expected_we):
                    # Check if active row matches request row (if bank is active)
                    if active_row is not None and req_row == active_row:
                        matched_idx = i
                        break
                    elif active_row is None:
                        # Bank not active - we already reported PROTO_001
                        # Still try to match the request for SCHED_002 purposes
                        matched_idx = i
                        break
            
            if matched_idx is not None:
                # Remove the matched request from pending
                self.pending_requests.pop(matched_idx)
            else:
                # No matching request found
                violations.append(Violation(
                    rule="SCHED_002",
                    detail=f"{'RD' if cmd_type == self.CMD_RD else 'WR'} to bank={bank} col={col} matches no enqueued request",
                    severity="critical",
                    taxonomy_id="SCHED_002",
                    txns=[txn]
                ))
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check for outstanding requests (starvation)."""
        violations = []
        
        # SCHED_001: Every enqueued request must eventually issue as CAS
        for (row, bank, col, we, txn) in self.pending_requests:
            violations.append(Violation(
                rule="SCHED_001",
                detail=f"Request row={row} bank={bank} col={col} we={we} never issued",
                severity="critical",
                taxonomy_id="SCHED_001",
                txns=[txn]
            ))
        
        return violations
