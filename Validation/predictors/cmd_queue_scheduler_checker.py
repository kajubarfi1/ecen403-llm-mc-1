from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from collections import deque


@dataclass
class PendingRequest:
    """Tracks an enqueued request awaiting CAS completion."""
    row: int
    col: int
    bank: int
    we: int
    order: int  # sequence number for FIFO ordering
    txn: Txn


class CmdQueueSchedulerChecker(LegalityChecker):
    """Legality checker for cmd_queue + scheduler stage.
    
    Validates FR-FCFS scheduler behavior including:
    - Request completion (no dropped requests)
    - No invented CAS commands
    - Protocol correctness (bank state machine)
    - Row correctness for CAS commands
    """
    
    INPUT_IFACES = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'REF_002', 'SCHED_004')
    
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
        # Pending requests indexed by (bank, col, we) for efficient lookup
        # Each key maps to a list of PendingRequest, maintained in order
        self._pending: Dict[Tuple[int, int, int], List[PendingRequest]] = {}
        
        # Bank state: None means idle/precharged, int means active with that row
        self._bank_row: List[Optional[int]] = [None] * self.num_banks
        
        # Sequence counter for ordering
        self._seq = 0
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []
        
        if txn.iface == 'cq_enq' and txn.kind == 'enqueue':
            self._handle_enqueue(txn)
        elif txn.iface == 'sched_cmd' and txn.kind == 'command':
            violations.extend(self._handle_command(txn))
        # refresh_req is observed but doesn't trigger violations directly
        # (refresh violations come from sched_cmd issuing REF)
        
        return violations
    
    def _handle_enqueue(self, txn: Txn) -> None:
        """Track a new request entering the command queue."""
        row = txn.fields.get('row')
        col = txn.fields.get('col')
        bank = txn.fields.get('bank')
        we = txn.fields.get('we')
        
        key = (bank, col, we)
        req = PendingRequest(row=row, col=col, bank=bank, we=we, order=self._seq, txn=txn)
        self._seq += 1
        
        if key not in self._pending:
            self._pending[key] = []
        self._pending[key].append(req)
    
    def _handle_command(self, txn: Txn) -> List[Violation]:
        """Process a scheduler command and check for violations."""
        violations = []
        
        cmd_type = txn.fields.get('type')
        bank = txn.fields.get('bank')
        row = txn.fields.get('row')
        col = txn.fields.get('col')
        we = txn.fields.get('we')
        
        if cmd_type == self.CMD_ACT:
            violations.extend(self._check_activate(txn, bank, row))
        elif cmd_type == self.CMD_RD or cmd_type == self.CMD_WR:
            violations.extend(self._check_cas(txn, bank, row, col, we, cmd_type))
        elif cmd_type == self.CMD_PRE:
            self._handle_precharge(bank)
        elif cmd_type == self.CMD_REF:
            violations.extend(self._check_refresh(txn))
        # NOP does nothing
        
        return violations
    
    def _check_activate(self, txn: Txn, bank: int, row: int) -> List[Violation]:
        """Check ACTIVATE command for protocol violations."""
        violations = []
        
        # PROTO_002: Double activate without intervening precharge
        if self._bank_row[bank] is not None:
            violations.append(Violation(
                rule="double_activate",
                detail=f"ACTIVATE to bank {bank} row {row} while row {self._bank_row[bank]} already active",
                severity="critical",
                taxonomy_id="PROTO_002",
                txns=[txn]
            ))
        
        # Update bank state (even if violation, the activate still happens)
        self._bank_row[bank] = row
        
        return violations
    
    def _check_cas(self, txn: Txn, bank: int, row: int, col: int, we: int, cmd_type: int) -> List[Violation]:
        """Check READ/WRITE command for violations."""
        violations = []
        cmd_name = "READ" if cmd_type == self.CMD_RD else "WRITE"
        
        # PROTO_001: CAS to idle bank
        if self._bank_row[bank] is None:
            violations.append(Violation(
                rule="cas_to_idle_bank",
                detail=f"{cmd_name} to bank {bank} which has no active row",
                severity="major",
                taxonomy_id="PROTO_001",
                txns=[txn]
            ))
        
        # Find matching pending request for SCHED_002 and SCHED_004
        key = (bank, col, we)
        pending_list = self._pending.get(key, [])
        
        matched_req = None
        matched_idx = None
        
        # First try to find request with matching row (FR-FCFS preference)
        for idx, req in enumerate(pending_list):
            if req.row == row:
                matched_req = req
                matched_idx = idx
                break
        
        # If no row match, take oldest request to this (bank, col, we)
        if matched_req is None and pending_list:
            matched_req = pending_list[0]
            matched_idx = 0
        
        if matched_req is None:
            # SCHED_002: No matching request exists
            violations.append(Violation(
                rule="invented_cas",
                detail=f"{cmd_name} to bank={bank} col={col} we={we} row={row} has no matching pending request",
                severity="critical",
                taxonomy_id="SCHED_002",
                txns=[txn]
            ))
        else:
            # SCHED_004: Check if CAS lands on correct row
            # The violation is if bank's open row != paired request's row
            open_row = self._bank_row[bank]
            if open_row is not None and open_row != matched_req.row:
                violations.append(Violation(
                    rule="wrong_row_cas",
                    detail=f"{cmd_name} for request row={matched_req.row} but bank {bank} has row {open_row} open",
                    severity="critical",
                    taxonomy_id="SCHED_004",
                    txns=[matched_req.txn, txn]
                ))
            
            # Remove the matched request from pending
            del pending_list[matched_idx]
            if not pending_list:
                del self._pending[key]
        
        return violations
    
    def _handle_precharge(self, bank: int) -> None:
        """Handle PRECHARGE command - closes the bank."""
        self._bank_row[bank] = None
    
    def _check_refresh(self, txn: Txn) -> List[Violation]:
        """Check REFRESH command for violations."""
        violations = []
        
        # REF_002: Check if any bank is still active
        active_banks = [i for i in range(self.num_banks) if self._bank_row[i] is not None]
        if active_banks:
            violations.append(Violation(
                rule="refresh_with_active_banks",
                detail=f"REFRESH issued while banks {active_banks} are still active",
                severity="major",
                taxonomy_id="REF_002",
                txns=[txn]
            ))
        
        # REFRESH closes all banks (resynchronizes bank model per spec)
        for i in range(self.num_banks):
            self._bank_row[i] = None
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: report any outstanding requests as dropped."""
        violations = []
        
        # SCHED_001: All pending requests are dropped requests
        for key, pending_list in self._pending.items():
            for req in pending_list:
                violations.append(Violation(
                    rule="dropped_request",
                    detail=f"Request to bank={req.bank} row={req.row} col={req.col} we={req.we} never issued",
                    severity="critical",
                    taxonomy_id="SCHED_001",
                    txns=[req.txn]
                ))
        
        return violations
