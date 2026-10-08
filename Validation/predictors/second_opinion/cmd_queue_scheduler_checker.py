from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from collections import OrderedDict


@dataclass
class PendingRequest:
    """A request enqueued but not yet serviced."""
    row: int
    col: int
    bank: int
    we: int
    txn: Txn
    order: int  # insertion order for FCFS tie-breaking


class CmdQueueSchedulerChecker(LegalityChecker):
    """Legality checker for cmd_queue + scheduler stage.
    
    Checks invariants over the command stream without predicting exact order,
    since FR-FCFS scheduling admits multiple legal orderings.
    """
    
    INPUT_IFACES: tuple = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES: tuple = ('sched_cmd',)
    COVERS: tuple = (
        'SCHED_001',  # Dropped request
        'SCHED_002',  # Invented command (CAS with no matching request)
        'PROTO_001',  # CAS to idle bank
        'PROTO_002',  # Double activate
        'REF_002',    # Refresh during active bank
        'SCHED_004',  # CAS to wrong row
    )
    
    # Command type encoding from spec
    CMD_TYPE_TABLE: Dict[str, int] = {
        'NOP': 0,
        'ACT': 1,
        'RD': 2,
        'WR': 3,
        'PRE': 4,
        'REF': 5,
    }
    
    # Reverse lookup table
    CMD_TYPE_NAME: Dict[int, str] = {v: k for k, v in CMD_TYPE_TABLE.items()}
    
    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract geometry from spec
        self.num_banks = 1 << spec['memory_geometry']['bank_bits']
        self.row_bits = spec['memory_geometry']['row_bits']
        self.col_bits = spec['memory_geometry']['column_bits']
        self.bank_bits = spec['memory_geometry']['bank_bits']
        
        # Violation severity table derived from failure_taxonomy
        self.severity_table: Dict[str, str] = {}
        for cat in spec['failure_taxonomy']['categories']:
            self.severity_table[cat['id']] = cat['severity']
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Bank state: None means precharged/idle, integer means row is active
        # Per PROTO_002 spec: "a bank is 'active' from its ACTIVATE until a
        # PRECHARGE to it, or any REFRESH"
        self.bank_open_row: List[Optional[int]] = [None] * self.num_banks
        
        # Pending requests: keyed by (bank, col, we) -> list of PendingRequest
        # Using list to handle multiple requests to same (bank, col, we)
        # OrderedDict preserves insertion order for FCFS
        self.pending_requests: Dict[Tuple[int, int, int], List[PendingRequest]] = {}
        
        # Global request counter for FCFS ordering
        self.request_order: int = 0
        
        # All pending requests for final() checking
        self.all_pending: List[PendingRequest] = []
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations: List[Violation] = []
        
        # Dispatch table for transaction interfaces
        handler_table = {
            'cq_enq': self._handle_enqueue,
            'refresh_req': self._handle_refresh_req,
            'sched_cmd': self._handle_sched_cmd,
        }
        
        handler = handler_table.get(txn.iface)
        if handler is not None:
            violations.extend(handler(txn))
        
        return violations
    
    def _handle_enqueue(self, txn: Txn) -> List[Violation]:
        """Handle cq_enq transaction: track pending request."""
        # Only handle 'enqueue' kind
        if txn.kind != 'enqueue':
            return []
        
        row = txn.fields.get('row', 0)
        col = txn.fields.get('col', 0)
        bank = txn.fields.get('bank', 0)
        we = txn.fields.get('we', 0)
        
        req = PendingRequest(
            row=row,
            col=col,
            bank=bank,
            we=we,
            txn=txn,
            order=self.request_order
        )
        self.request_order += 1
        
        key = (bank, col, we)
        if key not in self.pending_requests:
            self.pending_requests[key] = []
        self.pending_requests[key].append(req)
        self.all_pending.append(req)
        
        return []
    
    def _handle_refresh_req(self, txn: Txn) -> List[Violation]:
        """Handle refresh_req transaction: no violations generated here.
        
        Per spec, refresh requests are inputs to the scheduler. The actual
        REF command is checked when it appears on sched_cmd.
        """
        return []
    
    def _handle_sched_cmd(self, txn: Txn) -> List[Violation]:
        """Handle sched_cmd transaction: check command legality."""
        if txn.kind != 'command':
            return []
        
        cmd_type = txn.fields.get('type', 0)
        
        # Dispatch by command type
        cmd_handler_table = {
            self.CMD_TYPE_TABLE['NOP']: self._check_nop,
            self.CMD_TYPE_TABLE['ACT']: self._check_activate,
            self.CMD_TYPE_TABLE['RD']: self._check_cas,
            self.CMD_TYPE_TABLE['WR']: self._check_cas,
            self.CMD_TYPE_TABLE['PRE']: self._check_precharge,
            self.CMD_TYPE_TABLE['REF']: self._check_refresh,
        }
        
        handler = cmd_handler_table.get(cmd_type)
        if handler is not None:
            return handler(txn)
        
        return []
    
    def _check_nop(self, txn: Txn) -> List[Violation]:
        """NOP commands have no invariants to check."""
        return []
    
    def _check_activate(self, txn: Txn) -> List[Violation]:
        """Check ACTIVATE command for PROTO_002 (double activate)."""
        violations: List[Violation] = []
        
        bank = txn.fields.get('bank', 0)
        row = txn.fields.get('row', 0)
        
        # PROTO_002: ACTIVATE issued to a bank that already has an active row
        # without intervening PRECHARGE
        if self.bank_open_row[bank] is not None:
            violations.append(Violation(
                rule='double_activate',
                detail=(f"ACTIVATE to bank {bank} row {row} while row "
                        f"{self.bank_open_row[bank]} already active"),
                severity=self.severity_table.get('PROTO_002', 'critical'),
                taxonomy_id='PROTO_002',
                txns=[txn]
            ))
        
        # Update bank state: row is now active
        # Per spec: "a bank is 'active' from its ACTIVATE"
        self.bank_open_row[bank] = row
        
        return violations
    
    def _check_cas(self, txn: Txn) -> List[Violation]:
        """Check READ/WRITE command for PROTO_001, SCHED_002, SCHED_004."""
        violations: List[Violation] = []
        
        cmd_type = txn.fields.get('type', 0)
        bank = txn.fields.get('bank', 0)
        row = txn.fields.get('row', 0)
        col = txn.fields.get('col', 0)
        we = txn.fields.get('we', 0)
        
        cmd_name = self.CMD_TYPE_NAME.get(cmd_type, 'CAS')
        
        # PROTO_001: READ/WRITE issued to a bank that has no active row
        if self.bank_open_row[bank] is None:
            violations.append(Violation(
                rule='cas_to_idle_bank',
                detail=f"{cmd_name} to bank {bank} which has no active row",
                severity=self.severity_table.get('PROTO_001', 'major'),
                taxonomy_id='PROTO_001',
                txns=[txn]
            ))
        
        # Find matching request using SCHED_004 pairing rules:
        # "a CAS is paired with the pending request to its (bank, col, we) whose
        # row equals the CAS's row field when one exists; otherwise with the
        # OLDEST pending request to that (bank, col, we)"
        key = (bank, col, we)
        pending_list = self.pending_requests.get(key, [])
        
        paired_request: Optional[PendingRequest] = None
        paired_index: Optional[int] = None
        
        if pending_list:
            # First try: find request whose row matches CAS row
            for i, req in enumerate(pending_list):
                if req.row == row:
                    paired_request = req
                    paired_index = i
                    break
            
            # Second try: oldest request to (bank, col, we)
            if paired_request is None:
                # Find oldest by order field
                oldest_idx = 0
                for i, req in enumerate(pending_list):
                    if req.order < pending_list[oldest_idx].order:
                        oldest_idx = i
                paired_request = pending_list[oldest_idx]
                paired_index = oldest_idx
        
        # SCHED_002: No CAS command may issue that matches no enqueued request
        if paired_request is None:
            violations.append(Violation(
                rule='invented_cas',
                detail=(f"{cmd_name} to bank={bank} col={col} we={we} row={row} "
                        f"matches no pending request"),
                severity=self.severity_table.get('SCHED_002', 'critical'),
                taxonomy_id='SCHED_002',
                txns=[txn]
            ))
        else:
            # SCHED_004: CAS must execute against the row its request asked for
            # "the row open in that bank (set by the most recent ACTIVATE to it)
            # must be the request's row"
            open_row = self.bank_open_row[bank]
            request_row = paired_request.row
            
            # Only check if bank is active (PROTO_001 already reported if not)
            if open_row is not None and open_row != request_row:
                violations.append(Violation(
                    rule='cas_wrong_row',
                    detail=(f"{cmd_name} for request row={request_row} executed "
                            f"while bank {bank} has row={open_row} open"),
                    severity=self.severity_table.get('SCHED_004', 'critical'),
                    taxonomy_id='SCHED_004',
                    txns=[paired_request.txn, txn]
                ))
            
            # Remove the paired request from pending
            pending_list.pop(paired_index)
            if not pending_list:
                del self.pending_requests[key]
            
            # Remove from all_pending
            if paired_request in self.all_pending:
                self.all_pending.remove(paired_request)
        
        return violations
    
    def _check_precharge(self, txn: Txn) -> List[Violation]:
        """Check PRECHARGE command: update bank state."""
        bank = txn.fields.get('bank', 0)
        
        # Per spec: bank becomes precharged (idle) after PRECHARGE
        # No violations defined for PRECHARGE to idle bank in this checker's scope
        self.bank_open_row[bank] = None
        
        return []
    
    def _check_refresh(self, txn: Txn) -> List[Violation]:
        """Check REFRESH command for REF_002."""
        violations: List[Violation] = []
        
        # REF_002: REFRESH issued while one or more banks are still active
        active_banks = [i for i in range(self.num_banks) 
                        if self.bank_open_row[i] is not None]
        
        if active_banks:
            violations.append(Violation(
                rule='refresh_active_banks',
                detail=(f"REFRESH issued while banks {active_banks} have active "
                        f"rows {[self.bank_open_row[b] for b in active_banks]}"),
                severity=self.severity_table.get('REF_002', 'major'),
                taxonomy_id='REF_002',
                txns=[txn]
            ))
        
        # Per spec: "after any REFRESH every bank is treated as precharged (idle),
        # legal or not -- a REFRESH issued with a bank open is this violation and
        # RESYNCHRONISES the bank model"
        for i in range(self.num_banks):
            self.bank_open_row[i] = None
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check for dropped requests (SCHED_001)."""
        violations: List[Violation] = []
        
        # SCHED_001: Every enqueued request must eventually issue as a CAS command
        # Outstanding requests at end of trace are dropped requests
        for req in self.all_pending:
            violations.append(Violation(
                rule='dropped_request',
                detail=(f"Request bank={req.bank} row={req.row} col={req.col} "
                        f"we={req.we} never issued"),
                severity=self.severity_table.get('SCHED_001', 'critical'),
                taxonomy_id='SCHED_001',
                txns=[req.txn]
            ))
        
        return violations
