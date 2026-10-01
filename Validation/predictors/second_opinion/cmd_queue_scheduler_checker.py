from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Set, Optional
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
    """
    Legality checker for cmd_queue + scheduler stage.
    
    Validates invariants over command streams without predicting exact ordering.
    Per FR-FCFS scheduler policy, multiple orderings are legal; we check only
    what the spec requires of any valid implementation.
    """
    
    INPUT_IFACES = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = (
        'SCHED_001',  # Every request must eventually issue as CAS
        'SCHED_002',  # No CAS without matching request
        'PROTO_001',  # CAS to idle bank
        'PROTO_002',  # Double activate
        'REF_002',    # Refresh while banks active
        'SCHED_004',  # CAS to wrong row
    )
    
    # Command type encoding from schema
    CMD_NOP = 0
    CMD_ACT = 1
    CMD_RD = 2
    CMD_WR = 3
    CMD_PRE = 4
    CMD_REF = 5
    
    # Table mapping command type codes to names for reporting
    CMD_NAMES = {
        0: 'NOP',
        1: 'ACT',
        2: 'RD',
        3: 'WR',
        4: 'PRE',
        5: 'REF',
    }
    
    def __init__(self, spec: dict):
        """Initialize checker state from specification."""
        # Extract geometry from spec
        geometry = spec['memory_geometry']
        self._num_banks = 2 ** geometry['bank_bits']  # 8 banks per spec
        self._row_bits = geometry['row_bits']
        self._col_bits = geometry['column_bits']
        
        # Extract controller architecture parameters
        arch = spec['controller_architecture']
        self._queue_depth = arch['command_queue_depth']
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on defaults."""
        # Per-bank state tracking
        # bank_active[b] = True if bank b has an open row
        self._bank_active: List[bool] = [False] * self._num_banks
        
        # open_row[b] = row number currently active in bank b (valid only if bank_active[b])
        self._open_row: List[Optional[int]] = [None] * self._num_banks
        
        # Pending requests awaiting CAS completion
        # List of PendingRequest objects - use list to preserve FCFS ordering info
        self._pending_requests: List[PendingRequest] = []
    
    def observe(self, txn: Txn) -> List[Violation]:
        """
        Process one observed transaction and return any violations found.
        
        Dispatch table routes to appropriate handler based on interface and kind.
        """
        violations = []
        
        # Dispatch table: (iface, kind) -> handler
        dispatch = {
            ('cq_enq', 'enqueue'): self._handle_enqueue,
            ('refresh_req', 'request'): self._handle_refresh_req,
            ('sched_cmd', 'command'): self._handle_sched_cmd,
        }
        
        key = (txn.iface, txn.kind)
        handler = dispatch.get(key)
        
        if handler is not None:
            violations = handler(txn)
        
        return violations
    
    def _handle_enqueue(self, txn: Txn) -> List[Violation]:
        """
        Handle cq_enq.enqueue: record pending request.
        
        Per spec SCHED_001: Every enqueued request must eventually issue as CAS.
        We track all enqueues and verify completion via CAS commands.
        """
        row = txn.fields['row']
        col = txn.fields['col']
        bank = txn.fields['bank']
        we = txn.fields['we']
        
        req = PendingRequest(
            row=row,
            col=col,
            bank=bank,
            we=we,
            txn=txn
        )
        self._pending_requests.append(req)
        
        return []
    
    def _handle_refresh_req(self, txn: Txn) -> List[Violation]:
        """
        Handle refresh_req.request: refresh controller signals.
        
        This is informational input tracking refresh urgency.
        No violations generated on input side.
        """
        # Refresh request is input side - no violations to report here
        # The actual REF command on sched_cmd is where we check REF_002
        return []
    
    def _handle_sched_cmd(self, txn: Txn) -> List[Violation]:
        """
        Handle sched_cmd.command: scheduler output command.
        
        Dispatch to specific command handlers based on command type.
        """
        cmd_type_raw = txn.fields['type']
        
        # Handle string or integer type encoding
        if isinstance(cmd_type_raw, str):
            type_map = {'NOP': 0, 'ACT': 1, 'RD': 2, 'WR': 3, 'PRE': 4, 'REF': 5}
            cmd_type = type_map.get(cmd_type_raw, cmd_type_raw)
        else:
            cmd_type = cmd_type_raw
        
        # Command handler dispatch table
        cmd_handlers = {
            self.CMD_NOP: self._handle_nop,
            self.CMD_ACT: self._handle_activate,
            self.CMD_RD: self._handle_cas_read,
            self.CMD_WR: self._handle_cas_write,
            self.CMD_PRE: self._handle_precharge,
            self.CMD_REF: self._handle_refresh,
        }
        
        handler = cmd_handlers.get(cmd_type)
        if handler is not None:
            return handler(txn)
        
        return []
    
    def _handle_nop(self, txn: Txn) -> List[Violation]:
        """NOP command: no state change, no violations possible."""
        return []
    
    def _handle_activate(self, txn: Txn) -> List[Violation]:
        """
        Handle ACT command.
        
        Per PROTO_002: ACTIVATE to a bank that already has an active row
        without intervening PRECHARGE is a violation.
        
        Per SCHED_004 note: An ACTIVATE that no pending request asked for
        is NOT a violation by itself - speculative row opens are allowed.
        """
        violations = []
        bank = txn.fields['bank']
        row = txn.fields['row']
        
        # PROTO_002: Check for double activate
        if self._bank_active[bank]:
            violations.append(Violation(
                rule='double_activate',
                detail=f'ACTIVATE to bank {bank} row {row} while row {self._open_row[bank]} already active',
                severity='critical',
                taxonomy_id='PROTO_002',
                txns=[txn]
            ))
        
        # Update bank state: row is now open
        self._bank_active[bank] = True
        self._open_row[bank] = row
        
        return violations
    
    def _handle_cas_read(self, txn: Txn) -> List[Violation]:
        """Handle RD (READ) command - CAS operation."""
        return self._handle_cas(txn, is_write=False)
    
    def _handle_cas_write(self, txn: Txn) -> List[Violation]:
        """Handle WR (WRITE) command - CAS operation."""
        return self._handle_cas(txn, is_write=True)
    
    def _handle_cas(self, txn: Txn, is_write: bool) -> List[Violation]:
        """
        Handle CAS command (RD or WR).
        
        Checks:
        - PROTO_001: CAS to idle bank (no active row)
        - SCHED_002: CAS with no matching enqueued request
        - SCHED_004: CAS lands on wrong row (open row != request's row)
        
        Per spec: Match request by (bank, col, we). The row the CAS executes
        against is determined by the currently open row, not carried in the
        CAS command itself (DDR3 protocol).
        """
        violations = []
        bank = txn.fields['bank']
        col = txn.fields['col']
        we = txn.fields['we']
        cmd_name = 'WRITE' if is_write else 'READ'
        expected_we = 1 if is_write else 0
        
        # PROTO_001: Check bank is active before CAS
        # Per JESD79-3: READ/WRITE commands require an active row
        if not self._bank_active[bank]:
            violations.append(Violation(
                rule='cas_to_idle_bank',
                detail=f'{cmd_name} to bank {bank} col {col} but bank has no active row',
                severity='major',
                taxonomy_id='PROTO_001',
                txns=[txn]
            ))
            # Still try to match request even if protocol violation
        
        # Find matching request by (bank, col, we)
        # Per spec: CAS must match request on these fields
        matched_request = None
        matched_index = None
        
        for idx, req in enumerate(self._pending_requests):
            if req.bank == bank and req.col == col and req.we == expected_we:
                matched_request = req
                matched_index = idx
                break
        
        if matched_request is None:
            # SCHED_002: No matching request found
            violations.append(Violation(
                rule='cas_no_request',
                detail=f'{cmd_name} to bank {bank} col {col} matches no enqueued request',
                severity='critical',
                taxonomy_id='SCHED_002',
                txns=[txn]
            ))
        else:
            # Found matching request - check row correctness
            # SCHED_004: The open row must match the request's row
            # Per spec: "when the CAS for a request issues, the row open in
            # that bank (set by the most recent ACTIVATE to it) must be the
            # request's row"
            if self._bank_active[bank]:
                current_open_row = self._open_row[bank]
                if current_open_row != matched_request.row:
                    violations.append(Violation(
                        rule='cas_wrong_row',
                        detail=f'{cmd_name} to bank {bank} col {col}: request wanted row {matched_request.row} but row {current_open_row} is open',
                        severity='critical',
                        taxonomy_id='SCHED_004',
                        txns=[matched_request.txn, txn]
                    ))
            
            # Remove the matched request from pending (request is serviced)
            # This happens regardless of row mismatch - the CAS consumed a request
            self._pending_requests.pop(matched_index)
        
        return violations
    
    def _handle_precharge(self, txn: Txn) -> List[Violation]:
        """
        Handle PRE (PRECHARGE) command.
        
        Updates bank state to inactive. No protocol violations checked here
        (timing violations are out of scope per checker contract).
        """
        bank = txn.fields['bank']
        
        # Update bank state: row closed
        self._bank_active[bank] = False
        self._open_row[bank] = None
        
        return []
    
    def _handle_refresh(self, txn: Txn) -> List[Violation]:
        """
        Handle REF (REFRESH) command.
        
        Per REF_002: REFRESH issued while one or more banks are still active
        is a violation.
        
        Per JESD79-3 section 4.13: All banks must be precharged before REFRESH.
        """
        violations = []
        
        # REF_002: Check all banks are precharged
        active_banks = [b for b in range(self._num_banks) if self._bank_active[b]]
        
        if active_banks:
            violations.append(Violation(
                rule='refresh_banks_active',
                detail=f'REFRESH issued while banks {active_banks} are active',
                severity='major',
                taxonomy_id='REF_002',
                txns=[txn]
            ))
        
        # After refresh, all banks remain in precharged state
        # Per JESD79-3: REFRESH does not change bank active/inactive state
        # (banks must already be precharged for valid REFRESH)
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace checks.
        
        Per SCHED_001: Every enqueued request must eventually issue as CAS.
        Any requests still pending at end of trace are dropped requests.
        """
        violations = []
        
        # SCHED_001: Report any outstanding requests as dropped
        for req in self._pending_requests:
            violations.append(Violation(
                rule='request_dropped',
                detail=f'Request for bank {req.bank} row {req.row} col {req.col} we={req.we} never issued as CAS',
                severity='critical',
                taxonomy_id='SCHED_001',
                txns=[req.txn]
            ))
        
        return violations
