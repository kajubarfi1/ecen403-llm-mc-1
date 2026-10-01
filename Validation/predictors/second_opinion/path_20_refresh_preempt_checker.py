from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple, Optional


class FullControllerLegalityChecker(LegalityChecker):
    """
    Legality checker for the full controller path:
    wb_port + addr_decoder + cmd_queue + scheduler + refresh_ctrl + cmd_gen
    
    Validates invariants over the observed command stream without predicting
    exact ordering, since FR-FCFS scheduling with refresh interleaving permits
    multiple legal orderings.
    """
    
    INPUT_IFACES: tuple = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES: tuple = ('ddr_cmd',)
    COVERS: tuple = ('REF_002', 'SCHED_003', 'SCHED_001')
    
    # Command encoding table from schema
    # Per ddr_cmd schema: cmd field uses this encoding
    CMD_ENCODING: Dict[str, int] = {
        'MRS': 0b0000,
        'REF': 0b0001,
        'PRE': 0b0010,
        'ACT': 0b0011,
        'WR': 0b0100,
        'RD': 0b0101,
        'NOP': 0b0111,
        'DESL': 0b1111,
    }
    
    # Reverse mapping for decoding
    CMD_DECODING: Dict[int, str] = {v: k for k, v in CMD_ENCODING.items()}
    
    def __init__(self, spec: dict):
        """
        Initialize checker with spec-derived constants.
        
        Per spec section memory_geometry:
        - bank_bits: 3 (8 banks)
        - row_bits: 15
        - column_bits: 10
        """
        self._spec = spec
        
        # Extract geometry from spec - memory_geometry section
        geometry = spec.get('memory_geometry', {})
        self._num_banks = 1 << geometry.get('bank_bits', 3)  # 2^3 = 8 banks
        self._row_bits = geometry.get('row_bits', 15)
        self._col_bits = geometry.get('column_bits', 10)
        
        # Extract refresh policy from spec - controller_architecture.refresh_policy
        controller_arch = spec.get('controller_architecture', {})
        refresh_policy = controller_arch.get('refresh_policy', {})
        self._max_postpone = refresh_policy.get('max_postpone_count', 8)
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Bank state tracking for REF_002
        # Per JESD79-3: Banks start in precharged (idle) state after reset
        # True = active (has open row), False = precharged (idle)
        self._bank_active: List[bool] = [False] * self._num_banks
        
        # Track open row per bank for protocol validation
        self._bank_open_row: List[Optional[int]] = [None] * self._num_banks
        
        # Pending host requests for SCHED_001
        # Key: (bank, col, we) tuple, Value: list of request records
        # We track by (bank, col, we) since CAS commands target bank+col
        # and the we field determines RD vs WR
        self._pending_requests: List[Dict] = []
        
        # Refresh request tracking for SCHED_003
        # Count of refresh requests that need servicing
        self._pending_refresh_count: int = 0
        
        # Transaction history for violation reporting
        self._last_refresh_req_txn: Optional[Txn] = None
    
    def observe(self, txn: Txn) -> List[Violation]:
        """
        Consume one observed transaction and return any rule violations.
        
        Dispatch table based on interface:
        - cq_enq: Track enqueued requests for SCHED_001
        - refresh_req: Track refresh requests for SCHED_003
        - ddr_cmd: Check bank state for REF_002, match against pending for SCHED_001/003
        """
        violations: List[Violation] = []
        
        # Dispatch table for transaction handling
        handler_table = {
            'cq_enq': self._handle_cq_enq,
            'refresh_req': self._handle_refresh_req,
            'ddr_cmd': self._handle_ddr_cmd,
        }
        
        iface = txn.iface
        handler = handler_table.get(iface)
        
        if handler is not None:
            violations.extend(handler(txn))
        
        return violations
    
    def _handle_cq_enq(self, txn: Txn) -> List[Violation]:
        """
        Handle command queue enqueue transaction.
        
        Per cq_enq schema (enqueue kind):
        - row: target row address
        - col: target column address
        - bank: target bank
        - we: write enable (1=write, 0=read)
        
        Track for SCHED_001: every enqueued request must issue as matching CAS.
        """
        violations: List[Violation] = []
        
        if txn.kind != 'enqueue':
            return violations
        
        fields = txn.fields
        
        # Extract request parameters
        row = fields.get('row')
        col = fields.get('col')
        bank = fields.get('bank')
        we = fields.get('we')
        
        # Validate fields are present (schema requires them)
        if row is None or col is None or bank is None or we is None:
            return violations
        
        # Record the pending request
        # Per spec scheduler_policy: fr_fcfs - requests eventually service
        request_record = {
            'row': row,
            'col': col,
            'bank': bank,
            'we': we,
            'txn': txn,
        }
        self._pending_requests.append(request_record)
        
        return violations
    
    def _handle_refresh_req(self, txn: Txn) -> List[Violation]:
        """
        Handle refresh request transaction.
        
        Per refresh_req schema (request kind):
        - urgent: refresh is urgent
        - pending: pending refresh count
        - starve: starvation flag
        
        Track for SCHED_003: every refresh request must be serviced with REF.
        
        Per spec controller_architecture.refresh_policy:
        - max_postpone_count: 8
        - refresh_priority: urgent_preempt
        """
        violations: List[Violation] = []
        
        if txn.kind != 'request':
            return violations
        
        fields = txn.fields
        
        # Each refresh_req transaction indicates a refresh is needed
        # The pending field shows how many are queued
        pending = fields.get('pending', 0)
        
        # Track that we have a refresh request that needs servicing
        # We increment our count for each request transaction observed
        self._pending_refresh_count += 1
        self._last_refresh_req_txn = txn
        
        return violations
    
    def _handle_ddr_cmd(self, txn: Txn) -> List[Violation]:
        """
        Handle DDR command transaction.
        
        Per ddr_cmd schema (command kind):
        - cmd: command encoding (4 bits)
        - addr: address (15 bits, meaning depends on command)
        - bank: bank address (3 bits)
        
        Check invariants:
        - REF_002: REFRESH with active banks
        - Update bank state for ACT/PRE
        - Match CAS commands to pending requests for SCHED_001
        - Match REF commands to refresh requests for SCHED_003
        """
        violations: List[Violation] = []
        
        if txn.kind != 'command':
            return violations
        
        fields = txn.fields
        cmd_code = fields.get('cmd')
        addr = fields.get('addr')
        bank = fields.get('bank')
        
        if cmd_code is None:
            return violations
        
        # Decode command
        cmd_name = self.CMD_DECODING.get(cmd_code, 'UNKNOWN')
        
        # Command handling dispatch table
        cmd_handler_table = {
            'ACT': self._handle_activate,
            'PRE': self._handle_precharge,
            'REF': self._handle_refresh,
            'RD': self._handle_read,
            'WR': self._handle_write,
            'NOP': lambda t, a, b: [],  # No-op
            'DESL': lambda t, a, b: [],  # Deselect
            'MRS': lambda t, a, b: [],  # Mode register set - no bank state change
        }
        
        handler = cmd_handler_table.get(cmd_name, lambda t, a, b: [])
        violations.extend(handler(txn, addr, bank))
        
        return violations
    
    def _handle_activate(self, txn: Txn, addr: int, bank: int) -> List[Violation]:
        """
        Handle ACTIVATE command.
        
        Per JESD79-3: ACTIVATE opens a row in a bank.
        The addr field contains the row address.
        
        Updates bank state to active.
        """
        violations: List[Violation] = []
        
        if bank is not None and 0 <= bank < self._num_banks:
            # Bank becomes active with this row
            self._bank_active[bank] = True
            self._bank_open_row[bank] = addr
        
        return violations
    
    def _handle_precharge(self, txn: Txn, addr: int, bank: int) -> List[Violation]:
        """
        Handle PRECHARGE command.
        
        Per JESD79-3: PRECHARGE closes a row in a bank.
        addr[10] (A10) indicates all-bank precharge when high.
        
        Updates bank state to precharged (idle).
        """
        violations: List[Violation] = []
        
        # Per JESD79-3 section on PRECHARGE:
        # A10 HIGH = precharge all banks
        # A10 LOW = precharge bank specified by BA[2:0]
        if addr is not None:
            a10 = (addr >> 10) & 1
        else:
            a10 = 0
        
        if a10 == 1:
            # Precharge all banks
            for i in range(self._num_banks):
                self._bank_active[i] = False
                self._bank_open_row[i] = None
        elif bank is not None and 0 <= bank < self._num_banks:
            # Precharge single bank
            self._bank_active[bank] = False
            self._bank_open_row[bank] = None
        
        return violations
    
    def _handle_refresh(self, txn: Txn, addr: int, bank: int) -> List[Violation]:
        """
        Handle REFRESH command.
        
        Per spec failure_taxonomy REF_002:
        "REFRESH issued while one or more banks are still active (not precharged)."
        
        Per JESD79-3 section on REFRESH:
        All banks must be precharged before REFRESH can be issued.
        """
        violations: List[Violation] = []
        
        # REF_002 check: All banks must be precharged
        active_banks = [i for i in range(self._num_banks) if self._bank_active[i]]
        
        if active_banks:
            # Per spec REF_002: "REFRESH issued while one or more banks 
            # are still active (not precharged)."
            violations.append(Violation(
                rule='refresh_during_active_bank',
                detail=f'REFRESH issued with active banks: {active_banks}',
                severity='major',  # Per failure_taxonomy: severity is "major"
                taxonomy_id='REF_002',
                txns=[txn],
            ))
        
        # Service a pending refresh request (for SCHED_003 tracking)
        if self._pending_refresh_count > 0:
            self._pending_refresh_count -= 1
        
        # After refresh, per JESD79-3, all banks remain precharged
        # (REFRESH operates on all banks but doesn't change their idle state)
        
        return violations
    
    def _handle_read(self, txn: Txn, addr: int, bank: int) -> List[Violation]:
        """
        Handle READ command (CAS read).
        
        Per JESD79-3: READ is a column access to an active bank.
        The addr field contains the column address.
        
        Match against pending requests for SCHED_001.
        """
        violations: List[Violation] = []
        
        # Extract column address from addr field
        # Per JESD79-3, column address is in the lower bits
        col = addr & ((1 << self._col_bits) - 1) if addr is not None else None
        
        # Match against pending read requests (we=0)
        self._match_cas_request(bank, col, we=0)
        
        return violations
    
    def _handle_write(self, txn: Txn, addr: int, bank: int) -> List[Violation]:
        """
        Handle WRITE command (CAS write).
        
        Per JESD79-3: WRITE is a column access to an active bank.
        The addr field contains the column address.
        
        Match against pending requests for SCHED_001.
        """
        violations: List[Violation] = []
        
        # Extract column address from addr field
        col = addr & ((1 << self._col_bits) - 1) if addr is not None else None
        
        # Match against pending write requests (we=1)
        self._match_cas_request(bank, col, we=1)
        
        return violations
    
    def _match_cas_request(self, bank: Optional[int], col: Optional[int], we: int) -> bool:
        """
        Match a CAS command against pending requests.
        
        For SCHED_001: Find and remove a matching pending request.
        Returns True if a match was found.
        
        Per spec scheduler_policy: fr_fcfs allows reordering, so we match
        by (bank, col, we) without requiring strict FIFO order.
        """
        if bank is None or col is None:
            return False
        
        # Find a matching request
        for i, req in enumerate(self._pending_requests):
            if (req['bank'] == bank and 
                req['col'] == col and 
                req['we'] == we):
                # Found a match - remove it from pending
                self._pending_requests.pop(i)
                return True
        
        # No match found - this CAS doesn't correspond to any enqueued request
        # This could indicate a bug, but we only report violations for
        # requests that were enqueued but never issued (checked in final())
        return False
    
    def final(self) -> List[Violation]:
        """
        End-of-trace checks.
        
        Per spec invariants:
        - SCHED_001: Every enqueued request must issue as matching CAS
        - SCHED_003: Every refresh request must be serviced with REFRESH
        """
        violations: List[Violation] = []
        
        # SCHED_001: Check for requests that were never issued
        # Per spec: "Refresh preemption must not drop host requests: 
        # every enqueued request still issues as a matching CAS."
        if self._pending_requests:
            # Group by (bank, we) for clearer reporting
            pending_summary = []
            for req in self._pending_requests:
                cmd_type = 'WR' if req['we'] else 'RD'
                pending_summary.append(
                    f"bank={req['bank']},col={req['col']},type={cmd_type}"
                )
            
            violations.append(Violation(
                rule='request_not_issued',
                detail=f'{len(self._pending_requests)} enqueued request(s) never issued as CAS: [{", ".join(pending_summary[:5])}{"..." if len(pending_summary) > 5 else ""}]',
                severity='critical',
                taxonomy_id='SCHED_001',
                txns=[req['txn'] for req in self._pending_requests[:3]],
            ))
        
        # SCHED_003: Check for refresh requests that were never serviced
        # Per spec: "Every refresh request must eventually be serviced 
        # with a REFRESH command."
        if self._pending_refresh_count > 0:
            violations.append(Violation(
                rule='refresh_not_serviced',
                detail=f'{self._pending_refresh_count} refresh request(s) never serviced with REFRESH command',
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=[self._last_refresh_req_txn] if self._last_refresh_req_txn else [],
            ))
        
        return violations
