from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple, Optional


class FullControllerLegalityChecker(LegalityChecker):
    INPUT_IFACES = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('REF_002', 'SCHED_003', 'SCHED_001')

    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract geometry from spec
        geometry = spec.get('memory_geometry', {})
        self.num_banks = 1 << geometry.get('bank_bits', 3)
        self.row_bits = geometry.get('row_bits', 15)
        self.col_bits = geometry.get('column_bits', 10)
        
        # Extract refresh policy from spec
        controller_arch = spec.get('controller_architecture', {})
        refresh_policy = controller_arch.get('refresh_policy', {})
        self.max_postpone_count = refresh_policy.get('max_postpone_count', 8)
        
        # Command encoding
        self.CMD_MRS = 0b0000
        self.CMD_REF = 0b0001
        self.CMD_PRE = 0b0010
        self.CMD_ACT = 0b0011
        self.CMD_WR = 0b0100
        self.CMD_RD = 0b0101
        self.CMD_NOP = 0b0111
        self.CMD_DESL = 0b1111
        
        self.reset()

    def reset(self) -> None:
        # Bank state tracking: True = active (has open row), False = precharged/idle
        self.bank_active: List[bool] = [False] * self.num_banks
        # Track which row is open in each bank (only valid if bank_active[i] is True)
        self.bank_open_row: List[Optional[int]] = [None] * self.num_banks
        
        # Track pending refresh requests (count of refresh_req transactions seen)
        self.pending_refresh_count: int = 0
        # Track refresh commands issued
        self.refresh_commands_issued: int = 0
        # Store refresh request transactions for violation reporting
        self.refresh_requests: List[Txn] = []
        
        # Track enqueued host requests: list of (row, col, bank, we, txn)
        self.pending_requests: List[Tuple[int, int, int, int, Txn]] = []
        
        # Track CAS commands issued for matching
        self.cas_commands_issued: List[Tuple[int, int, int, Txn]] = []
        
        # Transaction counter for ordering
        self.txn_counter: int = 0

    def observe(self, txn: Txn) -> List[Violation]:
        violations = []
        self.txn_counter += 1
        
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields
        
        if iface == 'cq_enq' and kind == 'enqueue':
            # Host request enqueued - track it
            row = fields.get('row', 0)
            col = fields.get('col', 0)
            bank = fields.get('bank', 0)
            we = fields.get('we', 0)
            self.pending_requests.append((row, col, bank, we, txn))
            
        elif iface == 'refresh_req' and kind == 'request':
            # Refresh request - track it
            self.pending_refresh_count += 1
            self.refresh_requests.append(txn)
            
        elif iface == 'ddr_cmd' and kind == 'command':
            cmd = fields.get('cmd', self.CMD_NOP)
            addr = fields.get('addr', 0)
            bank = fields.get('bank', 0)
            
            if cmd == self.CMD_ACT:
                # Activate command - bank becomes active with this row
                self.bank_active[bank] = True
                self.bank_open_row[bank] = addr  # addr contains row address for ACT
                
            elif cmd == self.CMD_PRE:
                # Precharge command
                # Check if this is precharge all (typically addr[10] set) or single bank
                precharge_all = (addr >> 10) & 1
                if precharge_all:
                    for i in range(self.num_banks):
                        self.bank_active[i] = False
                        self.bank_open_row[i] = None
                else:
                    self.bank_active[bank] = False
                    self.bank_open_row[bank] = None
                    
            elif cmd == self.CMD_REF:
                # REF_002: Check if any bank is still active
                active_banks = [i for i in range(self.num_banks) if self.bank_active[i]]
                if active_banks:
                    v = Violation(
                        rule="REF_002",
                        detail=f"REFRESH issued while banks {active_banks} are still active",
                        severity="major",
                        taxonomy_id="REF_002",
                        txns=[txn]
                    )
                    violations.append(v)
                
                # Track refresh servicing
                self.refresh_commands_issued += 1
                
                # After refresh, all banks are precharged
                for i in range(self.num_banks):
                    self.bank_active[i] = False
                    self.bank_open_row[i] = None
                    
            elif cmd == self.CMD_RD or cmd == self.CMD_WR:
                # CAS command - try to match with a pending request
                # Extract column from addr (lower bits)
                col = addr & ((1 << self.col_bits) - 1)
                is_write = (cmd == self.CMD_WR)
                
                # Find the row for this bank (from bank_open_row)
                row = self.bank_open_row[bank] if self.bank_active[bank] else None
                
                # Try to match with pending request
                matched_idx = None
                for idx, (req_row, req_col, req_bank, req_we, req_txn) in enumerate(self.pending_requests):
                    # Match on bank and write/read type
                    bank_match = (req_bank == bank)
                    we_match = (req_we == is_write) or (req_we == 1 and is_write) or (req_we == 0 and not is_write)
                    
                    # For column, the CAS command addr should match the request col
                    col_match = (req_col == col)
                    
                    # For row, if bank is active, the open row should match
                    row_match = (row is None) or (req_row == row)
                    
                    if bank_match and we_match and col_match and row_match:
                        matched_idx = idx
                        break
                
                if matched_idx is not None:
                    self.pending_requests.pop(matched_idx)
                
        return violations

    def final(self) -> List[Violation]:
        violations = []
        
        # SCHED_003: Every refresh request must be serviced
        # Count how many refresh requests were not serviced
        unserviced_refreshes = self.pending_refresh_count - self.refresh_commands_issued
        if unserviced_refreshes > 0:
            # Get the refresh request transactions that weren't serviced
            unserviced_txns = self.refresh_requests[-unserviced_refreshes:] if unserviced_refreshes <= len(self.refresh_requests) else self.refresh_requests
            v = Violation(
                rule="SCHED_003",
                detail=f"{unserviced_refreshes} refresh request(s) never serviced with REFRESH command",
                severity="critical",
                taxonomy_id="SCHED_003",
                txns=unserviced_txns[:3]  # Limit to first 3 for brevity
            )
            violations.append(v)
        
        # SCHED_001: Every enqueued request must issue as a matching CAS
        if self.pending_requests:
            # These requests were enqueued but never matched to a CAS
            pending_txns = [req[4] for req in self.pending_requests]
            v = Violation(
                rule="SCHED_001",
                detail=f"{len(self.pending_requests)} enqueued request(s) never issued as CAS commands",
                severity="critical",
                taxonomy_id="SCHED_001",
                txns=pending_txns[:3]  # Limit to first 3 for brevity
            )
            violations.append(v)
        
        return violations
