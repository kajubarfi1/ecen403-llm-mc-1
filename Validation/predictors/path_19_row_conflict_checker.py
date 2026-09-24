from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Set
from collections import defaultdict


class FullPathLegalityChecker(LegalityChecker):
    """Legality checker for full command path from host request to DDR pins."""
    
    INPUT_IFACES = ('cq_enq',)
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'SCHED_004')
    
    def __init__(self, spec: dict):
        self.spec = spec
        self.num_banks = 1 << spec['memory_geometry']['bank_bits']
        self.row_bits = spec['memory_geometry']['row_bits']
        self.col_bits = spec['memory_geometry']['column_bits']
        
        self.cmd_encoding = {
            'MRS': 0b0000,
            'REF': 0b0001,
            'PRE': 0b0010,
            'ACT': 0b0011,
            'WR': 0b0100,
            'RD': 0b0101,
            'NOP': 0b0111,
            'DESL': 0b1111,
        }
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        self.pending_requests: Dict[int, List[dict]] = defaultdict(list)
        self.bank_active: Dict[int, bool] = {i: False for i in range(self.num_banks)}
        self.bank_open_row: Dict[int, Optional[int]] = {i: None for i in range(self.num_banks)}
        self.all_enqueued: List[dict] = []
        self.txn_counter = 0
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []
        self.txn_counter += 1
        
        if txn.iface == 'cq_enq' and txn.kind == 'enqueue':
            violations.extend(self._handle_enqueue(txn))
        elif txn.iface == 'ddr_cmd' and txn.kind == 'command':
            violations.extend(self._handle_ddr_command(txn))
        
        return violations
    
    def _handle_enqueue(self, txn: Txn) -> List[Violation]:
        """Handle an enqueued request."""
        row = txn.fields.get('row')
        col = txn.fields.get('col')
        bank = txn.fields.get('bank')
        we = txn.fields.get('we')
        
        request = {
            'row': row,
            'col': col,
            'bank': bank,
            'we': we,
            'txn': txn,
            'id': self.txn_counter,
        }
        
        self.pending_requests[bank].append(request)
        self.all_enqueued.append(request)
        
        return []
    
    def _handle_ddr_command(self, txn: Txn) -> List[Violation]:
        """Handle a DDR command."""
        violations = []
        
        cmd = txn.fields.get('cmd')
        addr = txn.fields.get('addr')
        bank = txn.fields.get('bank')
        
        if cmd == self.cmd_encoding['ACT']:
            violations.extend(self._handle_activate(txn, bank, addr))
        elif cmd == self.cmd_encoding['RD']:
            violations.extend(self._handle_cas(txn, bank, addr, is_write=False))
        elif cmd == self.cmd_encoding['WR']:
            violations.extend(self._handle_cas(txn, bank, addr, is_write=True))
        elif cmd == self.cmd_encoding['PRE']:
            self._handle_precharge(txn, bank)
        elif cmd == self.cmd_encoding['REF']:
            self._handle_refresh(txn)
        
        return violations
    
    def _handle_activate(self, txn: Txn, bank: int, row: int) -> List[Violation]:
        """Handle ACTIVATE command."""
        violations = []
        
        if self.bank_active.get(bank, False):
            violations.append(Violation(
                rule="double_activate",
                detail=f"ACTIVATE issued to bank {bank} which already has row {self.bank_open_row[bank]} active",
                severity="critical",
                taxonomy_id="PROTO_002",
                txns=[txn]
            ))
        
        pending_in_bank = self.pending_requests.get(bank, [])
        rows_needed = {req['row'] for req in pending_in_bank}
        
        if row not in rows_needed:
            violations.append(Violation(
                rule="spurious_activate",
                detail=f"ACTIVATE to bank {bank} row {row} but no pending request needs that row. Pending rows: {rows_needed}",
                severity="critical",
                taxonomy_id="SCHED_004",
                txns=[txn]
            ))
        
        self.bank_active[bank] = True
        self.bank_open_row[bank] = row
        
        return violations
    
    def _handle_cas(self, txn: Txn, bank: int, col_addr: int, is_write: bool) -> List[Violation]:
        """Handle READ or WRITE (CAS) command."""
        violations = []
        cmd_name = "WR" if is_write else "RD"
        
        if not self.bank_active.get(bank, False):
            violations.append(Violation(
                rule="cas_to_idle_bank",
                detail=f"{cmd_name} issued to bank {bank} which has no active row",
                severity="major",
                taxonomy_id="PROTO_001",
                txns=[txn]
            ))
            return violations
        
        open_row = self.bank_open_row.get(bank)
        we_val = 1 if is_write else 0
        
        pending_in_bank = self.pending_requests.get(bank, [])
        
        matched_idx = None
        for idx, req in enumerate(pending_in_bank):
            if (req['row'] == open_row and 
                req['col'] == col_addr and 
                req['we'] == we_val):
                matched_idx = idx
                break
        
        if matched_idx is not None:
            del pending_in_bank[matched_idx]
        else:
            violations.append(Violation(
                rule="spurious_cas",
                detail=f"{cmd_name} to bank {bank} col {col_addr} (open row {open_row}) matches no enqueued request. "
                       f"Pending requests in bank: {[(r['row'], r['col'], r['we']) for r in pending_in_bank]}",
                severity="critical",
                taxonomy_id="SCHED_002",
                txns=[txn]
            ))
        
        return violations
    
    def _handle_precharge(self, txn: Txn, bank: int) -> None:
        """Handle PRECHARGE command."""
        if bank == 0b111 or (txn.fields.get('addr', 0) & (1 << 10)):
            for b in range(self.num_banks):
                self.bank_active[b] = False
                self.bank_open_row[b] = None
        else:
            self.bank_active[bank] = False
            self.bank_open_row[bank] = None
    
    def _handle_refresh(self, txn: Txn) -> None:
        """Handle REFRESH command - all banks become idle."""
        for b in range(self.num_banks):
            self.bank_active[b] = False
            self.bank_open_row[b] = None
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check for requests never issued."""
        violations = []
        
        for bank, pending in self.pending_requests.items():
            for req in pending:
                cmd_type = "WR" if req['we'] else "RD"
                violations.append(Violation(
                    rule="request_not_serviced",
                    detail=f"Enqueued {cmd_type} to bank {bank} row {req['row']} col {req['col']} was never issued as CAS",
                    severity="critical",
                    taxonomy_id="SCHED_001",
                    txns=[req['txn']]
                ))
        
        return violations
