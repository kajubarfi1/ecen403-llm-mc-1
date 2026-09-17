from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from collections import defaultdict


class FullControllerLegalityChecker(LegalityChecker):
    INPUT_IFACES: tuple = ('cq_enq',)
    OUTPUT_IFACES: tuple = ('ddr_cmd',)
    COVERS: tuple = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002')

    def __init__(self, spec: dict):
        self.spec = spec
        
        geom = spec.get('memory_geometry', {})
        self.num_banks = 2 ** geom.get('bank_bits', 3)
        self.row_bits = geom.get('row_bits', 15)
        self.col_bits = geom.get('column_bits', 10)
        
        self.cmd_encoding = {
            'MRS': 0,
            'REF': 1,
            'PRE': 2,
            'ACT': 3,
            'WR': 4,
            'RD': 5,
            'NOP': 7,
            'DESL': 15
        }
        
        self.cmd_decode = {v: k for k, v in self.cmd_encoding.items()}
        
        self.reset()

    def reset(self) -> None:
        self.bank_active_row: Dict[int, Optional[int]] = {
            b: None for b in range(self.num_banks)
        }
        
        self.pending_requests: List[Tuple[Txn, int, int, int, int]] = []
        
        self.issued_cas_without_request: List[Txn] = []

    def observe(self, txn: Txn) -> List[Violation]:
        violations = []
        
        if txn.iface == 'cq_enq':
            violations.extend(self._observe_enqueue(txn))
        elif txn.iface == 'ddr_cmd':
            violations.extend(self._observe_ddr_cmd(txn))
        
        return violations

    def _observe_enqueue(self, txn: Txn) -> List[Violation]:
        row = txn.fields.get('row', 0)
        col = txn.fields.get('col', 0)
        bank = txn.fields.get('bank', 0)
        we = txn.fields.get('we', 0)
        
        self.pending_requests.append((txn, row, col, bank, we))
        
        return []

    def _observe_ddr_cmd(self, txn: Txn) -> List[Violation]:
        violations = []
        
        cmd_val = txn.fields.get('cmd', self.cmd_encoding['NOP'])
        addr = txn.fields.get('addr', 0)
        bank = txn.fields.get('bank', 0)
        
        cmd_name = self.cmd_decode.get(cmd_val, 'UNKNOWN')
        
        if cmd_name == 'ACT':
            violations.extend(self._handle_activate(txn, bank, addr))
        elif cmd_name == 'PRE':
            self._handle_precharge(txn, bank, addr)
        elif cmd_name in ('RD', 'WR'):
            violations.extend(self._handle_cas(txn, cmd_name, bank, addr))
        elif cmd_name == 'REF':
            self._handle_refresh(txn)
        
        return violations

    def _handle_activate(self, txn: Txn, bank: int, row: int) -> List[Violation]:
        violations = []
        
        if self.bank_active_row.get(bank) is not None:
            violations.append(Violation(
                rule='double_activate',
                detail=f'ACTIVATE to bank {bank} with row {row} but bank already has active row {self.bank_active_row[bank]}',
                severity='critical',
                taxonomy_id='PROTO_002',
                txns=[txn]
            ))
        
        self.bank_active_row[bank] = row
        
        return violations

    def _handle_precharge(self, txn: Txn, bank: int, addr: int) -> List[Violation]:
        all_banks = (addr >> 10) & 1
        
        if all_banks:
            for b in range(self.num_banks):
                self.bank_active_row[b] = None
        else:
            self.bank_active_row[bank] = None
        
        return []

    def _handle_cas(self, txn: Txn, cmd_name: str, bank: int, col_addr: int) -> List[Violation]:
        violations = []
        
        active_row = self.bank_active_row.get(bank)
        if active_row is None:
            violations.append(Violation(
                rule='cas_to_idle_bank',
                detail=f'{cmd_name} issued to bank {bank} which has no active row',
                severity='major',
                taxonomy_id='PROTO_001',
                txns=[txn]
            ))
        
        is_write = (cmd_name == 'WR')
        
        col = col_addr & ((1 << self.col_bits) - 1)
        
        matched_idx = None
        for idx, (req_txn, req_row, req_col, req_bank, req_we) in enumerate(self.pending_requests):
            if req_bank == bank and req_we == is_write:
                if active_row is not None and req_row == active_row:
                    matched_idx = idx
                    break
                elif active_row is None:
                    matched_idx = idx
                    break
        
        if matched_idx is None:
            for idx, (req_txn, req_row, req_col, req_bank, req_we) in enumerate(self.pending_requests):
                if req_bank == bank and req_we == is_write:
                    matched_idx = idx
                    break
        
        if matched_idx is not None:
            self.pending_requests.pop(matched_idx)
        else:
            violations.append(Violation(
                rule='spurious_cas',
                detail=f'{cmd_name} to bank {bank} has no matching enqueued request',
                severity='critical',
                taxonomy_id='SCHED_002',
                txns=[txn]
            ))
        
        return violations

    def _handle_refresh(self, txn: Txn) -> List[Violation]:
        for b in range(self.num_banks):
            self.bank_active_row[b] = None
        
        return []

    def final(self) -> List[Violation]:
        violations = []
        
        for req_txn, req_row, req_col, req_bank, req_we in self.pending_requests:
            op_type = 'WRITE' if req_we else 'READ'
            violations.append(Violation(
                rule='request_not_serviced',
                detail=f'Enqueued {op_type} request to bank {req_bank}, row {req_row}, col {req_col} was never issued',
                severity='critical',
                taxonomy_id='SCHED_001',
                txns=[req_txn]
            ))
        
        return violations
