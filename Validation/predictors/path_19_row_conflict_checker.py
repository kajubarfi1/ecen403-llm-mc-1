from txn_contract import LegalityChecker, Txn, Violation
from typing import List, Optional, Tuple


class FullControllerChecker(LegalityChecker):
    INPUT_IFACES = ('cq_enq',)
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'SCHED_004')

    CMD_MRS = 0
    CMD_REF = 1
    CMD_PRE = 2
    CMD_ACT = 3
    CMD_WR = 4
    CMD_RD = 5
    CMD_NOP = 7
    CMD_DESL = 15

    def __init__(self, spec: dict):
        self.spec = spec
        self.num_banks = 2 ** spec['memory_geometry']['bank_bits']
        self.col_bits = spec['memory_geometry']['column_bits']
        self.col_mask = (1 << self.col_bits) - 1
        self.row_bits = spec['memory_geometry']['row_bits']
        self.row_mask = (1 << self.row_bits) - 1
        self.reset()

    def reset(self) -> None:
        self.bank_state: List[Optional[int]] = [None] * self.num_banks
        self.pending_requests: List[Tuple[int, int, int, int, Txn]] = []

    def observe(self, txn: Txn) -> List[Violation]:
        violations = []

        if txn.iface == 'cq_enq':
            row = txn.fields['row']
            col = txn.fields['col']
            bank = txn.fields['bank']
            we = txn.fields['we']
            self.pending_requests.append((row, col, bank, we, txn))

        elif txn.iface == 'ddr_cmd':
            cmd = txn.fields['cmd']
            addr = txn.fields['addr']
            bank = txn.fields['bank']

            if cmd == self.CMD_ACT:
                row_addr = addr & self.row_mask
                if self.bank_state[bank] is not None:
                    violations.append(Violation(
                        rule='double_activate',
                        detail=f'ACTIVATE to bank {bank} which already has row {self.bank_state[bank]} active',
                        severity='critical',
                        taxonomy_id='PROTO_002',
                        txns=[txn]
                    ))
                self.bank_state[bank] = row_addr

            elif cmd == self.CMD_PRE:
                a10 = (addr >> 10) & 1
                if a10:
                    for b in range(self.num_banks):
                        self.bank_state[b] = None
                else:
                    self.bank_state[bank] = None

            elif cmd == self.CMD_RD or cmd == self.CMD_WR:
                is_write = 1 if cmd == self.CMD_WR else 0
                col_addr = addr & self.col_mask

                if self.bank_state[bank] is None:
                    violations.append(Violation(
                        rule='cas_to_idle_bank',
                        detail=f'{"WRITE" if is_write else "READ"} issued to bank {bank} which has no active row',
                        severity='major',
                        taxonomy_id='PROTO_001',
                        txns=[txn]
                    ))
                    candidates = [
                        (i, r, c, b, w, t)
                        for i, (r, c, b, w, t) in enumerate(self.pending_requests)
                        if b == bank and c == col_addr and w == is_write
                    ]
                    if candidates:
                        idx, req_row, req_col, req_bank, req_we, req_txn = candidates[0]
                        violations.append(Violation(
                            rule='wrong_row',
                            detail=f'{"WRITE" if is_write else "READ"} to bank {bank} col {col_addr} issued with no active row; request wanted row {req_row}',
                            severity='critical',
                            taxonomy_id='SCHED_004',
                            txns=[req_txn, txn]
                        ))
                        self.pending_requests.pop(idx)
                    else:
                        violations.append(Violation(
                            rule='orphan_cas',
                            detail=f'{"WRITE" if is_write else "READ"} to bank {bank} col {col_addr} has no matching enqueued request',
                            severity='critical',
                            taxonomy_id='SCHED_002',
                            txns=[txn]
                        ))
                else:
                    open_row = self.bank_state[bank]
                    exact_match_idx = None
                    partial_match = None

                    for i, (req_row, req_col, req_bank, req_we, req_txn) in enumerate(self.pending_requests):
                        if req_bank == bank and req_col == col_addr and req_we == is_write:
                            if req_row == open_row:
                                exact_match_idx = i
                                break
                            elif partial_match is None:
                                partial_match = (i, req_row, req_txn)

                    if exact_match_idx is not None:
                        self.pending_requests.pop(exact_match_idx)
                    elif partial_match is not None:
                        idx, req_row, req_txn = partial_match
                        violations.append(Violation(
                            rule='wrong_row',
                            detail=f'{"WRITE" if is_write else "READ"} to bank {bank} col {col_addr} executed on row {open_row} but request asked for row {req_row}',
                            severity='critical',
                            taxonomy_id='SCHED_004',
                            txns=[req_txn, txn]
                        ))
                        self.pending_requests.pop(idx)
                    else:
                        violations.append(Violation(
                            rule='orphan_cas',
                            detail=f'{"WRITE" if is_write else "READ"} to bank {bank} col {col_addr} row {open_row} has no matching enqueued request',
                            severity='critical',
                            taxonomy_id='SCHED_002',
                            txns=[txn]
                        ))

            elif cmd == self.CMD_REF:
                for b in range(self.num_banks):
                    self.bank_state[b] = None

        return violations

    def final(self) -> List[Violation]:
        violations = []
        for row, col, bank, we, txn in self.pending_requests:
            violations.append(Violation(
                rule='request_not_serviced',
                detail=f'Request to bank {bank} row {row} col {col} {"write" if we else "read"} was never issued as a matching CAS',
                severity='critical',
                taxonomy_id='SCHED_001',
                txns=[txn]
            ))
        return violations
