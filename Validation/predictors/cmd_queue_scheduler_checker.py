from txn_contract import LegalityChecker, Txn, Violation
from typing import List, Dict, Optional, Tuple


class SchedulerLegalityChecker(LegalityChecker):
    INPUT_IFACES = ('cq_enq', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'REF_002', 'SCHED_004')

    def __init__(self, spec: dict):
        self.spec = spec
        self.num_banks = 1 << spec['memory_geometry']['bank_bits']
        
        self.CMD_NOP = 0
        self.CMD_ACT = 1
        self.CMD_RD = 2
        self.CMD_WR = 3
        self.CMD_PRE = 4
        self.CMD_REF = 5
        
        self.reset()

    def reset(self) -> None:
        self.pending_requests: List[Tuple[int, int, int, int, Txn]] = []
        self.bank_active_row: Dict[int, Optional[int]] = {
            i: None for i in range(self.num_banks)
        }

    def observe(self, txn: Txn) -> List[Violation]:
        violations = []

        if txn.iface == 'cq_enq' and txn.kind == 'enqueue':
            row = txn.fields['row']
            col = txn.fields['col']
            bank = txn.fields['bank']
            we = txn.fields['we']
            self.pending_requests.append((row, col, bank, we, txn))

        elif txn.iface == 'sched_cmd' and txn.kind == 'command':
            cmd_type = txn.fields['type']
            bank = txn.fields['bank']
            row = txn.fields['row']
            col = txn.fields['col']
            we = txn.fields['we']

            if cmd_type == self.CMD_ACT:
                if self.bank_active_row[bank] is not None:
                    violations.append(Violation(
                        rule="double_activate",
                        detail=f"ACTIVATE to bank {bank} which already has row {self.bank_active_row[bank]} active",
                        severity="critical",
                        taxonomy_id="PROTO_002",
                        txns=[txn]
                    ))

                rows_needed_in_bank = set()
                for r, c, b, w, t in self.pending_requests:
                    if b == bank:
                        rows_needed_in_bank.add(r)

                if row not in rows_needed_in_bank:
                    violations.append(Violation(
                        rule="activate_wrong_row",
                        detail=f"ACTIVATE to bank {bank} row {row} but no pending request needs that row; needed rows: {rows_needed_in_bank if rows_needed_in_bank else 'none'}",
                        severity="critical",
                        taxonomy_id="SCHED_004",
                        txns=[txn]
                    ))

                self.bank_active_row[bank] = row

            elif cmd_type == self.CMD_RD or cmd_type == self.CMD_WR:
                if self.bank_active_row[bank] is None:
                    cmd_name = "RD" if cmd_type == self.CMD_RD else "WR"
                    violations.append(Violation(
                        rule="cas_to_idle_bank",
                        detail=f"{cmd_name} issued to bank {bank} which has no active row",
                        severity="major",
                        taxonomy_id="PROTO_001",
                        txns=[txn]
                    ))

                active_row = self.bank_active_row[bank]
                expected_we = 0 if cmd_type == self.CMD_RD else 1

                match_idx = None
                for idx, (r, c, b, w, t) in enumerate(self.pending_requests):
                    if b == bank and r == active_row and c == col and w == expected_we:
                        match_idx = idx
                        break

                if match_idx is None:
                    cmd_name = "RD" if cmd_type == self.CMD_RD else "WR"
                    violations.append(Violation(
                        rule="cas_no_matching_request",
                        detail=f"{cmd_name} to bank {bank} row {active_row} col {col} matches no enqueued request",
                        severity="critical",
                        taxonomy_id="SCHED_002",
                        txns=[txn]
                    ))
                else:
                    self.pending_requests.pop(match_idx)

            elif cmd_type == self.CMD_PRE:
                self.bank_active_row[bank] = None

            elif cmd_type == self.CMD_REF:
                active_banks = [b for b in range(self.num_banks) if self.bank_active_row[b] is not None]
                if active_banks:
                    violations.append(Violation(
                        rule="refresh_active_banks",
                        detail=f"REFRESH issued while banks {active_banks} are still active",
                        severity="major",
                        taxonomy_id="REF_002",
                        txns=[txn]
                    ))
                for b in range(self.num_banks):
                    self.bank_active_row[b] = None

        return violations

    def final(self) -> List[Violation]:
        violations = []

        for r, c, b, w, t in self.pending_requests:
            op = "WR" if w else "RD"
            violations.append(Violation(
                rule="request_dropped",
                detail=f"Request to bank {b} row {r} col {c} ({op}) was never serviced",
                severity="critical",
                taxonomy_id="SCHED_001",
                txns=[t]
            ))

        return violations
