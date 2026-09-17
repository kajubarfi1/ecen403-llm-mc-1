from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class BankTrackerSchedulerChecker(LegalityChecker):
    INPUT_IFACES = ('cfg_timing', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('PROTO_001', 'PROTO_002', 'REF_002')

    def __init__(self, spec: dict):
        self.spec = spec
        self.num_banks = 2 ** spec['memory_geometry']['bank_bits']
        
        self.CMD_NOP = 0
        self.CMD_ACT = 1
        self.CMD_RD = 2
        self.CMD_WR = 3
        self.CMD_PRE = 4
        self.CMD_REF = 5
        
        self.reset()

    def reset(self) -> None:
        self.bank_active_row = [None] * self.num_banks

    def observe(self, txn: Txn) -> List[Violation]:
        violations = []
        
        if txn.iface != 'sched_cmd':
            return violations
        
        if txn.kind != 'command':
            return violations
        
        cmd_type = txn.fields.get('type')
        bank = txn.fields.get('bank')
        row = txn.fields.get('row')
        
        if cmd_type == self.CMD_NOP:
            pass
        
        elif cmd_type == self.CMD_ACT:
            if bank is not None and self.bank_active_row[bank] is not None:
                violations.append(Violation(
                    rule="double_activate",
                    detail=f"ACTIVATE issued to bank {bank} which already has row {self.bank_active_row[bank]} active without intervening PRECHARGE",
                    severity="critical",
                    taxonomy_id="PROTO_002",
                    txns=[txn]
                ))
            if bank is not None:
                self.bank_active_row[bank] = row
        
        elif cmd_type == self.CMD_RD:
            if bank is not None and self.bank_active_row[bank] is None:
                violations.append(Violation(
                    rule="command_to_idle_bank",
                    detail=f"READ issued to bank {bank} that has no active row",
                    severity="major",
                    taxonomy_id="PROTO_001",
                    txns=[txn]
                ))
        
        elif cmd_type == self.CMD_WR:
            if bank is not None and self.bank_active_row[bank] is None:
                violations.append(Violation(
                    rule="command_to_idle_bank",
                    detail=f"WRITE issued to bank {bank} that has no active row",
                    severity="major",
                    taxonomy_id="PROTO_001",
                    txns=[txn]
                ))
        
        elif cmd_type == self.CMD_PRE:
            if bank is not None:
                self.bank_active_row[bank] = None
        
        elif cmd_type == self.CMD_REF:
            active_banks = [i for i, r in enumerate(self.bank_active_row) if r is not None]
            if active_banks:
                violations.append(Violation(
                    rule="refresh_during_active_bank",
                    detail=f"REFRESH issued while banks {active_banks} are still active (not precharged)",
                    severity="major",
                    taxonomy_id="REF_002",
                    txns=[txn]
                ))
            for i in range(self.num_banks):
                self.bank_active_row[i] = None
        
        return violations

    def final(self) -> List[Violation]:
        return []
