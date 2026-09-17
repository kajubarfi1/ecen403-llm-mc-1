from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class RefreshSchedulerChecker(LegalityChecker):
    INPUT_IFACES = ('refresh_req',)
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')

    CMD_MRS = 0b0000
    CMD_REF = 0b0001
    CMD_PRE = 0b0010
    CMD_ACT = 0b0011
    CMD_WR = 0b0100
    CMD_RD = 0b0101
    CMD_NOP = 0b0111
    CMD_DESL = 0b1111

    def __init__(self, spec: dict):
        self.spec = spec
        self.max_postpone_count = spec['controller_architecture']['refresh_policy']['max_postpone_count']
        self.num_banks = spec['controller_architecture']['$derived']['bank_count']
        self.reset()

    def reset(self) -> None:
        self.bank_active = [False] * self.num_banks
        self.pending_refresh_count = 0
        self.total_refresh_requests_seen = 0
        self.total_refresh_commands_issued = 0
        self.last_pending_count = 0
        self.refresh_request_txns = []

    def observe(self, txn: Txn) -> List[Violation]:
        violations = []

        if txn.iface == 'refresh_req':
            pending = txn.fields.get('pending', 0)
            starve = txn.fields.get('starve', 0)

            if pending > self.last_pending_count:
                new_requests = pending - self.last_pending_count
                self.total_refresh_requests_seen += new_requests
                self.refresh_request_txns.append(txn)

            self.pending_refresh_count = pending
            self.last_pending_count = pending

            if pending > self.max_postpone_count:
                violations.append(Violation(
                    rule="REF_001",
                    detail=f"Refresh postpone count {pending} exceeded max_postpone_count {self.max_postpone_count}",
                    severity="critical",
                    taxonomy_id="REF_001",
                    txns=[txn]
                ))

            if starve:
                violations.append(Violation(
                    rule="REF_001",
                    detail=f"Refresh starvation flag asserted (pending={pending}, max_postpone={self.max_postpone_count})",
                    severity="critical",
                    taxonomy_id="REF_001",
                    txns=[txn]
                ))

        elif txn.iface == 'ddr_cmd':
            cmd = txn.fields.get('cmd', self.CMD_NOP)
            bank = txn.fields.get('bank', 0)
            addr = txn.fields.get('addr', 0)

            if cmd == self.CMD_ACT:
                if 0 <= bank < self.num_banks:
                    self.bank_active[bank] = True

            elif cmd == self.CMD_PRE:
                precharge_all = (addr >> 10) & 1
                if precharge_all:
                    for i in range(self.num_banks):
                        self.bank_active[i] = False
                else:
                    if 0 <= bank < self.num_banks:
                        self.bank_active[bank] = False

            elif cmd == self.CMD_REF:
                self.total_refresh_commands_issued += 1

                active_banks = [i for i, active in enumerate(self.bank_active) if active]
                if active_banks:
                    violations.append(Violation(
                        rule="REF_002",
                        detail=f"REFRESH issued while banks {active_banks} are still active (not precharged)",
                        severity="major",
                        taxonomy_id="REF_002",
                        txns=[txn]
                    ))

                if self.pending_refresh_count > 0:
                    self.pending_refresh_count -= 1
                    self.last_pending_count = self.pending_refresh_count

        return violations

    def final(self) -> List[Violation]:
        violations = []

        if self.pending_refresh_count > 0:
            violations.append(Violation(
                rule="SCHED_003",
                detail=f"End of trace with {self.pending_refresh_count} pending refresh request(s) not serviced",
                severity="critical",
                taxonomy_id="SCHED_003",
                txns=self.refresh_request_txns[-3:] if self.refresh_request_txns else []
            ))

        outstanding = self.total_refresh_requests_seen - self.total_refresh_commands_issued
        if outstanding > 0 and self.pending_refresh_count == 0:
            violations.append(Violation(
                rule="SCHED_003",
                detail=f"Total refresh requests ({self.total_refresh_requests_seen}) exceeds REFRESH commands issued ({self.total_refresh_commands_issued})",
                severity="critical",
                taxonomy_id="SCHED_003",
                txns=self.refresh_request_txns[-3:] if self.refresh_request_txns else []
            ))

        return violations
