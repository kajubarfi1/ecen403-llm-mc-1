from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class RefreshSchedulerChecker(LegalityChecker):
    """Legality checker for refresh request handling and scheduler refresh commands."""

    INPUT_IFACES = ('refresh_req',)
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')

    CMD_NOP = 0
    CMD_ACT = 1
    CMD_RD = 2
    CMD_WR = 3
    CMD_PRE = 4
    CMD_REF = 5

    def __init__(self, spec: dict):
        self.spec = spec
        self.max_postpone_count = spec['controller_architecture']['refresh_policy']['max_postpone_count']
        self.num_banks = 1 << spec['memory_geometry']['bank_bits']
        self.reset()

    def reset(self) -> None:
        """Return all tracked state to power-on."""
        self.bank_active = [False] * self.num_banks
        self.bank_open_row = [None] * self.num_banks
        self.pending_refresh_requests = 0
        self.prev_pending_cnt = 0
        self.prev_urgent = 0
        self.refresh_requests_outstanding = 0
        self.max_pending_seen = 0

    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []

        if txn.iface == 'refresh_req':
            violations.extend(self._handle_refresh_req(txn))
        elif txn.iface == 'sched_cmd':
            violations.extend(self._handle_sched_cmd(txn))

        return violations

    def _handle_refresh_req(self, txn: Txn) -> List[Violation]:
        """Handle refresh request transactions."""
        violations = []

        if txn.kind != 'request':
            return violations

        pending = txn.fields.get('pending', 0)
        urgent = txn.fields.get('urgent', 0)
        starve = txn.fields.get('starve', 0)

        if pending > self.prev_pending_cnt:
            new_requests = pending - self.prev_pending_cnt
            self.refresh_requests_outstanding += new_requests

        if pending > self.max_pending_seen:
            self.max_pending_seen = pending

        if pending > self.max_postpone_count:
            violations.append(Violation(
                taxonomy_id='REF_001',
                rule='Refresh postpone count exceeded max_postpone_count',
                detail=f'Pending refresh count {pending} exceeds max_postpone_count {self.max_postpone_count}'
            ))

        self.prev_pending_cnt = pending
        self.prev_urgent = urgent

        return violations

    def _handle_sched_cmd(self, txn: Txn) -> List[Violation]:
        """Handle scheduler command transactions."""
        violations = []

        if txn.kind != 'command':
            return violations

        cmd_type = txn.fields.get('type', self.CMD_NOP)
        bank = txn.fields.get('bank', 0)
        row = txn.fields.get('row', 0)

        if cmd_type == self.CMD_ACT:
            self.bank_active[bank] = True
            self.bank_open_row[bank] = row

        elif cmd_type == self.CMD_PRE:
            self.bank_active[bank] = False
            self.bank_open_row[bank] = None

        elif cmd_type == self.CMD_REF:
            any_active = any(self.bank_active)
            if any_active:
                active_banks = [i for i, active in enumerate(self.bank_active) if active]
                violations.append(Violation(
                    taxonomy_id='REF_002',
                    rule='REFRESH issued while one or more banks are still active',
                    detail=f'REFRESH command issued with banks {active_banks} still active (not precharged)'
                ))

            if self.refresh_requests_outstanding > 0:
                self.refresh_requests_outstanding -= 1

            for i in range(self.num_banks):
                self.bank_active[i] = False
                self.bank_open_row[i] = None

        elif cmd_type == self.CMD_RD or cmd_type == self.CMD_WR:
            pass

        return violations

    def final(self) -> List[Violation]:
        """End-of-trace rules: check for unserviced refresh requests."""
        violations = []

        if self.refresh_requests_outstanding > 0:
            violations.append(Violation(
                taxonomy_id='SCHED_003',
                rule='Every refresh request must eventually be serviced with a REFRESH command',
                detail=f'{self.refresh_requests_outstanding} refresh request(s) were never serviced with a REFRESH command'
            ))

        return violations
