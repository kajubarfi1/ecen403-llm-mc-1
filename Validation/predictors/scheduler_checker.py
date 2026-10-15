from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class SchedulerLegalityChecker(LegalityChecker):
    """Legality checker for scheduler refresh and bank state invariants."""

    INPUT_IFACES = ('refresh_req', 'refresh_level')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')

    CMD_NOP = 0
    CMD_ACT = 1
    CMD_RD = 2
    CMD_WR = 3
    CMD_PRE = 4
    CMD_REF = 5

    def __init__(self, spec: dict):
        self._spec = spec
        self._max_postpone_count = spec['controller_architecture']['refresh_policy']['max_postpone_count']
        self._num_banks = 1 << spec['memory_geometry']['bank_bits']
        self.reset()

    def reset(self) -> None:
        """Return all tracked state to power-on."""
        self._refresh_request_seen = False
        self._refresh_command_issued = False
        self._refresh_request_txns = []
        self._bank_active = [False] * self._num_banks

    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []

        if txn.iface == 'refresh_req':
            if txn.kind == 'request':
                self._refresh_request_seen = True
                self._refresh_request_txns.append(txn)

        elif txn.iface == 'refresh_level':
            if txn.kind == 'state':
                pending = txn.fields.get('pending', 0)
                starve = txn.fields.get('starve', 0)

                if pending > self._max_postpone_count:
                    violations.append(Violation(
                        rule='refresh_postpone_exceeded',
                        detail=f'pending count {pending} exceeds max_postpone_count {self._max_postpone_count}',
                        severity='critical',
                        taxonomy_id='REF_001',
                        txns=[txn]
                    ))

                if starve == 1:
                    violations.append(Violation(
                        rule='refresh_starve_flag',
                        detail=f'starve flag asserted with pending count {pending}',
                        severity='critical',
                        taxonomy_id='REF_001',
                        txns=[txn]
                    ))

        elif txn.iface == 'sched_cmd':
            if txn.kind == 'command':
                cmd_type = txn.fields.get('type', self.CMD_NOP)
                bank = txn.fields.get('bank', 0)

                if cmd_type == self.CMD_ACT:
                    self._bank_active[bank] = True

                elif cmd_type == self.CMD_PRE:
                    self._bank_active[bank] = False

                elif cmd_type == self.CMD_REF:
                    self._refresh_command_issued = True

                    active_banks = [i for i, active in enumerate(self._bank_active) if active]
                    if active_banks:
                        violations.append(Violation(
                            rule='refresh_during_active_bank',
                            detail=f'REFRESH issued while banks {active_banks} are active',
                            severity='major',
                            taxonomy_id='REF_002',
                            txns=[txn]
                        ))

                    for i in range(self._num_banks):
                        self._bank_active[i] = False

        return violations

    def final(self) -> List[Violation]:
        """End-of-trace rules: check if refresh requests were serviced."""
        violations = []

        if self._refresh_request_seen and not self._refresh_command_issued:
            violations.append(Violation(
                rule='refresh_never_serviced',
                detail='refresh request was seen but no REFRESH command was ever issued',
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=self._refresh_request_txns[:3]
            ))

        return violations
