from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class InitRefreshLegalityChecker(LegalityChecker):
    """Legality checker for init_fsm + refresh_ctrl ordering invariants.
    
    Validates that refresh requests only occur after initialization completes,
    and that at least one refresh request is raised after init_done.
    """
    
    INPUT_IFACES = ('init_status',)
    OUTPUT_IFACES = ('refresh_req',)
    COVERS = ('REF_003', 'REF_004')
    
    def __init__(self, spec: dict):
        self._spec = spec
        self._init_done = False
        self._init_done_txn = None
        self._refresh_requested_after_init = False
        self._refresh_requests_before_init: List[Txn] = []
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        self._init_done = False
        self._init_done_txn = None
        self._refresh_requested_after_init = False
        self._refresh_requests_before_init = []
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any rule violations."""
        violations = []
        
        if txn.iface == 'init_status':
            if txn.kind == 'done':
                fail_value = txn.fields.get('fail', 0)
                if fail_value == 0:
                    self._init_done = True
                    self._init_done_txn = txn
        
        elif txn.iface == 'refresh_req':
            if txn.kind == 'request':
                if not self._init_done:
                    violations.append(Violation(
                        rule='REF_003',
                        detail='Refresh requested before init_done: refresh timer must be held until initialisation completes',
                        severity='critical',
                        taxonomy_id='REF_003',
                        txns=[txn]
                    ))
                    self._refresh_requests_before_init.append(txn)
                else:
                    self._refresh_requested_after_init = True
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check that refresh was requested after init_done."""
        violations = []
        
        if self._init_done and not self._refresh_requested_after_init:
            txns_involved = [self._init_done_txn] if self._init_done_txn else []
            violations.append(Violation(
                rule='REF_004',
                detail='No refresh request raised after init_done: controller cannot honour tREFI without requesting refresh',
                severity='critical',
                taxonomy_id='REF_004',
                txns=txns_involved
            ))
        
        return violations
