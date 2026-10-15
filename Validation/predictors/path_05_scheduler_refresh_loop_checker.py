from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import field
from typing import List


class RefreshSchedulerChecker(LegalityChecker):
    """Legality checker for scheduler + refresh_ctrl stage.
    
    Checks:
    - SCHED_003: Refresh requests must be serviced
    - REF_001: Refresh postpone count must not exceed max_postpone_count
    - REF_002: REFRESH must not be issued while banks are active
    """
    
    INPUT_IFACES = ('refresh_req', 'refresh_level')
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_003', 'REF_001', 'REF_002')
    
    def __init__(self, spec: dict):
        self._spec = spec
        
        refresh_policy = spec['controller_architecture']['refresh_policy']
        self._max_postpone_count = refresh_policy['max_postpone_count']
        
        geometry = spec['memory_geometry']
        self._num_banks = 1 << geometry['bank_bits']
        
        self._cmd_encoding = {
            'MRS': 0b0000,
            'REF': 0b0001,
            'PRE': 0b0010,
            'ACT': 0b0011,
            'WR': 0b0100,
            'RD': 0b0101,
            'NOP': 0b0111,
            'DESL': 0b1111,
        }
        
        self._a10_bit = 10
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        self._bank_active = [False] * self._num_banks
        
        self._refresh_request_seen = False
        self._refresh_cmd_issued = False
    
    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []
        
        if txn.iface == 'refresh_req' and txn.kind == 'request':
            self._refresh_request_seen = True
        
        elif txn.iface == 'refresh_level' and txn.kind == 'state':
            violations.extend(self._check_refresh_level(txn))
        
        elif txn.iface == 'ddr_cmd' and txn.kind == 'command':
            violations.extend(self._check_ddr_cmd(txn))
        
        return violations
    
    def _check_refresh_level(self, txn: Txn) -> List[Violation]:
        """Check REF_001: pending count and starve flag from refresh_level.state."""
        violations = []
        
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
                rule='refresh_starvation_flag',
                detail=f'starve flag asserted with pending count {pending}',
                severity='critical',
                taxonomy_id='REF_001',
                txns=[txn]
            ))
        
        return violations
    
    def _check_ddr_cmd(self, txn: Txn) -> List[Violation]:
        """Check commands and update bank state."""
        violations = []
        
        cmd = txn.fields.get('cmd', self._cmd_encoding['NOP'])
        bank = txn.fields.get('bank', 0)
        addr = txn.fields.get('addr', 0)
        
        if cmd == self._cmd_encoding['ACT']:
            self._bank_active[bank] = True
        
        elif cmd == self._cmd_encoding['PRE']:
            a10_set = (addr >> self._a10_bit) & 1
            if a10_set:
                for i in range(self._num_banks):
                    self._bank_active[i] = False
            else:
                self._bank_active[bank] = False
        
        elif cmd == self._cmd_encoding['REF']:
            self._refresh_cmd_issued = True
            
            active_banks = [i for i in range(self._num_banks) if self._bank_active[i]]
            if active_banks:
                violations.append(Violation(
                    rule='refresh_with_active_banks',
                    detail=f'REFRESH issued while banks {active_banks} are active',
                    severity='major',
                    taxonomy_id='REF_002',
                    txns=[txn]
                ))
            
            for i in range(self._num_banks):
                self._bank_active[i] = False
        
        return violations
    
    def final(self) -> List[Violation]:
        """End-of-trace rules: check SCHED_003."""
        violations = []
        
        if self._refresh_request_seen and not self._refresh_cmd_issued:
            violations.append(Violation(
                rule='refresh_never_serviced',
                detail='refresh request was observed but no REFRESH command was ever issued',
                severity='critical',
                taxonomy_id='SCHED_003',
                txns=[]
            ))
        
        return violations
