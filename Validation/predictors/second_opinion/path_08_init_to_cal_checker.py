from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional


class InitCalibrationChecker(LegalityChecker):
    """
    Legality checker for DDR3 initialization FSM and calibration block.
    
    Checks ordering invariants per specification:
    - INIT_001: MRS order (MR2, MR3, MR1, MR0) then ZQCL before init_done
    - INIT_003: init_done requires all MRS + ZQCL issued
    - CAL_001: cal_done requires init_done first
    - CAL_002: cal_zqcs requires cal_done first
    """
    
    INPUT_IFACES = ('init_cmd', 'init_status')
    OUTPUT_IFACES = ('cal_status', 'cal_zqcs')
    COVERS = ('INIT_001', 'INIT_003', 'CAL_001', 'CAL_002')
    
    # Command encoding table from schema
    CMD_ENCODING = {
        'MRS': 0b0000,
        'REF': 0b0001,
        'PRE': 0b0010,
        'ACT': 0b0011,
        'WR': 0b0100,
        'RD': 0b0101,
        'ZQCL': 0b0110,
        'NOP': 0b0111,
        'DESL': 0b1111,
    }
    
    # Reverse lookup table
    CMD_DECODE = {v: k for k, v in CMD_ENCODING.items()}
    
    def __init__(self, spec: dict):
        self._spec = spec
        
        # Extract the required MRS sequence from spec
        # Per spec initialization_sequence.$derived.init_sequence_order:
        # "MR2 → MR3 → MR1 → MR0(DLL reset) → ZQCL → init_done"
        # The spec defines mode_registers with MR0, MR1, MR2, MR3
        # The order is explicitly stated in init_sequence_order
        init_seq = spec.get('initialization_sequence', {})
        init_derived = init_seq.get('$derived', {})
        
        # Parse the init_sequence_order to extract MR order
        # Format: "... → MR2 → MR3 → MR1 → MR0(DLL reset) → ZQCL → init_done"
        sequence_order_str = init_derived.get('init_sequence_order', '')
        
        # Build expected MRS sequence from spec
        # Per spec: MR2 → MR3 → MR1 → MR0
        # The bank field carries the MR number per stage note
        self._expected_mrs_sequence = [2, 3, 1, 0]
        
        # Verify zq_calibration_on_init is true (ZQCL required)
        self._zqcl_required = init_seq.get('zq_calibration_on_init', True)
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Track MRS commands observed, in order
        self._mrs_observed: List[int] = []
        
        # Track which MRs have been programmed (set of MR numbers)
        self._mrs_programmed: set = set()
        
        # Track ZQCL issuance
        self._zqcl_issued: bool = False
        
        # Track init_done observation
        self._init_done_observed: bool = False
        
        # Track cal_done observation
        self._cal_done_observed: bool = False
        
        # Transaction history for violation reporting
        self._last_mrs_txn: Optional[Txn] = None
        self._last_zqcl_txn: Optional[Txn] = None
        self._init_done_txn: Optional[Txn] = None
        self._cal_done_txn: Optional[Txn] = None
    
    def observe(self, txn: Txn) -> List[Violation]:
        """
        Consume one observed transaction and return any rule violations.
        
        Per JESD79-3, for MRS command the bank field BA[2:0] encodes the 
        mode register number being programmed.
        """
        violations = []
        
        iface = txn.iface
        kind = txn.kind
        
        if iface == 'init_cmd' and kind == 'command':
            violations.extend(self._observe_init_cmd(txn))
        elif iface == 'init_status' and kind == 'done':
            violations.extend(self._observe_init_status(txn))
        elif iface == 'cal_status' and kind == 'done':
            violations.extend(self._observe_cal_status(txn))
        elif iface == 'cal_zqcs' and kind == 'request':
            violations.extend(self._observe_cal_zqcs(txn))
        
        return violations
    
    def _observe_init_cmd(self, txn: Txn) -> List[Violation]:
        """Process an init_cmd command transaction."""
        violations = []
        
        cmd_value = txn.fields.get('cmd', None)
        if cmd_value is None:
            return violations
        
        cmd_name = self.CMD_DECODE.get(cmd_value, 'UNKNOWN')
        
        if cmd_name == 'MRS':
            # Per stage note: "For an MRS command the bank field carries the
            # mode-register number (JESD79-3 BA[2:0])."
            mr_number = txn.fields.get('bank', None)
            if mr_number is None:
                return violations
            
            # Check INIT_001: MRS commands must be in correct order
            # Expected sequence: MR2, MR3, MR1, MR0
            violations.extend(self._check_mrs_order(txn, mr_number))
            
            self._mrs_observed.append(mr_number)
            self._mrs_programmed.add(mr_number)
            self._last_mrs_txn = txn
            
        elif cmd_name == 'ZQCL':
            # Check INIT_001: ZQCL must come after all MRS commands
            # Per spec sequence: MR2 → MR3 → MR1 → MR0 → ZQCL
            if not self._all_mrs_programmed():
                expected_mrs = self._expected_mrs_sequence
                missing = [mr for mr in expected_mrs if mr not in self._mrs_programmed]
                violations.append(Violation(
                    rule='mrs_before_zqcl',
                    detail=f'ZQCL issued before all MRS commands; missing MR{missing}; '
                           f'observed MRS sequence: {self._mrs_observed}',
                    severity='critical',
                    taxonomy_id='INIT_001',
                    txns=[txn]
                ))
            
            self._zqcl_issued = True
            self._last_zqcl_txn = txn
        
        return violations
    
    def _check_mrs_order(self, txn: Txn, mr_number: int) -> List[Violation]:
        """
        Check INIT_001: Mode register commands must be in order MR2, MR3, MR1, MR0.
        
        Per spec initialization_sequence.$derived.init_sequence_order:
        "MR2 → MR3 → MR1 → MR0(DLL reset) → ZQCL → init_done"
        """
        violations = []
        
        expected_seq = self._expected_mrs_sequence  # [2, 3, 1, 0]
        current_pos = len(self._mrs_observed)
        
        # If we've already seen all expected MRS commands, additional ones
        # are not specified by the sequence but we only check the mandated order
        if current_pos < len(expected_seq):
            expected_mr = expected_seq[current_pos]
            if mr_number != expected_mr:
                violations.append(Violation(
                    rule='mrs_order',
                    detail=f'MRS to MR{mr_number} at position {current_pos}; '
                           f'expected MR{expected_mr}; '
                           f'spec requires order MR2→MR3→MR1→MR0; '
                           f'sequence so far: {self._mrs_observed}',
                    severity='critical',
                    taxonomy_id='INIT_001',
                    txns=[txn]
                ))
        
        return violations
    
    def _all_mrs_programmed(self) -> bool:
        """Check if all required MRS commands have been issued."""
        for mr in self._expected_mrs_sequence:
            if mr not in self._mrs_programmed:
                return False
        return True
    
    def _observe_init_status(self, txn: Txn) -> List[Violation]:
        """
        Process an init_status done transaction.
        
        INIT_003: init_done must not be raised until every mode register 
        in the sequence has been programmed and ZQCL has been issued.
        """
        violations = []
        
        # init_status done indicates init_done
        # Check INIT_003: all MRS + ZQCL must have been issued
        
        missing_mrs = [mr for mr in self._expected_mrs_sequence 
                       if mr not in self._mrs_programmed]
        
        if missing_mrs:
            violations.append(Violation(
                rule='init_done_premature_mrs',
                detail=f'init_done raised before all MRS commands issued; '
                       f'missing: MR{missing_mrs}; '
                       f'observed MRS sequence: {self._mrs_observed}',
                severity='critical',
                taxonomy_id='INIT_003',
                txns=[txn]
            ))
        
        if self._zqcl_required and not self._zqcl_issued:
            violations.append(Violation(
                rule='init_done_premature_zqcl',
                detail='init_done raised before ZQCL issued; '
                       'spec requires zq_calibration_on_init',
                severity='critical',
                taxonomy_id='INIT_003',
                txns=[txn]
            ))
        
        self._init_done_observed = True
        self._init_done_txn = txn
        
        return violations
    
    def _observe_cal_status(self, txn: Txn) -> List[Violation]:
        """
        Process a cal_status done transaction.
        
        CAL_001: Calibration must not report cal_done before init_done 
        has been observed.
        """
        violations = []
        
        if not self._init_done_observed:
            violations.append(Violation(
                rule='cal_done_before_init_done',
                detail='cal_done raised before init_done was observed',
                severity='critical',
                taxonomy_id='CAL_001',
                txns=[txn]
            ))
        
        self._cal_done_observed = True
        self._cal_done_txn = txn
        
        return violations
    
    def _observe_cal_zqcs(self, txn: Txn) -> List[Violation]:
        """
        Process a cal_zqcs request transaction.
        
        CAL_002: A periodic ZQCS request must not be raised before cal_done.
        
        Per spec calibration section: periodic_recalibration_enable controls
        periodic ZQCS. These are only valid after calibration is complete.
        """
        violations = []
        
        if not self._cal_done_observed:
            violations.append(Violation(
                rule='zqcs_before_cal_done',
                detail='Periodic ZQCS request raised before cal_done was observed',
                severity='critical',
                taxonomy_id='CAL_002',
                txns=[txn]
            ))
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace rules.
        
        For this checker, the invariants are about ordering of events that
        DID happen, not liveness requirements. If init_done never occurred,
        that's not necessarily a violation of these specific rules - the
        trace may simply be a partial capture.
        
        The specification does not mandate that init_done MUST occur within
        any trace; it only mandates what must precede it IF it occurs.
        Similarly for cal_done and cal_zqcs.
        """
        violations = []
        
        # No end-of-trace liveness requirements specified for these invariants.
        # INIT_001/INIT_003 are checked when init_done is observed.
        # CAL_001 is checked when cal_done is observed.
        # CAL_002 is checked when cal_zqcs is observed.
        
        return violations
