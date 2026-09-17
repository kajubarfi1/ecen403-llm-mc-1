from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import dataclass, field
from typing import List


class InitCalibrationChecker(LegalityChecker):
    """Legality checker for init_fsm + calibration stage.
    
    Validates:
    - INIT_001: MRS order (MR2, MR3, MR1, MR0) then ZQCL before init_done
    - INIT_003: init_done requires all MRs + ZQCL issued
    - CAL_001: cal_done requires init_done first
    - CAL_002: ZQCS requires cal_done first
    """

    INPUT_IFACES = ('init_cmd', 'init_status')
    OUTPUT_IFACES = ('cal_status', 'cal_zqcs')
    COVERS = ('INIT_001', 'INIT_003', 'CAL_001', 'CAL_002')

    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract the initialization sequence order from spec
        init_seq = spec.get('initialization_sequence', {})
        derived = init_seq.get('$derived', {})
        # The spec states: MR2 -> MR3 -> MR1 -> MR0 -> ZQCL -> init_done
        # This is the required MRS order (by MR number)
        self.expected_mr_order = [2, 3, 1, 0]
        
        # Command encoding from schema
        self.CMD_MRS = 0b0000
        self.CMD_ZQCL = 0b0110
        
        self.reset()

    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Track which MRs have been programmed (in order)
        self.mrs_issued = []  # List of MR numbers in order they were issued
        self.zqcl_issued = False
        self.init_done_seen = False
        self.cal_done_seen = False
        
        # Track transactions for violation reporting
        self.mrs_txns = []
        self.zqcl_txn = None
        self.init_done_txn = None
        self.cal_done_txn = None

    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        violations = []
        
        if txn.iface == 'init_cmd' and txn.kind == 'command':
            violations.extend(self._handle_init_cmd(txn))
        elif txn.iface == 'init_status' and txn.kind == 'done':
            violations.extend(self._handle_init_status(txn))
        elif txn.iface == 'cal_status' and txn.kind == 'done':
            violations.extend(self._handle_cal_status(txn))
        elif txn.iface == 'cal_zqcs' and txn.kind == 'request':
            violations.extend(self._handle_cal_zqcs(txn))
        
        return violations

    def _handle_init_cmd(self, txn: Txn) -> List[Violation]:
        """Handle init_cmd command transactions."""
        violations = []
        
        cmd = txn.fields.get('cmd', -1)
        bank = txn.fields.get('bank', -1)
        
        if cmd == self.CMD_MRS:
            # MRS command - bank field is the MR number
            mr_num = bank
            
            # Check if init_done already happened - MRS after init_done is violation
            if self.init_done_seen:
                violations.append(Violation(
                    rule="INIT_001",
                    detail=f"MRS to MR{mr_num} issued after init_done",
                    severity="critical",
                    taxonomy_id="INIT_001",
                    txns=[txn, self.init_done_txn] if self.init_done_txn else [txn]
                ))
            else:
                # Check order - what MR should be next?
                next_index = len(self.mrs_issued)
                if next_index < len(self.expected_mr_order):
                    expected_mr = self.expected_mr_order[next_index]
                    if mr_num != expected_mr:
                        violations.append(Violation(
                            rule="INIT_001",
                            detail=f"MRS order violation: expected MR{expected_mr}, got MR{mr_num}",
                            severity="critical",
                            taxonomy_id="INIT_001",
                            txns=[txn]
                        ))
                    else:
                        self.mrs_issued.append(mr_num)
                        self.mrs_txns.append(txn)
                else:
                    # Extra MRS after all expected ones - still a violation
                    violations.append(Violation(
                        rule="INIT_001",
                        detail=f"Unexpected MRS to MR{mr_num} after sequence complete",
                        severity="critical",
                        taxonomy_id="INIT_001",
                        txns=[txn]
                    ))
        
        elif cmd == self.CMD_ZQCL:
            # ZQCL command
            if self.init_done_seen:
                violations.append(Violation(
                    rule="INIT_001",
                    detail="ZQCL issued after init_done",
                    severity="critical",
                    taxonomy_id="INIT_001",
                    txns=[txn, self.init_done_txn] if self.init_done_txn else [txn]
                ))
            elif len(self.mrs_issued) < len(self.expected_mr_order):
                # ZQCL before all MRS commands
                missing = [self.expected_mr_order[i] for i in range(len(self.mrs_issued), len(self.expected_mr_order))]
                violations.append(Violation(
                    rule="INIT_001",
                    detail=f"ZQCL issued before all MRS commands; missing MR{missing}",
                    severity="critical",
                    taxonomy_id="INIT_001",
                    txns=[txn]
                ))
            else:
                self.zqcl_issued = True
                self.zqcl_txn = txn
        
        return violations

    def _handle_init_status(self, txn: Txn) -> List[Violation]:
        """Handle init_status done transactions."""
        violations = []
        
        fail = txn.fields.get('fail', 0)
        
        # Only check if not a failure
        if not fail:
            # INIT_003: init_done must not be raised until all MRs programmed and ZQCL issued
            if len(self.mrs_issued) < len(self.expected_mr_order):
                missing = [self.expected_mr_order[i] for i in range(len(self.mrs_issued), len(self.expected_mr_order))]
                violations.append(Violation(
                    rule="INIT_003",
                    detail=f"init_done raised before all MRS commands; missing MR{missing}",
                    severity="critical",
                    taxonomy_id="INIT_003",
                    txns=[txn]
                ))
            
            if not self.zqcl_issued:
                violations.append(Violation(
                    rule="INIT_003",
                    detail="init_done raised before ZQCL issued",
                    severity="critical",
                    taxonomy_id="INIT_003",
                    txns=[txn]
                ))
        
        self.init_done_seen = True
        self.init_done_txn = txn
        
        return violations

    def _handle_cal_status(self, txn: Txn) -> List[Violation]:
        """Handle cal_status done transactions."""
        violations = []
        
        fail = txn.fields.get('fail', 0)
        
        # CAL_001: cal_done must not happen before init_done
        if not self.init_done_seen:
            violations.append(Violation(
                rule="CAL_001",
                detail="cal_done raised before init_done observed",
                severity="critical",
                taxonomy_id="CAL_001",
                txns=[txn]
            ))
        
        self.cal_done_seen = True
        self.cal_done_txn = txn
        
        return violations

    def _handle_cal_zqcs(self, txn: Txn) -> List[Violation]:
        """Handle cal_zqcs request transactions."""
        violations = []
        
        # CAL_002: periodic ZQCS must not be raised before cal_done
        if not self.cal_done_seen:
            violations.append(Violation(
                rule="CAL_002",
                detail="ZQCS request raised before cal_done",
                severity="critical",
                taxonomy_id="CAL_002",
                txns=[txn]
            ))
        
        return violations

    def final(self) -> List[Violation]:
        """End-of-trace rules."""
        # No end-of-trace violations defined for this checker
        # The invariants are all about ordering, not completeness
        return []
