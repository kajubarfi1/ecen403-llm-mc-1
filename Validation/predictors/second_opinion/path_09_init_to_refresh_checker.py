from txn_contract import LegalityChecker, Txn, Violation
from typing import List


class InitRefreshLegalityChecker(LegalityChecker):
    """
    Legality checker for init_fsm + refresh_ctrl ordering invariants.
    
    This checker validates the ordering relationship between initialization
    completion and refresh requests. Per the specification, refresh requests
    must not occur before init_done, and at least one refresh must be
    requested after init_done before trace ends.
    """
    
    INPUT_IFACES = ('init_status',)
    OUTPUT_IFACES = ('refresh_req',)
    COVERS = ('REF_003', 'REF_004')
    
    # Table mapping invariant IDs to their properties
    # Derived from failure_taxonomy and stage invariant descriptions
    INVARIANT_TABLE = {
        'REF_003': {
            'rule': 'no_refresh_before_init',
            'severity': 'critical',
            'description': 'No refresh may be requested before init_done: the refresh timer is held until initialisation completes.'
        },
        'REF_004': {
            'rule': 'refresh_after_init_required',
            'severity': 'critical',
            'description': 'After init_done at least one refresh request must be raised before the end of the trace; a controller that never requests refresh cannot honour tREFI.'
        }
    }
    
    # Table mapping transaction interface+kind to checker actions
    # Each entry specifies what state transitions and checks to perform
    TXN_ACTION_TABLE = {
        ('init_status', 'done'): 'handle_init_done',
        ('refresh_req', 'request'): 'handle_refresh_request',
    }
    
    def __init__(self, spec: dict):
        """
        Initialize checker state from specification.
        
        The spec contains refresh_policy under controller_architecture,
        but for these ordering invariants we only need to track:
        - Whether init_done has been observed
        - Whether any refresh request has been observed after init_done
        """
        self._spec = spec
        
        # Extract any relevant configuration from spec for future extensibility
        # Per spec: controller_architecture.refresh_policy exists but these
        # ordering rules don't depend on its specific values (max_postpone_count, etc.)
        # The timing (tREFI) is handled by SVA per stage note (TIMING_012 in cmd_gen_sva)
        
        self.reset()
    
    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Track whether init_done event has been observed
        # Per spec initialization_sequence.$derived.init_sequence_order:
        # init_done is the final event of initialization
        self._init_done_observed = False
        
        # Track the init_status transaction that signaled init_done (for violation reporting)
        self._init_done_txn = None
        
        # Track whether at least one refresh request occurred after init_done
        # Per REF_004: required for tREFI compliance
        self._refresh_requested_after_init = False
        
        # Track refresh requests observed before init_done for REF_003 reporting
        self._pre_init_refresh_count = 0
    
    def observe(self, txn: Txn) -> List[Violation]:
        """
        Consume one observed transaction and return any violations.
        
        Transaction routing is table-driven based on iface and kind.
        """
        violations = []
        
        # Lookup action in dispatch table
        action_key = (txn.iface, txn.kind)
        action_name = self.TXN_ACTION_TABLE.get(action_key)
        
        if action_name is not None:
            # Dispatch to appropriate handler
            handler = getattr(self, '_' + action_name)
            handler_violations = handler(txn)
            violations.extend(handler_violations)
        
        # Transactions with unrecognized iface/kind are silently ignored
        # per contract: observe must not raise on any transaction the schemas permit
        
        return violations
    
    def _handle_init_done(self, txn: Txn) -> List[Violation]:
        """
        Handle init_status.done transaction.
        
        Per spec initialization_sequence.$derived.init_sequence_order:
        The init_done signal marks completion of the full initialization sequence.
        
        Per init_status schema: fields include 'fail' and 'state'.
        We record init_done regardless of fail status - the ordering invariants
        apply to the event occurrence, not its success/failure outcome.
        """
        violations = []
        
        # Record that init_done was observed
        # Note: spec doesn't prohibit multiple init_done events (e.g., after re-init)
        # but for these invariants, we care about the first occurrence
        if not self._init_done_observed:
            self._init_done_observed = True
            self._init_done_txn = txn
        
        return violations
    
    def _handle_refresh_request(self, txn: Txn) -> List[Violation]:
        """
        Handle refresh_req.request transaction.
        
        Per spec refresh section and controller_architecture.refresh_policy:
        Refresh requests are generated by refresh_ctrl with fields:
        - urgent: indicates urgent refresh needed (per urgent_threshold)
        - pending: count of pending refreshes (ref_pending_cnt)
        - starve: starvation flag (ref_starve_flag)
        
        REF_003 check: No refresh may be requested before init_done.
        Per spec, the refresh timer is held until initialisation completes.
        """
        violations = []
        
        if not self._init_done_observed:
            # REF_003 violation: refresh request before init_done
            # Per spec: "the refresh timer is held until initialisation completes"
            self._pre_init_refresh_count += 1
            
            inv_info = self.INVARIANT_TABLE['REF_003']
            violations.append(Violation(
                rule=inv_info['rule'],
                detail=(
                    f"Refresh request observed before init_done "
                    f"(pre-init refresh count: {self._pre_init_refresh_count}). "
                    f"Fields: urgent={txn.fields.get('urgent')}, "
                    f"pending={txn.fields.get('pending')}, "
                    f"starve={txn.fields.get('starve')}"
                ),
                severity=inv_info['severity'],
                taxonomy_id='REF_003',
                txns=[txn]
            ))
        else:
            # Refresh request after init_done - this is valid behavior
            # Record that we've seen at least one (for REF_004 end-of-trace check)
            self._refresh_requested_after_init = True
        
        return violations
    
    def final(self) -> List[Violation]:
        """
        End-of-trace checks.
        
        REF_004: After init_done, at least one refresh request must be raised
        before end of trace. A controller that never requests refresh cannot
        honour tREFI (7800ns per spec timing_model.tREFI).
        
        Note: If init_done was never observed, we cannot check REF_004 - 
        the trace may have ended during initialization, which is a different
        concern (not covered by these invariants).
        """
        violations = []
        
        # REF_004 check: only applies if init completed
        if self._init_done_observed and not self._refresh_requested_after_init:
            inv_info = self.INVARIANT_TABLE['REF_004']
            
            # Include the init_done transaction in the violation for context
            involved_txns = []
            if self._init_done_txn is not None:
                involved_txns.append(self._init_done_txn)
            
            violations.append(Violation(
                rule=inv_info['rule'],
                detail=(
                    "No refresh request observed after init_done. "
                    "A controller that never requests refresh cannot honour tREFI "
                    f"(spec: {self._spec.get('timing_model', {}).get('tREFI', 'N/A')}ns)."
                ),
                severity=inv_info['severity'],
                taxonomy_id='REF_004',
                txns=involved_txns
            ))
        
        return violations
