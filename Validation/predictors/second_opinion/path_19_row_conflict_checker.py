from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import field
from typing import List, Dict, Optional, Tuple


# Command encoding table derived from the schema
CMD_DECODE = {
    0b0000: "MRS",
    0b0001: "REF",
    0b0010: "PRE",
    0b0011: "ACT",
    0b0100: "WR",
    0b0101: "RD",
    0b0111: "NOP",
    0b1111: "DESL",
}

# Which commands are CAS (column-access) commands
CAS_CMDS = {"RD", "WR"}

# A10 bit index for precharge-all detection per JESD79-3
A10_BIT = 10


class DDRCommandPathChecker(LegalityChecker):
    """
    Legality checker for the full command path from host request (cq_enq)
    to DDR pins (ddr_cmd).

    Checks covered:
      SCHED_001 - Every enqueued request must eventually issue as a matching CAS.
      SCHED_002 - No CAS may issue without a corresponding enqueued request.
      PROTO_001 - READ/WRITE to a bank with no active row.
      PROTO_002 - ACTIVATE to an already-active bank without intervening PRECHARGE.
      SCHED_004 - CAS must execute against the row its request asked for.
    """

    INPUT_IFACES = ('cq_enq',)
    OUTPUT_IFACES = ('ddr_cmd',)
    COVERS = ('SCHED_001', 'SCHED_002', 'PROTO_001', 'PROTO_002', 'SCHED_004')

    def __init__(self, spec: dict):
        # Read geometry from spec
        geom = spec["memory_geometry"]
        self._num_banks = 2 ** geom["bank_bits"]  # 8 banks per spec
        self._row_bits = geom["row_bits"]          # 15
        self._col_bits = geom["column_bits"]       # 10

        self.reset()

    def reset(self) -> None:
        """Return all tracked state to power-on."""
        # Bank state tracking: None means idle/precharged, int value means active row
        # Per JESD79-3: all banks start in idle (precharged) state after reset
        self._bank_active_row: Dict[int, Optional[int]] = {
            b: None for b in range(self._num_banks)
        }

        # Pending requests queue: list of dicts with keys: row, col, bank, we, txn, matched
        # Each entry represents an enqueued request that hasn't been matched to a CAS yet.
        self._pending_requests: List[dict] = []

        # Transaction sequence counter for ordering
        self._seq = 0

    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and return any violations."""
        self._seq += 1
        violations = []

        if txn.iface == 'cq_enq' and txn.kind == 'enqueue':
            violations.extend(self._observe_enqueue(txn))
        elif txn.iface == 'ddr_cmd' and txn.kind == 'command':
            violations.extend(self._observe_ddr_command(txn))

        return violations

    def _observe_enqueue(self, txn: Txn) -> List[Violation]:
        """Track an enqueued request."""
        entry = {
            'row': txn.fields['row'],
            'col': txn.fields['col'],
            'bank': txn.fields['bank'],
            'we': txn.fields['we'],
            'txn': txn,
            'matched': False,
            'seq': self._seq,
        }
        self._pending_requests.append(entry)
        return []

    def _observe_ddr_command(self, txn: Txn) -> List[Violation]:
        """Process a DDR command and check protocol/scheduling rules."""
        violations = []
        cmd_raw = txn.fields['cmd']
        addr = txn.fields['addr']
        bank = txn.fields['bank']

        cmd_name = CMD_DECODE.get(cmd_raw)
        if cmd_name is None:
            # Unknown command encoding; not something the spec defines as checkable
            return violations

        # Dispatch table for command types
        handler = self._CMD_HANDLERS.get(cmd_name)
        if handler is not None:
            violations.extend(handler(self, txn, cmd_name, bank, addr))

        return violations

    def _handle_act(self, txn: Txn, cmd_name: str, bank: int, addr: int) -> List[Violation]:
        """
        ACTIVATE command handler.

        PROTO_002 (failure_taxonomy): ACTIVATE issued to a bank that already has an
        active row without intervening PRECHARGE.

        Per the invariant description:
        "State convention: a bank is 'active' from its ACTIVATE until a PRECHARGE to it,
        a precharge-all (A10), or any REFRESH (which closes every bank whether or not
        it was legal, so an illegal REFRESH is reported once as REF_002 and does not
        cascade into this rule on the next ACTIVATE)."
        """
        violations = []

        if self._bank_active_row[bank] is not None:
            # PROTO_002: Double activate
            violations.append(Violation(
                rule="double_activate",
                detail=(
                    f"ACTIVATE to bank {bank} which already has row "
                    f"{self._bank_active_row[bank]} active (new row={addr})"
                ),
                severity="critical",
                taxonomy_id="PROTO_002",
                txns=[txn],
            ))

        # Regardless of violation, update state: the bank is now active with this row.
        # An implementation that double-activates still results in the new row being
        # considered open for subsequent CAS matching purposes.
        self._bank_active_row[bank] = addr

        return violations

    def _handle_pre(self, txn: Txn, cmd_name: str, bank: int, addr: int) -> List[Violation]:
        """
        PRECHARGE command handler.

        Per JESD79-3 Section 3.8 / the invariant clarification:
        "A PRECHARGE closes only the addressed bank unless address bit A10 is set
        (JESD79-3 precharge-all); the bank number never means 'all banks'."
        """
        # Check A10 for precharge-all per JESD79-3
        a10_set = (addr >> A10_BIT) & 1

        if a10_set:
            # Precharge all banks
            for b in range(self._num_banks):
                self._bank_active_row[b] = None
        else:
            # Precharge single bank
            self._bank_active_row[bank] = None

        return []

    def _handle_ref(self, txn: Txn, cmd_name: str, bank: int, addr: int) -> List[Violation]:
        """
        REFRESH command handler.

        Per the invariant for PROTO_002:
        "any REFRESH (which closes every bank whether or not it was legal, so an
        illegal REFRESH is reported once as REF_002 and does not cascade into this
        rule on the next ACTIVATE)."

        Note: REF_002 is NOT in our COVERS list, so we don't report it, but we
        still must update state correctly (close all banks) to avoid false
        PROTO_002 cascades.
        """
        # REFRESH closes all banks per JESD79-3 and per the spec's state convention
        for b in range(self._num_banks):
            self._bank_active_row[b] = None

        return []

    def _handle_cas(self, txn: Txn, cmd_name: str, bank: int, addr: int) -> List[Violation]:
        """
        READ or WRITE command handler.

        Checks:
          PROTO_001: CAS to bank with no active row.
          SCHED_002: CAS with no matching enqueued request.
          SCHED_004: CAS row mismatch (open row != request's row).

        Matching rule (from stage note):
        "A CAS matches an enqueued request when its bank matches, the DDR addr
        carries the request's col, the command direction matches we, and the
        bank's open row (set by the preceding ACT's addr) is the request's row."
        """
        violations = []
        is_write = 1 if cmd_name == "WR" else 0

        # PROTO_001: CAS to idle bank
        # Per failure_taxonomy PROTO_001: "READ/WRITE issued to a bank that has no active row."
        current_row = self._bank_active_row[bank]
        if current_row is None:
            violations.append(Violation(
                rule="cas_to_idle_bank",
                detail=f"{cmd_name} issued to bank {bank} which has no active row",
                severity="major",
                taxonomy_id="PROTO_001",
                txns=[txn],
            ))
            # With no active row, we cannot meaningfully match a request or check
            # SCHED_004, but we still check SCHED_002 (no matching request).
            # Since current_row is None, no request can match on row, so we try
            # to find a request matching bank+col+we only for SCHED_002 detection.
            # Actually, per the matching rule, the bank's open row must match the
            # request's row. Since there is no open row, no request can match,
            # so this CAS is also SCHED_002.
            violations.append(Violation(
                rule="cas_no_matching_request",
                detail=(
                    f"{cmd_name} to bank {bank}, col(addr)={addr} has no matching "
                    f"enqueued request (bank has no active row, so no row can match)"
                ),
                severity="critical",
                taxonomy_id="SCHED_002",
                txns=[txn],
            ))
            return violations

        # Bank is active with current_row. Now find a matching request.
        # The col is carried in the DDR addr field for CAS commands.
        # Per the stage note, we extract col from addr.
        cas_col = addr & ((1 << self._col_bits) - 1)

        # Search for a matching unmatched request (FIFO order for determinism,
        # but any match is legal under FR-FCFS).
        # Match criteria from stage note:
        #   - bank matches
        #   - DDR addr carries the request's col
        #   - command direction matches we
        #   - bank's open row == request's row
        matched_idx = None
        # Also track if there's a request matching bank+col+we but with wrong row
        # (for SCHED_004 reporting)
        wrong_row_candidates = []

        for i, req in enumerate(self._pending_requests):
            if req['matched']:
                continue
            if req['bank'] != bank:
                continue
            if req['we'] != is_write:
                continue
            if req['col'] != cas_col:
                continue
            # bank, col, we match. Check row.
            if req['row'] == current_row:
                # Full match
                matched_idx = i
                break
            else:
                # bank+col+we match but row mismatch
                wrong_row_candidates.append(i)

        if matched_idx is not None:
            # Successful match - mark request as served
            self._pending_requests[matched_idx]['matched'] = True
        elif wrong_row_candidates:
            # SCHED_004: There is a request for this bank+col+we but the open row
            # doesn't match what the request asked for.
            # Per the invariant: "when the CAS for a request issues, the row open
            # in that bank must be the request's row."
            # We pick the first candidate (oldest) as the one the CAS was
            # presumably intended for.
            cand_idx = wrong_row_candidates[0]
            cand = self._pending_requests[cand_idx]
            violations.append(Violation(
                rule="cas_wrong_row",
                detail=(
                    f"{cmd_name} to bank {bank}, col={cas_col}: open row is "
                    f"{current_row} but request's row is {cand['row']}"
                ),
                severity="critical",
                taxonomy_id="SCHED_004",
                txns=[txn, cand['txn']],
            ))
            # Mark the request as consumed so we don't double-report it
            self._pending_requests[cand_idx]['matched'] = True
        else:
            # SCHED_002: No enqueued request matches this CAS at all
            violations.append(Violation(
                rule="cas_no_matching_request",
                detail=(
                    f"{cmd_name} to bank {bank}, col={cas_col}, "
                    f"open_row={current_row}, we={is_write} "
                    f"has no matching enqueued request"
                ),
                severity="critical",
                taxonomy_id="SCHED_002",
                txns=[txn],
            ))

        return violations

    # Command handler dispatch table
    _CMD_HANDLERS = {
        "ACT": _handle_act,
        "PRE": _handle_pre,
        "REF": _handle_ref,
        "RD":  _handle_cas,
        "WR":  _handle_cas,
        # NOP, DESL, MRS: no action needed for our invariants
    }

    def final(self) -> List[Violation]:
        """
        End-of-trace rules.

        SCHED_001: Every enqueued request must eventually issue as a matching CAS.
        "Outstanding requests at end of trace are dropped."
        - Per the invariant description, outstanding requests at EOT are violations.
        """
        violations = []

        for req in self._pending_requests:
            if not req['matched']:
                violations.append(Violation(
                    rule="request_not_served",
                    detail=(
                        f"Enqueued request (bank={req['bank']}, row={req['row']}, "
                        f"col={req['col']}, we={req['we']}) was never issued as a "
                        f"matching CAS"
                    ),
                    severity="critical",
                    taxonomy_id="SCHED_001",
                    txns=[req['txn']],
                ))

        return violations
