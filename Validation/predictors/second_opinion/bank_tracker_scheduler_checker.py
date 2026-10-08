from txn_contract import LegalityChecker, Txn, Violation
from dataclasses import field
from typing import List


# Command type encoding table, derived from schema
CMD_NOP = 0
CMD_ACT = 1
CMD_RD = 2
CMD_WR = 3
CMD_PRE = 4
CMD_REF = 5

CMD_NAME = {
    CMD_NOP: "NOP",
    CMD_ACT: "ACT",
    CMD_RD: "RD",
    CMD_WR: "WR",
    CMD_PRE: "PRE",
    CMD_REF: "REF",
}

# Table: which commands require an active row in the target bank?
# Derived from JESD79-3: READ and WRITE are column-access commands that
# require a prior ACTIVATE to the same bank.
REQUIRES_ACTIVE_ROW = {
    CMD_NOP: False,
    CMD_ACT: False,
    CMD_RD: True,   # JESD79-3: READ requires prior ACTIVATE
    CMD_WR: True,   # JESD79-3: WRITE requires prior ACTIVATE
    CMD_PRE: False,
    CMD_REF: False,
}

# Table: which commands require the bank to be idle (precharged)?
# Derived from JESD79-3: ACTIVATE opens a row in an idle bank;
# issuing ACTIVATE to an already-active bank without PRECHARGE is illegal.
REQUIRES_IDLE_BANK = {
    CMD_NOP: False,
    CMD_ACT: True,   # JESD79-3: ACT requires bank idle (precharged)
    CMD_RD: False,
    CMD_WR: False,
    CMD_PRE: False,
    CMD_REF: False,
}

# Table: REFRESH requires ALL banks idle (precharged)
# Derived from JESD79-3: REFRESH command requires all banks precharged.
REQUIRES_ALL_IDLE = {
    CMD_NOP: False,
    CMD_ACT: False,
    CMD_RD: False,
    CMD_WR: False,
    CMD_PRE: False,
    CMD_REF: True,  # JESD79-3: REF requires all banks precharged
}


class BankTrackerSchedulerChecker(LegalityChecker):
    """Legality checker for bank_tracker + scheduler stage.

    Checks protocol-level invariants on the command stream:
      PROTO_001: RD/WR to a bank with no active row
      PROTO_002: ACT to a bank that already has an active row
      REF_002:   REF while any bank is still active

    State convention (from the invariant specification):
      - A bank is 'active' from its ACTIVATE until a PRECHARGE to it,
        or any REFRESH command.
      - After any REFRESH, every bank is treated as precharged (idle),
        whether or not the REFRESH was legal. An illegal REFRESH is
        reported once as REF_002 and does not cascade into PROTO_002
        on the next ACTIVATE.
    """

    INPUT_IFACES = ('cfg_timing', 'refresh_req')
    OUTPUT_IFACES = ('sched_cmd',)
    COVERS = ('PROTO_001', 'PROTO_002', 'REF_002')

    def __init__(self, spec: dict):
        # Read bank count from spec geometry
        # spec.controller_architecture.$derived.bank_count
        self._bank_count = spec["controller_architecture"]["$derived"]["bank_count"]
        self.reset()

    def reset(self) -> None:
        """Return all tracked state to power-on.

        Per JESD79-3, after power-up and initialization all banks are in
        the precharged (idle) state. We model each bank as either:
          - None: idle (precharged, no active row)
          - <row_number>: active with that row open
        """
        # bank_state[bank_index] = None (idle) or row_number (active)
        self._bank_state: list = [None] * self._bank_count

    def observe(self, txn: Txn) -> List[Violation]:
        """Consume one observed transaction and check protocol invariants."""

        # Only sched_cmd transactions carry commands to check
        if txn.iface != 'sched_cmd':
            # cfg_timing and refresh_req are input interfaces;
            # they do not produce DRAM commands and have no protocol
            # invariants in this checker's scope.
            return []

        if txn.kind != 'command':
            return []

        violations = []

        cmd_type = txn.fields.get('type')
        bank = txn.fields.get('bank')
        row = txn.fields.get('row')

        # Skip NOP commands — they have no protocol effect
        # (JESD79-3: NOP/DESELECT maintains current state)
        if cmd_type == CMD_NOP:
            return []

        cmd_name = CMD_NAME.get(cmd_type, f"UNKNOWN({cmd_type})")

        # -----------------------------------------------------------
        # Check: REQUIRES_ALL_IDLE (REF_002)
        # JESD79-3 Section 4.13: "All banks must be precharged [...]
        # before the REFRESH command can be applied."
        # Invariant spec: REF_002 — REFRESH issued while one or more
        # banks are still active.
        # -----------------------------------------------------------
        if REQUIRES_ALL_IDLE.get(cmd_type, False):
            active_banks = [
                b for b in range(self._bank_count)
                if self._bank_state[b] is not None
            ]
            if active_banks:
                active_detail = ", ".join(
                    f"bank {b} (row {self._bank_state[b]})"
                    for b in active_banks
                )
                violations.append(Violation(
                    rule="refresh_during_active_bank",
                    detail=(
                        f"REF issued while {len(active_banks)} bank(s) still active: "
                        f"{active_detail}"
                    ),
                    severity="major",
                    taxonomy_id="REF_002",
                    txns=[txn],
                ))
            # State convention: after any REFRESH, all banks become idle
            # regardless of whether the REFRESH was legal.
            for b in range(self._bank_count):
                self._bank_state[b] = None
            return violations

        # -----------------------------------------------------------
        # Check: REQUIRES_ACTIVE_ROW (PROTO_001)
        # JESD79-3: READ/WRITE are column access commands that require
        # the addressed bank to have an active (open) row.
        # Invariant spec: PROTO_001 — READ/WRITE issued to a bank
        # that has no active row.
        # -----------------------------------------------------------
        if REQUIRES_ACTIVE_ROW.get(cmd_type, False):
            if bank is not None and self._bank_state[bank] is None:
                violations.append(Violation(
                    rule="command_to_idle_bank",
                    detail=(
                        f"{cmd_name} issued to bank {bank} which has no active row"
                    ),
                    severity="major",
                    taxonomy_id="PROTO_001",
                    txns=[txn],
                ))
            # RD/WR do not change bank active/idle state
            # (JESD79-3: column access does not close or open a row,
            #  unless auto-precharge is set — but auto-precharge is
            #  not part of the invariants we are checking here, and
            #  the cmd_type encoding does not distinguish RDA/WRA)
            return violations

        # -----------------------------------------------------------
        # Check: REQUIRES_IDLE_BANK (PROTO_002)
        # JESD79-3: ACTIVATE opens a row in a bank that must be idle.
        # Invariant spec: PROTO_002 — ACTIVATE issued to a bank that
        # already has an active row without intervening PRECHARGE.
        # -----------------------------------------------------------
        if REQUIRES_IDLE_BANK.get(cmd_type, False):
            # This is ACT
            if bank is not None and self._bank_state[bank] is not None:
                violations.append(Violation(
                    rule="double_activate",
                    detail=(
                        f"ACT to bank {bank} (row {row}) but bank already has "
                        f"active row {self._bank_state[bank]} — no intervening PRECHARGE"
                    ),
                    severity="critical",
                    taxonomy_id="PROTO_002",
                    txns=[txn],
                ))
            # Regardless of violation, update state: the bank is now
            # active with the new row. This follows the convention that
            # the command takes effect for subsequent state tracking.
            if bank is not None:
                self._bank_state[bank] = row
            return violations

        # -----------------------------------------------------------
        # PRECHARGE: closes one bank (or all banks if encoded so,
        # but the schema uses a single bank field; per JESD79-3,
        # PRECHARGE can target a single bank).
        # No invariant to check for PRECHARGE in our COVERS set.
        # State update: bank becomes idle.
        # -----------------------------------------------------------
        if cmd_type == CMD_PRE:
            if bank is not None:
                # Check aux field bit for precharge-all.
                # JESD79-3: A10 high during PRECHARGE means all banks.
                # The schema has an 'aux' field (4 bits). Convention:
                # if aux bit indicates precharge-all, close all banks.
                # However, the spec schema does not explicitly define
                # aux bit semantics for PRE. We check if this might be
                # a precharge-all by looking at aux field.
                # JESD79-3 Section 4.7: PRECHARGE command with A10=HIGH
                # precharges all banks. A10 is typically mapped to
                # address bit 10, which could be in aux or encoded
                # differently. Since the spec does not define aux
                # encoding for PRE explicitly, we handle the single-bank
                # case (bank field is always present per schema) and
                # treat it as single-bank precharge.
                # A safe approach: precharge the indicated bank.
                self._bank_state[bank] = None
            return violations

        return violations

    def final(self) -> List[Violation]:
        """End-of-trace checks.

        The invariants PROTO_001, PROTO_002, and REF_002 are all
        per-command checks reported in observe(). There are no
        end-of-trace liveness or completeness rules in this checker's
        COVERS set.
        """
        return []
