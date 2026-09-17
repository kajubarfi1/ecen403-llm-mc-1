from txn_contract import TransactionPredictor, Txn
from typing import List


class CmdGenPredictor(TransactionPredictor):
    """
    Transaction predictor for cmd_gen block.
    Translates scheduler commands (sched_in) to DDR3 pin-level commands (ddr_cmd).
    """

    INPUT_IFACES = ('sched_in',)
    OUTPUT_IFACES = ('ddr_cmd',)

    # Scheduler input command type encodings (sched_in.type)
    SCHED_NOP = 0
    SCHED_ACT = 1
    SCHED_RD = 2
    SCHED_WR = 3
    SCHED_PRE = 4
    SCHED_REF = 5

    # DDR command output encodings (ddr_cmd.cmd)
    DDR_REF = 1
    DDR_PRE = 2
    DDR_ACT = 3
    DDR_WR = 4
    DDR_RD = 5

    def __init__(self, spec: dict):
        self.spec = spec
        self._build_command_map()
        self.reset()

    def _build_command_map(self):
        """Build the mapping from scheduler command types to DDR command encodings."""
        # Mapping from sched_in.type to ddr_cmd.cmd
        self.cmd_translate = {
            self.SCHED_ACT: self.DDR_ACT,
            self.SCHED_RD: self.DDR_RD,
            self.SCHED_WR: self.DDR_WR,
            self.SCHED_PRE: self.DDR_PRE,
            self.SCHED_REF: self.DDR_REF,
        }

        # Commands that use column address instead of row address
        self.col_addr_cmds = {self.SCHED_RD, self.SCHED_WR}

        # Commands that should not produce output (NOP idles the bus)
        self.no_output_cmds = {self.SCHED_NOP}

    def reset(self) -> None:
        """Return all modeled state to its power-on values."""
        # This block is combinational/stateless translation
        # No persistent state to reset
        pass

    def process(self, txn: Txn) -> List[Txn]:
        """
        Process one input transaction and return resulting output transactions.
        Translates sched_in commands to ddr_cmd commands.
        """
        # Ignore transactions on interfaces we don't model
        if txn.iface != 'sched_in':
            return []

        # Only handle 'command' kind
        if txn.kind != 'command':
            return []

        # Extract input fields
        sched_type = txn.fields.get('type', 0)
        sched_row = txn.fields.get('row', 0)
        sched_col = txn.fields.get('col', 0)
        sched_bank = txn.fields.get('bank', 0)

        # NOP commands do not produce output transactions
        # The pins idle at NOP state - that's not a transaction
        if sched_type in self.no_output_cmds:
            return []

        # Check if this is a command we know how to translate
        if sched_type not in self.cmd_translate:
            return []

        # Translate command type
        ddr_cmd = self.cmd_translate[sched_type]

        # Determine address based on command type
        # RD and WR commands carry column address
        # ACT, PRE, REF commands carry row address
        if sched_type in self.col_addr_cmds:
            ddr_addr = sched_col
        else:
            ddr_addr = sched_row

        # Create output transaction
        out_txn = Txn(
            iface='ddr_cmd',
            kind='command',
            fields={
                'cmd': ddr_cmd,
                'addr': ddr_addr,
                'bank': sched_bank,
            }
        )

        return [out_txn]

    def drain(self) -> List[Txn]:
        """
        Return any pending output transactions at end of trace.
        This block has no buffering, so nothing to drain.
        """
        return []
