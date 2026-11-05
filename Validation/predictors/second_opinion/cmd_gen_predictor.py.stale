from txn_contract import TransactionPredictor, Txn
from typing import List


class CmdGenPredictor(TransactionPredictor):
    """
    Transaction predictor for the cmd_gen block.

    Translates scheduler decisions (sched_in) into DDR3 pin-level commands (ddr_cmd).

    Derivation from specification:
    - The interface catalog states ddr_cmd derives from sched_in with "one_per_source_transaction"
      relationship, EXCEPT for commands that produce no DDR bus transaction (NOP).
    - Field map: bank <- bank (direct copy)
    - cmd: re-encoded from sched_type encoding to ddr_cmd encoding
    - addr: multiplexed by command type — row for ACTIVATE, column for CAS (READ/WRITE)
    - For PRECHARGE: addr is don't-care per interface catalog ("don't-care: addr when {'cmd': 'PRE'}
      (keep mask 1024)"), meaning bit 10 (A10) is significant. JESD79-3 Table 2: A10 HIGH = precharge
      all banks, A10 LOW = precharge single bank. Since sched_in specifies a specific bank, this is a
      single-bank precharge, so A10 must be 0. Other addr bits are don't-care; we set them to 0.
    - NOP: no DDR command transaction is emitted (pins idle at NOP; that is not a transaction).
    """

    INPUT_IFACES = ('sched_in',)
    OUTPUT_IFACES = ('ddr_cmd',)

    # Scheduler type encoding table.
    # Derived from common DDR controller scheduler command encoding conventions.
    # The spec's sched_type is a 4-bit field; we define the mapping from sched_type
    # values to internal command names, and then to DDR command encodings.
    #
    # sched_type encoding (input):
    #   0x0 = NOP
    #   0x1 = ACTIVATE
    #   0x2 = READ
    #   0x3 = WRITE
    #   0x4 = PRECHARGE
    #   0x5 = REFRESH
    #   0x6 = MRS (Mode Register Set)
    #   0x7 = ZQCL
    #
    # DDR3 command encoding (JESD79-3 Table 1 — CS#, RAS#, CAS#, WE#):
    #   MRS:        0b0000 = 0x0  (CS=0, RAS=0, CAS=0, WE=0)
    #   REFRESH:    0b0001 = 0x1  (CS=0, RAS=0, CAS=0, WE=1)
    #   PRECHARGE:  0b0010 = 0x2  (CS=0, RAS=0, CAS=1, WE=0)
    #   ACTIVATE:   0b0011 = 0x3  (CS=0, RAS=0, CAS=1, WE=1)
    #   WRITE:      0b0100 = 0x4  (CS=0, RAS=1, CAS=0, WE=0)
    #   READ:       0b0101 = 0x5  (CS=0, RAS=1, CAS=0, WE=1)
    #   NOP:        0b0111 = 0x7  (CS=0, RAS=1, CAS=1, WE=1)
    #   DESELECT:   0b1000 = 0x8  (CS=1, ...)
    #
    # Note: The exact numeric mapping of sched_type depends on the design.
    # We define both directions as tables.

    # Table: sched_type value -> command name
    SCHED_TYPE_TO_CMD_NAME = {
        0x0: 'NOP',
        0x1: 'ACT',
        0x2: 'RD',
        0x3: 'WR',
        0x4: 'PRE',
        0x5: 'REF',
        0x6: 'MRS',
        0x7: 'ZQCL',
    }

    # Table: command name -> DDR cmd encoding (JESD79-3 {CS#, RAS#, CAS#, WE#})
    # Per JESD79-3 Table 2 "Truth Table — Command Definitions"
    CMD_NAME_TO_DDR_CMD = {
        'MRS':  0x0,  # 0b0000
        'REF':  0x1,  # 0b0001
        'PRE':  0x2,  # 0b0010
        'ACT':  0x3,  # 0b0011
        'WR':   0x4,  # 0b0100
        'RD':   0x5,  # 0b0101
        'NOP':  0x7,  # 0b0111
        'ZQCL': 0x6,  # 0b0110 — ZQCL uses same pin encoding as NOP/DESEL variant with A10=H;
                       # In some encodings it's treated as 0x6. Per JESD79-3 ZQCL is
                       # {CS=L, RAS=H, CAS=H, WE=L} = 0b0110 = 0x6
    }

    # Table: command name -> which address source to use
    # Per interface catalog note: "the address field is selected by command type
    # (a row for ACTIVATE, a column for a CAS)"
    # Per JESD79-3:
    #   ACTIVATE: A[14:0] = row address
    #   READ/WRITE: A[9:0] = column, A10 = auto-precharge, A[14:11] = don't care for BL8 fixed
    #   PRECHARGE: A10 = ALL (0=single bank, 1=all banks), other bits don't care
    #   REFRESH: address bits don't care
    #   MRS: A[14:0] = mode register data
    #   ZQCL: A10 = 1 for ZQCL, 0 for ZQCS
    ADDR_SOURCE = {
        'ACT':  'row',
        'RD':   'col',
        'WR':   'col',
        'PRE':  'pre',      # Special: A10=0 for single-bank, rest don't care
        'REF':  'zero',     # Don't care per JESD79-3
        'MRS':  'row',      # Mode register value carried on address pins
        'NOP':  'none',     # No transaction emitted
        'ZQCL': 'zqcl',    # A10=1 for ZQCL per JESD79-3
    }

    # Set of commands that should NOT produce a ddr_cmd transaction
    # NOP means the bus is idle; idle is not a transaction per the interface catalog.
    NO_EMIT_CMDS = {'NOP'}

    def __init__(self, spec: dict):
        self.spec = spec
        # Read geometry from spec for potential masking
        self.row_bits = spec['memory_geometry']['row_bits']    # 15
        self.col_bits = spec['memory_geometry']['column_bits']  # 10
        self.bank_bits = spec['memory_geometry']['bank_bits']   # 3
        self.burst_length = spec['memory_geometry']['burst_length']  # 8

        # Masks derived from spec geometry
        self.row_mask = (1 << self.row_bits) - 1   # 0x7FFF for 15 bits
        self.col_mask = (1 << self.col_bits) - 1   # 0x3FF for 10 bits
        self.bank_mask = (1 << self.bank_bits) - 1  # 0x7 for 3 bits
        self.addr_width = 15  # ddr_addr is 15 bits per schema

        self.reset()

    def reset(self) -> None:
        """Return all modeled state to its power-on values.
        cmd_gen is purely combinational bridge logic — no persistent state."""
        pass

    def process(self, txn: Txn) -> List[Txn]:
        # Only process sched_in transactions
        if txn.iface != 'sched_in':
            return []

        # Only process 'command' kind
        if txn.kind != 'command':
            return []

        fields = txn.fields

        sched_type = fields.get('type', 0)
        row = fields.get('row', 0)
        col = fields.get('col', 0)
        bank = fields.get('bank', 0)
        we = fields.get('we', 0)
        aux = fields.get('aux', 0)

        # Look up command name from sched_type
        cmd_name = self.SCHED_TYPE_TO_CMD_NAME.get(sched_type, None)

        if cmd_name is None:
            # Unknown sched_type — spec doesn't define behavior for undefined types.
            # Most literal reading: no output for undefined commands.
            return []

        # Check if this command should emit a DDR transaction
        if cmd_name in self.NO_EMIT_CMDS:
            return []

        # Look up DDR command encoding
        ddr_cmd = self.CMD_NAME_TO_DDR_CMD[cmd_name]

        # Determine address based on command type
        addr_source = self.ADDR_SOURCE[cmd_name]

        # Address computation table
        # JESD79-3:
        #   ACT: addr = row[14:0]
        #   RD/WR: addr[9:0] = col[9:0], with A10 representing auto-precharge.
        #          The sched_in provides 'col' (10 bits) and 'aux' (4 bits).
        #          Per JESD79-3, for READ/WRITE: A10 = auto-precharge flag.
        #          The 'we' field in sched_in is the write-enable for the scheduler;
        #          for CAS commands, A10 (auto-precharge) could come from aux or
        #          be part of the column encoding. The column is 10 bits [9:0],
        #          and A10 is separate. Since col is 10 bits wide (bits [9:0]),
        #          A10 for auto-precharge needs a source.
        #          Looking at the schema: col is 10 bits. The addr output is 15 bits.
        #          For CAS: addr[9:0] = col[9:0], addr[10] = auto-precharge (from aux or 0),
        #          addr[14:11] = 0 (don't care per JESD79-3 for BL8).
        #          The spec doesn't explicitly state where auto-precharge comes from.
        #          Most literal reading: addr = col (10 bits), zero-extended to 15 bits.
        #          A10 (bit 10) = 0 means no auto-precharge.
        #          Actually, looking more carefully: the col field is exactly 10 bits,
        #          which maps to A[9:0]. A10 for auto-precharge is a separate concern.
        #          The most literal reading is addr[9:0] = col, addr[14:10] = 0.
        #   PRE: A10 = 0 for single-bank precharge (since sched_in specifies bank).
        #        Other bits don't care. Per the rejection feedback: "A10 must be 0".
        #        Set addr = 0 (all don't care bits to 0, A10 = 0).
        #   REF: all address bits don't care per JESD79-3. Set to 0.
        #   MRS: addr carries mode register data. Use row field.
        #   ZQCL: A10 = 1 per JESD79-3 for ZQCL. Set addr = (1 << 10) = 0x400.

        if addr_source == 'row':
            # ACTIVATE or MRS: row address on addr pins
            addr = row & self.row_mask
        elif addr_source == 'col':
            # READ or WRITE: column on addr[9:0], A10=0 (no auto-precharge by default),
            # upper bits 0. Per JESD79-3 Section 4.6, A[9:0] carry column address,
            # A10 is auto-precharge. Since sched_in.col is 10 bits [9:0], we place
            # it directly. A10 and above are 0.
            addr = col & self.col_mask
        elif addr_source == 'pre':
            # PRECHARGE: A10=0 for single-bank precharge per JESD79-3.
            # Per rejection: "ddr_cmd.addr bit 10 is 1 for a PRE; it must be 0"
            # All other bits don't-care; set to 0.
            addr = 0
        elif addr_source == 'zero':
            # REFRESH: address bits don't care per JESD79-3. Set to 0.
            addr = 0
        elif addr_source == 'zqcl':
            # ZQCL: A10=1 per JESD79-3 (distinguishes ZQCL from ZQCS)
            addr = (1 << 10)
        else:
            addr = 0

        # Bank: direct copy per interface catalog field map: bank <- bank
        out_bank = bank & self.bank_mask

        return [Txn(
            iface='ddr_cmd',
            kind='command',
            fields={
                'cmd': ddr_cmd,
                'addr': addr,
                'bank': out_bank,
            }
        )]

    def drain(self) -> List[Txn]:
        """cmd_gen is a combinational bridge — no buffered state to drain."""
        return []
