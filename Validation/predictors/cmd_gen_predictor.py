from txn_contract import TransactionPredictor, Txn


class Predictor(TransactionPredictor):
    INPUT_IFACES = ('sched_in',)
    OUTPUT_IFACES = ('ddr_cmd',)

    # Scheduler type encoding (input side)
    SCHED_NOP = 0
    SCHED_ACT = 1
    SCHED_READ = 2
    SCHED_WRITE = 3
    SCHED_PRE = 4
    SCHED_REF = 5
    SCHED_MRS = 6
    SCHED_ZQCL = 7

    # DDR command encoding (output side, active-low CS#/RAS#/CAS#/WE#)
    # Standard DDR3 command truth table (active-low signals):
    # MRS:        0b0000  (CS=0, RAS=0, CAS=0, WE=0)
    # REF:        0b0001  (CS=0, RAS=0, CAS=0, WE=1)
    # PRE:        0b0010  (CS=0, RAS=0, CAS=1, WE=0)
    # ACT:        0b0011  (CS=0, RAS=0, CAS=1, WE=1)
    # WRITE:      0b0100  (CS=0, RAS=1, CAS=0, WE=0)
    # READ:       0b0101  (CS=0, RAS=1, CAS=0, WE=1)
    # NOP:        0b0111  (CS=0, RAS=1, CAS=1, WE=1)
    # DESEL:      0b1xxx
    #
    # But actual encoding used by the design may differ. We use a mapping
    # that the spec implies: cmd_gen re-encodes between two different encodings.
    # The scheduler encoding maps to DDR pin-level encoding.

    def __init__(self, spec: dict):
        self.spec = spec
        self._build_encoding_map()
        self.reset()

    def _build_encoding_map(self):
        """Build the mapping from scheduler command type to DDR command encoding.

        The spec says: 'the command VALUE is re-encoded between two different encodings'
        and 'the address field is selected by command type (a row for ACTIVATE, a column for a CAS)'.

        Scheduler encoding (from sched_type values):
          0 = NOP
          1 = ACTIVATE
          2 = READ
          3 = WRITE
          4 = PRECHARGE
          5 = REFRESH
          6 = MRS
          7 = ZQCL

        DDR3 pin-level command encoding {CS#, RAS#, CAS#, WE#}:
          MRS:       0b0000 = 0
          REFRESH:   0b0001 = 1
          PRECHARGE: 0b0010 = 2
          ACTIVATE:  0b0011 = 3
          WRITE:     0b0100 = 4
          READ:      0b0101 = 5
          NOP:       0b0111 = 7
          DESELECT:  0b1000 = 8
        """
        self.sched_to_ddr = {
            1: 3,   # ACT -> 0b0011
            2: 5,   # READ -> 0b0101
            3: 4,   # WRITE -> 0b0100
            4: 2,   # PRE -> 0b0010
            5: 1,   # REF -> 0b0001
            6: 0,   # MRS -> 0b0000
            7: 8,   # ZQCL -> could be mapped; using deselect-like or special
        }
        # Commands that use row address
        self.row_cmds = {1}  # ACTIVATE
        # Commands that use column address
        self.col_cmds = {2, 3}  # READ, WRITE
        # Commands where addr is don't-care (PRE, REF, ZQCL)
        self.dont_care_addr_cmds = {4, 5, 7}
        # MRS uses row for mode register data
        self.mrs_cmds = {6}

    def reset(self) -> None:
        pass

    def process(self, txn: Txn) -> list:
        if txn.iface != 'sched_in':
            return []

        if txn.kind != 'command':
            return []

        sched_type = int(txn.fields.get('type', 0))
        row = int(txn.fields.get('row', 0))
        col = int(txn.fields.get('col', 0))
        bank = int(txn.fields.get('bank', 0))

        # NOP produces no transaction - pins idle at NOP
        if sched_type == self.SCHED_NOP:
            return []

        if sched_type not in self.sched_to_ddr:
            return []

        ddr_cmd = self.sched_to_ddr[sched_type]

        # Determine address based on command type
        if sched_type in self.row_cmds:
            addr = row
        elif sched_type in self.col_cmds:
            addr = col
        elif sched_type in self.mrs_cmds:
            # MRS: address carries mode register settings
            addr = row
        elif sched_type in self.dont_care_addr_cmds:
            # For PRECHARGE: A10=0 means single-bank precharge (spec says
            # "the scheduler's PRECHARGE names one bank; A10 high would
            # precharge every bank"). So we set addr to 0 (A10=0).
            # For REF and ZQCL: address is don't care, use 0.
            addr = 0
        else:
            addr = 0

        # Mask to field widths from schema
        addr_width = 15  # ddr_addr width from schema
        bank_width = 3   # ddr_bank width from schema
        cmd_width = 4    # ddr_cmd width from schema

        addr = addr & ((1 << addr_width) - 1)
        bank = bank & ((1 << bank_width) - 1)
        ddr_cmd = ddr_cmd & ((1 << cmd_width) - 1)

        out_txn = Txn(
            iface='ddr_cmd',
            kind='command',
            fields={
                'cmd': ddr_cmd,
                'addr': addr,
                'bank': bank,
            }
        )

        return [out_txn]

    def drain(self) -> list:
        return []
