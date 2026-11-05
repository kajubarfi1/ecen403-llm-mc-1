from typing import Any, Dict, List

from txn_contract import TransactionPredictor, Txn


class CmdGenPredictor(TransactionPredictor):
    """Reference model for the cmd_gen bridge.

    cmd_gen takes one scheduler decision (sched_in) and drives the pin-level
    DDR3 command bus (ddr_cmd).  Per the interface catalog it is a bridge with
    exactly two things a plain field map cannot express:

      * the command VALUE is re-encoded from the scheduler's logical command
        enum into the JEDEC pin encoding {CS#,RAS#,CAS#,WE#};
      * the address field is MUXed by command type: a row for ACTIVATE, a
        column for a CAS (READ/WRITE).

    The bank field passes straight through.  An idle scheduler slot (NOP) does
    not produce a command transaction at all: the pins simply idle, which is
    not an observable transaction on ddr_cmd.
    """

    INPUT_IFACES: tuple = ('sched_in',)
    OUTPUT_IFACES: tuple = ('ddr_cmd',)

    #: Scheduler-side logical command enum (sched_type).  The specification
    #: carries no encoding table, so the conventional controller enum is used;
    #: it can be overridden from the spec (see _load_encodings).
    _DEFAULT_SCHED_ENCODING: Dict[int, str] = {
        0: 'NOP',
        1: 'ACT',
        2: 'RD',
        3: 'WR',
        4: 'PRE',
        5: 'REF',
        6: 'ZQCS',
        7: 'MRS',
    }

    #: DRAM-side pin encoding: {CS#, RAS#, CAS#, WE#}, CS# low (selected).
    _DEFAULT_PIN_ENCODING: Dict[str, int] = {
        'MRS': 0b0000,
        'REF': 0b0001,
        'PRE': 0b0010,
        'PREA': 0b0010,
        'ACT': 0b0011,
        'WR': 0b0100,
        'RD': 0b0101,
        'ZQCS': 0b0110,
        'ZQCL': 0b0110,
        'NOP': 0b0111,
    }

    #: Logical commands whose address field is the row.
    _ROW_ADDRESSED = ('ACT',)
    #: Logical commands whose address field is the column (a CAS).
    _COL_ADDRESSED = ('RD', 'WR')
    #: Logical commands that are not driven onto the bus as a transaction.
    _IDLE = ('NOP', 'DES')

    def __init__(self, spec: dict):
        self.spec = spec if isinstance(spec, dict) else {}
        self._load_geometry()
        self._load_encodings()
        self.reset()

    # ------------------------------------------------------------------
    # configuration taken from the spec
    # ------------------------------------------------------------------
    def _load_geometry(self) -> None:
        geom = self.spec.get('memory_geometry', {}) or {}
        self.row_bits = int(geom.get('row_bits', 0) or 0)
        self.column_bits = int(geom.get('column_bits', 0) or 0)
        self.bank_bits = int(geom.get('bank_bits', 0) or 0)

        # A10 on the address bus is the "all banks" qualifier for PRECHARGE
        # and the auto-precharge qualifier on a CAS.  It sits immediately
        # above the column field.
        if self.column_bits > 0:
            self.all_banks_bit = 1 << self.column_bits
        else:
            self.all_banks_bit = 0

        if self.bank_bits > 0:
            self.bank_mask = (1 << self.bank_bits) - 1
        else:
            self.bank_mask = None

    def _load_encodings(self) -> None:
        enc = {}
        for key in ('command_encoding', 'cmd_encoding', 'encodings'):
            cand = self.spec.get(key)
            if isinstance(cand, dict):
                enc = cand
                break

        sched_tbl = None
        for key in ('sched_type', 'sched_in', 'scheduler', 'logical'):
            cand = enc.get(key)
            if isinstance(cand, dict):
                sched_tbl = cand
                break
        if sched_tbl is None:
            self.sched_encoding = dict(self._DEFAULT_SCHED_ENCODING)
        else:
            self.sched_encoding = {}
            for k, v in sched_tbl.items():
                try:
                    if isinstance(k, str) and not k.lstrip('-').isdigit():
                        # name -> code form
                        self.sched_encoding[int(v)] = str(k).upper()
                    else:
                        self.sched_encoding[int(k)] = str(v).upper()
                except (TypeError, ValueError):
                    continue

        pin_tbl = None
        for key in ('ddr_cmd', 'pin', 'dram'):
            cand = enc.get(key)
            if isinstance(cand, dict):
                pin_tbl = cand
                break
        if pin_tbl is None:
            self.pin_encoding = dict(self._DEFAULT_PIN_ENCODING)
        else:
            self.pin_encoding = {}
            for k, v in pin_tbl.items():
                try:
                    if isinstance(k, str) and not k.lstrip('-').isdigit():
                        self.pin_encoding[str(k).upper()] = int(v)
                    else:
                        self.pin_encoding[str(v).upper()] = int(k)
                except (TypeError, ValueError):
                    continue

    # ------------------------------------------------------------------
    # lifecycle
    # ------------------------------------------------------------------
    def reset(self) -> None:
        # Re-read everything configurable from the spec so that reset() really
        # is a power-on state restore.
        self._load_geometry()
        self._load_encodings()
        # cmd_gen is a combinational bridge: it holds no architectural state
        # that affects the predicted command stream.  Nothing is buffered.
        self._pending: List[Txn] = []

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    @staticmethod
    def _fields(txn: Any) -> Dict[str, Any]:
        f = getattr(txn, 'fields', None)
        if isinstance(f, dict):
            return f
        return {}

    @staticmethod
    def _as_int(value: Any, default: int = 0) -> int:
        if value is None:
            return default
        if isinstance(value, bool):
            return 1 if value else 0
        if isinstance(value, int):
            return value
        try:
            return int(value)
        except (TypeError, ValueError):
            try:
                return int(str(value), 0)
            except (TypeError, ValueError):
                return default

    def _decode(self, sched_type: int, we: int) -> str:
        name = self.sched_encoding.get(sched_type)
        if name is None:
            return 'UNKNOWN'
        name = name.upper()
        # Only if the scheduler enum does not itself distinguish the CAS
        # direction does sched_we pick it.
        if name in ('CAS', 'RDWR', 'COL', 'COLUMN'):
            return 'WR' if we else 'RD'
        return name

    # ------------------------------------------------------------------
    # main entry point
    # ------------------------------------------------------------------
    def process(self, txn: Any) -> List[Txn]:
        iface = getattr(txn, 'iface', None)
        if iface not in self.INPUT_IFACES:
            return []
        kind = getattr(txn, 'kind', None)
        if kind is not None and kind != 'command':
            return []

        f = self._fields(txn)
        sched_type = self._as_int(f.get('type'))
        row = self._as_int(f.get('row'))
        col = self._as_int(f.get('col'))
        bank = self._as_int(f.get('bank'))
        we = self._as_int(f.get('we'))

        name = self._decode(sched_type, we)

        # An idle slot is not a transaction on the command bus.
        if name in self._IDLE:
            return []
        if name == 'UNKNOWN':
            return []

        cmd_code = self.pin_encoding.get(name)
        if cmd_code is None:
            return []

        # Address mux by command type.
        if name in self._ROW_ADDRESSED:
            addr = row
        elif name in self._COL_ADDRESSED:
            addr = col
        elif name in ('PREA', 'PRECHARGE_ALL', 'PRE_ALL'):
            addr = self.all_banks_bit
        elif name in ('MRS',):
            # Mode-register opcode travels on the address pins; the scheduler
            # presents it on the wide (row) field.
            addr = row
        else:
            # PRE (single bank), REF, ZQCS: no address is required; A10 low.
            addr = 0

        if self.bank_mask is not None:
            bank = bank & self.bank_mask

        out = Txn(
            iface='ddr_cmd',
            kind='command',
            fields={
                'cmd': cmd_code,
                'addr': addr,
                'bank': bank,
            },
        )
        return [out]

    def drain(self) -> List[Txn]:
        # Nothing is buffered inside the bridge.
        pending = self._pending
        self._pending = []
        return pending
