from collections import deque
from typing import List

from txn_contract import TransactionPredictor, Txn


class DataPathPredictor(TransactionPredictor):
    """Reference model for the DDR controller data path.

    Models only the pack/unpack behaviour declared by
    spec['data_path_mapping']:

      * WRITE (UNPACK): a host word accepted on dp_wr is held under its aux
        tag until a dp_cmd.write carrying the same aux arrives; that command
        emits host_width/channel_width beats on ddr_wr_beat, lowest-order
        slice first for little endianness.  The byte-enable mask is sliced
        the same way and converted to the DM polarity the spec declares
        (active_high_mask => DM is the inverted byte-enable slice).

      * READ (PACK): a dp_cmd.read reserves one host word; the next
        host_width/channel_width beats seen on ddr_rd_beat are packed into
        that word (lowest-order slice first for little endianness) and
        returned on dp_rd_rsp with the read command's aux.

    No timing, latency or pipelining is modelled: ordering is carried by the
    emission order alone.
    """

    INPUT_IFACES = ('ddr_rd_beat', 'dp_cmd', 'dp_wr')
    OUTPUT_IFACES = ('ddr_wr_beat', 'dp_rd_rsp')

    # ------------------------------------------------------------------ #
    # construction / configuration
    # ------------------------------------------------------------------ #
    def __init__(self, spec: dict):
        self.spec = spec if isinstance(spec, dict) else {}
        self._configure()
        self.reset()

    def _configure(self) -> None:
        """(Re-)read every constant this model needs from the spec."""
        spec = self.spec
        dpm = spec.get('data_path_mapping', {}) or {}
        host_if = spec.get('host_interface', {}) or {}
        geom = spec.get('memory_geometry', {}) or {}
        geom_der = geom.get('$derived', {}) or {}
        phy = spec.get('phy_interface', {}) or {}
        ctrl = spec.get('controller_architecture', {}) or {}

        # host word width
        self.host_width = self._as_int(
            dpm.get('host_width_bits',
                    host_if.get('data_width_bits', 32)), 32)

        # DDR channel (DQ) width
        self.chan_width = self._as_int(
            dpm.get('ddr_channel_width_bits',
                    geom_der.get('channel_data_width_bits',
                                 phy.get('dq_width_bits', 16))), 16)

        # byte granularity used by the byte-enable / data-mask signals
        self.granularity = self._as_int(host_if.get('granularity_bits', 8), 8)
        if self.granularity <= 0:
            self.granularity = 8

        if self.chan_width <= 0:
            self.chan_width = self.host_width if self.host_width > 0 else 16
        if self.host_width <= 0:
            self.host_width = self.chan_width

        # number of DDR beats per host word (pack / unpack ratio)
        beats = self.host_width // self.chan_width
        if beats < 1:
            beats = 1
        self.beats_per_word = beats

        # mask widths
        self.host_mask_bits = max(1, self.host_width // self.granularity)
        self.beat_mask_bits = max(1, self.chan_width // self.granularity)

        # endianness: little => lowest-order slice travels first
        endian = str(dpm.get('endianness', 'little')).lower()
        self.little_endian = not endian.startswith('big')

        # DM polarity: active_high_mask => DM==1 masks the byte, so DM is the
        # inverse of the wishbone byte-enable slice.
        polarity = str(dpm.get('ddr_dm_polarity', 'active_high_mask')).lower()
        self.invert_mask = 'active_high' in polarity or polarity == 'active_high_mask'

        # aux / tag width
        self.aux_width = self._as_int(ctrl.get('aux_width', 4), 4)
        if self.aux_width <= 0:
            self.aux_width = 4

        # command interface decoding
        self.cmd_read_kind = 'read'
        self.cmd_write_kind = 'write'

    @staticmethod
    def _as_int(value, default):
        try:
            if isinstance(value, bool):
                return int(value)
            if isinstance(value, str):
                return int(value, 0)
            return int(value)
        except (TypeError, ValueError):
            return default

    # ------------------------------------------------------------------ #
    # lifecycle
    # ------------------------------------------------------------------ #
    def reset(self) -> None:
        # re-read configuration so a changed spec dict takes effect
        self._configure()
        # tag-indexed host write buffer: aux -> FIFO of (data, mask)
        self._wr_buffer = {}
        # outstanding read commands, in arrival order: list of aux tags
        self._rd_pending = deque()
        # beats accumulated for the read command at the head of _rd_pending
        self._rd_beats = []

    # ------------------------------------------------------------------ #
    # helpers
    # ------------------------------------------------------------------ #
    @staticmethod
    def _bitmask(bits):
        return (1 << bits) - 1 if bits > 0 else 0

    def _field(self, txn, name, default=0):
        fields = getattr(txn, 'fields', None)
        if isinstance(fields, dict) and name in fields:
            return self._as_int(fields.get(name), default)
        value = getattr(txn, name, None)
        if value is None:
            return default
        return self._as_int(value, default)

    def _has_field(self, txn, name):
        fields = getattr(txn, 'fields', None)
        if isinstance(fields, dict):
            return name in fields
        return getattr(txn, name, None) is not None

    def _make(self, iface, kind, fields):
        try:
            return Txn(iface=iface, kind=kind, fields=fields)
        except TypeError:
            return Txn(iface, kind, fields)

    def _slices(self, value, slice_bits, count):
        """Split value into `count` slices of `slice_bits`, transmission order."""
        m = self._bitmask(slice_bits)
        parts = [(value >> (i * slice_bits)) & m for i in range(count)]
        if not self.little_endian:
            parts.reverse()
        return parts

    def _assemble(self, parts, slice_bits):
        """Inverse of _slices: parts are in transmission order."""
        ordered = list(parts)
        if not self.little_endian:
            ordered.reverse()
        m = self._bitmask(slice_bits)
        word = 0
        for i, p in enumerate(ordered):
            word |= (p & m) << (i * slice_bits)
        return word

    # ------------------------------------------------------------------ #
    # transaction processing
    # ------------------------------------------------------------------ #
    def process(self, txn) -> List[Txn]:
        iface = getattr(txn, 'iface', None)
        kind = getattr(txn, 'kind', None)

        if iface == 'dp_wr':
            return self._on_host_write(txn, kind)
        if iface == 'dp_cmd':
            return self._on_command(txn, kind)
        if iface == 'ddr_rd_beat':
            return self._on_read_beat(txn, kind)
        return []

    # -- host write word: buffer it under its aux tag -------------------- #
    def _on_host_write(self, txn, kind):
        if kind is not None and kind != 'write':
            return []
        data = self._field(txn, 'data', 0) & self._bitmask(self.host_width)
        if self._has_field(txn, 'mask'):
            mask = self._field(txn, 'mask', 0) & self._bitmask(self.host_mask_bits)
        else:
            # no byte-enable information: every byte enabled
            mask = self._bitmask(self.host_mask_bits)
        aux = self._field(txn, 'aux', 0) & self._bitmask(self.aux_width)
        self._wr_buffer.setdefault(aux, deque()).append((data, mask))
        return []

    # -- data-path command ----------------------------------------------- #
    def _on_command(self, txn, kind):
        aux = self._field(txn, 'aux', 0) & self._bitmask(self.aux_width)

        if kind == self.cmd_write_kind:
            return self._emit_write_beats(aux)
        if kind == self.cmd_read_kind:
            self._rd_pending.append(aux)
            return []
        return []

    def _emit_write_beats(self, aux):
        queue = self._wr_buffer.get(aux)
        if not queue:
            # The spec guarantees the word arrives no later than its command;
            # with no word under this tag there is nothing defined to drive.
            return []
        data, mask = queue.popleft()
        if not queue:
            self._wr_buffer.pop(aux, None)

        data_parts = self._slices(data, self.chan_width, self.beats_per_word)
        mask_parts = self._slices(mask, self.beat_mask_bits, self.beats_per_word)

        beat_mask_full = self._bitmask(self.beat_mask_bits)
        out = []
        for i in range(self.beats_per_word):
            dm = mask_parts[i]
            if self.invert_mask:
                dm = (~dm) & beat_mask_full
            out.append(self._make('ddr_wr_beat', 'beat',
                                  {'data': data_parts[i] & self._bitmask(self.chan_width),
                                   'mask': dm & beat_mask_full}))
        return out

    # -- read beat from the PHY ------------------------------------------- #
    def _on_read_beat(self, txn, kind):
        if kind is not None and kind != 'beat':
            return []
        if not self._rd_pending:
            # No read command is outstanding: the spec only defines packing
            # for beats that follow a read command.
            return []
        data = self._field(txn, 'data', 0) & self._bitmask(self.chan_width)
        self._rd_beats.append(data)
        if len(self._rd_beats) < self.beats_per_word:
            return []

        parts = self._rd_beats[:self.beats_per_word]
        self._rd_beats = self._rd_beats[self.beats_per_word:]
        aux = self._rd_pending.popleft()
        word = self._assemble(parts, self.chan_width) & self._bitmask(self.host_width)
        return [self._make('dp_rd_rsp', 'response',
                           {'data': word,
                            'aux': aux & self._bitmask(self.aux_width)})]

    # ------------------------------------------------------------------ #
    def drain(self) -> List[Txn]:
        # Partial bursts and commands whose data never arrived produce no
        # defined output; nothing is buffered awaiting a later trigger.
        return []
