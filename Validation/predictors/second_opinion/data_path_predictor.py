"""Reference model (transaction predictor) for the `data_path` validation scope
of design `ddr3_mc_core_v2`.

Scope modelled
--------------
Inputs  : dp_wr        - host write words accepted by the data path (tagged by aux)
          dp_cmd       - data-movement commands (kind 'write' / kind 'read'), tagged by aux
          ddr_rd_beat  - DQ beats sampled from the DDR PHY on read
Outputs : ddr_wr_beat  - DQ/DM beats driven toward the DDR PHY on write
          dp_rd_rsp    - packed read words returned to the host

Every behaviour below is derived from the specification clause named in the
comment, or - where the specification is silent - from the standard named in
the comment (JESD79-3 for the DDR3 pins, Wishbone B4 for the host side).
No clock cycles, latencies or pipeline depths are modelled (ordering only).
"""

from collections import deque, OrderedDict

from txn_contract import TransactionPredictor, Txn


class DataPathPredictor(TransactionPredictor):
    """Independent implementation of spec.data_path_mapping (pack/unpack)."""

    INPUT_IFACES = ('ddr_rd_beat', 'dp_cmd', 'dp_wr')
    OUTPUT_IFACES = ('ddr_wr_beat', 'dp_rd_rsp')

    # ------------------------------------------------------------------
    # Decision tables (one table per decision the spec makes)
    # ------------------------------------------------------------------

    # data_path_mapping.endianness -> order in which the host word's chunks
    # leave on the channel / arrive from the channel.
    #   'little' : low half first  (spec: "low half first for little endianness")
    #   'big'    : high half first (mirror of the same clause)
    # Each entry maps beat_index -> chunk_index inside the host word.
    _ENDIAN_CHUNK_ORDER = {
        'little': lambda k, n: k,
        'big':    lambda k, n: (n - 1 - k),
    }

    # data_path_mapping.ddr_dm_polarity -> value driven on ddr_dm_o for a
    # given slice of the Wishbone byte-enable (SEL) field.
    #   'active_high_mask' : DM=1 masks the byte  => DM = ~SEL      (spec clause)
    #   'active_low_mask'  : DM=0 masks the byte  => DM =  SEL      (mirror)
    # (JESD79-3 2.9 "Data Mask": DM high at the sampling edge masks the write
    #  of that byte; the spec's 'active_high_mask' is exactly that pin sense.)
    _DM_POLARITY = {
        'active_high_mask': lambda sel_slice, width: (~sel_slice) & ((1 << width) - 1),
        'active_low_mask':  lambda sel_slice, width: sel_slice & ((1 << width) - 1),
    }

    # ------------------------------------------------------------------
    # Construction / configuration
    # ------------------------------------------------------------------

    def __init__(self, spec: dict):
        self.spec = spec if isinstance(spec, dict) else {}
        self._load_config()
        self.reset()

    # -- configuration helpers -----------------------------------------

    @staticmethod
    def _dget(d, *path, default=None):
        cur = d
        for key in path:
            if not isinstance(cur, dict) or key not in cur:
                return default
            cur = cur[key]
        return cur

    def _load_config(self):
        spec = self.spec
        dpm = self._dget(spec, 'data_path_mapping', default={}) or {}
        host_if = self._dget(spec, 'host_interface', default={}) or {}
        phy_if = self._dget(spec, 'phy_interface', default={}) or {}

        # host word width: data_path_mapping.host_width_bits is authoritative;
        # host_interface.data_width_bits is the same number in this spec.
        self.host_width = int(
            dpm.get('host_width_bits',
                    host_if.get('data_width_bits', 32)))

        # DDR channel width: data_path_mapping.ddr_channel_width_bits, with
        # phy_interface.dq_width_bits / memory_geometry.$derived as fallbacks.
        self.chan_width = int(
            dpm.get('ddr_channel_width_bits',
                    phy_if.get('dq_width_bits',
                               self._dget(spec, 'memory_geometry', '$derived',
                                          'channel_data_width_bits',
                                          default=16))))
        if self.chan_width <= 0:
            self.chan_width = 1

        # data_path_mapping.pack_mode: host_width/channel_width beats per word.
        self.beats_per_word = max(1, self.host_width // self.chan_width)

        # byte_enable_semantics == 'wishbone_sel_per_byte':
        # one SEL bit per host_interface.granularity_bits bits of data
        # (Wishbone B4 rule 3.45 / 3.1.3: SEL_O() selects where data is valid).
        self.gran_bits = int(host_if.get('granularity_bits', 8)) or 8
        self.sel_width = int(
            self._dget(host_if, '$derived', 'sel_width_bits',
                       default=max(1, self.host_width // self.gran_bits)))
        self.sel_bits_per_beat = max(1, self.chan_width // self.gran_bits)

        self.endianness = str(dpm.get('endianness', 'little')).lower()
        self.dm_polarity = str(dpm.get('ddr_dm_polarity', 'active_high_mask')).lower()

        # phy_interface.dm_enabled / host_interface.enable_data_mask.
        # When data masking is not provisioned the DM pins must still be driven
        # to their inactive level (JESD79-3 2.9: DM is an input that must be
        # driven; masking disabled => no byte masked).
        self.dm_enabled = bool(phy_if.get('dm_enabled', True)) and \
            bool(host_if.get('enable_data_mask', True))

        # Useful masks
        self.host_mask = (1 << self.host_width) - 1
        self.chan_mask = (1 << self.chan_width) - 1
        self.sel_mask = (1 << self.sel_width) - 1
        self.beat_sel_mask = (1 << self.sel_bits_per_beat) - 1

        # aux tag width (controller_architecture.aux_width); used only to
        # normalise the tag used as a buffer key, never to alter the value
        # reported back to the host.
        aux_w = self._dget(spec, 'controller_architecture', 'aux_width', default=4)
        try:
            self.aux_width = int(aux_w)
        except (TypeError, ValueError):
            self.aux_width = 4
        if self.aux_width <= 0:
            self.aux_width = 1
        self.aux_mask = (1 << self.aux_width) - 1

        # Depth of the tag-indexed host write buffer (host_interface.
        # write_buffer_depth). Not used to drop anything - the spec gives no
        # overflow behaviour - kept for completeness / documentation.
        self.write_buffer_depth = int(host_if.get('write_buffer_depth', 16))
        self.read_buffer_depth = int(host_if.get('read_buffer_depth', 16))

        # Interface dispatch table (one entry per modelled input interface).
        self._iface_handlers = {
            'dp_wr': self._on_dp_wr,
            'dp_cmd': self._on_dp_cmd,
            'ddr_rd_beat': self._on_ddr_rd_beat,
        }
        # Command-kind dispatch table (dp_cmd kinds from the schema).
        self._cmd_handlers = {
            'write': self._on_cmd_write,
            'read': self._on_cmd_read,
        }

    # ------------------------------------------------------------------
    # Lifecycle
    # ------------------------------------------------------------------

    def reset(self) -> None:
        """Power-on state: all buffers empty, nothing in flight."""
        self._load_config()          # re-read every constant from the spec
        # Tag-indexed host write buffer: aux -> FIFO of words waiting for the
        # dp_cmd.write that carries the same aux (interface-catalog note on
        # dp_wr, drop 2a18a7929dce / check DP-015).
        self._wr_buffer = OrderedDict()
        # Read commands awaiting their DDR beats. DDR3 returns read data in
        # command order (JESD79-3 4.x: no out-of-order read data on a rank),
        # so a plain FIFO of tags is the correct pairing.
        self._pending_reads = deque()
        # Beats accumulated toward the host word currently being packed.
        self._rd_chunks = []

    def process(self, txn):
        iface = getattr(txn, 'iface', None)
        handler = self._iface_handlers.get(iface)
        if handler is None:
            return []                      # interface not modelled by this scope
        try:
            return handler(txn)
        except Exception:
            # A malformed transaction must never raise out of process().
            return []

    def drain(self):
        # Nothing is buffered on the output side: ddr_wr_beat is emitted when
        # its dp_cmd.write arrives and dp_rd_rsp when its last beat arrives.
        # A partially-received read word is not a host word, and an unmatched
        # buffered write word has no command, so neither can be emitted.
        return []

    # ------------------------------------------------------------------
    # Input handlers
    # ------------------------------------------------------------------

    def _on_dp_wr(self, txn):
        """dp_wr.write: hold the word under its aux; emit nothing yet.

        Interface-catalog note on dp_wr: "a word is held under its aux until a
        dp_cmd.write with the same aux arrives, and THAT command's beats carry
        this word".
        """
        if getattr(txn, 'kind', None) != 'write':
            return []
        f = getattr(txn, 'fields', {}) or {}
        data = self._as_int(f.get('data'), 0) & self.host_mask
        # Wishbone B4 3.1.3 SEL_O: when the transfer carries no SEL information
        # the whole data port is valid -> all byte lanes enabled.
        mask = self._as_int(f.get('mask'), self.sel_mask) & self.sel_mask
        tag = self._tag(f.get('aux'))
        self._wr_buffer.setdefault(tag, deque()).append((data, mask))
        return []

    def _on_dp_cmd(self, txn):
        handler = self._cmd_handlers.get(getattr(txn, 'kind', None))
        if handler is None:
            return []                      # unknown command kind: nothing implied
        return handler(txn)

    def _on_cmd_write(self, txn):
        """dp_cmd.write: UNPACK the word held under this aux onto the channel.

        data_path_mapping.pack_mode = pack_32_to_16 -> host_width/channel_width
        beats, endianness = little -> low half first.
        """
        f = getattr(txn, 'fields', {}) or {}
        tag = self._tag(f.get('aux'))
        q = self._wr_buffer.get(tag)
        if not q:
            # The spec states a word always arrives no later than its command
            # (DP-015). With no word the beats' data is undefined, so nothing
            # may be invented: emit nothing.
            return []
        data, sel = q.popleft()
        if not q:
            del self._wr_buffer[tag]
        return self._unpack(data, sel)

    def _on_cmd_read(self, txn):
        """dp_cmd.read: arm capture of one host word under this aux."""
        f = getattr(txn, 'fields', {}) or {}
        # The aux returned on dp_rd_rsp is the command's aux, passed through
        # unmodified (schema: rd_rsp_aux, width = controller aux_width).
        self._pending_reads.append(f.get('aux'))
        return []

    def _on_ddr_rd_beat(self, txn):
        """ddr_rd_beat.beat: PACK channel beats into one host word.

        dp_rd_rsp note: "after a read command on dp_cmd, host_width/
        channel_width beats received on ddr_rd_beat pack into one host word,
        low half first for little endianness".
        """
        if getattr(txn, 'kind', None) != 'beat':
            return []
        if not self._pending_reads:
            # No armed read command: the beat belongs to no host word and no
            # aux exists for it. The spec only defines packing "after a read
            # command", so such a beat produces nothing.
            return []
        f = getattr(txn, 'fields', {}) or {}
        self._rd_chunks.append(self._as_int(f.get('data'), 0) & self.chan_mask)
        if len(self._rd_chunks) < self.beats_per_word:
            return []
        word = self._pack(self._rd_chunks)
        self._rd_chunks = []
        aux = self._pending_reads.popleft()
        return [Txn(iface='dp_rd_rsp', kind='response',
                    fields={'data': word, 'aux': aux})]

    # ------------------------------------------------------------------
    # Pack / unpack primitives (table driven)
    # ------------------------------------------------------------------

    def _chunk_index(self, beat_index):
        order = self._ENDIAN_CHUNK_ORDER.get(
            self.endianness, self._ENDIAN_CHUNK_ORDER['little'])
        return order(beat_index, self.beats_per_word)

    def _unpack(self, data, sel):
        """One host word -> beats_per_word ddr_wr_beat transactions."""
        out = []
        dm_fn = self._DM_POLARITY.get(
            self.dm_polarity, self._DM_POLARITY['active_high_mask'])
        for k in range(self.beats_per_word):
            c = self._chunk_index(k)
            beat_data = (data >> (c * self.chan_width)) & self.chan_mask
            sel_slice = (sel >> (c * self.sel_bits_per_beat)) & self.beat_sel_mask
            if self.dm_enabled:
                beat_mask = dm_fn(sel_slice, self.sel_bits_per_beat)
            else:
                # Masking not provisioned: DM held at its inactive level so no
                # byte is masked (JESD79-3 2.9).
                beat_mask = dm_fn(self.beat_sel_mask, self.sel_bits_per_beat)
            out.append(Txn(iface='ddr_wr_beat', kind='beat',
                           fields={'data': beat_data, 'mask': beat_mask}))
        return out

    def _pack(self, chunks):
        """beats_per_word channel beats -> one host word."""
        word = 0
        for k, chunk in enumerate(chunks[:self.beats_per_word]):
            c = self._chunk_index(k)
            word |= (chunk & self.chan_mask) << (c * self.chan_width)
        return word & self.host_mask

    # ------------------------------------------------------------------
    # Small helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _as_int(value, default=0):
        if value is None:
            return default
        if isinstance(value, bool):
            return int(value)
        if isinstance(value, int):
            return value
        try:
            return int(value, 0) if isinstance(value, str) else int(value)
        except (TypeError, ValueError):
            return default

    def _tag(self, aux):
        """Normalise an aux value for use as a buffer key."""
        return self._as_int(aux, 0) & self.aux_mask
