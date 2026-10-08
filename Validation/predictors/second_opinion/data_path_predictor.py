from txn_contract import TransactionPredictor, Txn
from typing import List


class DataPathPredictor(TransactionPredictor):
    """
    Transaction predictor for the data_path validation scope.
    
    Models the PACK and UNPACK sides of data_path_mapping:
    
    UNPACK (write path): Each 32-bit host write word is split into
    host_width/channel_width = 2 DDR beats of 16 bits each, low half first
    (little endian). The 4-bit byte-enable mask is sliced into 2-bit groups
    per beat, and INVERTED per ddr_dm_polarity = active_high_mask
    (DM=1 masks/inhibits the byte, so DM = ~byte_enable).
    Spec refs: data_path_mapping.pack_mode, data_path_mapping.endianness,
    data_path_mapping.ddr_dm_polarity.
    
    PACK (read path): After a read command on dp_cmd, host_width/channel_width = 2
    beats from ddr_rd_beat are packed into one 32-bit host word, low half first
    (little endian). The aux field from the read command is echoed back.
    Spec refs: data_path_mapping.pack_mode, data_path_mapping.endianness,
    controller_architecture.aux_width.
    """

    INPUT_IFACES = ('ddr_rd_beat', 'dp_cmd', 'dp_wr')
    OUTPUT_IFACES = ('ddr_wr_beat', 'dp_rd_rsp')

    def __init__(self, spec: dict):
        self._spec = spec

        # Extract configuration from spec
        dpm = spec['data_path_mapping']
        self._host_width_bits = dpm['host_width_bits']
        self._channel_width_bits = dpm['ddr_channel_width_bits']
        # Number of DDR beats per host word
        # Spec: pack_mode = "pack_32_to_16" => ratio = host_width / channel_width = 2
        self._beats_per_word = self._host_width_bits // self._channel_width_bits

        # Endianness determines beat ordering: "little" => low half first
        # Spec ref: data_path_mapping.endianness
        self._endianness = dpm['endianness']

        # DM polarity: "active_high_mask" means DM=1 masks (inhibits) the byte
        # So DM = inverted byte-enable
        # Spec ref: data_path_mapping.ddr_dm_polarity
        self._dm_polarity = dpm['ddr_dm_polarity']

        # Aux width from controller_architecture
        # Spec ref: controller_architecture.aux_width
        self._aux_width = spec['controller_architecture']['aux_width']

        # Byte-enable semantics from spec
        # Spec ref: data_path_mapping.byte_enable_semantics
        self._be_semantics = dpm['byte_enable_semantics']

        # Derived masks
        self._channel_mask = (1 << self._channel_width_bits) - 1
        self._bytes_per_beat = self._channel_width_bits // 8  # 2 bytes per 16-bit beat
        self._dm_bits_per_beat = self._bytes_per_beat  # 2 DM bits per beat (one per byte lane)
        self._host_bytes = self._host_width_bits // 8  # 4 bytes per 32-bit word
        self._dm_mask_per_beat = (1 << self._dm_bits_per_beat) - 1

        self.reset()

    def reset(self) -> None:
        """Return all modeled state to power-on values."""
        # Write path state: buffer for write data words waiting for a write command
        self._wr_data_queue: List[dict] = []

        # Read path state: pending read commands waiting for DDR beats
        self._rd_cmd_queue: List[dict] = []
        # Accumulator for incoming DDR read beats for the current read command
        self._rd_beat_accumulator: List[int] = []

    def process(self, txn: Txn) -> List[Txn]:
        iface = txn.iface
        kind = txn.kind

        # Dispatch table keyed by (iface, kind)
        dispatch = {
            ('dp_wr', 'write'): self._handle_dp_wr,
            ('dp_cmd', 'write'): self._handle_dp_cmd_write,
            ('dp_cmd', 'read'): self._handle_dp_cmd_read,
            ('ddr_rd_beat', 'beat'): self._handle_ddr_rd_beat,
        }

        handler = dispatch.get((iface, kind))
        if handler is None:
            # Unknown interface or kind — return nothing per contract
            return []

        return handler(txn)

    def _handle_dp_wr(self, txn: Txn) -> List[Txn]:
        """
        Host write data accepted by the data path.
        Buffer the data+mask; actual DDR beats are emitted when the write command arrives.
        
        Spec ref: dp_wr schema — fields: data (32-bit), mask (4-bit byte-enable).
        The note on ddr_wr_beat says it "derives from dp_wr", meaning write data
        flows from dp_wr through dp_cmd(write) to ddr_wr_beat.
        
        Based on the interface catalog note, each accepted host write word is emitted
        as beats. We buffer write data here and emit beats when we receive it,
        since the dp_wr transaction represents data already accepted by the data path.
        
        Re-reading the note: "each accepted host write word is emitted as 
        host_width/channel_width beats on the DDR side" — this is the UNPACK operation.
        The dp_wr is the input; ddr_wr_beat is the output derived from it.
        
        The relationship between dp_cmd(write) and dp_wr: dp_cmd triggers the command,
        dp_wr provides the data. Looking at the schema, dp_wr is a separate stream.
        
        Since the note says ddr_wr_beat "derives from: dp_wr", the most literal reading
        is that each dp_wr directly produces the DDR write beats.
        """
        data = txn.fields['data']
        mask = txn.fields['mask']

        return self._unpack_write(data, mask)

    def _unpack_write(self, data: int, mask: int) -> List[Txn]:
        """
        UNPACK: Split a 32-bit host word into beats_per_word 16-bit DDR beats.
        
        Spec ref: data_path_mapping.endianness = "little" => low half first.
        Spec ref: data_path_mapping.ddr_dm_polarity = "active_high_mask" =>
            DM=1 means mask/inhibit that byte => DM = ~byte_enable per byte.
        
        Per the interface catalog note on ddr_wr_beat:
        "each beat's mask is the INVERTED byte-enable slice"
        """
        results = []

        for beat_idx in range(self._beats_per_word):
            # For little endian: beat 0 = low bits, beat 1 = high bits
            # Spec ref: data_path_mapping.endianness = "little"
            if self._endianness == 'little':
                bit_offset = beat_idx * self._channel_width_bits
                mask_bit_offset = beat_idx * self._bytes_per_beat
            else:
                # Big endian: beat 0 = high bits (reverse order)
                bit_offset = (self._beats_per_word - 1 - beat_idx) * self._channel_width_bits
                mask_bit_offset = (self._beats_per_word - 1 - beat_idx) * self._bytes_per_beat

            # Extract the data slice for this beat
            beat_data = (data >> bit_offset) & self._channel_mask

            # Extract the byte-enable slice for this beat
            # mask field is 4 bits for 4 bytes; each beat takes bytes_per_beat bits
            beat_be = (mask >> mask_bit_offset) & self._dm_mask_per_beat

            # Apply DM polarity inversion
            # Spec ref: ddr_dm_polarity = "active_high_mask"
            # "DM=1 masks the byte, so each beat's mask is the INVERTED byte-enable slice"
            # Per the interface note (decided 2026-10-08, graded by the gate)
            if self._dm_polarity == 'active_high_mask':
                beat_dm = (~beat_be) & self._dm_mask_per_beat
            else:
                # active_low_mask: DM=0 masks => DM = byte_enable directly
                beat_dm = beat_be & self._dm_mask_per_beat

            results.append(Txn(
                iface='ddr_wr_beat',
                kind='beat',
                fields={
                    'data': beat_data,
                    'mask': beat_dm,
                }
            ))

        return results

    def _handle_dp_cmd_write(self, txn: Txn) -> List[Txn]:
        """
        Write command on dp_cmd. The actual data beats are produced by dp_wr,
        so the write command itself does not produce output transactions.
        
        Spec ref: dp_cmd schema has only 'aux' field for write kind.
        The write command coordinates the data path but the data comes from dp_wr.
        """
        # Write commands don't directly produce output; dp_wr does.
        return []

    def _handle_dp_cmd_read(self, txn: Txn) -> List[Txn]:
        """
        Read command on dp_cmd. Queue the command so we know how many beats
        to collect from ddr_rd_beat and what aux to echo back.
        
        Spec ref: dp_cmd read kind has 'aux' field.
        Spec ref: dp_rd_rsp response kind has 'aux' field that echoes the command's aux.
        """
        aux = txn.fields['aux']
        self._rd_cmd_queue.append({
            'aux': aux,
            'beats_remaining': self._beats_per_word,
            'beat_data': [],
        })
        return []

    def _handle_ddr_rd_beat(self, txn: Txn) -> List[Txn]:
        """
        DDR read beat arriving from PHY. Accumulate beats_per_word beats,
        then pack into a host word and emit dp_rd_rsp.
        
        Spec ref: PACK side — host_width/channel_width beats pack into one host word,
        low half first for little endianness.
        Spec ref: data_path_mapping.endianness = "little"
        """
        if not self._rd_cmd_queue:
            # Beat without a pending read command — spec doesn't define this case.
            # Most literal reading: ignore spurious beats.
            return []

        beat_data = txn.fields['data']
        cmd = self._rd_cmd_queue[0]
        cmd['beat_data'].append(beat_data)
        cmd['beats_remaining'] -= 1

        if cmd['beats_remaining'] > 0:
            return []

        # All beats collected — pack into host word
        self._rd_cmd_queue.pop(0)
        return [self._pack_read(cmd)]

    def _pack_read(self, cmd: dict) -> Txn:
        """
        PACK: Combine beats_per_word 16-bit beats into one 32-bit host word.
        
        Spec ref: data_path_mapping.endianness = "little" => first beat is low half.
        """
        host_data = 0
        for beat_idx, beat_val in enumerate(cmd['beat_data']):
            if self._endianness == 'little':
                bit_offset = beat_idx * self._channel_width_bits
            else:
                bit_offset = (self._beats_per_word - 1 - beat_idx) * self._channel_width_bits
            host_data |= (beat_val & self._channel_mask) << bit_offset

        return Txn(
            iface='dp_rd_rsp',
            kind='response',
            fields={
                'data': host_data,
                'aux': cmd['aux'],
            }
        )

    def drain(self) -> List[Txn]:
        """
        No pending outputs expected at end of trace under normal operation.
        
        If there are partially accumulated read beats, the spec doesn't define
        what happens with incomplete bursts. Most literal reading: do not emit
        partial responses.
        """
        return []
