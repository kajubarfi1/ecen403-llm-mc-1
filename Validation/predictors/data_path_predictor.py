from txn_contract import TransactionPredictor, Txn
from typing import List, Optional


class DataPathPredictor(TransactionPredictor):
    """
    Transaction predictor for the data_path scope.
    
    Models the data path mapping between host interface (32-bit) and
    DDR channel (16-bit) according to pack_32_to_16 mode with little-endian.
    """
    
    INPUT_IFACES: tuple = ('ddr_rd_beat', 'dp_cmd', 'dp_wr')
    OUTPUT_IFACES: tuple = ('ddr_wr_beat', 'dp_rd_rsp')
    
    def __init__(self, spec: dict):
        self.spec = spec
        
        # Extract data path mapping configuration
        dp_mapping = spec.get('data_path_mapping', {})
        self.host_width_bits = dp_mapping.get('host_width_bits', 32)
        self.channel_width_bits = dp_mapping.get('ddr_channel_width_bits', 16)
        self.pack_mode = dp_mapping.get('pack_mode', 'pack_32_to_16')
        self.endianness = dp_mapping.get('endianness', 'little')
        
        # Calculate beats per host word
        self.beats_per_word = self.host_width_bits // self.channel_width_bits
        
        # Extract controller architecture for aux width
        ctrl_arch = spec.get('controller_architecture', {})
        self.aux_width = ctrl_arch.get('aux_width', 4)
        
        self.reset()
    
    def reset(self) -> None:
        """Reset all modeled state to power-on values."""
        # Pending read commands with their aux values
        self._pending_read_cmds: List[int] = []
        
        # Buffer for incoming DDR read beats (collecting beats for one word)
        self._read_beat_buffer: List[int] = []
        
        # Current aux value for the read being assembled
        self._current_read_aux: Optional[int] = None
    
    def process(self, txn: Txn) -> List[Txn]:
        """Process one input transaction and return any resulting outputs."""
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields
        
        if iface == 'dp_cmd':
            return self._process_cmd(kind, fields)
        elif iface == 'dp_wr':
            return self._process_write(kind, fields)
        elif iface == 'ddr_rd_beat':
            return self._process_read_beat(kind, fields)
        else:
            # Unknown interface - ignore
            return []
    
    def _process_cmd(self, kind: str, fields: dict) -> List[Txn]:
        """Process a data path command."""
        if kind == 'read':
            # Store aux value for when read data arrives
            aux = fields.get('aux', 0)
            self._pending_read_cmds.append(aux)
        elif kind == 'write':
            # Write command - data will follow via dp_wr
            pass
        return []
    
    def _process_write(self, kind: str, fields: dict) -> List[Txn]:
        """Process host write data, producing DDR write beats."""
        if kind != 'write':
            return []
        
        data = fields.get('data', 0)
        mask = fields.get('mask', 0xF)
        
        # Pack 32-bit host word into 2 x 16-bit DDR beats (little-endian)
        # First beat is low 16 bits, second beat is high 16 bits
        outputs = []
        
        channel_mask = (1 << self.channel_width_bits) - 1
        bytes_per_beat = self.channel_width_bits // 8  # 2 bytes for 16-bit
        
        for beat_idx in range(self.beats_per_word):
            # Extract 16-bit data for this beat
            shift = beat_idx * self.channel_width_bits
            beat_data = (data >> shift) & channel_mask
            
            # Extract mask bits for this beat (2 bits per 16-bit beat)
            mask_shift = beat_idx * bytes_per_beat
            beat_mask = (mask >> mask_shift) & ((1 << bytes_per_beat) - 1)
            
            out_txn = Txn(
                iface='ddr_wr_beat',
                kind='beat',
                fields={
                    'data': beat_data,
                    'mask': beat_mask
                }
            )
            outputs.append(out_txn)
        
        return outputs
    
    def _process_read_beat(self, kind: str, fields: dict) -> List[Txn]:
        """Process DDR read beat, potentially producing host read response."""
        if kind != 'beat':
            return []
        
        data = fields.get('data', 0)
        
        # Mask to channel width (16 bits)
        channel_mask = (1 << self.channel_width_bits) - 1
        beat_data = data & channel_mask
        
        # Add beat to buffer
        self._read_beat_buffer.append(beat_data)
        
        # If this is the first beat of a word, get the aux from pending commands
        if len(self._read_beat_buffer) == 1 and self._pending_read_cmds:
            self._current_read_aux = self._pending_read_cmds.pop(0)
        
        # Check if we have collected enough beats for a full host word
        if len(self._read_beat_buffer) >= self.beats_per_word:
            # Pack beats into 32-bit word (little-endian: first beat is LSB)
            packed_data = 0
            for beat_idx, beat_val in enumerate(self._read_beat_buffer[:self.beats_per_word]):
                shift = beat_idx * self.channel_width_bits
                packed_data |= (beat_val << shift)
            
            # Clear the buffer
            self._read_beat_buffer = self._read_beat_buffer[self.beats_per_word:]
            
            # Get aux value
            aux = self._current_read_aux if self._current_read_aux is not None else 0
            self._current_read_aux = None
            
            # Emit read response
            out_txn = Txn(
                iface='dp_rd_rsp',
                kind='response',
                fields={
                    'data': packed_data,
                    'aux': aux
                }
            )
            return [out_txn]
        
        return []
    
    def drain(self) -> List[Txn]:
        """Return any pending outputs at end of trace."""
        outputs = []
        
        # If there are remaining beats that form complete words, emit them
        while len(self._read_beat_buffer) >= self.beats_per_word:
            packed_data = 0
            for beat_idx in range(self.beats_per_word):
                beat_val = self._read_beat_buffer[beat_idx]
                shift = beat_idx * self.channel_width_bits
                packed_data |= (beat_val << shift)
            
            self._read_beat_buffer = self._read_beat_buffer[self.beats_per_word:]
            
            aux = 0
            if self._pending_read_cmds:
                aux = self._pending_read_cmds.pop(0)
            
            out_txn = Txn(
                iface='dp_rd_rsp',
                kind='response',
                fields={
                    'data': packed_data,
                    'aux': aux
                }
            )
            outputs.append(out_txn)
        
        return outputs
