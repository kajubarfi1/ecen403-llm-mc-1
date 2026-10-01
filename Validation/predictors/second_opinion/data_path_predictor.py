from txn_contract import TransactionPredictor, Txn
from typing import List
from collections import deque


class DataPathPredictor(TransactionPredictor):
    """
    Transaction predictor for data_path validation scope.
    
    Models the data width conversion between host interface (32-bit) and
    DDR interface (16-bit) per the data_path_mapping section of the spec.
    """
    
    INPUT_IFACES = ('ddr_rd_beat', 'dp_cmd', 'dp_wr')
    OUTPUT_IFACES = ('ddr_wr_beat', 'dp_rd_rsp')
    
    def __init__(self, spec: dict):
        self._spec = spec
        
        # Extract data path mapping parameters from spec
        # Spec section: data_path_mapping
        data_path_mapping = spec.get('data_path_mapping', {})
        self._ddr_width_bits = data_path_mapping.get('ddr_channel_width_bits', 16)
        self._host_width_bits = data_path_mapping.get('host_width_bits', 32)
        self._endianness = data_path_mapping.get('endianness', 'little')
        
        # Spec section: controller_architecture
        controller_arch = spec.get('controller_architecture', {})
        self._aux_width = controller_arch.get('aux_width', 4)
        
        # Spec section: memory_geometry
        memory_geom = spec.get('memory_geometry', {})
        self._burst_length = memory_geom.get('burst_length', 8)
        
        # Derived: number of DDR beats per host word
        # Per data_path_mapping.pack_mode: "pack_32_to_16"
        # 32-bit host word packs to 2x 16-bit DDR beats
        self._beats_per_host_word = self._host_width_bits // self._ddr_width_bits
        
        # Masks per spec
        # host_interface.granularity_bits = 8, so 4 byte enables for 32-bit
        # phy_interface.dm_enabled = true, dq_width_bits = 16, so 2 DM bits
        self._host_mask_width = self._host_width_bits // 8  # 4 bits
        self._ddr_mask_width = self._ddr_width_bits // 8    # 2 bits
        
        self.reset()
    
    def reset(self) -> None:
        """Return all modeled state to power-on values."""
        # Queue of pending read commands (each entry is the aux value)
        # Per spec section controller_architecture: read data flows from DDR
        # back to host with aux tagging for response routing
        self._pending_read_aux = deque()
        
        # Accumulator for incoming DDR read beats
        # We need to combine beats_per_host_word beats into one host word
        self._read_beat_accumulator = []
    
    def process(self, txn: Txn) -> List[Txn]:
        """
        Process one input transaction and return any output transactions it implies.
        
        Data path behavior per spec section data_path_mapping:
        - pack_mode: "pack_32_to_16" - 32-bit host data packs to 2x 16-bit DDR
        - endianness: "little" - lower address bytes in lower bit positions
        - byte_enable_semantics: "wishbone_sel_per_byte" per Wishbone B4 3.1.3
        """
        iface = txn.iface
        kind = txn.kind
        
        if iface == 'dp_cmd':
            return self._process_cmd(txn)
        elif iface == 'dp_wr':
            return self._process_wr(txn)
        elif iface == 'ddr_rd_beat':
            return self._process_rd_beat(txn)
        else:
            # Unknown interface - ignore per contract
            return []
    
    def _process_cmd(self, txn: Txn) -> List[Txn]:
        """
        Process data path command.
        
        Per spec section data_path_mapping and controller_architecture:
        - read command: signals that DDR read beats will arrive, aux tags response
        - write command: signals that host write data should be sent to DDR
        """
        kind = txn.kind
        fields = txn.fields
        
        if kind == 'read':
            # Spec: controller_architecture.aux_width = 4
            # The aux field travels with the read to tag the response
            aux = fields.get('aux', 0)
            self._pending_read_aux.append(aux)
            return []
        
        elif kind == 'write':
            # Write command indicates write burst start
            # Actual data comes via dp_wr transactions
            # No output generated from command alone
            return []
        
        else:
            # Unknown command kind - ignore
            return []
    
    def _process_wr(self, txn: Txn) -> List[Txn]:
        """
        Process host write data and generate DDR write beats.
        
        Per spec section data_path_mapping:
        - pack_mode: "pack_32_to_16" - split 32-bit host word to 2x 16-bit DDR
        - endianness: "little" - per JESD79-3 and Wishbone B4 3.1.3, 
          lower address bytes map to lower DQ pins
        
        Per spec section phy_interface:
        - dm_enabled: true - data mask is active
        - dq_width_bits: 16
        """
        if txn.kind != 'write':
            return []
        
        fields = txn.fields
        host_data = fields.get('data', 0)
        host_mask = fields.get('mask', 0)
        
        outputs = []
        
        # Build table of beat extractions based on endianness
        # Per spec data_path_mapping.endianness = "little"
        # Little endian: beat 0 = lower bits, beat 1 = upper bits
        # Per JESD79-3 section 3.1: DQ[7:0] carries lower byte, DQ[15:8] upper byte
        beat_extraction_table = self._build_write_beat_table()
        
        for beat_idx in range(self._beats_per_host_word):
            data_shift, data_mask, mask_shift, mask_bits = beat_extraction_table[beat_idx]
            
            # Extract 16-bit data for this beat
            beat_data = (host_data >> data_shift) & data_mask
            
            # Extract 2-bit mask for this beat
            # Per Wishbone B4 3.1.3: SEL_O indicates valid byte lanes
            # Per JESD79-3 4.6: DM is asserted to mask (not write) bytes
            # The mask semantics depend on interpretation - assuming mask=1 means write
            beat_mask = (host_mask >> mask_shift) & mask_bits
            
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
    
    def _build_write_beat_table(self):
        """
        Build extraction table for converting host word to DDR beats.
        
        Returns list of tuples: (data_shift, data_mask, mask_shift, mask_bits)
        
        Per spec data_path_mapping.endianness = "little":
        - Beat 0: bits [15:0] of host word, mask bits [1:0]
        - Beat 1: bits [31:16] of host word, mask bits [3:2]
        """
        table = []
        bits_per_beat = self._ddr_width_bits  # 16
        mask_bits_per_beat = self._ddr_mask_width  # 2
        data_mask = (1 << bits_per_beat) - 1  # 0xFFFF
        mask_mask = (1 << mask_bits_per_beat) - 1  # 0x3
        
        if self._endianness == 'little':
            # Little endian: lower bits first
            for i in range(self._beats_per_host_word):
                data_shift = i * bits_per_beat
                mask_shift = i * mask_bits_per_beat
                table.append((data_shift, data_mask, mask_shift, mask_mask))
        else:
            # Big endian: upper bits first
            # Per JESD79-3 this would be non-standard but handle if spec says so
            for i in range(self._beats_per_host_word):
                data_shift = (self._beats_per_host_word - 1 - i) * bits_per_beat
                mask_shift = (self._beats_per_host_word - 1 - i) * mask_bits_per_beat
                table.append((data_shift, data_mask, mask_shift, mask_mask))
        
        return table
    
    def _process_rd_beat(self, txn: Txn) -> List[Txn]:
        """
        Process DDR read beat and generate host read response when complete.
        
        Per spec section data_path_mapping:
        - pack_mode: "pack_32_to_16" - combine 2x 16-bit DDR to 32-bit host
        - endianness: "little" - first beat is lower bits
        
        Per spec section controller_architecture:
        - aux_width: 4 - aux tag from read command flows to response
        """
        if txn.kind != 'beat':
            return []
        
        fields = txn.fields
        beat_data = fields.get('data', 0)
        
        # Accumulate beat
        self._read_beat_accumulator.append(beat_data)
        
        # Check if we have enough beats for one host word
        if len(self._read_beat_accumulator) < self._beats_per_host_word:
            return []
        
        # We have enough beats - assemble host word
        host_data = self._assemble_read_data(self._read_beat_accumulator[:self._beats_per_host_word])
        
        # Remove consumed beats
        self._read_beat_accumulator = self._read_beat_accumulator[self._beats_per_host_word:]
        
        # Get aux from pending read command
        # Per spec: aux tags the response to the originating command
        if self._pending_read_aux:
            aux = self._pending_read_aux.popleft()
        else:
            # No pending command - per spec this shouldn't happen in valid traces
            # Per Wishbone B4 3.1.7: responses must correspond to requests
            # Use 0 as default since spec is silent on error handling here
            aux = 0
        
        out_txn = Txn(
            iface='dp_rd_rsp',
            kind='response',
            fields={
                'data': host_data,
                'aux': aux
            }
        )
        
        return [out_txn]
    
    def _assemble_read_data(self, beats: List[int]) -> int:
        """
        Assemble host word from DDR beats.
        
        Per spec data_path_mapping.endianness = "little":
        - Beat 0 provides bits [15:0]
        - Beat 1 provides bits [31:16]
        
        Returns assembled 32-bit host word.
        """
        assembly_table = self._build_read_assembly_table()
        
        host_data = 0
        for beat_idx, beat_data in enumerate(beats):
            shift = assembly_table[beat_idx]
            host_data |= (beat_data & ((1 << self._ddr_width_bits) - 1)) << shift
        
        return host_data
    
    def _build_read_assembly_table(self):
        """
        Build assembly table for combining DDR beats into host word.
        
        Returns list of shift amounts for each beat index.
        
        Per spec data_path_mapping.endianness = "little":
        - Beat 0 -> shift 0 (bits 15:0)
        - Beat 1 -> shift 16 (bits 31:16)
        """
        table = []
        bits_per_beat = self._ddr_width_bits  # 16
        
        if self._endianness == 'little':
            for i in range(self._beats_per_host_word):
                table.append(i * bits_per_beat)
        else:
            # Big endian: first beat goes to upper bits
            for i in range(self._beats_per_host_word):
                table.append((self._beats_per_host_word - 1 - i) * bits_per_beat)
        
        return table
    
    def drain(self) -> List[Txn]:
        """
        Return any pending output transactions at end of trace.
        
        Per spec: at trace end, any accumulated partial read data would be
        incomplete. Per Wishbone B4 3.2.1: a cycle must complete before
        termination. Incomplete data indicates trace truncation.
        
        We do not emit partial responses as spec requires complete burst
        transfers (memory_geometry.burst_length = 8).
        """
        # No partial outputs - incomplete bursts are trace artifacts
        return []
