from txn_contract import TransactionPredictor, Txn
from typing import List


class WbPortPredictor(TransactionPredictor):
    """
    Transaction predictor for wb_port -> cmd_queue interface.
    
    Models the address decomposition from Wishbone requests to command queue
    entries per the specification's memory_geometry and address_mapping.
    """
    
    INPUT_IFACES = ('req',)
    OUTPUT_IFACES = ('cq_enq',)
    
    def __init__(self, spec: dict):
        self._spec = spec
        self._build_tables()
        self.reset()
    
    def _build_tables(self) -> None:
        """
        Build lookup tables from spec for address decomposition.
        
        Per spec memory_geometry section:
        - row_bits: number of bits for row address
        - column_bits: number of bits for column address
        - bank_bits: number of bits for bank address
        - burst_length: DDR burst length (affects column alignment)
        - address_mapping: field ordering ("row-bank-column")
        
        Per spec memory_geometry.$derived:
        - channel_data_width_bits: width of DDR data channel
        
        Per spec host_interface:
        - addressing: "byte" means byte-addressed host interface
        """
        mem_geom = self._spec['memory_geometry']
        
        # Extract geometry parameters from spec
        self._row_bits = mem_geom['row_bits']
        self._column_bits = mem_geom['column_bits']
        self._bank_bits = mem_geom['bank_bits']
        self._burst_length = mem_geom['burst_length']
        
        # Channel width determines byte offset bits at bottom of address
        # Per spec memory_geometry.$derived.channel_data_width_bits
        channel_width_bits = mem_geom['$derived']['channel_data_width_bits']
        channel_width_bytes = channel_width_bits // 8
        
        # Number of bits for byte offset within a single DDR beat
        # Per host_interface.addressing = "byte", addresses are byte addresses
        self._byte_offset_bits = (channel_width_bytes - 1).bit_length()
        if channel_width_bytes == 1:
            self._byte_offset_bits = 0
        elif channel_width_bytes > 1:
            # log2 of channel_width_bytes
            self._byte_offset_bits = (channel_width_bytes).bit_length() - 1
            if (1 << self._byte_offset_bits) != channel_width_bytes:
                # Not power of 2, round up
                self._byte_offset_bits = channel_width_bytes.bit_length()
        
        # For 16-bit channel (2 bytes), byte_offset_bits = 1
        self._byte_offset_bits = 1 if channel_width_bytes == 2 else self._byte_offset_bits
        
        # Address mapping from spec: "row-bank-column"
        # This means fields are arranged high-to-low as: row | bank | column | byte_offset
        # Per spec memory_geometry.address_mapping
        self._address_mapping = mem_geom['address_mapping']
        
        # Build field position table based on address_mapping
        # Fields stack high-to-low above the channel byte-offset bit(s)
        self._field_positions = self._compute_field_positions()
        
        # Burst alignment: column must have low log2(burst_length) bits zeroed
        # Per error feedback: "a burst-aligned field zeroes its low log2(burst_length) bits"
        self._burst_align_bits = (self._burst_length).bit_length() - 1
        if (1 << self._burst_align_bits) != self._burst_length:
            self._burst_align_bits = self._burst_length.bit_length()
        # For burst_length=8, burst_align_bits = 3
        self._column_align_mask = ~((1 << self._burst_align_bits) - 1) & ((1 << self._column_bits) - 1)
    
    def _compute_field_positions(self) -> dict:
        """
        Compute bit positions for each address field based on address_mapping.
        
        Per spec memory_geometry.address_mapping = "row-bank-column":
        Fields are listed high-to-low, so actual bit positions from LSB are:
        - byte_offset: bits [byte_offset_bits-1:0]
        - column: bits [byte_offset_bits + column_bits - 1 : byte_offset_bits]
        - bank: bits [byte_offset_bits + column_bits + bank_bits - 1 : byte_offset_bits + column_bits]
        - row: bits [byte_offset_bits + column_bits + bank_bits + row_bits - 1 : byte_offset_bits + column_bits + bank_bits]
        """
        positions = {}
        
        # Parse mapping - format is "row-bank-column" meaning high to low
        # So column is lowest (just above byte offset), then bank, then row
        mapping_parts = self._address_mapping.split('-')
        
        # Reverse to get low-to-high order
        fields_low_to_high = list(reversed(mapping_parts))
        
        # Map field names to their bit widths
        width_table = {
            'row': self._row_bits,
            'bank': self._bank_bits,
            'column': self._column_bits
        }
        
        current_bit = self._byte_offset_bits
        
        for field in fields_low_to_high:
            field_width = width_table[field]
            positions[field] = {
                'start': current_bit,
                'width': field_width,
                'mask': (1 << field_width) - 1
            }
            current_bit += field_width
        
        return positions
    
    def reset(self) -> None:
        """
        Reset model to power-on state.
        
        This predictor is stateless for address decomposition - each request
        is independently transformed. No state to reset.
        """
        pass
    
    def process(self, txn: Txn) -> List[Txn]:
        """
        Process an input transaction and return resulting output transactions.
        
        For 'req' interface with 'request' kind:
        - Decompose the byte address into row, bank, column per address_mapping
        - Pass through the we (write enable) field
        
        Per spec memory_geometry.address_mapping = "row-bank-column":
        Address bits are assigned as: [row | bank | column | byte_offset]
        
        Column is burst-aligned by zeroing low log2(burst_length) bits.
        """
        # Ignore transactions on interfaces we don't model
        if txn.iface != 'req':
            return []
        
        # Only handle 'request' kind
        if txn.kind != 'request':
            return []
        
        # Extract fields from input transaction
        # Per schema: we, addr, data, mask
        addr = txn.fields['addr']
        we = txn.fields['we']
        
        # Decompose address using field position table
        row = self._extract_field(addr, 'row')
        bank = self._extract_field(addr, 'bank')
        col = self._extract_field(addr, 'column')
        
        # Apply burst alignment to column
        # Per spec memory_geometry.burst_length = 8, and error feedback indicates
        # column must have low log2(burst_length) = 3 bits zeroed
        col = col & self._column_align_mask
        
        # Create output transaction
        # Per cq_enq schema: row, col, bank, we
        out_txn = Txn(
            iface='cq_enq',
            kind='enqueue',
            fields={
                'row': row,
                'col': col,
                'bank': bank,
                'we': we
            }
        )
        
        return [out_txn]
    
    def _extract_field(self, addr: int, field_name: str) -> int:
        """
        Extract a field from the address using the precomputed position table.
        
        Per spec memory_geometry.address_mapping, fields are positioned
        relative to byte offset bits at the bottom.
        """
        pos = self._field_positions[field_name]
        return (addr >> pos['start']) & pos['mask']
    
    def drain(self) -> List[Txn]:
        """
        Return any pending output transactions at end of trace.
        
        This predictor produces outputs synchronously in process(),
        so nothing is buffered.
        """
        return []
