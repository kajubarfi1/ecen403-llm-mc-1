from txn_contract import TransactionPredictor, Txn
from typing import List
import math


class DDR3TransactionPredictor(TransactionPredictor):
    INPUT_IFACES = ('req',)
    OUTPUT_IFACES = ('cq_enq',)

    def __init__(self, spec: dict):
        self.spec = spec
        geo = spec['memory_geometry']
        self.row_bits = geo['row_bits']
        self.column_bits = geo['column_bits']
        self.bank_bits = geo['bank_bits']
        self.burst_length = geo['burst_length']
        self.address_mapping = geo['address_mapping']

        host = spec['host_interface']
        self.host_data_width_bits = host['data_width_bits']
        self.host_addr_width = host['address_width_bits']

        data_path = spec['data_path_mapping']
        self.ddr_channel_width_bits = data_path['ddr_channel_width_bits']

        self.reset()

    def reset(self) -> None:
        pass

    def process(self, txn: Txn) -> List[Txn]:
        if txn.iface != 'req':
            return []

        addr = txn.fields.get('addr', 0)
        we = txn.fields.get('we', 0)

        # The host interface is byte-addressed with 29-bit address.
        # The DDR channel width is 16 bits = 2 bytes, so the lowest bit
        # is the channel byte offset bit.
        # burst_length = 8 transfers on the DDR bus.
        # 
        # Address mapping: row-bank-column (high to low), stacked above
        # the channel byte-offset bit(s).
        #
        # Channel width in bytes = ddr_channel_width_bits / 8 = 2
        # So byte_offset_bits = log2(2) = 1
        #
        # Column is burst-aligned, meaning its low log2(burst_length) bits
        # are zero. So the column field in the address is only the upper
        # (column_bits - log2(burst_length)) bits.
        #
        # Layout from LSB to MSB of the byte address:
        #   [byte_offset : 1 bit]
        #   [burst_offset: log2(BL) = 3 bits] -- these become the low column bits (always 0 in the extracted col field)
        #   [column_upper: column_bits - log2(BL) bits]
        #   [bank: bank_bits]
        #   [row: row_bits]

        channel_bytes = self.ddr_channel_width_bits // 8  # 2
        byte_offset_bits = int(math.log2(channel_bytes))  # 1

        burst_offset_bits = int(math.log2(self.burst_length))  # 3

        # The column address has column_bits total bits. The low burst_offset_bits
        # of the column are implicitly zero (burst-aligned). The address encodes
        # the upper (column_bits - burst_offset_bits) bits of the column.
        col_upper_bits = self.column_bits - burst_offset_bits  # 10 - 3 = 7

        # Strip byte offset
        a = addr >> byte_offset_bits

        # Extract burst offset (these map to low column bits, which are 0 for burst-aligned)
        # We skip these bits - they are part of the column but forced to 0
        a = a >> burst_offset_bits

        # Extract upper column bits
        col_upper = a & ((1 << col_upper_bits) - 1)
        a = a >> col_upper_bits

        # Reconstruct full column: upper bits shifted left by burst_offset_bits
        col = col_upper << burst_offset_bits

        # Extract bank
        bank = a & ((1 << self.bank_bits) - 1)
        a = a >> self.bank_bits

        # Extract row
        row = a & ((1 << self.row_bits) - 1)

        out_txn = Txn(
            iface='cq_enq',
            kind='enqueue',
            fields={
                'row': row,
                'col': col,
                'bank': bank,
                'we': we,
            }
        )

        return [out_txn]

    def drain(self) -> List[Txn]:
        return []
