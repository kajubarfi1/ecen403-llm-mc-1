from txn_contract import TransactionPredictor, Txn
from typing import List, Dict


class TransactionPredictor(TransactionPredictor):
    INPUT_IFACES = ('wb',)
    OUTPUT_IFACES = ('req', 'wb_rsp')

    def __init__(self, spec: dict):
        self.spec = spec
        self._extract_spec_params()
        self.reset()

    def _extract_spec_params(self):
        """Extract needed parameters from the specification."""
        # Host interface parameters
        host_if = self.spec.get('host_interface', {})
        self.data_width_bits = host_if.get('data_width_bits', 32)
        self.address_width_bits = host_if.get('address_width_bits', 29)
        
        # CSR register map
        self.csr_map = self.spec.get('csr_register_map', {})
        self.csr_base = int(self.csr_map.get('base_address', '0x00000000'), 16)
        self.csr_addr_width = self.csr_map.get('address_width_bits', 8)
        self.csr_registers = {}
        for reg in self.csr_map.get('registers', []):
            offset = int(reg.get('offset', '0x00'), 16)
            reset_val = reg.get('reset_value', '0x00000000')
            if isinstance(reset_val, str):
                reset_val = int(reset_val, 16)
            self.csr_registers[offset] = {
                'name': reg.get('name', ''),
                'reset_value': reset_val,
                'access': reg.get('access', 'RW'),
                'fields': reg.get('fields', [])
            }

    def reset(self) -> None:
        """Return all modeled state to its power-on values."""
        # Memory model for tracking writes
        self.memory: Dict[int, int] = {}
        
        # CSR state - initialize from reset values
        self.csr_state: Dict[int, int] = {}
        for offset, reg_info in self.csr_registers.items():
            self.csr_state[offset] = reg_info['reset_value']

    def _is_csr_access(self, addr: int) -> bool:
        """Check if address falls within CSR space."""
        csr_end = self.csr_base + (1 << self.csr_addr_width)
        return self.csr_base <= addr < csr_end

    def _read_csr(self, addr: int) -> int:
        """Read from CSR register."""
        offset = addr - self.csr_base
        if offset in self.csr_state:
            return self.csr_state[offset]
        return 0

    def _write_csr(self, addr: int, data: int, mask: int) -> None:
        """Write to CSR register with byte mask."""
        offset = addr - self.csr_base
        if offset not in self.csr_registers:
            return
            
        reg_info = self.csr_registers[offset]
        access = reg_info['access']
        
        # RO registers cannot be written
        if access == 'RO':
            return
            
        current = self.csr_state.get(offset, 0)
        
        # Build full mask from byte enables
        full_mask = 0
        for i in range(4):
            if mask & (1 << i):
                full_mask |= (0xFF << (i * 8))
        
        # For RW1C registers, writing 1 clears the bit
        if access == 'RW1C':
            bits_to_clear = data & full_mask
            new_value = current & ~bits_to_clear
        else:
            # Normal RW: update masked bits
            new_value = (current & ~full_mask) | (data & full_mask)
        
        self.csr_state[offset] = new_value

    def _read_memory(self, addr: int) -> int:
        """Read from memory model."""
        if self._is_csr_access(addr):
            return self._read_csr(addr)
        # For regular memory, return stored value or 0
        return self.memory.get(addr, 0)

    def _write_memory(self, addr: int, data: int, mask: int) -> None:
        """Write to memory model with byte mask."""
        if self._is_csr_access(addr):
            self._write_csr(addr, data, mask)
            return
            
        # Apply byte mask to memory write
        full_mask = 0
        for i in range(4):
            if mask & (1 << i):
                full_mask |= (0xFF << (i * 8))
        
        current = self.memory.get(addr, 0)
        new_value = (current & ~full_mask) | (data & full_mask)
        self.memory[addr] = new_value

    def process(self, txn: Txn) -> List[Txn]:
        """Process one input transaction and return resulting output transactions."""
        if txn.iface != 'wb':
            return []
        
        outputs = []
        
        if txn.kind == 'write':
            addr = txn.fields.get('addr', 0)
            data = txn.fields.get('data', 0)
            sel = txn.fields.get('sel', 0xF)
            
            # Update internal memory model
            self._write_memory(addr, data, sel)
            
            # Emit request descriptor for write
            req_txn = Txn(
                iface='req',
                kind='request',
                fields={
                    'we': 1,
                    'addr': addr,
                    'data': data,
                    'mask': sel
                }
            )
            outputs.append(req_txn)
            
        elif txn.kind == 'read':
            addr = txn.fields.get('addr', 0)
            
            # Emit request descriptor for read
            req_txn = Txn(
                iface='req',
                kind='request',
                fields={
                    'we': 0,
                    'addr': addr,
                    'data': 0,
                    'mask': 0xF
                }
            )
            outputs.append(req_txn)
            
            # Read data from memory model
            read_data = self._read_memory(addr)
            
            # Emit wishbone response with read data
            rsp_txn = Txn(
                iface='wb_rsp',
                kind='read_data',
                fields={
                    'addr': addr,
                    'data': read_data
                }
            )
            outputs.append(rsp_txn)
        
        return outputs

    def drain(self) -> List[Txn]:
        """Return any pending output transactions at end of trace."""
        # No buffered transactions in this model
        return []
