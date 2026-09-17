from txn_contract import TransactionPredictor, Txn
from typing import List, Dict, Any


class ConfigRegsPredictor(TransactionPredictor):
    INPUT_IFACES = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES = ('csr_rsp',)

    def __init__(self, spec: dict):
        self.spec = spec
        self._parse_spec()
        self.reset()

    def _parse_spec(self):
        csr_map = self.spec['csr_register_map']
        self.addr_width = csr_map['address_width_bits']
        self.data_width = csr_map['data_width_bits']
        
        self.registers = {}
        self.reg_by_offset = {}
        
        for reg in csr_map['registers']:
            name = reg['name']
            offset_str = reg['offset']
            offset = int(offset_str, 16) if isinstance(offset_str, str) else offset_str
            reset_val_str = reg['reset_value']
            reset_val = int(reset_val_str, 16) if isinstance(reset_val_str, str) else reset_val_str
            access = reg['access']
            
            fields = []
            for field in reg['fields']:
                field_info = {
                    'name': field['name'],
                    'access': field['access'],
                    'reset_value': field['reset_value']
                }
                bits_str = field['bits']
                if ':' in bits_str:
                    high, low = bits_str.split(':')
                    field_info['high'] = int(high)
                    field_info['low'] = int(low)
                else:
                    field_info['high'] = int(bits_str)
                    field_info['low'] = int(bits_str)
                fields.append(field_info)
            
            reg_info = {
                'name': name,
                'offset': offset,
                'access': access,
                'reset_value': reset_val,
                'fields': fields
            }
            self.registers[name] = reg_info
            self.reg_by_offset[offset] = reg_info
        
        self.max_addr = max(self.reg_by_offset.keys())

    def reset(self) -> None:
        self.reg_values = {}
        for name, reg_info in self.registers.items():
            self.reg_values[name] = reg_info['reset_value']
        
        self.hw_status_levels = {
            'init_done': 0,
            'cal_done': 0,
            'cal_fail': 0,
            'bist_done': 0,
            'bist_fail': 0,
            'ref_pending': 0,
            'self_refresh': 0,
            'ecc_ce_count': 0,
            'bist_fail_addr': 0
        }
        
        self.rw1c_flags = {
            'ecc_ue_flag': 0,
            'ref_starve_flag': 0,
            'init_fail_flag': 0
        }

    def _get_field_mask(self, high: int, low: int) -> int:
        width = high - low + 1
        return ((1 << width) - 1) << low

    def _extract_field(self, value: int, high: int, low: int) -> int:
        mask = self._get_field_mask(high, low)
        return (value & mask) >> low

    def _insert_field(self, reg_value: int, field_value: int, high: int, low: int) -> int:
        mask = self._get_field_mask(high, low)
        width = high - low + 1
        field_value = field_value & ((1 << width) - 1)
        return (reg_value & ~mask) | (field_value << low)

    def _build_ctrl_status(self) -> int:
        value = 0
        value = self._insert_field(value, self.hw_status_levels['init_done'], 0, 0)
        value = self._insert_field(value, self.hw_status_levels['cal_done'], 1, 1)
        value = self._insert_field(value, self.hw_status_levels['cal_fail'], 2, 2)
        value = self._insert_field(value, self.hw_status_levels['bist_done'], 3, 3)
        value = self._insert_field(value, self.hw_status_levels['bist_fail'], 4, 4)
        value = self._insert_field(value, self.hw_status_levels['ref_pending'], 7, 5)
        value = self._insert_field(value, self.hw_status_levels['self_refresh'], 8, 8)
        return value

    def _build_error_status(self) -> int:
        value = 0
        value = self._insert_field(value, self.hw_status_levels['ecc_ce_count'], 15, 0)
        value = self._insert_field(value, self.rw1c_flags['ecc_ue_flag'], 16, 16)
        value = self._insert_field(value, self.rw1c_flags['ref_starve_flag'], 17, 17)
        value = self._insert_field(value, self.rw1c_flags['init_fail_flag'], 18, 18)
        value = self._insert_field(value, self.hw_status_levels['bist_fail_addr'], 31, 19)
        return value

    def _read_register(self, offset: int) -> tuple:
        if offset not in self.reg_by_offset:
            return (0, 1)
        
        reg_info = self.reg_by_offset[offset]
        name = reg_info['name']
        
        if name == 'CTRL_STATUS':
            return (self._build_ctrl_status(), 0)
        elif name == 'ERROR_STATUS':
            return (self._build_error_status(), 0)
        else:
            return (self.reg_values[name], 0)

    def _write_register(self, offset: int, data: int) -> int:
        if offset not in self.reg_by_offset:
            return 1
        
        reg_info = self.reg_by_offset[offset]
        name = reg_info['name']
        access = reg_info['access']
        
        if access == 'RO':
            return 0
        
        if name == 'ERROR_STATUS':
            for field in reg_info['fields']:
                if field['access'] == 'RW1C':
                    field_name = field['name']
                    high = field['high']
                    low = field['low']
                    write_bits = self._extract_field(data, high, low)
                    if write_bits:
                        self.rw1c_flags[field_name] = 0
            return 0
        
        if name == 'CTRL_CONFIG':
            current_val = self.reg_values[name]
            new_val = current_val
            
            for field in reg_info['fields']:
                field_name = field['name']
                field_access = field['access']
                high = field['high']
                low = field['low']
                
                if field_access == 'RW':
                    write_bits = self._extract_field(data, high, low)
                    new_val = self._insert_field(new_val, write_bits, high, low)
                elif field_access == 'WO':
                    pass
            
            self.reg_values[name] = new_val
            return 0
        
        if access == 'RW':
            current_val = self.reg_values[name]
            new_val = current_val
            
            for field in reg_info['fields']:
                field_access = field['access']
                high = field['high']
                low = field['low']
                
                if field_access == 'RW':
                    write_bits = self._extract_field(data, high, low)
                    new_val = self._insert_field(new_val, write_bits, high, low)
            
            self.reg_values[name] = new_val
            return 0
        
        return 0

    def _handle_csr_sts(self, txn: Txn) -> List[Txn]:
        if txn.kind != 'event':
            return []
        
        fields = txn.fields
        
        if fields.get('ecc_ue', 0):
            self.rw1c_flags['ecc_ue_flag'] = 1
        if fields.get('ref_starve', 0):
            self.rw1c_flags['ref_starve_flag'] = 1
        if fields.get('init_fail', 0):
            self.rw1c_flags['init_fail_flag'] = 1
        
        return []

    def _handle_csr_sts_level(self, txn: Txn) -> List[Txn]:
        if txn.kind != 'state':
            return []
        
        fields = txn.fields
        
        if 'init_done' in fields:
            self.hw_status_levels['init_done'] = fields['init_done'] & 1
        if 'cal_done' in fields:
            self.hw_status_levels['cal_done'] = fields['cal_done'] & 1
        if 'cal_fail' in fields:
            self.hw_status_levels['cal_fail'] = fields['cal_fail'] & 1
        if 'bist_done' in fields:
            self.hw_status_levels['bist_done'] = fields['bist_done'] & 1
        if 'bist_fail' in fields:
            self.hw_status_levels['bist_fail'] = fields['bist_fail'] & 1
        if 'ref_pending' in fields:
            self.hw_status_levels['ref_pending'] = fields['ref_pending'] & 0x7
        if 'self_refresh' in fields:
            self.hw_status_levels['self_refresh'] = fields['self_refresh'] & 1
        if 'ecc_ce_count' in fields:
            self.hw_status_levels['ecc_ce_count'] = fields['ecc_ce_count'] & 0xFFFF
        if 'bist_fail_addr' in fields:
            self.hw_status_levels['bist_fail_addr'] = fields['bist_fail_addr'] & 0x1FFF
        
        return []

    def _handle_csr(self, txn: Txn) -> List[Txn]:
        kind = txn.kind
        fields = txn.fields
        addr = fields.get('addr', 0)
        
        if kind == 'read':
            data, err = self._read_register(addr)
            return [Txn(
                iface='csr_rsp',
                kind='read_data',
                fields={
                    'addr': addr,
                    'data': data,
                    'err': err
                }
            )]
        elif kind == 'write':
            data = fields.get('data', 0)
            err = self._write_register(addr, data)
            return [Txn(
                iface='csr_rsp',
                kind='write_ack',
                fields={
                    'addr': addr,
                    'err': err
                }
            )]
        
        return []

    def process(self, txn: Txn) -> List[Txn]:
        iface = txn.iface
        
        if iface == 'csr':
            return self._handle_csr(txn)
        elif iface == 'csr_sts':
            return self._handle_csr_sts(txn)
        elif iface == 'csr_sts_level':
            return self._handle_csr_sts_level(txn)
        
        return []

    def drain(self) -> List[Txn]:
        return []
