from txn_contract import TransactionPredictor, Txn
from typing import List
import math


class ConfigRegsPredictor(TransactionPredictor):
    INPUT_IFACES = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES = ('cfg_refresh', 'cfg_timing', 'csr_rsp')

    def __init__(self, spec: dict):
        self.spec = spec
        self.reg_map = spec['csr_register_map']
        self.registers_spec = self.reg_map['registers']
        self.data_width = self.reg_map['data_width_bits']

        # Build register info indexed by offset
        self._build_reg_info()

        self.reset()

    def _build_reg_info(self):
        """Parse the register map from the spec into internal structures."""
        self.reg_info = {}  # offset -> register info dict
        self.offset_by_name = {}

        for reg in self.registers_spec:
            offset = int(reg['offset'], 16)
            fields = []
            for f in reg.get('fields', []):
                bits_str = f['bits']
                if ':' in bits_str:
                    hi, lo = bits_str.split(':')
                    hi, lo = int(hi), int(lo)
                else:
                    hi = lo = int(bits_str)
                fields.append({
                    'name': f['name'],
                    'hi': hi,
                    'lo': lo,
                    'width': hi - lo + 1,
                    'access': f['access'],
                    'reset_value': f['reset_value'],
                    'description': f.get('description', '')
                })

            self.reg_info[offset] = {
                'name': reg['name'],
                'offset': offset,
                'access': reg['access'],
                'reset_value': int(reg['reset_value'], 16) if isinstance(reg['reset_value'], str) else reg['reset_value'],
                'fields': fields
            }
            self.offset_by_name[reg['name']] = offset

    def _get_field_mask(self, hi, lo):
        return ((1 << (hi - lo + 1)) - 1) << lo

    def _extract_field(self, value, hi, lo):
        return (value >> lo) & ((1 << (hi - lo + 1)) - 1)

    def _insert_field(self, reg_val, hi, lo, field_val):
        mask = self._get_field_mask(hi, lo)
        reg_val &= ~mask
        reg_val |= (field_val << lo) & mask
        return reg_val

    def reset(self) -> None:
        self.regs = {}
        for offset, info in self.reg_info.items():
            self.regs[offset] = info['reset_value']

        # Hardware status levels (from csr_sts_level)
        self.hw_init_done = 0
        self.hw_cal_done = 0
        self.hw_cal_fail = 0
        self.hw_bist_done = 0
        self.hw_bist_fail = 0
        self.hw_ref_pending = 0
        self.hw_self_refresh = 0
        self.hw_ecc_ce_count = 0
        self.hw_bist_fail_addr = 0

        # Hardware status events (RW1C flags from csr_sts)
        self.hw_ecc_ue_flag = 0
        self.hw_ref_starve_flag = 0
        self.hw_init_fail_flag = 0

        # Track previous output values for change-qualified emission
        self._prev_cfg_timing = None
        self._prev_cfg_refresh = None

    def _get_valid_offsets(self):
        return set(self.reg_info.keys())

    def _compute_ctrl_status(self):
        """Compose CTRL_STATUS from hardware level signals."""
        val = 0
        val |= (self.hw_init_done & 1) << 0
        val |= (self.hw_cal_done & 1) << 1
        val |= (self.hw_cal_fail & 1) << 2
        val |= (self.hw_bist_done & 1) << 3
        val |= (self.hw_bist_fail & 1) << 4
        val |= (self.hw_ref_pending & 0x7) << 5
        val |= (self.hw_self_refresh & 1) << 8
        return val

    def _compute_error_status(self):
        """Compose ERROR_STATUS from stored reg value plus hardware inputs."""
        offset = self.offset_by_name['ERROR_STATUS']
        base = self.regs[offset]

        # Bits 15:0 - ecc_ce_count (RO, from hardware level)
        val = self.hw_ecc_ce_count & 0xFFFF

        # Bits 16 - ecc_ue_flag (RW1C)
        val |= (self.hw_ecc_ue_flag & 1) << 16

        # Bit 17 - ref_starve_flag (RW1C)
        val |= (self.hw_ref_starve_flag & 1) << 17

        # Bit 18 - init_fail_flag (RW1C)
        val |= (self.hw_init_fail_flag & 1) << 18

        # Bits 31:19 - bist_fail_addr (RO, from hardware level)
        val |= (self.hw_bist_fail_addr & 0x1FFF) << 19

        return val

    def _read_register(self, offset):
        """Read a register, returning (data, err)."""
        if offset not in self.reg_info:
            return (0, 1)

        info = self.reg_info[offset]
        name = info['name']

        if name == 'CTRL_STATUS':
            val = self._compute_ctrl_status()
        elif name == 'ERROR_STATUS':
            val = self._compute_error_status()
        else:
            val = self.regs[offset]

        # For fields that are WO, they read as 0
        result = val
        for f in info['fields']:
            if f['access'] == 'WO':
                mask = self._get_field_mask(f['hi'], f['lo'])
                result &= ~mask

        result &= (1 << self.data_width) - 1
        return (result, 0)

    def _write_register(self, offset, data):
        """Write to a register. Returns True if write was accepted (even partially)."""
        if offset not in self.reg_info:
            return False

        info = self.reg_info[offset]
        name = info['name']

        if info['access'] == 'RO':
            # Write to RO register: ignored, no error (per spec note)
            return True

        if name == 'ERROR_STATUS':
            # RW1C register: writing 1 to RW1C bits clears them
            for f in info['fields']:
                if f['access'] == 'RW1C':
                    written_field = self._extract_field(data, f['hi'], f['lo'])
                    if written_field:
                        if f['name'] == 'ecc_ue_flag':
                            self.hw_ecc_ue_flag = 0
                        elif f['name'] == 'ref_starve_flag':
                            self.hw_ref_starve_flag = 0
                        elif f['name'] == 'init_fail_flag':
                            self.hw_init_fail_flag = 0
            # RO fields in this register are not affected by writes
            return True

        # Normal RW register
        old_val = self.regs[offset]
        new_val = old_val

        for f in info['fields']:
            if f['access'] in ('RW', 'WO'):
                field_val = self._extract_field(data, f['hi'], f['lo'])
                new_val = self._insert_field(new_val, f['hi'], f['lo'], field_val)
            # RO fields within an RW register keep their value

        new_val &= (1 << self.data_width) - 1
        self.regs[offset] = new_val
        return True

    def _get_cfg_timing_values(self):
        """Extract current timing config values from registers."""
        t0_off = self.offset_by_name['TIMING_0']
        t1_off = self.offset_by_name['TIMING_1']
        t2_off = self.offset_by_name['TIMING_2']
        t3_off = self.offset_by_name['TIMING_3']

        t0 = self.regs[t0_off]
        t1 = self.regs[t1_off]
        t2 = self.regs[t2_off]
        t3 = self.regs[t3_off]

        return {
            'trcd': self._extract_field(t0, 7, 0),
            'trp': self._extract_field(t0, 15, 8),
            'tras': self._extract_field(t0, 23, 16),
            'trc': self._extract_field(t0, 31, 24),
            'trrd': self._extract_field(t1, 7, 0),
            'twtr': self._extract_field(t1, 15, 8),
            'tfaw': self._extract_field(t1, 23, 16),
            'trfc': self._extract_field(t1, 31, 24),
            'twr': self._extract_field(t2, 7, 0),
            'trtp': self._extract_field(t2, 15, 8),
            'tccd': self._extract_field(t3, 7, 0),
        }

    def _get_cfg_refresh_values(self):
        """Extract current refresh config values from registers."""
        t3_off = self.offset_by_name['TIMING_3']
        ref_off = self.offset_by_name['REFRESH_CONFIG']
        ctrl_off = self.offset_by_name['CTRL_CONFIG']

        t3 = self.regs[t3_off]
        ref = self.regs[ref_off]
        ctrl = self.regs[ctrl_off]

        return {
            'trefi': self._extract_field(t3, 31, 8),
            'max_postpone': self._extract_field(ref, 3, 0),
            'urgent_threshold': self._extract_field(ref, 7, 4),
            'priority': self._extract_field(ref, 8, 8),
            'force_refresh': self._extract_field(ctrl, 6, 6),
        }

    def _emit_cfg_timing_if_changed(self):
        """Emit a cfg_timing update if any timing field changed."""
        current = self._get_cfg_timing_values()
        if current != self._prev_cfg_timing:
            self._prev_cfg_timing = dict(current)
            return [Txn(iface='cfg_timing', kind='update', fields=dict(current))]
        return []

    def _emit_cfg_refresh_if_changed(self):
        """Emit a cfg_refresh update if any refresh field changed."""
        current = self._get_cfg_refresh_values()
        if current != self._prev_cfg_refresh:
            self._prev_cfg_refresh = dict(current)
            return [Txn(iface='cfg_refresh', kind='update', fields=dict(current))]
        return []

    def process(self, txn: Txn) -> List[Txn]:
        if txn.iface == 'csr_sts_level':
            return self._process_sts_level(txn)
        elif txn.iface == 'csr_sts':
            return self._process_sts_event(txn)
        elif txn.iface == 'csr':
            return self._process_csr(txn)
        return []

    def _process_sts_level(self, txn: Txn) -> List[Txn]:
        """Process hardware status level updates."""
        fields = txn.fields
        if 'init_done' in fields:
            self.hw_init_done = fields['init_done']
        if 'cal_done' in fields:
            self.hw_cal_done = fields['cal_done']
        if 'cal_fail' in fields:
            self.hw_cal_fail = fields['cal_fail']
        if 'bist_done' in fields:
            self.hw_bist_done = fields['bist_done']
        if 'bist_fail' in fields:
            self.hw_bist_fail = fields['bist_fail']
        if 'ref_pending' in fields:
            self.hw_ref_pending = fields['ref_pending']
        if 'self_refresh' in fields:
            self.hw_self_refresh = fields['self_refresh']
        if 'ecc_ce_count' in fields:
            self.hw_ecc_ce_count = fields['ecc_ce_count']
        if 'bist_fail_addr' in fields:
            self.hw_bist_fail_addr = fields['bist_fail_addr']
        return []

    def _process_sts_event(self, txn: Txn) -> List[Txn]:
        """Process hardware status events (set RW1C flags)."""
        fields = txn.fields
        if fields.get('ecc_ue', 0):
            self.hw_ecc_ue_flag = 1
        if fields.get('ref_starve', 0):
            self.hw_ref_starve_flag = 1
        if fields.get('init_fail', 0):
            self.hw_init_fail_flag = 1
        return []

    def _process_csr(self, txn: Txn) -> List[Txn]:
        outputs = []

        if txn.kind == 'read':
            addr = txn.fields['addr']
            data, err = self._read_register(addr)
            outputs.append(Txn(iface='csr_rsp', kind='read_data', fields={
                'addr': addr,
                'data': data,
                'err': err
            }))

        elif txn.kind == 'write':
            addr = txn.fields['addr']
            data = txn.fields['data']

            # Check if address is valid
            if addr not in self.reg_info:
                outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                    'addr': addr,
                    'err': 1
                }))
                return outputs

            reg_name = self.reg_info[addr]['name']

            # Check if this is a register with force_refresh (CTRL_CONFIG)
            has_force_refresh = False
            if reg_name == 'CTRL_CONFIG':
                force_refresh_bit = self._extract_field(data, 6, 6)
                has_force_refresh = (force_refresh_bit == 1)

            # Perform the write
            self._write_register(addr, data)

            # Write ack (no error for valid addresses, even RO)
            outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                'addr': addr,
                'err': 0
            }))

            # Check for cfg_timing changes
            if reg_name in ('TIMING_0', 'TIMING_1', 'TIMING_2', 'TIMING_3'):
                outputs.extend(self._emit_cfg_timing_if_changed())

            # Check for cfg_refresh changes
            # TIMING_3 has tREFI, REFRESH_CONFIG has max_postpone/urgent_threshold/priority,
            # CTRL_CONFIG has force_refresh
            if reg_name in ('TIMING_3', 'REFRESH_CONFIG', 'CTRL_CONFIG'):
                outputs.extend(self._emit_cfg_refresh_if_changed())

            # Handle force_refresh pulse: if force_refresh was written as 1,
            # it's a pulse - auto-clears back to 0, producing a second update
            if has_force_refresh:
                # Clear force_refresh back to 0
                ctrl_off = self.offset_by_name['CTRL_CONFIG']
                self.regs[ctrl_off] = self._insert_field(self.regs[ctrl_off], 6, 6, 0)
                # Emit the clearing update
                outputs.extend(self._emit_cfg_refresh_if_changed())

            # Also check TIMING_3 for cfg_timing (tCCD is in TIMING_3)
            if reg_name == 'TIMING_3':
                # Already handled timing above, but also check refresh since tREFI is in TIMING_3
                pass  # Already handled

            # For WO fields bist_start and force_self_ref in CTRL_CONFIG, auto-clear
            if reg_name == 'CTRL_CONFIG':
                ctrl_off = self.offset_by_name['CTRL_CONFIG']
                # Clear bist_start (bit 5) and force_self_ref (bit 7) - they are WO pulse fields
                self.regs[ctrl_off] = self._insert_field(self.regs[ctrl_off], 5, 5, 0)
                self.regs[ctrl_off] = self._insert_field(self.regs[ctrl_off], 7, 7, 0)

        return outputs

    def drain(self) -> List[Txn]:
        return []
