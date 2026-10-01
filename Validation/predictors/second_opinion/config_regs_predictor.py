from txn_contract import TransactionPredictor, Txn
from typing import List
import math


class Predictor(TransactionPredictor):
    INPUT_IFACES = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES = ('cfg_refresh', 'cfg_timing', 'csr_rsp')

    def __init__(self, spec: dict):
        self.spec = spec
        self._build_register_tables(spec)
        self.reset()

    def _parse_bit_range(self, bits_str):
        if ':' in bits_str:
            parts = bits_str.split(':')
            hi = int(parts[0])
            lo = int(parts[1])
            return lo, hi
        else:
            b = int(bits_str)
            return b, b

    def _build_register_tables(self, spec):
        csr_map = spec['csr_register_map']
        self.addr_width = csr_map['address_width_bits']
        self.data_width = csr_map['data_width_bits']

        self.registers = {}
        self.reg_by_offset = {}

        for reg_def in csr_map['registers']:
            name = reg_def['name']
            offset_str = reg_def['offset']
            offset = int(offset_str, 16) if isinstance(offset_str, str) else int(offset_str)
            reset_val_raw = reg_def['reset_value']
            if isinstance(reset_val_raw, str):
                reset_value = int(reset_val_raw, 16)
            else:
                reset_value = int(reset_val_raw)
            reg_access = reg_def['access']

            fields = []
            for f in reg_def['fields']:
                lo, hi = self._parse_bit_range(f['bits'])
                width = hi - lo + 1
                mask = ((1 << width) - 1) << lo
                f_reset = int(f.get('reset_value', 0))
                fields.append({
                    'name': f['name'],
                    'lo': lo,
                    'hi': hi,
                    'width': width,
                    'mask': mask,
                    'access': f['access'],
                    'reset_value': f_reset,
                })

            reg_info = {
                'name': name,
                'offset': offset,
                'reset_value': reset_value,
                'access': reg_access,
                'fields': fields,
            }
            self.registers[name] = reg_info
            self.reg_by_offset[offset] = reg_info

        # Build set of valid offsets
        self.valid_offsets = set(self.reg_by_offset.keys())

        # Precompute which registers feed cfg_timing and cfg_refresh
        # cfg_timing fields come from TIMING_0, TIMING_1, TIMING_2, TIMING_3
        # cfg_refresh fields come from TIMING_3 (tREFI), REFRESH_CONFIG, CTRL_CONFIG (force_refresh)

        # Map from cfg_timing field name to (register_name, field_name)
        self.timing_field_map = {
            'trcd': ('TIMING_0', 'tRCD_nCK'),
            'trp': ('TIMING_0', 'tRP_nCK'),
            'tras': ('TIMING_0', 'tRAS_nCK'),
            'trc': ('TIMING_0', 'tRC_nCK'),
            'trrd': ('TIMING_1', 'tRRD_nCK'),
            'twtr': ('TIMING_1', 'tWTR_nCK'),
            'tfaw': ('TIMING_1', 'tFAW_nCK'),
            'trfc': ('TIMING_1', 'tRFC_nCK'),
            'twr': ('TIMING_2', 'tWR_nCK'),
            'trtp': ('TIMING_2', 'tRTP_nCK'),
            'tccd': ('TIMING_3', 'tCCD_nCK'),
        }

        self.refresh_field_map = {
            'trefi': ('TIMING_3', 'tREFI_nCK'),
            'max_postpone': ('REFRESH_CONFIG', 'max_postpone'),
            'urgent_threshold': ('REFRESH_CONFIG', 'urgent_threshold'),
            'priority': ('REFRESH_CONFIG', 'ref_priority'),
            'force_refresh': ('CTRL_CONFIG', 'force_refresh'),
        }

        # Registers whose writes can affect cfg_timing
        self.timing_trigger_regs = set()
        for reg_name, _ in self.timing_field_map.values():
            self.timing_trigger_regs.add(reg_name)

        # Registers whose writes can affect cfg_refresh
        self.refresh_trigger_regs = set()
        for reg_name, _ in self.refresh_field_map.values():
            self.refresh_trigger_regs.add(reg_name)

    def reset(self) -> None:
        # Initialize register storage with reset values
        self.reg_values = {}
        for name, info in self.registers.items():
            self.reg_values[name] = info['reset_value'] & ((1 << self.data_width) - 1)

        # Hardware status levels - initialize to reset defaults
        self.hw_levels = {
            'init_done': 0,
            'cal_done': 0,
            'cal_fail': 0,
            'bist_done': 0,
            'bist_fail': 0,
            'ref_pending': 0,
            'self_refresh': 0,
            'ecc_ce_count': 0,
            'bist_fail_addr': 0,
        }

        # Track last emitted values for change-qualification
        self.last_timing = None
        self.last_refresh = None

    def _get_field_value(self, reg_name, field_name):
        reg_info = self.registers[reg_name]
        reg_val = self.reg_values[reg_name]
        for f in reg_info['fields']:
            if f['name'] == field_name:
                return (reg_val >> f['lo']) & ((1 << f['width']) - 1)
        raise KeyError(f"Field {field_name} not found in {reg_name}")

    def _set_field_value(self, reg_name, field_name, value):
        reg_info = self.registers[reg_name]
        reg_val = self.reg_values[reg_name]
        for f in reg_info['fields']:
            if f['name'] == field_name:
                mask = f['mask']
                reg_val = (reg_val & ~mask) | ((value << f['lo']) & mask)
                self.reg_values[reg_name] = reg_val
                return
        raise KeyError(f"Field {field_name} not found in {reg_name}")

    def _build_read_value(self, reg_name):
        """Build the value returned for a read of the given register.
        
        Per the spec notes: WO fields read as zero (CSR_001 / access violation
        convention: err=0, WO field reads as zero).
        RO fields in CTRL_STATUS mirror hardware levels.
        RO fields in ERROR_STATUS mirror hardware levels for ecc_ce_count and bist_fail_addr.
        RW1C fields reflect their current stored state.
        """
        reg_info = self.registers[reg_name]
        result = 0

        for f in reg_info['fields']:
            if f['access'] == 'WO':
                # Per spec note: WO field reads as zero
                val = 0
            elif reg_name == 'CTRL_STATUS':
                # All CTRL_STATUS fields are RO and mirror hardware levels
                val = self._get_ctrl_status_field(f['name'])
            elif reg_name == 'ERROR_STATUS':
                val = self._get_error_status_field(f['name'])
            else:
                val = (self.reg_values[reg_name] >> f['lo']) & ((1 << f['width']) - 1)
            result |= (val & ((1 << f['width']) - 1)) << f['lo']

        return result

    def _get_ctrl_status_field(self, field_name):
        """CTRL_STATUS fields are all RO and mirror hardware level signals."""
        level_map = {
            'init_done': 'init_done',
            'cal_done': 'cal_done',
            'cal_fail': 'cal_fail',
            'bist_done': 'bist_done',
            'bist_fail': 'bist_fail',
            'ref_pending_cnt': 'ref_pending',
            'self_refresh_active': 'self_refresh',
            'reserved': None,
        }
        hw_key = level_map.get(field_name)
        if hw_key is None:
            return 0
        return self.hw_levels[hw_key]

    def _get_error_status_field(self, field_name):
        """ERROR_STATUS has mixed field types: RO level-mirrors and RW1C flags."""
        if field_name == 'ecc_ce_count':
            # RO, mirrors hardware level
            return self.hw_levels['ecc_ce_count']
        elif field_name == 'bist_fail_addr':
            # RO, mirrors hardware level
            return self.hw_levels['bist_fail_addr']
        elif field_name in ('ecc_ue_flag', 'ref_starve_flag', 'init_fail_flag'):
            # RW1C stored in reg_values
            reg_info = self.registers['ERROR_STATUS']
            for f in reg_info['fields']:
                if f['name'] == field_name:
                    return (self.reg_values['ERROR_STATUS'] >> f['lo']) & ((1 << f['width']) - 1)
        elif field_name == 'reserved':
            return 0
        return 0

    def _write_register(self, reg_name, write_data):
        """Apply a write to a register, respecting field access types.
        
        Per spec notes:
        - RO fields: write is silently ignored (err=0), field keeps value
        - WO fields: write value is accepted (pulse semantics for some)
        - RW fields: write value is accepted
        - RW1C fields: writing 1 clears the bit
        - Reserved/RO bits within an RW register are not modified
        """
        reg_info = self.registers[reg_name]
        current = self.reg_values[reg_name]
        new_val = current

        for f in reg_info['fields']:
            field_write_val = (write_data >> f['lo']) & ((1 << f['width']) - 1)

            if f['access'] == 'RO':
                # Write ignored; field keeps its value
                pass
            elif f['access'] == 'RW':
                new_val = (new_val & ~f['mask']) | ((field_write_val << f['lo']) & f['mask'])
            elif f['access'] == 'WO':
                # Accept the write value into storage
                new_val = (new_val & ~f['mask']) | ((field_write_val << f['lo']) & f['mask'])
            elif f['access'] == 'RW1C':
                # Writing 1 clears the corresponding bit(s)
                clear_mask = field_write_val << f['lo']
                new_val = new_val & ~clear_mask

        self.reg_values[reg_name] = new_val

    def _build_timing_snapshot(self):
        """Build a dict of all cfg_timing fields from current register state."""
        result = {}
        for output_field, (reg_name, field_name) in self.timing_field_map.items():
            result[output_field] = self._get_field_value(reg_name, field_name)
        return result

    def _build_refresh_snapshot(self):
        """Build a dict of all cfg_refresh fields from current register state."""
        result = {}
        for output_field, (reg_name, field_name) in self.refresh_field_map.items():
            result[output_field] = self._get_field_value(reg_name, field_name)
        return result

    def _emit_timing_if_changed(self, outputs):
        """Emit a cfg_timing update if any field has changed."""
        snap = self._build_timing_snapshot()
        if snap != self.last_timing:
            self.last_timing = dict(snap)
            outputs.append(Txn(iface='cfg_timing', kind='update', fields=dict(snap)))

    def _emit_refresh_if_changed(self, outputs, force_refresh_pulse=False):
        """Emit cfg_refresh update(s) if any field has changed.
        
        For force_refresh (WO pulse): if written as 1, emit update with
        force_refresh=1, then auto-clear and emit update with force_refresh=0.
        """
        snap = self._build_refresh_snapshot()

        if force_refresh_pulse and snap.get('force_refresh', 0) == 1:
            # First emit with force_refresh=1
            if snap != self.last_refresh:
                self.last_refresh = dict(snap)
                outputs.append(Txn(iface='cfg_refresh', kind='update', fields=dict(snap)))

            # Auto-clear force_refresh back to 0
            self._set_field_value('CTRL_CONFIG', 'force_refresh', 0)
            snap2 = self._build_refresh_snapshot()
            if snap2 != self.last_refresh:
                self.last_refresh = dict(snap2)
                outputs.append(Txn(iface='cfg_refresh', kind='update', fields=dict(snap2)))
        else:
            if snap != self.last_refresh:
                self.last_refresh = dict(snap)
                outputs.append(Txn(iface='cfg_refresh', kind='update', fields=dict(snap)))

    def process(self, txn: Txn) -> List[Txn]:
        outputs = []

        if txn.iface == 'csr_sts_level':
            if txn.kind == 'state':
                # Update hardware level mirrors
                for key in ('init_done', 'cal_done', 'cal_fail', 'bist_done',
                            'bist_fail', 'ref_pending', 'self_refresh',
                            'ecc_ce_count', 'bist_fail_addr'):
                    if key in txn.fields:
                        self.hw_levels[key] = txn.fields[key]
            return outputs

        if txn.iface == 'csr_sts':
            if txn.kind == 'event':
                # RW1C flag fields: hardware events SET the flags
                # (only bus writes of 1 can clear them)
                if txn.fields.get('ecc_ue', 0):
                    self._set_field_value('ERROR_STATUS', 'ecc_ue_flag',
                                          self._get_field_value('ERROR_STATUS', 'ecc_ue_flag') | 1)
                if txn.fields.get('ref_starve', 0):
                    self._set_field_value('ERROR_STATUS', 'ref_starve_flag',
                                          self._get_field_value('ERROR_STATUS', 'ref_starve_flag') | 1)
                if txn.fields.get('init_fail', 0):
                    self._set_field_value('ERROR_STATUS', 'init_fail_flag',
                                          self._get_field_value('ERROR_STATUS', 'init_fail_flag') | 1)
            return outputs

        if txn.iface == 'csr':
            addr = txn.fields.get('addr', 0)

            if addr not in self.valid_offsets:
                # Unmapped address: err=1
                if txn.kind == 'write':
                    outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                        'addr': addr,
                        'err': 1,
                    }))
                elif txn.kind == 'read':
                    outputs.append(Txn(iface='csr_rsp', kind='read_data', fields={
                        'addr': addr,
                        'data': 0,
                        'err': 1,
                    }))
                return outputs

            reg_info = self.reg_by_offset[addr]
            reg_name = reg_info['name']

            if txn.kind == 'write':
                write_data = txn.fields.get('data', 0)

                # Check if this is a write to a fully RO register
                # Per spec note: write to RO register => err=0, write is ignored
                # (access violation convention)
                # But we still need to process field-by-field for mixed-access registers

                # Detect if force_refresh is being written as 1
                force_refresh_pulse = False
                if reg_name == 'CTRL_CONFIG':
                    fr_field = None
                    for f in reg_info['fields']:
                        if f['name'] == 'force_refresh':
                            fr_field = f
                            break
                    if fr_field:
                        fr_write_val = (write_data >> fr_field['lo']) & ((1 << fr_field['width']) - 1)
                        if fr_write_val == 1:
                            force_refresh_pulse = True

                # Perform the write
                self._write_register(reg_name, write_data)

                # Also auto-clear bist_start and force_self_ref (WO pulse fields)
                # after they've been captured — but they don't produce output stream events
                # except force_refresh which has special handling
                if reg_name == 'CTRL_CONFIG':
                    # Clear WO pulse fields back to 0 after write (except force_refresh
                    # which is handled in _emit_refresh_if_changed)
                    self._set_field_value('CTRL_CONFIG', 'bist_start', 0)
                    self._set_field_value('CTRL_CONFIG', 'force_self_ref', 0)
                    if not force_refresh_pulse:
                        self._set_field_value('CTRL_CONFIG', 'force_refresh', 0)

                # Emit write_ack with err=0
                outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                    'addr': addr,
                    'err': 0,
                }))

                # Check if this write triggers cfg_timing or cfg_refresh updates
                if reg_name in self.timing_trigger_regs:
                    self._emit_timing_if_changed(outputs)
                if reg_name in self.refresh_trigger_regs:
                    self._emit_refresh_if_changed(outputs, force_refresh_pulse=force_refresh_pulse)

            elif txn.kind == 'read':
                read_val = self._build_read_value(reg_name)
                outputs.append(Txn(iface='csr_rsp', kind='read_data', fields={
                    'addr': addr,
                    'data': read_val,
                    'err': 0,
                }))

            return outputs

        # Unknown interface: ignore
        return outputs

    def drain(self) -> List[Txn]:
        return []
