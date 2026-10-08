from txn_contract import TransactionPredictor, Txn
from typing import List, Dict, Any, Optional, Tuple


class ConfigRegsPredictor(TransactionPredictor):
    INPUT_IFACES = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES = ('cfg_refresh', 'cfg_timing', 'csr_rsp')

    def __init__(self, spec: dict):
        self.spec = spec
        self.reg_map_spec = spec['csr_register_map']['registers']
        self._build_register_info()
        self.reset()

    def _parse_bits(self, bits_str: str) -> Tuple[int, int]:
        """Return (msb, lsb) from a bits spec like '31:24' or '0'."""
        if ':' in str(bits_str):
            parts = str(bits_str).split(':')
            return int(parts[0]), int(parts[1])
        else:
            b = int(bits_str)
            return b, b

    def _parse_hex_or_int(self, val) -> int:
        if isinstance(val, str):
            return int(val, 0)
        return int(val)

    def _build_register_info(self):
        """Build internal data structures from the spec's register map."""
        self.registers = {}  # offset -> register info dict
        self.offset_by_name = {}
        self.valid_offsets = set()

        for reg_spec in self.reg_map_spec:
            offset = self._parse_hex_or_int(reg_spec['offset'])
            reset_val = self._parse_hex_or_int(reg_spec['reset_value'])
            name = reg_spec['name']
            access = reg_spec.get('access', 'RW')

            fields = []
            for f in reg_spec.get('fields', []):
                msb, lsb = self._parse_bits(f['bits'])
                width = msb - lsb + 1
                mask = ((1 << width) - 1) << lsb
                fields.append({
                    'name': f['name'],
                    'msb': msb,
                    'lsb': lsb,
                    'width': width,
                    'mask': mask,
                    'access': f.get('access', access),
                    'reset_value': f.get('reset_value', 0),
                })

            self.registers[offset] = {
                'name': name,
                'offset': offset,
                'access': access,
                'reset_value': reset_val,
                'fields': fields,
            }
            self.offset_by_name[name] = offset
            self.valid_offsets.add(offset)

    def _get_field_value(self, offset: int, field_name: str) -> int:
        reg = self.registers[offset]
        val = self.reg_values[offset]
        for f in reg['fields']:
            if f['name'] == field_name:
                return (val >> f['lsb']) & ((1 << f['width']) - 1)
        return 0

    def _set_field_value(self, offset: int, field_name: str, field_val: int):
        reg = self.registers[offset]
        val = self.reg_values[offset]
        for f in reg['fields']:
            if f['name'] == field_name:
                mask = f['mask']
                val = (val & ~mask) | ((field_val << f['lsb']) & mask)
                self.reg_values[offset] = val
                return

    def _snapshot_refresh_fields(self) -> dict:
        """Capture current refresh config fields."""
        timing3_offset = self.offset_by_name['TIMING_3']
        ctrl_config_offset = self.offset_by_name['CTRL_CONFIG']
        refresh_config_offset = self.offset_by_name['REFRESH_CONFIG']

        trefi = self._get_field_value(timing3_offset, 'tREFI_nCK')
        max_postpone = self._get_field_value(refresh_config_offset, 'max_postpone')
        urgent_threshold = self._get_field_value(refresh_config_offset, 'urgent_threshold')
        force_refresh = self._get_field_value(ctrl_config_offset, 'force_refresh')
        priority = self._get_field_value(refresh_config_offset, 'ref_priority')

        return {
            'trefi': trefi,
            'max_postpone': max_postpone,
            'urgent_threshold': urgent_threshold,
            'force_refresh': force_refresh,
            'priority': priority,
        }

    def _snapshot_timing_fields(self) -> dict:
        """Capture current timing config fields."""
        t0 = self.offset_by_name['TIMING_0']
        t1 = self.offset_by_name['TIMING_1']
        t2 = self.offset_by_name['TIMING_2']
        t3 = self.offset_by_name['TIMING_3']

        return {
            'trcd': self._get_field_value(t0, 'tRCD_nCK'),
            'trp': self._get_field_value(t0, 'tRP_nCK'),
            'tras': self._get_field_value(t0, 'tRAS_nCK'),
            'trc': self._get_field_value(t0, 'tRC_nCK'),
            'trrd': self._get_field_value(t1, 'tRRD_nCK'),
            'tfaw': self._get_field_value(t1, 'tFAW_nCK'),
            'twtr': self._get_field_value(t1, 'tWTR_nCK'),
            'twr': self._get_field_value(t2, 'tWR_nCK'),
            'trtp': self._get_field_value(t2, 'tRTP_nCK'),
            'tccd': self._get_field_value(t3, 'tCCD_nCK'),
            'trfc': self._get_field_value(t1, 'tRFC_nCK'),
        }

    def _make_refresh_txn(self, snapshot: dict) -> Txn:
        return Txn(iface='cfg_refresh', kind='update', fields=dict(snapshot))

    def _make_timing_txn(self, snapshot: dict) -> Txn:
        return Txn(iface='cfg_timing', kind='update', fields=dict(snapshot))

    def reset(self) -> None:
        self.reg_values = {}
        for offset, reg in self.registers.items():
            self.reg_values[offset] = reg['reset_value']

        # Status level state
        self.level_state = {
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

        # Snapshot the reset-state for change detection on output interfaces
        self.last_refresh_snapshot = self._snapshot_refresh_fields()
        self.last_timing_snapshot = self._snapshot_timing_fields()

    def _update_status_reg(self):
        """Rebuild CTRL_STATUS from level state."""
        offset = self.offset_by_name['CTRL_STATUS']
        val = 0
        val |= (self.level_state['init_done'] & 1) << 0
        val |= (self.level_state['cal_done'] & 1) << 1
        val |= (self.level_state['cal_fail'] & 1) << 2
        val |= (self.level_state['bist_done'] & 1) << 3
        val |= (self.level_state['bist_fail'] & 1) << 4
        val |= (self.level_state['ref_pending'] & 0xF) << 5
        val |= (self.level_state['self_refresh'] & 1) << 9
        self.reg_values[offset] = val

    def _update_error_status_ro_fields(self):
        """Update the RO fields in ERROR_STATUS from level state."""
        offset = self.offset_by_name['ERROR_STATUS']
        val = self.reg_values[offset]
        # ecc_ce_count: bits 15:0 (RO)
        val = (val & ~0xFFFF) | (self.level_state['ecc_ce_count'] & 0xFFFF)
        # bist_fail_addr: bits 31:19 (RO)
        val = (val & ~(0x1FFF << 19)) | ((self.level_state['bist_fail_addr'] & 0x1FFF) << 19)
        self.reg_values[offset] = val

    def _read_register(self, offset: int) -> Tuple[int, int]:
        """Return (data, err). For WO fields, read as 0."""
        if offset not in self.valid_offsets:
            return (0, 1)

        reg = self.registers[offset]
        raw_val = self.reg_values[offset]

        # Mask out WO fields (they read as 0)
        read_val = raw_val
        for f in reg['fields']:
            if f['access'] == 'WO':
                read_val = read_val & ~f['mask']

        return (read_val, 0)

    def _write_register(self, offset: int, data: int) -> Tuple[int, bool, bool, bool]:
        """
        Write to register. Returns (err, timing_changed, refresh_changed, force_refresh_written).
        For RO registers, the write is silently ignored (err=0).
        For RW1C registers, writing a 1 to a bit clears it (only for RW1C fields).
        For RW registers, only RW and WO fields are written; RO fields are preserved.
        """
        if offset not in self.valid_offsets:
            return (1, False, False, False)

        reg = self.registers[offset]
        reg_access = reg['access']

        # Check if entire register is RO -> silently ignore
        if reg_access == 'RO':
            return (0, False, False, False)

        old_val = self.reg_values[offset]
        new_val = old_val

        force_refresh_written = False

        for f in reg['fields']:
            field_data_bits = (data >> f['lsb']) & ((1 << f['width']) - 1)

            if f['access'] == 'RW':
                new_val = (new_val & ~f['mask']) | ((field_data_bits << f['lsb']) & f['mask'])
            elif f['access'] == 'WO':
                # WO fields: the written value takes effect but reads as 0.
                # Store the written value; it will be masked on read.
                new_val = (new_val & ~f['mask']) | ((field_data_bits << f['lsb']) & f['mask'])
                if f['name'] == 'force_refresh' and field_data_bits == 1:
                    force_refresh_written = True
            elif f['access'] == 'RW1C':
                # Writing 1 clears the bit
                clear_mask = (field_data_bits << f['lsb']) & f['mask']
                new_val = new_val & ~clear_mask
            elif f['access'] == 'RO':
                # Do not modify RO fields
                pass

        self.reg_values[offset] = new_val

        # Check if timing or refresh configs changed
        timing_changed = False
        refresh_changed = False

        timing_offsets = {
            self.offset_by_name.get('TIMING_0'),
            self.offset_by_name.get('TIMING_1'),
            self.offset_by_name.get('TIMING_2'),
            self.offset_by_name.get('TIMING_3'),
        }

        refresh_offsets = {
            self.offset_by_name.get('REFRESH_CONFIG'),
            self.offset_by_name.get('TIMING_3'),  # tREFI is here
            self.offset_by_name.get('CTRL_CONFIG'),  # force_refresh is here
        }

        if offset in timing_offsets:
            new_timing = self._snapshot_timing_fields()
            if new_timing != self.last_timing_snapshot:
                timing_changed = True

        if offset in refresh_offsets:
            new_refresh = self._snapshot_refresh_fields()
            if new_refresh != self.last_refresh_snapshot:
                refresh_changed = True

        return (0, timing_changed, refresh_changed, force_refresh_written)

    def process(self, txn: Txn) -> List[Txn]:
        iface = txn.iface
        kind = txn.kind
        fields = txn.fields
        outputs = []

        if iface == 'csr_sts_level':
            # Update level state from hardware
            if kind == 'state':
                for key in fields:
                    if key in self.level_state:
                        self.level_state[key] = fields[key]
                self._update_status_reg()
                self._update_error_status_ro_fields()
            return []

        elif iface == 'csr_sts':
            # Hardware status events - set RW1C flags
            if kind == 'event':
                error_offset = self.offset_by_name['ERROR_STATUS']
                val = self.reg_values[error_offset]
                if fields.get('ecc_ue', 0):
                    val |= (1 << 16)
                if fields.get('ref_starve', 0):
                    val |= (1 << 17)
                if fields.get('init_fail', 0):
                    val |= (1 << 18)
                self.reg_values[error_offset] = val
            return []

        elif iface == 'csr':
            if kind == 'write':
                addr = fields['addr']
                data = fields['data']

                err, timing_changed, refresh_changed, force_refresh_written = self._write_register(addr, data)

                # Emit write_ack
                outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                    'addr': addr,
                    'err': err,
                }))

                if err == 0:
                    # Handle timing changes
                    if timing_changed:
                        new_timing = self._snapshot_timing_fields()
                        outputs.append(self._make_timing_txn(new_timing))
                        self.last_timing_snapshot = new_timing

                    # Handle refresh changes
                    # If force_refresh was written as 1, we need special handling:
                    # emit update with force_refresh=1, then auto-clear and emit with force_refresh=0
                    if force_refresh_written:
                        # The refresh snapshot already has force_refresh=1 in it (from the write)
                        new_refresh = self._snapshot_refresh_fields()
                        if new_refresh != self.last_refresh_snapshot or True:
                            outputs.append(self._make_refresh_txn(new_refresh))
                            self.last_refresh_snapshot = new_refresh

                        # Auto-clear force_refresh (WO pulse field)
                        ctrl_config_offset = self.offset_by_name['CTRL_CONFIG']
                        self._set_field_value(ctrl_config_offset, 'force_refresh', 0)

                        cleared_refresh = self._snapshot_refresh_fields()
                        outputs.append(self._make_refresh_txn(cleared_refresh))
                        self.last_refresh_snapshot = cleared_refresh
                    elif refresh_changed:
                        new_refresh = self._snapshot_refresh_fields()
                        outputs.append(self._make_refresh_txn(new_refresh))
                        self.last_refresh_snapshot = new_refresh

                    # Auto-clear other WO fields (bist_start, force_self_ref) that are not pulse-output fields
                    # The spec only describes force_refresh as a pulse on cfg_refresh output.
                    # bist_start and force_self_ref are also WO. Clear them after write.
                    ctrl_config_offset = self.offset_by_name['CTRL_CONFIG']
                    for wo_field in ['bist_start', 'force_self_ref']:
                        self._set_field_value(ctrl_config_offset, wo_field, 0)

                return outputs

            elif kind == 'read':
                addr = fields['addr']

                # Update RO status fields before read
                self._update_status_reg()
                self._update_error_status_ro_fields()

                data, err = self._read_register(addr)

                outputs.append(Txn(iface='csr_rsp', kind='read_data', fields={
                    'addr': addr,
                    'data': data,
                    'err': err,
                }))
                return outputs

        return []

    def drain(self) -> List[Txn]:
        return []
