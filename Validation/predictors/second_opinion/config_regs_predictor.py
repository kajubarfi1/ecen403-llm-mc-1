from txn_contract import TransactionPredictor, Txn
from typing import List, Dict, Any, Optional, Tuple
import math


class Predictor(TransactionPredictor):
    """
    Transaction predictor for the config_regs scope of a DDR3 memory controller.
    
    Derives all behaviour from the specification's csr_register_map, interface notes,
    and the CSR access rules described therein.
    """

    INPUT_IFACES: tuple = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES: tuple = ('cfg_refresh', 'cfg_timing', 'csr_rsp')

    def __init__(self, spec: dict):
        self._spec = spec
        self._build_register_tables()
        self.reset()

    def _parse_bit_spec(self, bit_str: str) -> Tuple[int, int]:
        """Parse a bit field spec like '31:8' or '0' into (high_bit, low_bit)."""
        if ':' in bit_str:
            parts = bit_str.split(':')
            high = int(parts[0])
            low = int(parts[1])
            return (high, low)
        else:
            bit = int(bit_str)
            return (bit, bit)

    def _parse_reset_value(self, val) -> int:
        """Parse a reset value which may be a hex string or an integer."""
        if isinstance(val, str):
            return int(val, 0)
        return int(val)

    def _build_register_tables(self):
        """Build lookup tables from the spec's csr_register_map.
        
        Tables built:
          - _reg_by_offset: offset (int) -> register dict from spec
          - _field_table: offset (int) -> list of field info dicts
          - _valid_offsets: set of valid register offsets
          - _reg_names: offset -> register name
          - _reg_access: offset -> register-level access string
        """
        reg_map = self._spec['csr_register_map']
        self._addr_width = reg_map['address_width_bits']
        self._data_width = reg_map['data_width_bits']

        self._reg_by_offset: Dict[int, dict] = {}
        self._field_table: Dict[int, list] = {}
        self._valid_offsets: set = set()
        self._reg_names: Dict[int, str] = {}
        self._reg_access: Dict[int, str] = {}

        for reg in reg_map['registers']:
            offset = int(reg['offset'], 0)
            self._reg_by_offset[offset] = reg
            self._valid_offsets.add(offset)
            self._reg_names[offset] = reg['name']
            self._reg_access[offset] = reg['access']

            fields = []
            for field in reg['fields']:
                high, low = self._parse_bit_spec(field['bits'])
                width = high - low + 1
                mask = ((1 << width) - 1) << low
                fields.append({
                    'name': field['name'],
                    'high': high,
                    'low': low,
                    'width': width,
                    'mask': mask,
                    'access': field['access'],
                    'reset_value': int(field.get('reset_value', 0)),
                })
            self._field_table[offset] = fields

        # Build mapping from register name to offset for quick lookup
        self._offset_by_name: Dict[str, int] = {
            name: offset for offset, name in self._reg_names.items()
        }

        # Identify which cfg_timing fields come from which registers/fields
        # This table maps cfg_timing output field names to (register_offset, field_name_in_register)
        # Based on spec: TIMING_0 has tRCD, tRP, tRAS, tRC; TIMING_1 has tRRD, tWTR, tFAW, tRFC(actually named tRFC_nCK)
        # TIMING_2 has tWR, tRTP; TIMING_3 has tCCD
        # The cfg_timing output fields are: trcd, trp, tras, trc, trrd, tfaw, twtr, twr, trtp, tccd, trfc
        self._timing_field_sources = self._build_timing_field_sources()
        
        # Identify which cfg_refresh fields come from which registers/fields
        # Based on spec: TIMING_3 has tREFI_nCK; REFRESH_CONFIG has max_postpone, urgent_threshold, ref_priority
        # CTRL_CONFIG has force_refresh (WO)
        self._refresh_field_sources = self._build_refresh_field_sources()

    def _build_timing_field_sources(self) -> Dict[str, Tuple[int, str]]:
        """Map cfg_timing output field names to (register_offset, register_field_name).
        
        From the cfg_timing schema ports and the CSR register fields:
          trcd  -> TIMING_0.tRCD_nCK
          trp   -> TIMING_0.tRP_nCK
          tras  -> TIMING_0.tRAS_nCK
          trc   -> TIMING_0.tRC_nCK
          trrd  -> TIMING_1.tRRD_nCK
          twtr  -> TIMING_1.tWTR_nCK
          tfaw  -> TIMING_1.tFAW_nCK
          trfc  -> TIMING_1.tRFC_nCK
          twr   -> TIMING_2.tWR_nCK
          trtp  -> TIMING_2.tRTP_nCK
          tccd  -> TIMING_3.tCCD_nCK
        """
        t0 = self._offset_by_name['TIMING_0']
        t1 = self._offset_by_name['TIMING_1']
        t2 = self._offset_by_name['TIMING_2']
        t3 = self._offset_by_name['TIMING_3']
        return {
            'trcd': (t0, 'tRCD_nCK'),
            'trp':  (t0, 'tRP_nCK'),
            'tras': (t0, 'tRAS_nCK'),
            'trc':  (t0, 'tRC_nCK'),
            'trrd': (t1, 'tRRD_nCK'),
            'twtr': (t1, 'tWTR_nCK'),
            'tfaw': (t1, 'tFAW_nCK'),
            'trfc': (t1, 'tRFC_nCK'),
            'twr':  (t2, 'tWR_nCK'),
            'trtp': (t2, 'tRTP_nCK'),
            'tccd': (t3, 'tCCD_nCK'),
        }

    def _build_refresh_field_sources(self) -> Dict[str, Tuple[int, str]]:
        """Map cfg_refresh output field names to (register_offset, register_field_name).
        
        From the cfg_refresh schema ports and CSR register fields:
          trefi            -> TIMING_3.tREFI_nCK
          max_postpone     -> REFRESH_CONFIG.max_postpone
          urgent_threshold -> REFRESH_CONFIG.urgent_threshold
          priority         -> REFRESH_CONFIG.ref_priority
          force_refresh    -> CTRL_CONFIG.force_refresh
        """
        t3 = self._offset_by_name['TIMING_3']
        rc = self._offset_by_name['REFRESH_CONFIG']
        cc = self._offset_by_name['CTRL_CONFIG']
        return {
            'trefi':            (t3, 'tREFI_nCK'),
            'max_postpone':     (rc, 'max_postpone'),
            'urgent_threshold': (rc, 'urgent_threshold'),
            'priority':         (rc, 'ref_priority'),
            'force_refresh':    (cc, 'force_refresh'),
        }

    def _compute_register_reset_value(self, offset: int) -> int:
        """Compute the reset value of a register from its field reset values.
        
        We use the register-level reset_value from the spec directly.
        """
        return self._parse_reset_value(self._reg_by_offset[offset]['reset_value'])

    def reset(self) -> None:
        """Return all modeled state to power-on values.
        
        Per spec: each register has a defined reset_value. We store the
        full 32-bit register value for each offset.
        """
        # Register file: offset -> 32-bit value
        self._regs: Dict[int, int] = {}
        for offset in self._valid_offsets:
            self._regs[offset] = self._compute_register_reset_value(offset)

        # Hardware status levels (from csr_sts_level), tracked as latest seen values
        # These are reflected in CTRL_STATUS and ERROR_STATUS read-only fields
        self._hw_level_state: Dict[str, int] = {
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

        # Snapshot the current cfg_timing and cfg_refresh values for change detection
        # Per interface notes: "Nothing is emitted for reset itself"
        self._last_cfg_timing = self._collect_cfg_timing()
        self._last_cfg_refresh = self._collect_cfg_refresh()

    def _read_field(self, offset: int, field_name: str) -> int:
        """Extract a named field's value from a register."""
        for f in self._field_table[offset]:
            if f['name'] == field_name:
                return (self._regs[offset] >> f['low']) & ((1 << f['width']) - 1)
        raise KeyError(f"No field {field_name} at offset {offset:#x}")

    def _write_field(self, offset: int, field_name: str, value: int):
        """Write a value into a named field of a register."""
        for f in self._field_table[offset]:
            if f['name'] == field_name:
                mask = f['mask']
                self._regs[offset] = (self._regs[offset] & ~mask) | ((value << f['low']) & mask)
                return
        raise KeyError(f"No field {field_name} at offset {offset:#x}")

    def _collect_cfg_timing(self) -> Dict[str, int]:
        """Collect current cfg_timing field values from registers."""
        result = {}
        for out_field, (reg_offset, reg_field) in self._timing_field_sources.items():
            result[out_field] = self._read_field(reg_offset, reg_field)
        return result

    def _collect_cfg_refresh(self) -> Dict[str, int]:
        """Collect current cfg_refresh field values from registers.
        
        Note: force_refresh is a WO pulse field. Per the interface note:
        'a write of 1 produces an update with the field at 1 followed by
        an update with it back at 0.' The stored register value for WO fields
        is always 0 (they auto-clear). The pulse handling is done in the
        write processing path.
        """
        result = {}
        for out_field, (reg_offset, reg_field) in self._refresh_field_sources.items():
            result[out_field] = self._read_field(reg_offset, reg_field)
        return result

    def _make_cfg_timing_txn(self, values: Dict[str, int]) -> Txn:
        """Create a cfg_timing update transaction."""
        return Txn(iface='cfg_timing', kind='update', fields=dict(values))

    def _make_cfg_refresh_txn(self, values: Dict[str, int]) -> Txn:
        """Create a cfg_refresh update transaction."""
        return Txn(iface='cfg_refresh', kind='update', fields=dict(values))

    def _build_read_value(self, offset: int) -> int:
        """Build the 32-bit read value for a register.
        
        Per spec and interface notes:
        - RO fields: read the current value (hardware levels for CTRL_STATUS and ERROR_STATUS)
        - RW fields: read the stored register value
        - WO fields: read as 0 (per interface note for CSR_001: 
          'the WO field reads as zero')
        - RW1C fields: read the stored value
        
        CTRL_STATUS (offset from spec) fields are mirrored from hardware levels.
        ERROR_STATUS fields: ecc_ce_count and bist_fail_addr are RO from hw levels,
        RW1C flags are stored in register.
        """
        ctrl_status_offset = self._offset_by_name['CTRL_STATUS']
        error_status_offset = self._offset_by_name['ERROR_STATUS']

        if offset == ctrl_status_offset:
            # All fields are RO, sourced from hardware level state
            # Spec CTRL_STATUS fields:
            #   init_done[0], cal_done[1], cal_fail[2], bist_done[3], bist_fail[4],
            #   ref_pending_cnt[8:5], self_refresh_active[9], reserved[31:10]
            val = 0
            val |= (self._hw_level_state['init_done'] & 1) << 0
            val |= (self._hw_level_state['cal_done'] & 1) << 1
            val |= (self._hw_level_state['cal_fail'] & 1) << 2
            val |= (self._hw_level_state['bist_done'] & 1) << 3
            val |= (self._hw_level_state['bist_fail'] & 1) << 4
            val |= (self._hw_level_state['ref_pending'] & 0xF) << 5
            val |= (self._hw_level_state['self_refresh'] & 1) << 9
            # reserved[31:10] = 0 per spec reset_value
            return val

        elif offset == error_status_offset:
            # ecc_ce_count[15:0] RO from hw level
            # ecc_ue_flag[16] RW1C - stored in register
            # ref_starve_flag[17] RW1C - stored in register
            # init_fail_flag[18] RW1C - stored in register  
            # bist_fail_addr[31:19] RO from hw level
            val = 0
            val |= (self._hw_level_state['ecc_ce_count'] & 0xFFFF) << 0
            # RW1C flags from stored register value
            val |= (self._regs[offset] >> 16 & 1) << 16  # ecc_ue_flag
            val |= (self._regs[offset] >> 17 & 1) << 17  # ref_starve_flag
            val |= (self._regs[offset] >> 18 & 1) << 18  # init_fail_flag
            val |= (self._hw_level_state['bist_fail_addr'] & 0x1FFF) << 19
            return val

        else:
            # For other registers, compose from fields
            # WO fields read as 0; RO and RW fields read their stored value
            result = 0
            for f in self._field_table[offset]:
                if f['access'] == 'WO':
                    # Per interface note: WO field reads as zero
                    continue  # contributes 0
                else:
                    field_val = (self._regs[offset] >> f['low']) & ((1 << f['width']) - 1)
                    result |= (field_val << f['low'])
            return result

    def _apply_write(self, offset: int, data: int) -> Tuple[bool, bool]:
        """Apply a write to a register and return (wrote_something, force_refresh_written).
        
        Per spec and interface notes:
        - RW fields: written normally
        - RO fields: write is silently ignored (field keeps its value)
          Per interface note: 'a write to a read-only register ... is acknowledged
          with err=0: the write is ignored (RO fields keep their value)'
        - WO fields: write takes effect but field auto-clears to 0
          (the 'write 1 to force immediate refresh' semantics)
        - RW1C fields: writing 1 clears the bit, writing 0 has no effect
        - Reserved RO fields: not writable
        
        Returns (any_rw_field_changed, force_refresh_was_1).
        """
        force_refresh_written = False
        old_reg = self._regs[offset]

        for f in self._field_table[offset]:
            # Extract the written value for this field
            written_val = (data >> f['low']) & ((1 << f['width']) - 1)

            if f['access'] == 'RW':
                # Normal read-write: update the field
                mask = f['mask']
                self._regs[offset] = (self._regs[offset] & ~mask) | ((written_val << f['low']) & mask)

            elif f['access'] == 'WO':
                # Write-only: the action happens but the stored value stays 0
                # Per spec: bist_start, force_refresh, force_self_ref are WO
                # They are pulse fields - we don't store them (reset_value=0, stays 0)
                # But we need to know if force_refresh was written as 1
                if f['name'] == 'force_refresh' and written_val == 1:
                    force_refresh_written = True
                # WO fields remain at 0 in the register (their reset value)
                # No change to self._regs needed since they're already 0

            elif f['access'] == 'RW1C':
                # Write-1-to-clear: for each bit that is 1 in written_val, clear that bit
                clear_mask = (written_val << f['low']) & f['mask']
                self._regs[offset] = self._regs[offset] & ~clear_mask

            elif f['access'] == 'RO':
                # Read-only: silently ignored
                pass

        changed = (self._regs[offset] != old_reg)
        return changed, force_refresh_written

    def process(self, txn: Txn) -> List[Txn]:
        iface = txn.iface
        if iface == 'csr':
            return self._process_csr(txn)
        elif iface == 'csr_sts':
            return self._process_csr_sts(txn)
        elif iface == 'csr_sts_level':
            return self._process_csr_sts_level(txn)
        else:
            return []

    def _process_csr(self, txn: Txn) -> List[Txn]:
        """Process a CSR bus transaction (read or write).
        
        Per interface note on csr_rsp:
        'err asserts only for an UNMAPPED address (no register at the offset).
        An access violation -- a write to a read-only register or a read of a
        write-only field -- is acknowledged with err=0'
        """
        outputs = []
        kind = txn.kind
        addr = txn.fields['addr']

        # Check if address is mapped
        # Per spec: address_width_bits=8, addresses are byte offsets
        is_mapped = addr in self._valid_offsets

        if kind == 'read':
            if not is_mapped:
                # Unmapped address: err=1, data=0
                # Spec doesn't define read data for unmapped; Wishbone B4 (§3.2.1)
                # doesn't mandate a value. Using 0.
                outputs.append(Txn(iface='csr_rsp', kind='read_data', fields={
                    'addr': addr,
                    'data': 0,
                    'err': 1,
                }))
            else:
                # Mapped read: err=0, data from register
                read_val = self._build_read_value(addr)
                outputs.append(Txn(iface='csr_rsp', kind='read_data', fields={
                    'addr': addr,
                    'data': read_val,
                    'err': 0,
                }))

        elif kind == 'write':
            data = txn.fields['data']

            if not is_mapped:
                # Unmapped address: err=1
                outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                    'addr': addr,
                    'err': 1,
                }))
            else:
                # Mapped write: err=0, apply write
                # Per interface note: writing to RO register is not an error (err=0),
                # the write is silently ignored.
                
                # Save pre-write config state for change detection
                old_timing = self._last_cfg_timing.copy()
                old_refresh = self._last_cfg_refresh.copy()

                changed, force_refresh_written = self._apply_write(addr, data)

                # Acknowledge the write (err=0 for mapped addresses regardless of access type)
                outputs.append(Txn(iface='csr_rsp', kind='write_ack', fields={
                    'addr': addr,
                    'err': 0,
                }))

                # Check if cfg_timing fields changed
                new_timing = self._collect_cfg_timing()
                if new_timing != old_timing:
                    # Emit cfg_timing update with ALL current timing field values
                    # Per interface note: "emit exactly one update whenever any field changes,
                    # carrying EVERY field's current value"
                    outputs.append(self._make_cfg_timing_txn(new_timing))
                    self._last_cfg_timing = new_timing

                # Check if cfg_refresh fields changed, or if force_refresh pulse occurred
                # Per interface note for force_refresh:
                # 'a write of 1 produces an update with the field at 1 followed by
                # an update with it back at 0'
                if force_refresh_written:
                    # First: emit update with force_refresh=1 and all other current values
                    new_refresh = self._collect_cfg_refresh()
                    new_refresh_with_pulse = dict(new_refresh)
                    new_refresh_with_pulse['force_refresh'] = 1
                    outputs.append(self._make_cfg_refresh_txn(new_refresh_with_pulse))
                    # Second: emit update with force_refresh back to 0
                    # The other fields may also have changed in this write
                    new_refresh_after = dict(new_refresh)
                    new_refresh_after['force_refresh'] = 0
                    outputs.append(self._make_cfg_refresh_txn(new_refresh_after))
                    self._last_cfg_refresh = new_refresh_after
                else:
                    new_refresh = self._collect_cfg_refresh()
                    if new_refresh != old_refresh:
                        outputs.append(self._make_cfg_refresh_txn(new_refresh))
                        self._last_cfg_refresh = new_refresh

        return outputs

    def _process_csr_sts(self, txn: Txn) -> List[Txn]:
        """Process hardware status events (RW1C flag setting).
        
        Per csr_sts schema description: these events SET the RW1C flag fields.
        The bus can only CLEAR them (via write-1-to-clear).
        
        Events: ecc_ue, ref_starve, init_fail -> set bits 16, 17, 18 of ERROR_STATUS
        """
        error_offset = self._offset_by_name['ERROR_STATUS']

        # Map event fields to ERROR_STATUS register field bit positions
        # Per spec: ecc_ue_flag is bit 16, ref_starve_flag is bit 17, init_fail_flag is bit 18
        event_to_bit = {
            'ecc_ue': 16,       # ecc_ue_flag
            'ref_starve': 17,   # ref_starve_flag
            'init_fail': 18,    # init_fail_flag
        }

        if txn.kind == 'event':
            for event_name, bit_pos in event_to_bit.items():
                if event_name in txn.fields and txn.fields[event_name]:
                    # Set the flag bit (OR it in)
                    self._regs[error_offset] |= (1 << bit_pos)

        return []

    def _process_csr_sts_level(self, txn: Txn) -> List[Txn]:
        """Process hardware status level updates.
        
        Per csr_sts_level schema description: these are continuously-valid state
        that read-only status fields mirror.
        
        Level fields and their destinations:
          init_done     -> CTRL_STATUS.init_done (bit 0)
          cal_done      -> CTRL_STATUS.cal_done (bit 1)
          cal_fail      -> CTRL_STATUS.cal_fail (bit 2)
          bist_done     -> CTRL_STATUS.bist_done (bit 3)
          bist_fail     -> CTRL_STATUS.bist_fail (bit 4)
          ref_pending   -> CTRL_STATUS.ref_pending_cnt (bits 8:5)
          self_refresh  -> CTRL_STATUS.self_refresh_active (bit 9)
          ecc_ce_count  -> ERROR_STATUS.ecc_ce_count (bits 15:0)
          bist_fail_addr -> ERROR_STATUS.bist_fail_addr (bits 31:19)
        """
        if txn.kind == 'state':
            for field_name in self._hw_level_state:
                if field_name in txn.fields:
                    self._hw_level_state[field_name] = txn.fields[field_name]

        return []

    def drain(self) -> List[Txn]:
        """No pending outputs at end of trace for config_regs.
        
        The config_regs block responds synchronously to each CSR transaction;
        there are no buffered or deferred outputs.
        """
        return []
