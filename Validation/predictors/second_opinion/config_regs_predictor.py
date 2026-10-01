from txn_contract import TransactionPredictor, Txn
from typing import List, Dict, Any, Optional, Tuple


class ConfigRegsPredictor(TransactionPredictor):
    """
    Transaction predictor for the config_regs block.
    
    Models CSR read/write behavior, hardware status inputs, and
    configuration output broadcasts per the specification.
    """
    
    INPUT_IFACES: tuple = ('csr', 'csr_sts', 'csr_sts_level')
    OUTPUT_IFACES: tuple = ('cfg_refresh', 'cfg_timing', 'csr_rsp')
    
    def __init__(self, spec: dict):
        self.spec = spec
        self._build_register_tables()
        self.reset()
    
    def _build_register_tables(self) -> None:
        """Build lookup tables from spec for register decoding."""
        csr_map = self.spec['csr_register_map']
        self.addr_width_bits = csr_map['address_width_bits']
        self.data_width_bits = csr_map['data_width_bits']
        
        # Table: offset -> register definition
        self.reg_by_offset: Dict[int, dict] = {}
        # Table: register name -> offset
        self.offset_by_name: Dict[str, int] = {}
        
        for reg in csr_map['registers']:
            offset = int(reg['offset'], 16)
            self.reg_by_offset[offset] = reg
            self.offset_by_name[reg['name']] = offset
        
        # Build field tables for each register
        # Table: (offset, field_name) -> (lsb, width, access)
        self.field_info: Dict[Tuple[int, str], Tuple[int, int, str]] = {}
        
        for reg in csr_map['registers']:
            offset = int(reg['offset'], 16)
            for field in reg['fields']:
                lsb, width = self._parse_bits(field['bits'])
                self.field_info[(offset, field['name'])] = (lsb, width, field['access'])
        
        # Table: offset -> list of (field_name, lsb, width, access, reset_value)
        self.fields_by_offset: Dict[int, List[Tuple[str, int, int, str, int]]] = {}
        for reg in csr_map['registers']:
            offset = int(reg['offset'], 16)
            fields = []
            for field in reg['fields']:
                lsb, width = self._parse_bits(field['bits'])
                fields.append((field['name'], lsb, width, field['access'], field['reset_value']))
            self.fields_by_offset[offset] = fields
        
        # Table: which registers contribute to cfg_timing
        # Maps register offset to list of (field_name, output_field_name)
        self.timing_fields: Dict[int, List[Tuple[str, str]]] = {
            self.offset_by_name['TIMING_0']: [
                ('tRCD_nCK', 'trcd'),
                ('tRP_nCK', 'trp'),
                ('tRAS_nCK', 'tras'),
                ('tRC_nCK', 'trc'),
            ],
            self.offset_by_name['TIMING_1']: [
                ('tRRD_nCK', 'trrd'),
                ('tFAW_nCK', 'tfaw'),
                ('tWTR_nCK', 'twtr'),
                ('tRFC_nCK', 'trfc'),
            ],
            self.offset_by_name['TIMING_2']: [
                ('tWR_nCK', 'twr'),
                ('tRTP_nCK', 'trtp'),
            ],
            self.offset_by_name['TIMING_3']: [
                ('tCCD_nCK', 'tccd'),
            ],
        }
        
        # Table: which registers contribute to cfg_refresh
        # Maps register offset to list of (field_name, output_field_name)
        self.refresh_fields: Dict[int, List[Tuple[str, str]]] = {
            self.offset_by_name['TIMING_3']: [
                ('tREFI_nCK', 'trefi'),
            ],
            self.offset_by_name['REFRESH_CONFIG']: [
                ('max_postpone', 'max_postpone'),
                ('urgent_threshold', 'urgent_threshold'),
                ('ref_priority', 'priority'),
            ],
            self.offset_by_name['CTRL_CONFIG']: [
                ('force_refresh', 'force_refresh'),
            ],
        }
        
        # Table: csr_sts event field -> (register offset, field_name)
        self.sts_event_map: Dict[str, Tuple[int, str]] = {
            'ecc_ue': (self.offset_by_name['ERROR_STATUS'], 'ecc_ue_flag'),
            'ref_starve': (self.offset_by_name['ERROR_STATUS'], 'ref_starve_flag'),
            'init_fail': (self.offset_by_name['ERROR_STATUS'], 'init_fail_flag'),
        }
        
        # Table: csr_sts_level field -> (register offset, field_name)
        self.sts_level_map: Dict[str, Tuple[int, str]] = {
            'init_done': (self.offset_by_name['CTRL_STATUS'], 'init_done'),
            'cal_done': (self.offset_by_name['CTRL_STATUS'], 'cal_done'),
            'cal_fail': (self.offset_by_name['CTRL_STATUS'], 'cal_fail'),
            'bist_done': (self.offset_by_name['CTRL_STATUS'], 'bist_done'),
            'bist_fail': (self.offset_by_name['CTRL_STATUS'], 'bist_fail'),
            'ref_pending': (self.offset_by_name['CTRL_STATUS'], 'ref_pending_cnt'),
            'self_refresh': (self.offset_by_name['CTRL_STATUS'], 'self_refresh_active'),
            'ecc_ce_count': (self.offset_by_name['ERROR_STATUS'], 'ecc_ce_count'),
            'bist_fail_addr': (self.offset_by_name['ERROR_STATUS'], 'bist_fail_addr'),
        }
        
        # Valid address set for error detection
        self.valid_offsets = set(self.reg_by_offset.keys())
        
        # Max valid address per Wishbone B4: addresses outside valid range are bus errors
        # Spec: address_width_bits = 8, so addresses 0x00-0xFF are addressable
        # but only defined offsets are valid
        self.addr_mask = (1 << self.addr_width_bits) - 1
    
    def _parse_bits(self, bits_str: str) -> Tuple[int, int]:
        """Parse bit field specification like '7:0' or '0' into (lsb, width)."""
        if ':' in bits_str:
            msb, lsb = map(int, bits_str.split(':'))
            return lsb, msb - lsb + 1
        else:
            bit = int(bits_str)
            return bit, 1
    
    def reset(self) -> None:
        """Return all modeled state to its power-on values."""
        # Register storage: offset -> 32-bit value
        self.registers: Dict[int, int] = {}
        
        for reg in self.spec['csr_register_map']['registers']:
            offset = int(reg['offset'], 16)
            reset_val = int(reg['reset_value'], 16)
            self.registers[offset] = reset_val
        
        # Track last emitted cfg values for change detection
        # Per schema: "Level stream, change-qualified" - emit only on change
        self._last_cfg_timing = self._build_cfg_timing()
        self._last_cfg_refresh = self._build_cfg_refresh()
        
        # Track current hardware status levels
        self._hw_levels: Dict[str, int] = {
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
    
    def _get_field(self, offset: int, field_name: str) -> int:
        """Extract a field value from a register."""
        lsb, width, _ = self.field_info[(offset, field_name)]
        mask = (1 << width) - 1
        return (self.registers[offset] >> lsb) & mask
    
    def _set_field(self, offset: int, field_name: str, value: int) -> None:
        """Set a field value in a register."""
        lsb, width, _ = self.field_info[(offset, field_name)]
        mask = (1 << width) - 1
        value = value & mask
        clear_mask = ~(mask << lsb) & 0xFFFFFFFF
        self.registers[offset] = (self.registers[offset] & clear_mask) | (value << lsb)
    
    def _build_cfg_timing(self) -> Dict[str, int]:
        """Build cfg_timing output fields from current register state."""
        result = {}
        for offset, field_list in self.timing_fields.items():
            for reg_field, out_field in field_list:
                result[out_field] = self._get_field(offset, reg_field)
        return result
    
    def _build_cfg_refresh(self) -> Dict[str, int]:
        """Build cfg_refresh output fields from current register state."""
        result = {}
        for offset, field_list in self.refresh_fields.items():
            for reg_field, out_field in field_list:
                result[out_field] = self._get_field(offset, reg_field)
        return result
    
    def _read_register(self, offset: int) -> int:
        """
        Read a register, applying access rules.
        
        Per spec: WO fields read as 0 (CSR_001 in failure_taxonomy implies
        read from WO is defined behavior returning 0, not an error).
        RO fields read their current value.
        RW fields read their current value.
        RW1C fields read their current value.
        """
        value = 0
        for field_name, lsb, width, access, _ in self.fields_by_offset[offset]:
            mask = (1 << width) - 1
            if access == 'WO':
                # WO fields read as 0 per common CSR convention
                # Spec failure_taxonomy CSR_001 mentions "read from write-only register"
                # as a violation, but the register access is RW/RO/WO per field.
                # Per Wishbone B4, the data returned is implementation-defined for
                # inaccessible regions; reading 0 is the conservative choice.
                field_val = 0
            else:
                field_val = (self.registers[offset] >> lsb) & mask
            value |= (field_val << lsb)
        return value
    
    def _write_register(self, offset: int, data: int) -> bool:
        """
        Write to a register, applying access rules.
        
        Returns True if this was a valid write (register exists).
        
        Per spec:
        - RO fields: writes are ignored
        - RW fields: writes update the field
        - WO fields: writes update the field (value may be transient/self-clearing)
        - RW1C fields: writing 1 clears the bit
        
        Per spec, WO fields like bist_start, force_refresh, force_self_ref are
        write-only action triggers. The spec says reset_value=0 and they are WO.
        The spec does not say they auto-clear, but since they are WO and read as 0,
        a reasonable interpretation is they are strobes. However, for cfg_refresh
        output, force_refresh is emitted, so we need to track its written value.
        Since the spec says WO fields "reset_value": 0, and the output is
        change-qualified, writing 1 should emit a change, then presumably it
        auto-clears. But the spec doesn't explicitly state auto-clear behavior.
        
        Literal reading: WO fields accept writes, and since they read as 0,
        their stored value is not directly observable. For force_refresh in
        cfg_refresh output, we emit what was written. The spec is silent on
        whether WO bits persist or auto-clear. Given force_refresh is described
        as "Write 1 to force immediate refresh", it is a command strobe. We will
        treat WO command bits as edge-sensitive: they are set to the written value
        for the purpose of output emission, then implicitly cleared afterward.
        """
        reg = self.reg_by_offset[offset]
        
        for field_name, lsb, width, access, _ in self.fields_by_offset[offset]:
            mask = (1 << width) - 1
            written_val = (data >> lsb) & mask
            
            if access == 'RO':
                # Per spec: writes to RO fields are ignored
                pass
            elif access == 'RW':
                # Normal read-write: update field
                self._set_field(offset, field_name, written_val)
            elif access == 'WO':
                # Write-only: accept write
                # These are action triggers; we set them for output emission
                self._set_field(offset, field_name, written_val)
            elif access == 'RW1C':
                # Read-write-1-to-clear: writing 1 clears the bit
                current = self._get_field(offset, field_name)
                new_val = current & ~written_val
                self._set_field(offset, field_name, new_val)
        
        return True
    
    def _emit_cfg_timing_if_changed(self) -> List[Txn]:
        """Emit cfg_timing update if any timing field changed."""
        current = self._build_cfg_timing()
        if current != self._last_cfg_timing:
            self._last_cfg_timing = current
            return [Txn(iface='cfg_timing', kind='update', fields=current)]
        return []
    
    def _emit_cfg_refresh_if_changed(self) -> List[Txn]:
        """Emit cfg_refresh update if any refresh field changed."""
        current = self._build_cfg_refresh()
        if current != self._last_cfg_refresh:
            self._last_cfg_refresh = current
            return [Txn(iface='cfg_refresh', kind='update', fields=current)]
        return []
    
    def _clear_wo_fields_after_write(self, offset: int) -> None:
        """
        Clear WO fields after they have been processed.
        
        Per spec, WO fields like force_refresh are command strobes.
        After the command is acted upon (output emitted), the field
        returns to 0. This is the behavior required for level-based
        outputs to correctly represent transient commands.
        """
        for field_name, lsb, width, access, reset_val in self.fields_by_offset[offset]:
            if access == 'WO':
                self._set_field(offset, field_name, reset_val)
    
    def _process_csr_write(self, addr: int, data: int) -> List[Txn]:
        """Process a CSR write transaction."""
        outputs = []
        
        # Check for valid address
        # Per Wishbone B4 section 3.1.3: ERR_O indicates bus errors
        if addr not in self.valid_offsets:
            # Invalid address - return error response
            outputs.append(Txn(
                iface='csr_rsp',
                kind='write_ack',
                fields={'addr': addr, 'err': 1}
            ))
            return outputs
        
        # Perform the write
        self._write_register(addr, data)
        
        # Check for configuration output changes
        # Per schema: cfg_refresh and cfg_timing are change-qualified level streams
        
        # Determine which output categories this register affects
        timing_changed = addr in self.timing_fields
        refresh_changed = addr in self.refresh_fields
        
        if timing_changed:
            outputs.extend(self._emit_cfg_timing_if_changed())
        
        if refresh_changed:
            outputs.extend(self._emit_cfg_refresh_if_changed())
        
        # Clear WO fields after outputs are emitted
        # This ensures force_refresh=1 is captured in cfg_refresh, then cleared
        self._clear_wo_fields_after_write(addr)
        
        # After clearing WO fields, check for refresh change again
        # (force_refresh going 0->1->0 means we might need another update)
        if refresh_changed and addr == self.offset_by_name['CTRL_CONFIG']:
            # If force_refresh was written as 1, it's now 0, emit the clear
            outputs.extend(self._emit_cfg_refresh_if_changed())
        
        # Emit write acknowledgment
        # Per Wishbone B4: successful write gets ACK, no error
        outputs.append(Txn(
            iface='csr_rsp',
            kind='write_ack',
            fields={'addr': addr, 'err': 0}
        ))
        
        return outputs
    
    def _process_csr_read(self, addr: int) -> List[Txn]:
        """Process a CSR read transaction."""
        # Check for valid address
        if addr not in self.valid_offsets:
            # Invalid address - return error response
            # Per Wishbone B4: ERR_O with undefined data
            # Return 0 for data as a safe default
            return [Txn(
                iface='csr_rsp',
                kind='read_data',
                fields={'addr': addr, 'data': 0, 'err': 1}
            )]
        
        # Before reading, update RO fields from hardware levels
        # Per schema: csr_sts_level carries "continuously-valid state"
        # that "read-only status fields mirror"
        # This means reads should return the current hardware level
        for level_name, (offset, field_name) in self.sts_level_map.items():
            self._set_field(offset, field_name, self._hw_levels[level_name])
        
        # Perform the read
        data = self._read_register(addr)
        
        # Per Wishbone B4: successful read gets ACK, no error
        return [Txn(
            iface='csr_rsp',
            kind='read_data',
            fields={'addr': addr, 'data': data, 'err': 0}
        )]
    
    def _process_sts_event(self, txn: Txn) -> List[Txn]:
        """
        Process hardware status event (pulse) that sets RW1C flags.
        
        Per schema: "These are a genuine INPUT stream: they set RW1C flag
        fields that the bus can only clear"
        """
        # Per spec: events set the corresponding flag bits
        for event_name, (offset, field_name) in self.sts_event_map.items():
            if event_name in txn.fields:
                event_val = txn.fields[event_name]
                if event_val:
                    # Event occurred - set the flag (it can only be cleared by bus write)
                    self._set_field(offset, field_name, 1)
        
        # Events don't directly produce output transactions
        return []
    
    def _process_sts_level(self, txn: Txn) -> List[Txn]:
        """
        Process hardware status level update.
        
        Per schema: "continuously-valid state that read-only status fields mirror"
        """
        # Update internal tracking of hardware levels
        for level_name in self.sts_level_map:
            if level_name in txn.fields:
                self._hw_levels[level_name] = txn.fields[level_name]
        
        # Level updates don't directly produce output transactions
        # They are reflected on subsequent CSR reads
        return []
    
    def process(self, txn: Txn) -> List[Txn]:
        """Process one observed input transaction."""
        if txn.iface == 'csr':
            if txn.kind == 'write':
                return self._process_csr_write(txn.fields['addr'], txn.fields['data'])
            elif txn.kind == 'read':
                return self._process_csr_read(txn.fields['addr'])
            else:
                # Unknown kind - ignore per contract
                return []
        
        elif txn.iface == 'csr_sts':
            if txn.kind == 'event':
                return self._process_sts_event(txn)
            else:
                return []
        
        elif txn.iface == 'csr_sts_level':
            if txn.kind == 'state':
                return self._process_sts_level(txn)
            else:
                return []
        
        else:
            # Unknown interface - ignore per contract
            return []
    
    def drain(self) -> List[Txn]:
        """
        Return any pending outputs at end of trace.
        
        Per spec, the config_regs block doesn't buffer responses;
        all outputs are emitted synchronously with inputs.
        """
        return []
