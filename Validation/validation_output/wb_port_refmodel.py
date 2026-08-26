#!/usr/bin/env python3
"""
Wishbone Port Interface (wb_port) Reference Model for DDR3 Memory Controller

Derived from spec:
- interface_type: wishbone_pipelined
- data_width_bits: 32
- address_width_bits: 29
- sel_width_bits: 4 (derived)
- max_burst_length: 8
- read_buffer_depth: 16
- write_buffer_depth: 16
- aux_width: 4
"""

import json
import os
from collections import deque


class WishbonePortModel:
    """
    Reference model for the Wishbone Port Interface (wb_port).
    
    Models protocol rules for translating pipelined Wishbone bus transactions
    into internal request descriptors for the command queue.
    """
    
    # Constants from spec
    DATA_WIDTH_BITS = 32
    ADDRESS_WIDTH_BITS = 29
    SEL_WIDTH_BITS = 4
    AUX_WIDTH_BITS = 4
    MAX_BURST_LENGTH = 8
    READ_BUFFER_DEPTH = 16
    WRITE_BUFFER_DEPTH = 16
    
    # Wishbone CTI (Cycle Type Identifier) values
    CTI_CLASSIC = 0b000      # Classic cycle
    CTI_CONST_BURST = 0b001  # Constant address burst
    CTI_INCR_BURST = 0b010   # Incrementing burst
    CTI_END_BURST = 0b111    # End of burst
    
    # Wishbone BTE (Burst Type Extension) values
    BTE_LINEAR = 0b00        # Linear burst
    BTE_WRAP4 = 0b01         # 4-beat wrap burst
    BTE_WRAP8 = 0b10         # 8-beat wrap burst
    BTE_WRAP16 = 0b11        # 16-beat wrap burst
    
    # Address masks derived from spec
    ADDRESS_MASK = (1 << ADDRESS_WIDTH_BITS) - 1  # 29-bit address
    DATA_MASK = (1 << DATA_WIDTH_BITS) - 1        # 32-bit data
    SEL_MASK = (1 << SEL_WIDTH_BITS) - 1          # 4-bit select
    AUX_MASK = (1 << AUX_WIDTH_BITS) - 1          # 4-bit aux
    
    # Byte increment for burst addressing (data_width_bits / 8 = 4 bytes)
    BURST_INCREMENT = DATA_WIDTH_BITS // 8  # 4 bytes per beat
    
    def __init__(self):
        """Initialize the Wishbone port model."""
        self.reset()
    
    def reset(self):
        """Reset all internal state."""
        # Pending read queue: stores aux tags for outstanding read requests
        # Used to match responses to requests (FIFO order assumed)
        self._pending_reads = deque()
        
        # Read response buffer: stores completed read data awaiting delivery
        # Key: aux tag, Value: read data
        self._read_responses = deque()
        
        # Burst tracking state
        self._in_burst = False
        self._burst_count = 0
        self._burst_base_addr = 0
        
        # Internal aux counter for tagging requests (cycles 0-15 based on aux_width=4)
        self._aux_counter = 0
        
        # Last transaction state for debugging/verification
        self._last_req_valid = 0
        self._last_wb_ack = 0
    
    def _generate_aux_tag(self) -> int:
        """Generate a unique aux tag for request tracking."""
        tag = self._aux_counter
        self._aux_counter = (self._aux_counter + 1) & self.AUX_MASK
        return tag
    
    def _calculate_burst_address(self, base_addr: int, beat_index: int, bte: int) -> int:
        """
        Calculate the address for a burst beat.
        
        For linear burst (bte=00): address increments by 4 bytes each beat
        Wrap modes would wrap within a boundary (not fully implemented for basic model)
        """
        if bte == self.BTE_LINEAR:
            # Linear burst: simple increment
            addr = base_addr + (beat_index * self.BURST_INCREMENT)
        else:
            # For wrap bursts, implement wrap boundary logic
            # Wrap boundary depends on bte value
            wrap_size = {
                self.BTE_WRAP4: 4 * self.BURST_INCREMENT,
                self.BTE_WRAP8: 8 * self.BURST_INCREMENT,
                self.BTE_WRAP16: 16 * self.BURST_INCREMENT,
            }.get(bte, 4 * self.BURST_INCREMENT)
            
            # Calculate wrapped address
            wrap_mask = wrap_size - 1
            base_aligned = base_addr & ~wrap_mask
            offset = (base_addr & wrap_mask) + (beat_index * self.BURST_INCREMENT)
            addr = base_aligned | (offset & wrap_mask)
        
        return addr & self.ADDRESS_MASK
    
    def present_transaction(self, cyc: int, stb: int, we: int, adr: int,
                           dat: int, sel: int, cti: int, bte: int,
                           req_ready: int) -> dict:
        """
        Present one Wishbone bus cycle.
        
        Args:
            cyc: Wishbone cycle signal (1 = bus cycle active)
            stb: Wishbone strobe signal (1 = valid data transfer)
            we: Write enable (1 = write, 0 = read)
            adr: Address (29 bits)
            dat: Write data (32 bits)
            sel: Byte select (4 bits)
            cti: Cycle type identifier (3 bits)
            bte: Burst type extension (2 bits)
            req_ready: Downstream queue ready signal (1 = can accept request)
            
        Returns:
            dict with keys: wb_ack_o, wb_dat_o, wb_stall_o, wb_err_o,
                           req_valid, req_we, req_addr, req_wdata, req_wmask, req_aux
        """
        # Apply masks to inputs to ensure proper width
        cyc = cyc & 1
        stb = stb & 1
        we = we & 1
        adr = adr & self.ADDRESS_MASK
        dat = dat & self.DATA_MASK
        sel = sel & self.SEL_MASK
        cti = cti & 0b111
        bte = bte & 0b11
        req_ready = req_ready & 1
        
        # Initialize outputs
        result = {
            'wb_ack_o': 0,
            'wb_dat_o': 0,
            'wb_stall_o': 0,
            'wb_err_o': 0,
            'req_valid': 0,
            'req_we': 0,
            'req_addr': 0,
            'req_wdata': 0,
            'req_wmask': 0,
            'req_aux': 0,
        }
        
        # Rule 6 / Test case: stb without cyc is invalid - no transaction
        # Rule 5 / Test case: cyc=0 means no transaction
        if cyc == 0:
            # No bus cycle active - reset burst state and return idle
            self._in_burst = False
            self._burst_count = 0
            # wb_stall_o should be 0 when no transaction presented
            return result
        
        # cyc=1 at this point
        if stb == 0:
            # Cycle active but no strobe - idle beat in pipelined mode
            # Maintain burst state but don't generate request
            return result
        
        # Transaction presented: cyc=1 and stb=1
        # Rule 1: Check if we can accept the transaction
        
        # Handle burst address tracking
        if cti == self.CTI_INCR_BURST or cti == self.CTI_END_BURST:
            if not self._in_burst:
                # Start of new burst
                self._in_burst = True
                self._burst_count = 0
                self._burst_base_addr = adr
            
            # Calculate current address based on burst count
            current_addr = self._calculate_burst_address(
                self._burst_base_addr, self._burst_count, bte
            )
            
            # For incrementing burst, the address presented should match calculated
            # But we use the calculated address for the request
            req_addr = current_addr
            
            if cti == self.CTI_END_BURST:
                # End of burst - reset burst state after this beat
                # (State reset happens after we process this beat)
                pass
        else:
            # Classic cycle or constant burst - use presented address
            req_addr = adr
            self._in_burst = False
            self._burst_count = 0
        
        # Rule 4: Backpressure - stall if downstream not ready
        if req_ready == 0:
            result['wb_stall_o'] = 1
            # Do NOT assert req_valid when stalled
            result['req_valid'] = 0
            return result
        
        # req_ready=1 - we can accept the transaction
        # Generate aux tag for this request
        aux_tag = self._generate_aux_tag()
        
        # Populate request outputs
        result['req_valid'] = 1
        result['req_we'] = we
        result['req_addr'] = req_addr
        result['req_wdata'] = dat
        result['req_wmask'] = sel
        result['req_aux'] = aux_tag
        
        # Rule 2: Write transactions get immediate ack
        # Rule 3: Read transactions - no immediate data, ack when response arrives
        if we == 1:
            # Write: immediate acknowledgment
            result['wb_ack_o'] = 1
            result['wb_dat_o'] = 0  # No read data for writes
        else:
            # Read: track pending read, ack comes with complete_read()
            self._pending_reads.append(aux_tag)
            # Check if we have a response ready for immediate delivery
            if len(self._read_responses) > 0:
                # Deliver oldest pending response
                rdata = self._read_responses.popleft()
                result['wb_ack_o'] = 1
                result['wb_dat_o'] = rdata
                # Remove the matched pending read
                if len(self._pending_reads) > 0:
                    self._pending_reads.popleft()
            else:
                # No response ready yet
                result['wb_ack_o'] = 0
        
        # Update burst tracking for next beat
        if self._in_burst:
            self._burst_count += 1
            if cti == self.CTI_END_BURST:
                # End of burst - reset state
                self._in_burst = False
                self._burst_count = 0
            elif self._burst_count >= self.MAX_BURST_LENGTH:
                # Max burst length reached - force end
                self._in_burst = False
                self._burst_count = 0
        
        # Store last transaction state
        self._last_req_valid = result['req_valid']
        self._last_wb_ack = result['wb_ack_o']
        
        return result
    
    def complete_read(self, rsp_valid: int, rsp_rdata: int, rsp_aux: int) -> dict:
        """
        Deliver read response from downstream.
        
        Args:
            rsp_valid: Response valid signal (1 = valid response)
            rsp_rdata: Read data from memory (32 bits)
            rsp_aux: Aux tag to match with request (4 bits)
            
        Returns:
            dict with keys: wb_ack_o, wb_dat_o
        """
        result = {
            'wb_ack_o': 0,
            'wb_dat_o': 0,
        }
        
        # Apply masks
        rsp_valid = rsp_valid & 1
        rsp_rdata = rsp_rdata & self.DATA_MASK
        rsp_aux = rsp_aux & self.AUX_MASK
        
        if rsp_valid == 0:
            # No valid response
            return result
        
        # Valid response received
        if len(self._pending_reads) > 0:
            # Match response to pending read (FIFO order)
            # In a more complex model, we'd match by aux tag
            self._pending_reads.popleft()
            result['wb_ack_o'] = 1
            result['wb_dat_o'] = rsp_rdata
        else:
            # Response without matching pending read - buffer it
            # This shouldn't happen in normal operation but handle gracefully
            self._read_responses.append(rsp_rdata)
        
        return result
    
    def get_pending_read_count(self) -> int:
        """Return number of outstanding read requests awaiting response."""
        return len(self._pending_reads)


def run_self_test():
    """
    Run self-tests to verify the WishbonePortModel implementation.
    Tests are based on the spec requirements.
    """
    print("=" * 60)
    print("WishbonePortModel Self-Test")
    print("=" * 60)
    
    all_passed = True
    test_results = []
    
    def run_test(name, test_func):
        nonlocal all_passed
        try:
            passed, details = test_func()
            status = "PASS" if passed else "FAIL"
            if not passed:
                all_passed = False
            print(f"Test {name}: {status}")
            if details and not passed:
                print(f"  Details: {details}")
            test_results.append((name, passed))
        except Exception as e:
            all_passed = False
            print(f"Test {name}: FAIL (exception: {e})")
            test_results.append((name, False))
    
    # Test 1: Single write transaction
    def test_single_write():
        model = WishbonePortModel()
        model.reset()
        
        # Present write transaction with req_ready=1
        result = model.present_transaction(
            cyc=1, stb=1, we=1,
            adr=0x1000,
            dat=0xDEADBEEF,
            sel=0xF,
            cti=0b000,  # Classic cycle
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_valid'] != 1:
            errors.append(f"req_valid: expected 1, got {result['req_valid']}")
        if result['req_addr'] != 0x1000:
            errors.append(f"req_addr: expected 0x1000, got {hex(result['req_addr'])}")
        if result['req_wdata'] != 0xDEADBEEF:
            errors.append(f"req_wdata: expected 0xDEADBEEF, got {hex(result['req_wdata'])}")
        if result['req_wmask'] != 0xF:
            errors.append(f"req_wmask: expected 0xF, got {hex(result['req_wmask'])}")
        if result['req_we'] != 1:
            errors.append(f"req_we: expected 1, got {result['req_we']}")
        if result['wb_ack_o'] != 1:
            errors.append(f"wb_ack_o: expected 1 for write, got {result['wb_ack_o']}")
        if result['wb_stall_o'] != 0:
            errors.append(f"wb_stall_o: expected 0, got {result['wb_stall_o']}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 2: Single read transaction
    def test_single_read():
        model = WishbonePortModel()
        model.reset()
        
        # Present read transaction
        result = model.present_transaction(
            cyc=1, stb=1, we=0,
            adr=0x2000,
            dat=0,  # No write data for read
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_valid'] != 1:
            errors.append(f"req_valid: expected 1, got {result['req_valid']}")
        if result['req_we'] != 0:
            errors.append(f"req_we: expected 0 for read, got {result['req_we']}")
        if result['req_addr'] != 0x2000:
            errors.append(f"req_addr: expected 0x2000, got {hex(result['req_addr'])}")
        
        # Complete the read with response data
        read_result = model.complete_read(
            rsp_valid=1,
            rsp_rdata=0xCAFEBABE,
            rsp_aux=0
        )
        
        if read_result['wb_ack_o'] != 1:
            errors.append(f"wb_ack_o after complete: expected 1, got {read_result['wb_ack_o']}")
        if read_result['wb_dat_o'] != 0xCAFEBABE:
            errors.append(f"wb_dat_o: expected 0xCAFEBABE, got {hex(read_result['wb_dat_o'])}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 3: Backpressure (req_ready=0)
    def test_backpressure():
        model = WishbonePortModel()
        model.reset()
        
        # Present transaction with req_ready=0
        result = model.present_transaction(
            cyc=1, stb=1, we=1,
            adr=0x3000,
            dat=0x12345678,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=0  # Queue full!
        )
        
        errors = []
        if result['wb_stall_o'] != 1:
            errors.append(f"wb_stall_o: expected 1 when req_ready=0, got {result['wb_stall_o']}")
        if result['req_valid'] != 0:
            errors.append(f"req_valid: expected 0 when stalled, got {result['req_valid']}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 4: Burst write (4 incrementing writes)
    def test_burst_write():
        model = WishbonePortModel()
        model.reset()
        
        base_addr = 0x4000
        errors = []
        expected_addrs = [0x4000, 0x4004, 0x4008, 0x400C]
        
        for i in range(4):
            # CTI: 010 for first 3 beats, 111 for last beat
            if i < 3:
                cti = 0b010  # Incrementing burst
            else:
                cti = 0b111  # End of burst
            
            result = model.present_transaction(
                cyc=1, stb=1, we=1,
                adr=base_addr,  # Present base address (model calculates actual)
                dat=0x11111111 * (i + 1),
                sel=0xF,
                cti=cti,
                bte=0b00,  # Linear burst
                req_ready=1
            )
            
            if result['req_valid'] != 1:
                errors.append(f"Beat {i}: req_valid expected 1, got {result['req_valid']}")
            if result['req_addr'] != expected_addrs[i]:
                errors.append(f"Beat {i}: req_addr expected {hex(expected_addrs[i])}, got {hex(result['req_addr'])}")
            if result['wb_ack_o'] != 1:
                errors.append(f"Beat {i}: wb_ack_o expected 1 for write, got {result['wb_ack_o']}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 5: No transaction (cyc=0)
    def test_no_transaction():
        model = WishbonePortModel()
        model.reset()
        
        result = model.present_transaction(
            cyc=0, stb=0, we=0,
            adr=0x5000,
            dat=0,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_valid'] != 0:
            errors.append(f"req_valid: expected 0 when cyc=0, got {result['req_valid']}")
        if result['wb_stall_o'] != 0:
            errors.append(f"wb_stall_o: expected 0 when cyc=0, got {result['wb_stall_o']}")
        if result['wb_ack_o'] != 0:
            errors.append(f"wb_ack_o: expected 0 when cyc=0, got {result['wb_ack_o']}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 6: Stb without cyc (invalid bus state)
    def test_stb_without_cyc():
        model = WishbonePortModel()
        model.reset()
        
        result = model.present_transaction(
            cyc=0, stb=1, we=1,  # Invalid: stb=1 but cyc=0
            adr=0x6000,
            dat=0xABCDEF00,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_valid'] != 0:
            errors.append(f"req_valid: expected 0 for invalid bus state, got {result['req_valid']}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 7: get_pending_read_count
    def test_pending_read_count():
        model = WishbonePortModel()
        model.reset()
        
        errors = []
        
        # Initial count should be 0
        if model.get_pending_read_count() != 0:
            errors.append(f"Initial count: expected 0, got {model.get_pending_read_count()}")
        
        # Present first read
        model.present_transaction(
            cyc=1, stb=1, we=0,
            adr=0x7000,
            dat=0,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        if model.get_pending_read_count() != 1:
            errors.append(f"After 1 read: expected 1, got {model.get_pending_read_count()}")
        
        # Present second read
        model.present_transaction(
            cyc=1, stb=1, we=0,
            adr=0x7004,
            dat=0,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        if model.get_pending_read_count() != 2:
            errors.append(f"After 2 reads: expected 2, got {model.get_pending_read_count()}")
        
        # Complete first read
        model.complete_read(rsp_valid=1, rsp_rdata=0x11111111, rsp_aux=0)
        
        if model.get_pending_read_count() != 1:
            errors.append(f"After 1 complete: expected 1, got {model.get_pending_read_count()}")
        
        # Complete second read
        model.complete_read(rsp_valid=1, rsp_rdata=0x22222222, rsp_aux=1)
        
        if model.get_pending_read_count() != 0:
            errors.append(f"After 2 complete: expected 0, got {model.get_pending_read_count()}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 8: Address masking (verify 29-bit address width from spec)
    def test_address_masking():
        model = WishbonePortModel()
        model.reset()
        
        # Address with bits beyond 29 should be masked
        # 29 bits = 0x1FFFFFFF max
        large_addr = 0x3FFFFFFF  # 30 bits set
        expected_addr = 0x1FFFFFFF  # Masked to 29 bits
        
        result = model.present_transaction(
            cyc=1, stb=1, we=1,
            adr=large_addr,
            dat=0x12345678,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_addr'] != expected_addr:
            errors.append(f"Address mask: expected {hex(expected_addr)}, got {hex(result['req_addr'])}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 9: Data and select masking
    def test_data_masking():
        model = WishbonePortModel()
        model.reset()
        
        # Data beyond 32 bits should be masked
        large_data = 0x1FFFFFFFF  # 33 bits
        expected_data = 0xFFFFFFFF  # Masked to 32 bits
        
        # Sel beyond 4 bits should be masked
        large_sel = 0x1F  # 5 bits
        expected_sel = 0xF  # Masked to 4 bits
        
        result = model.present_transaction(
            cyc=1, stb=1, we=1,
            adr=0x1000,
            dat=large_data,
            sel=large_sel,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_wdata'] != expected_data:
            errors.append(f"Data mask: expected {hex(expected_data)}, got {hex(result['req_wdata'])}")
        if result['req_wmask'] != expected_sel:
            errors.append(f"Sel mask: expected {hex(expected_sel)}, got {hex(result['req_wmask'])}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 10: Write with partial byte select
    def test_partial_write():
        model = WishbonePortModel()
        model.reset()
        
        # Write with only byte 1 selected (bits 15:8)
        result = model.present_transaction(
            cyc=1, stb=1, we=1,
            adr=0x8000,
            dat=0xFF00FF00,
            sel=0b0010,  # Only byte 1
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        errors = []
        if result['req_valid'] != 1:
            errors.append(f"req_valid: expected 1, got {result['req_valid']}")
        if result['req_wmask'] != 0b0010:
            errors.append(f"req_wmask: expected 0b0010, got {bin(result['req_wmask'])}")
        if result['req_wdata'] != 0xFF00FF00:
            errors.append(f"req_wdata: expected 0xFF00FF00, got {hex(result['req_wdata'])}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 11: Reset clears state
    def test_reset():
        model = WishbonePortModel()
        
        # Create some state
        model.present_transaction(
            cyc=1, stb=1, we=0,
            adr=0x9000,
            dat=0,
            sel=0xF,
            cti=0b000,
            bte=0b00,
            req_ready=1
        )
        
        if model.get_pending_read_count() != 1:
            return False, "Setup failed: pending read not tracked"
        
        # Reset
        model.reset()
        
        errors = []
        if model.get_pending_read_count() != 0:
            errors.append(f"Pending count after reset: expected 0, got {model.get_pending_read_count()}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Test 12: Multiple reads then multiple completes
    def test_multiple_read_complete():
        model = WishbonePortModel()
        model.reset()
        
        errors = []
        
        # Issue 3 reads
        for i in range(3):
            model.present_transaction(
                cyc=1, stb=1, we=0,
                adr=0xA000 + i * 4,
                dat=0,
                sel=0xF,
                cti=0b000,
                bte=0b00,
                req_ready=1
            )
        
        if model.get_pending_read_count() != 3:
            errors.append(f"After 3 reads: expected count 3, got {model.get_pending_read_count()}")
        
        # Complete reads with specific data
        expected_data = [0xAAAAAAAA, 0xBBBBBBBB, 0xCCCCCCCC]
        for i in range(3):
            result = model.complete_read(
                rsp_valid=1,
                rsp_rdata=expected_data[i],
                rsp_aux=i
            )
            if result['wb_dat_o'] != expected_data[i]:
                errors.append(f"Read {i}: expected data {hex(expected_data[i])}, got {hex(result['wb_dat_o'])}")
            if result['wb_ack_o'] != 1:
                errors.append(f"Read {i}: expected ack=1, got {result['wb_ack_o']}")
        
        if model.get_pending_read_count() != 0:
            errors.append(f"After completes: expected count 0, got {model.get_pending_read_count()}")
        
        return len(errors) == 0, "; ".join(errors)
    
    # Run all tests
    run_test("1_single_write", test_single_write)
    run_test("2_single_read", test_single_read)
    run_test("3_backpressure", test_backpressure)
    run_test("4_burst_write", test_burst_write)
    run_test("5_no_transaction", test_no_transaction)
    run_test("6_stb_without_cyc", test_stb_without_cyc)
    run_test("7_pending_read_count", test_pending_read_count)
    run_test("8_address_masking", test_address_masking)
    run_test("9_data_masking", test_data_masking)
    run_test("10_partial_write", test_partial_write)
    run_test("11_reset", test_reset)
    run_test("12_multiple_read_complete", test_multiple_read_complete)
    
    # Print summary
    print("=" * 60)
    passed_count = sum(1 for _, p in test_results if p)
    total_count = len(test_results)
    print(f"Results: {passed_count}/{total_count} tests passed")
    
    if all_passed:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        for name, passed in test_results:
            if not passed:
                print(f"  - {name}")
    
    return all_passed


if __name__ == "__main__":
    run_self_test()