#!/usr/bin/env python3
"""
Reference model for DDR3 Memory Controller Path 07: Command Queue → Wishbone Backpressure

Models the INTEGRATION path: cmd_queue -> wb_port
Connection: enq_ready -> req_ready (Command queue backpressure to Wishbone port when full.)

The key behavior modeled:
- Command queue with depth 16, tracking valid entries
- Wishbone pipelined interface that stalls when command queue is full
- Backpressure signal (queue_full) propagates to wb_stall_o
- Wishbone transactions are accepted only when queue has space
"""

import json
import os
from collections import deque

# Command queue parameters from spec
CMD_QUEUE_DEPTH = 16
NUM_BANKS = 8
AUX_WIDTH = 4

# Address mapping from spec
ROW_BITS = 15
COL_BITS = 10
BANK_BITS = 3

# Host interface from spec
DATA_WIDTH = 32
ADDR_WIDTH = 29
SEL_WIDTH = 4
MAX_BURST = 8

# Wishbone CTI encodings
CTI_CLASSIC = 0b000
CTI_CONST_BURST = 0b001
CTI_INC_BURST = 0b010
CTI_END_BURST = 0b111

# Output signal names (all must be in step() return dict)
OUTPUT_SIGNALS = [
    "entry_valid",    # bitmask of valid entries in command queue
    "queue_full",     # 1 if command queue is full
    "queue_empty",    # 1 if command queue is empty
    "queue_count",    # number of valid entries
    "wb_ack_o",       # Wishbone acknowledge
    "wb_dat_o",       # Wishbone read data output
    "wb_stall_o",     # Wishbone stall (backpressure)
    "wb_err_o",       # Wishbone error
    "req_valid",      # request valid to downstream
    "req_we",         # request write enable
    "req_addr",       # request address
    "req_wdata",      # request write data
    "req_wmask",      # request write mask
    "req_aux",        # request auxiliary bits
]


class CommandQueueEntry:
    """One entry in the command queue."""
    def __init__(self):
        self.valid = False
        self.row = 0
        self.col = 0
        self.bank = 0
        self.we = 0
        self.aux = 0
        self.addr = 0      # original Wishbone address
        self.wdata = 0     # write data
        self.wmask = 0     # write byte mask (sel)


class PathModel:
    """
    Models the Command Queue → Wishbone Backpressure path.
    
    The command queue accepts enqueue requests. When full, it asserts queue_full,
    which propagates as wb_stall_o to the Wishbone port, preventing new transactions
    from being accepted.
    
    Data flow:
    1. Wishbone master drives wb_cyc_i, wb_stb_i, wb_adr_i, etc.
    2. wb_port converts Wishbone transactions into enqueue requests to cmd_queue
    3. When cmd_queue is full, enq_ready deasserts → wb_stall_o asserts
    4. Dequeue side (scheduler) removes entries via deq_grant/deq_idx
    
    The model also accepts direct enqueue signals (enq_valid, enq_row, etc.)
    for testing the command queue directly without going through Wishbone.
    """
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        """Reset all internal state to power-on defaults."""
        # Command queue entries
        self.queue = [CommandQueueEntry() for _ in range(CMD_QUEUE_DEPTH)]
        
        # Queue management
        self.queue_count = 0
        self.write_ptr = 0  # next slot to write into (circular)
        
        # Wishbone port state
        self.wb_ack_pending = False
        self.wb_read_pending = False
        self.wb_pending_addr = 0
        self.wb_pending_we = 0
        self.wb_pending_wdata = 0
        self.wb_pending_sel = 0
        
        # Read response buffer (from rsp_valid/rsp_rdata)
        self.read_buffer = deque(maxlen=16)  # read_buffer_depth=16
        
        # Burst tracking
        self.burst_active = False
        self.burst_count = 0
        self.burst_addr = 0
        self.burst_we = 0
        
        # Output registers (all reset to 0)
        self.out_wb_ack = 0
        self.out_wb_dat = 0
        self.out_wb_stall = 0
        self.out_wb_err = 0
        self.out_req_valid = 0
        self.out_req_we = 0
        self.out_req_addr = 0
        self.out_req_wdata = 0
        self.out_req_wmask = 0
        self.out_req_aux = 0
    
    def _get_queue_full(self):
        """Check if queue is full."""
        return self.queue_count >= CMD_QUEUE_DEPTH
    
    def _get_queue_empty(self):
        """Check if queue is empty."""
        return self.queue_count == 0
    
    def _get_entry_valid_bitmask(self):
        """Return bitmask of valid entries."""
        mask = 0
        for i in range(CMD_QUEUE_DEPTH):
            if self.queue[i].valid:
                mask |= (1 << i)
        return mask
    
    def _find_free_slot(self):
        """Find the first free slot in the queue. Returns index or -1 if full."""
        for i in range(CMD_QUEUE_DEPTH):
            if not self.queue[i].valid:
                return i
        return -1
    
    def _enqueue(self, row, col, bank, we, aux, addr=0, wdata=0, wmask=0):
        """
        Enqueue a command into the command queue.
        Returns True if successful, False if queue was full.
        """
        slot = self._find_free_slot()
        if slot < 0:
            return False
        
        entry = self.queue[slot]
        entry.valid = True
        entry.row = row & ((1 << ROW_BITS) - 1)
        entry.col = col & ((1 << COL_BITS) - 1)
        entry.bank = bank & ((1 << BANK_BITS) - 1)
        entry.we = we & 1
        entry.aux = aux & ((1 << AUX_WIDTH) - 1)
        entry.addr = addr
        entry.wdata = wdata
        entry.wmask = wmask
        self.queue_count += 1
        return True
    
    def _dequeue(self, idx):
        """
        Dequeue (invalidate) the entry at given index.
        Returns True if the entry was valid and is now dequeued.
        """
        if idx < 0 or idx >= CMD_QUEUE_DEPTH:
            return False
        if not self.queue[idx].valid:
            return False
        
        self.queue[idx].valid = False
        self.queue_count -= 1
        return True
    
    def _decode_address(self, wb_addr):
        """
        Decode a Wishbone byte address into row, bank, column using
        row-bank-column mapping.
        
        Address layout (byte address, 29 bits):
        Byte offset: bits [1:0] (2 bits for 4-byte word)
        Actually, with BL=8 and 16-bit bus, burst size = 16 bytes,
        so the low bits correspond to burst offset.
        
        With byte addressing and 32-bit data width:
        - bits [1:0]: byte within word (implicit in sel)
        - bits [3:2]: word within burst (for BL=8 with 16-bit DDR bus)
        
        For row-bank-column mapping:
        - Column bits: [col_bits+1:2] (column address, shifted for burst)
        - Bank bits: [bank_bits+col_bits+1:col_bits+2]
        - Row bits: [row_bits+bank_bits+col_bits+1:bank_bits+col_bits+2]
        
        Since the DDR burst length is 8 with 16-bit bus = 16 bytes per burst,
        and Wishbone is 32-bit, a single Wishbone word is 4 bytes.
        4 Wishbone words = 16 bytes = one DDR burst.
        
        For simplicity in this model, we extract row/bank/col from the address.
        """
        # Remove byte offset (2 bits for 32-bit words)
        word_addr = wb_addr >> 2
        
        # Extract column (low COL_BITS of word address)
        # Column addresses in DDR3 are in terms of burst-aligned,
        # but we'll keep it simple: col from low bits
        col = word_addr & ((1 << COL_BITS) - 1)
        
        # Extract bank
        bank = (word_addr >> COL_BITS) & ((1 << BANK_BITS) - 1)
        
        # Extract row
        row = (word_addr >> (COL_BITS + BANK_BITS)) & ((1 << ROW_BITS) - 1)
        
        return row, bank, col
    
    def step(self, **inputs):
        """
        Advance the model by one clock cycle.
        
        Models the backpressure path:
        1. Process dequeue requests (from scheduler side)
        2. Process Wishbone transactions → enqueue into command queue
        3. Process direct enqueue requests
        4. Compute backpressure: queue_full → wb_stall_o
        5. Process read responses
        """
        # Extract inputs with defaults
        enq_valid = inputs.get("enq_valid", 0)
        enq_row = inputs.get("enq_row", 0)
        enq_col = inputs.get("enq_col", 0)
        enq_bank = inputs.get("enq_bank", 0)
        enq_we = inputs.get("enq_we", 0)
        enq_aux = inputs.get("enq_aux", 0)
        
        deq_grant = inputs.get("deq_grant", 0)
        deq_idx = inputs.get("deq_idx", 0)
        
        wb_cyc = inputs.get("wb_cyc_i", 0)
        wb_stb = inputs.get("wb_stb_i", 0)
        wb_we = inputs.get("wb_we_i", 0)
        wb_adr = inputs.get("wb_adr_i", 0)
        wb_dat = inputs.get("wb_dat_i", 0)
        wb_sel = inputs.get("wb_sel_i", 0xF)
        wb_bte = inputs.get("wb_bte_i", 0)
        wb_cti = inputs.get("wb_cti_i", 0)
        
        rsp_valid = inputs.get("rsp_valid", 0)
        rsp_rdata = inputs.get("rsp_rdata", 0)
        rsp_aux = inputs.get("rsp_aux", 0)
        
        # --- Step 1: Process dequeue (scheduler removing entries) ---
        if deq_grant:
            self._dequeue(deq_idx)
        
        # --- Step 2: Process read responses into read buffer ---
        if rsp_valid:
            self.read_buffer.append(rsp_rdata)
        
        # --- Step 3: Compute current backpressure state ---
        queue_full = self._get_queue_full()
        enq_ready = not queue_full  # Space available in queue
        
        # wb_stall_o: stall when queue is full (no space for new requests)
        # In pipelined Wishbone, stall means the current request phase is not accepted
        wb_stall = 1 if queue_full else 0
        
        # --- Step 4: Process Wishbone transactions ---
        wb_ack = 0
        wb_dat_out = 0
        wb_err = 0
        req_valid = 0
        req_we = 0
        req_addr = 0
        req_wdata = 0
        req_wmask = 0
        req_aux = 0
        
        # Wishbone pipelined protocol:
        # - Master asserts cyc + stb to make a request
        # - If stall=0, the request is accepted this cycle
        # - ack comes later (possibly next cycle for writes, after data for reads)
        
        wb_request_valid = wb_cyc and wb_stb
        wb_request_accepted = wb_request_valid and not queue_full
        
        if wb_request_accepted:
            # Decode address
            row, bank, col = self._decode_address(wb_adr)
            
            # Enqueue into command queue
            success = self._enqueue(
                row=row,
                col=col,
                bank=bank,
                we=wb_we,
                aux=0,  # aux assigned by wb_port
                addr=wb_adr,
                wdata=wb_dat if wb_we else 0,
                wmask=wb_sel if wb_we else 0
            )
            
            if success:
                # For writes, ack can come immediately in pipelined mode
                # For reads, ack comes when data is available
                if wb_we:
                    wb_ack = 1
                    req_valid = 1
                    req_we = 1
                    req_addr = wb_adr
                    req_wdata = wb_dat
                    req_wmask = wb_sel
                else:
                    # Read request enqueued, ack when response available
                    req_valid = 1
                    req_we = 0
                    req_addr = wb_adr
                    # Check if read data is already available
                    if len(self.read_buffer) > 0:
                        wb_ack = 1
                        wb_dat_out = self.read_buffer.popleft()
        else:
            # Even if no new request, check if we can deliver read data
            if wb_cyc and not wb_stb and len(self.read_buffer) > 0:
                wb_ack = 1
                wb_dat_out = self.read_buffer.popleft()
        
        # If not going through Wishbone, handle direct enqueue interface
        if enq_valid and not wb_request_valid:
            if enq_ready:
                self._enqueue(
                    row=enq_row,
                    col=enq_col,
                    bank=enq_bank,
                    we=enq_we,
                    aux=enq_aux
                )
        
        # Deliver pending read responses via ack even without new stb
        if not wb_ack and wb_cyc and len(self.read_buffer) > 0:
            wb_ack = 1
            wb_dat_out = self.read_buffer.popleft()
        
        # --- Step 5: Recompute queue status after all operations ---
        queue_full_final = self._get_queue_full()
        queue_empty_final = self._get_queue_empty()
        entry_valid_mask = self._get_entry_valid_bitmask()
        queue_count = self.queue_count
        
        # Final stall output reflects post-operation state for NEXT cycle
        # In pipelined Wishbone, stall is combinational with current state
        wb_stall_final = 1 if queue_full_final else 0
        
        # Store outputs
        self.out_wb_ack = wb_ack
        self.out_wb_dat = wb_dat_out
        self.out_wb_stall = wb_stall_final
        self.out_wb_err = wb_err
        self.out_req_valid = req_valid
        self.out_req_we = req_we
        self.out_req_addr = req_addr
        self.out_req_wdata = req_wdata
        self.out_req_wmask = req_wmask
        self.out_req_aux = req_aux
        
        return {
            "entry_valid": entry_valid_mask,
            "queue_full": 1 if queue_full_final else 0,
            "queue_empty": 1 if queue_empty_final else 0,
            "queue_count": queue_count,
            "wb_ack_o": wb_ack,
            "wb_dat_o": wb_dat_out & 0xFFFFFFFF,
            "wb_stall_o": wb_stall_final,
            "wb_err_o": wb_err,
            "req_valid": req_valid,
            "req_we": req_we,
            "req_addr": req_addr & ((1 << ADDR_WIDTH) - 1),
            "req_wdata": req_wdata & 0xFFFFFFFF,
            "req_wmask": req_wmask & ((1 << SEL_WIDTH) - 1),
            "req_aux": req_aux & ((1 << AUX_WIDTH) - 1),
        }
    
    def get_state(self) -> dict:
        """Return full internal state for debugging."""
        entries = []
        for i in range(CMD_QUEUE_DEPTH):
            e = self.queue[i]
            entries.append({
                "idx": i,
                "valid": e.valid,
                "row": e.row,
                "col": e.col,
                "bank": e.bank,
                "we": e.we,
                "aux": e.aux,
                "addr": e.addr,
                "wdata": e.wdata,
                "wmask": e.wmask,
            })
        
        return {
            "queue_count": self.queue_count,
            "queue_full": self._get_queue_full(),
            "queue_empty": self._get_queue_empty(),
            "entry_valid_mask": self._get_entry_valid_bitmask(),
            "write_ptr": self.write_ptr,
            "read_buffer_len": len(self.read_buffer),
            "entries": entries,
        }


def run_self_test():
    """Run self-tests and print per-test PASS/FAIL."""
    results = []
    
    def check(test_name, condition):
        status = "PASS" if condition else "FAIL"
        results.append((test_name, condition))
        print(f"  {status}: {test_name}")
    
    model = PathModel()
    
    # =================================================================
    # Test 1: Reset values
    # =================================================================
    print("Test 1: Reset values")
    model.reset()
    out = model.step()
    
    check("After reset, queue_empty=1", out["queue_empty"] == 1)
    check("After reset, queue_full=0", out["queue_full"] == 0)
    check("After reset, queue_count=0", out["queue_count"] == 0)
    check("After reset, entry_valid=0", out["entry_valid"] == 0)
    check("After reset, wb_ack_o=0", out["wb_ack_o"] == 0)
    check("After reset, wb_stall_o=0", out["wb_stall_o"] == 0)
    check("After reset, wb_err_o=0", out["wb_err_o"] == 0)
    check("After reset, wb_dat_o=0", out["wb_dat_o"] == 0)
    check("After reset, req_valid=0", out["req_valid"] == 0)
    check("After reset, req_we=0", out["req_we"] == 0)
    check("After reset, req_addr=0", out["req_addr"] == 0)
    check("After reset, req_wdata=0", out["req_wdata"] == 0)
    check("After reset, req_wmask=0", out["req_wmask"] == 0)
    check("After reset, req_aux=0", out["req_aux"] == 0)
    
    # =================================================================
    # Test 2: All output signals present in step() return
    # =================================================================
    print("\nTest 2: All output signals present")
    model.reset()
    out = model.step()
    all_present = all(sig in out for sig in OUTPUT_SIGNALS)
    check("All output signals present in return dict", all_present)
    
    missing = [sig for sig in OUTPUT_SIGNALS if sig not in out]
    if missing:
        print(f"    Missing: {missing}")
    
    # =================================================================
    # Test 3: step() accepts and ignores unknown kwargs
    # =================================================================
    print("\nTest 3: Unknown kwargs handling")
    model.reset()
    try:
        out = model.step(unknown_signal_xyz=42, another_unknown=99)
        check("step() accepts unknown kwargs without error", True)
    except Exception as e:
        check(f"step() accepts unknown kwargs without error (got {e})", False)
    
    # =================================================================
    # Test 4: Direct enqueue fills queue
    # =================================================================
    print("\nTest 4: Direct enqueue interface")
    model.reset()
    
    # Enqueue one entry
    out = model.step(enq_valid=1, enq_row=100, enq_col=50, enq_bank=3, enq_we=1, enq_aux=5)
    check("After 1 enqueue, queue_count=1", out["queue_count"] == 1)
    check("After 1 enqueue, queue_empty=0", out["queue_empty"] == 0)
    check("After 1 enqueue, queue_full=0", out["queue_full"] == 0)
    
    # Verify entry is valid
    check("After 1 enqueue, entry_valid != 0", out["entry_valid"] != 0)
    
    # =================================================================
    # Test 5: Fill queue to full → backpressure
    # =================================================================
    print("\nTest 5: Fill queue to full (backpressure)")
    model.reset()
    
    # Enqueue 16 entries to fill the queue
    for i in range(CMD_QUEUE_DEPTH):
        out = model.step(enq_valid=1, enq_row=i, enq_col=i, enq_bank=i % 8, enq_we=0, enq_aux=i % 16)
    
    check(f"After {CMD_QUEUE_DEPTH} enqueues, queue_count={CMD_QUEUE_DEPTH}",
          out["queue_count"] == CMD_QUEUE_DEPTH)
    check("Queue is full", out["queue_full"] == 1)
    check("Queue is not empty", out["queue_empty"] == 0)
    check("wb_stall_o=1 when full", out["wb_stall_o"] == 1)
    check("entry_valid all set", out["entry_valid"] == (1 << CMD_QUEUE_DEPTH) - 1)
    
    # Try to enqueue one more (should fail, count stays at 16)
    out = model.step(enq_valid=1, enq_row=999, enq_col=999, enq_bank=7, enq_we=1, enq_aux=0)
    check("Enqueue when full: queue_count stays at 16", out["queue_count"] == CMD_QUEUE_DEPTH)
    check("Enqueue when full: still full", out["queue_full"] == 1)
    check("Enqueue when full: stall remains", out["wb_stall_o"] == 1)
    
    # =================================================================
    # Test 6: Dequeue frees space
    # =================================================================
    print("\nTest 6: Dequeue frees space")
    # Queue is full from test 5, dequeue index 0
    out = model.step(deq_grant=1, deq_idx=0)
    check("After dequeue, queue_count=15", out["queue_count"] == 15)
    check("After dequeue, queue_full=0", out["queue_full"] == 0)
    check("After dequeue, wb_stall_o=0", out["wb_stall_o"] == 0)
    check("After dequeue, entry at idx 0 is invalid", (out["entry_valid"] & 1) == 0)
    
    # =================================================================
    # Test 7: Wishbone write transaction → enqueue
    # =================================================================
    print("\nTest 7: Wishbone write transaction")
    model.reset()
    
    test_addr = 0x1000  # byte address
    test_data = 0xDEADBEEF
    test_sel = 0xF
    
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=test_addr, wb_dat_i=test_data, wb_sel_i=test_sel,
        wb_cti_i=CTI_CLASSIC
    )
    
    check("WB write: queue_count=1", out["queue_count"] == 1)
    check("WB write: wb_ack_o=1 for write", out["wb_ack_o"] == 1)
    check("WB write: wb_stall_o=0 (not full)", out["wb_stall_o"] == 0)
    check("WB write: req_valid=1", out["req_valid"] == 1)
    check("WB write: req_we=1", out["req_we"] == 1)
    check("WB write: req_addr matches", out["req_addr"] == test_addr)
    check("WB write: req_wdata matches", out["req_wdata"] == test_data)
    check("WB write: req_wmask matches", out["req_wmask"] == test_sel)
    
    # =================================================================
    # Test 8: Wishbone read transaction → enqueue, no immediate ack without data
    # =================================================================
    print("\nTest 8: Wishbone read transaction")
    model.reset()
    
    test_addr = 0x2000
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=0,
        wb_adr_i=test_addr, wb_sel_i=0xF,
        wb_cti_i=CTI_CLASSIC
    )
    
    check("WB read: queue_count=1", out["queue_count"] == 1)
    check("WB read: req_valid=1", out["req_valid"] == 1)
    check("WB read: req_we=0", out["req_we"] == 0)
    check("WB read: req_addr matches", out["req_addr"] == test_addr)
    
    # =================================================================
    # Test 9: Wishbone stall when queue full
    # =================================================================
    print("\nTest 9: Wishbone stall when queue full")
    model.reset()
    
    # Fill queue with direct enqueues
    for i in range(CMD_QUEUE_DEPTH):
        model.step(enq_valid=1, enq_row=i, enq_col=i, enq_bank=i % 8, enq_we=0, enq_aux=0)
    
    # Now try Wishbone write - should be stalled
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x3000, wb_dat_i=0xCAFEBABE, wb_sel_i=0xF
    )
    
    check("WB stall: wb_stall_o=1 when full", out["wb_stall_o"] == 1)
    check("WB stall: wb_ack_o=0 (request not accepted)", out["wb_ack_o"] == 0)
    check("WB stall: req_valid=0 (not forwarded)", out["req_valid"] == 0)
    check("WB stall: queue_count stays at 16", out["queue_count"] == CMD_QUEUE_DEPTH)
    
    # Dequeue one, then retry
    out = model.step(
        deq_grant=1, deq_idx=0,
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x3000, wb_dat_i=0xCAFEBABE, wb_sel_i=0xF
    )
    
    # After dequeue, space available, so request should be accepted
    check("After dequeue+WB: wb_ack_o=1 (write accepted)", out["wb_ack_o"] == 1)
    check("After dequeue+WB: queue_count=16 (one out, one in)", out["queue_count"] == CMD_QUEUE_DEPTH)
    
    # =================================================================
    # Test 10: Read response delivery
    # =================================================================
    print("\nTest 10: Read response delivery")
    model.reset()
    
    # Enqueue a read request via Wishbone
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=0,
        wb_adr_i=0x4000, wb_sel_i=0xF
    )
    check("Read enqueued: queue_count=1", out["queue_count"] == 1)
    
    # Provide read response
    read_data = 0x12345678
    out = model.step(
        wb_cyc_i=1, wb_stb_i=0,
        rsp_valid=1, rsp_rdata=read_data
    )
    
    check("Read response: wb_ack_o=1", out["wb_ack_o"] == 1)
    check("Read response: wb_dat_o matches", out["wb_dat_o"] == read_data)
    
    # =================================================================
    # Test 11: Simultaneous enqueue and dequeue
    # =================================================================
    print("\nTest 11: Simultaneous enqueue and dequeue")
    model.reset()
    
    # Enqueue 5 entries first
    for i in range(5):
        model.step(enq_valid=1, enq_row=i, enq_col=i, enq_bank=i, enq_we=0, enq_aux=0)
    
    # Simultaneous enqueue + dequeue
    out = model.step(
        enq_valid=1, enq_row=99, enq_col=99, enq_bank=7, enq_we=1, enq_aux=3,
        deq_grant=1, deq_idx=0
    )
    
    # Dequeue happens first, then enqueue: count should still be 5
    check("Simultaneous enq+deq: queue_count=5", out["queue_count"] == 5)
    check("Simultaneous enq+deq: entry 0 may be reused or another slot taken",
          out["entry_valid"] != 0)
    
    # =================================================================
    # Test 12: Address decoding (row-bank-column)
    # =================================================================
    print("\nTest 12: Address decoding")
    model.reset()
    
    # Construct an address: row=1, bank=2, col=3
    # Word addr = (row << (COL_BITS + BANK_BITS)) | (bank << COL_BITS) | col
    # Byte addr = word_addr << 2
    row_val = 1
    bank_val = 2
    col_val = 3
    word_addr = (row_val << (COL_BITS + BANK_BITS)) | (bank_val << COL_BITS) | col_val
    byte_addr = word_addr << 2
    
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=byte_addr, wb_dat_i=0xAAAAAAAA, wb_sel_i=0xF
    )
    
    # Verify the entry was stored with correct decoded values
    state = model.get_state()
    found = False
    for entry in state["entries"]:
        if entry["valid"]:
            if entry["row"] == row_val and entry["bank"] == bank_val and entry["col"] == col_val:
                found = True
                break
    
    check("Address decode: row/bank/col correct in queue entry", found)
    
    # =================================================================
    # Test 13: Queue empty after draining all entries
    # =================================================================
    print("\nTest 13: Drain queue to empty")
    model.reset()
    
    # Enqueue 3 entries
    for i in range(3):
        model.step(enq_valid=1, enq_row=i, enq_col=i, enq_bank=i, enq_we=0, enq_aux=0)
    
    # Dequeue all
    for i in range(3):
        out = model.step(deq_grant=1, deq_idx=i)
    
    check("After draining: queue_empty=1", out["queue_empty"] == 1)
    check("After draining: queue_count=0", out["queue_count"] == 0)
    check("After draining: entry_valid=0", out["entry_valid"] == 0)
    check("After draining: wb_stall_o=0", out["wb_stall_o"] == 0)
    
    # =================================================================
    # Test 14: get_state() returns valid dict
    # =================================================================
    print("\nTest 14: get_state() check")
    model.reset()
    state = model.get_state()
    check("get_state() returns dict", isinstance(state, dict))
    check("get_state() has queue_count", "queue_count" in state)
    check("get_state() has entries", "entries" in state)
    check("get_state() entries length = 16", len(state["entries"]) == CMD_QUEUE_DEPTH)
    
    # =================================================================
    # Test 15: No Wishbone activity (cyc=0) → no enqueue
    # =================================================================
    print("\nTest 15: No Wishbone activity")
    model.reset()
    out = model.step(wb_cyc_i=0, wb_stb_i=1, wb_we_i=1, wb_adr_i=0x5000, wb_dat_i=0xFF)
    check("cyc=0: queue_count=0", out["queue_count"] == 0)
    check("cyc=0: wb_ack_o=0", out["wb_ack_o"] == 0)
    check("cyc=0: req_valid=0", out["req_valid"] == 0)
    
    # =================================================================
    # Test 16: Boundary - dequeue invalid index
    # =================================================================
    print("\nTest 16: Dequeue invalid index")
    model.reset()
    model.step(enq_valid=1, enq_row=1, enq_col=1, enq_bank=1, enq_we=0, enq_aux=0)
    
    # Try to dequeue index 5 (which has no valid entry)
    out = model.step(deq_grant=1, deq_idx=5)
    check("Dequeue invalid idx: queue_count stays at 1", out["queue_count"] == 1)
    
    # =================================================================
    # Test 17: Multiple read responses buffered
    # =================================================================
    print("\nTest 17: Multiple read responses")
    model.reset()
    
    # Provide 3 read responses without Wishbone requests
    model.step(rsp_valid=1, rsp_rdata=0xAABBCCDD)
    model.step(rsp_valid=1, rsp_rdata=0x11223344)
    model.step(rsp_valid=1, rsp_rdata=0x55667788)
    
    # Now read them out via Wishbone cyc (no stb, just collecting)
    out1 = model.step(wb_cyc_i=1)
    check("Buffered read 1: wb_ack_o=1", out1["wb_ack_o"] == 1)
    check("Buffered read 1: data=0xAABBCCDD", out1["wb_dat_o"] == 0xAABBCCDD)
    
    out2 = model.step(wb_cyc_i=1)
    check("Buffered read 2: wb_ack_o=1", out2["wb_ack_o"] == 1)
    check("Buffered read 2: data=0x11223344", out2["wb_dat_o"] == 0x11223344)
    
    out3 = model.step(wb_cyc_i=1)
    check("Buffered read 3: wb_ack_o=1", out3["wb_ack_o"] == 1)
    check("Buffered read 3: data=0x55667788", out3["wb_dat_o"] == 0x55667788)
    
    # No more data
    out4 = model.step(wb_cyc_i=1)
    check("No more buffered reads: wb_ack_o=0", out4["wb_ack_o"] == 0)
    
    # =================================================================
    # Test 18: Backpressure cycle - fill, stall, drain, unstall
    # =================================================================
    print("\nTest 18: Full backpressure cycle")
    model.reset()
    
    # Phase 1: Fill to full via Wishbone writes
    for i in range(CMD_QUEUE_DEPTH):
        addr = (i + 1) * 4
        out = model.step(
            wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
            wb_adr_i=addr, wb_dat_i=i, wb_sel_i=0xF
        )
    
    check("Phase 1: queue full", out["queue_full"] == 1)
    check("Phase 1: stall asserted", out["wb_stall_o"] == 1)
    
    # Phase 2: Attempt write while stalled
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0x9000, wb_dat_i=0xFF, wb_sel_i=0xF
    )
    check("Phase 2: write rejected (stall)", out["wb_ack_o"] == 0)
    check("Phase 2: count still 16", out["queue_count"] == CMD_QUEUE_DEPTH)
    
    # Phase 3: Drain half
    for i in range(8):
        model.step(deq_grant=1, deq_idx=i)
    
    out = model.step()
    check("Phase 3: queue_count=8", out["queue_count"] == 8)
    check("Phase 3: stall deasserted", out["wb_stall_o"] == 0)
    check("Phase 3: not full", out["queue_full"] == 0)
    check("Phase 3: not empty", out["queue_empty"] == 0)
    
    # Phase 4: Can accept new writes
    out = model.step(
        wb_cyc_i=1, wb_stb_i=1, wb_we_i=1,
        wb_adr_i=0xA000, wb_dat_i=0xBEEF, wb_sel_i=0xF
    )
    check("Phase 4: write accepted after drain", out["wb_ack_o"] == 1)
    check("Phase 4: queue_count=9", out["queue_count"] == 9)
    
    # =================================================================
    # Summary
    # =================================================================
    print("\n" + "=" * 60)
    total = len(results)
    passed = sum(1 for _, ok in results if ok)
    failed = total - passed
    
    if failed > 0:
        print(f"SUMMARY: {passed}/{total} passed, {failed} FAILED")
        for name, ok in results:
            if not ok:
                print(f"  FAILED: {name}")
    else:
        print(f"SUMMARY: {passed}/{total} passed")
        print("ALL TESTS PASSED")


if __name__ == "__main__":
    run_self_test()