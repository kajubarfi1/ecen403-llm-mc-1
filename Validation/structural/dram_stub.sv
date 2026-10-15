`timescale 1ns/1ps
// dram_stub.sv — minimal DRAM behavioral model for the integration harness.
//
// The chain harness needs something on the far side of the DDR pins, or
// every read returns the tied-off bus. This is the smallest honest model of
// the drop's abstract pin protocol (controller-domain, one dq bus, level
// dqs; spec phy_interface.mode = abstract):
//
//   ACT  opens a row per bank (ddr_addr carries the row)
//   WR   after CWL the data path drives dq for BURST_CTRL_CYC cycles, one
//        beat per cycle (host_width / channel_width beats, low half first);
//        the stub stores every beat at {bank, open row, column}
//   RD   ceil(CL / CLK_RATIO) controller cycles after the cycle in which it
//        samples the RD, the stub drives the stored beats back in order on
//        dq_i, one per cycle, with dqs_i high for the burst
//
// The read timing is derived from JEDEC CL and the clock ratio, never from
// the design's own counters: a stub tuned to the DUT's capture window hides
// exactly the defect it should expose. (Until 2026-10-15 it was: "+1 because
// the data path registers the rd command one cycle later" — a fudge from an
// older drop — and it stored one word per burst with both beats identical,
// so every read-after-write returned the low beat twice and the design's
// one-cycle-early capture went unseen.)
//
// It is a testbench component, not a reference model: it never checks
// anything, and nothing judges the design against it. State lives in plain
// arrays with an absolute cycle counter (Xcelium rejects writes to queue
// elements in procedural code), sized DEPTH deep — more outstanding
// operations than that is not a traffic pattern this stub supports.
//
// Command encodings default to the DDR pin encoding declared in
// interface_catalog.json (ddr_cmd.command_encoding, catalog v1.15).

module dram_stub #(
    parameter DQ_W    = 32,
    parameter ADDR_W  = 15,
    parameter BANK_W  = 3,
    parameter BURST_CTRL_CYC = 2,   // beats per burst (host_width / channel_width)
    parameter CLK_RATIO = 4,        // DDR clocks per controller clock
    parameter DEPTH   = 16,
    parameter CMD_ACT = 4'b0011,
    parameter CMD_WR  = 4'b0100,
    parameter CMD_RD  = 4'b0101
) (
    input  logic               clk,
    input  logic               rst_n,
    input  logic [3:0]         ddr_cmd,
    input  logic [ADDR_W-1:0]  ddr_addr,
    input  logic [BANK_W-1:0]  ddr_bank,
    input  logic [DQ_W-1:0]    ddr_dq_o,
    input  logic               ddr_dq_oe,
    input  logic [7:0]         cfg_CL_nCK,
    input  logic [7:0]         cfg_CWL_nCK,
    output logic [DQ_W-1:0]    ddr_dq_i,
    output logic               ddr_dqs_i
);

  typedef logic [BANK_W+ADDR_W+ADDR_W-1:0] key_t;
  typedef logic [BURST_CTRL_CYC*DQ_W-1:0]  burst_t;   // beat k at [k*DQ_W +: DQ_W]

  // What an unwritten location reads as. NOT zero: a read of zeros packs to
  // zeros whatever the data path does with the beats, and every read-only
  // path passed that way for a month (path_02/03, 2026-10-15). A pattern
  // derived from the address, different in every beat, makes the assembly
  // of beats into a host word visible on every read.
  function automatic burst_t unwritten(input key_t k);
    burst_t b;
    for (int i = 0; i < BURST_CTRL_CYC; i++)
      b[i*DQ_W +: DQ_W] = DQ_W'((k >> (i * 4)) ^ {DQ_W{1'b1}} ^ (i * 16'h5A5A));
    return b;
  endfunction

  burst_t            mem [key_t];                 // sparse storage, one burst per column
  logic [ADDR_W-1:0] open_row [0:(1<<BANK_W)-1];

  int unsigned cyc;
  logic oe_q;

  // pending writes: addresses issued but whose data burst has not started
  key_t        wq [0:DEPTH-1];
  int unsigned wq_head, wq_tail;

  // the write burst being captured: its key and the next beat index
  key_t        wkey;
  int unsigned widx;
  logic        wcap;
  burst_t      wtmp;

  // scheduled read replies: reply i drives beat (cyc - rstart[i]) on cycles
  // [rstart[i], rstart[i]+BURST_CTRL_CYC)
  logic              rvalid [0:DEPTH-1];
  int unsigned       rstart [0:DEPTH-1];
  burst_t            rdata  [0:DEPTH-1];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cyc     = 0;
      oe_q    = 1'b0;
      wq_head = 0;
      wq_tail = 0;
      widx    = 0;
      wcap    = 1'b0;
      for (int i = 0; i < DEPTH; i++) rvalid[i] = 1'b0;
    end else begin
      cyc = cyc + 1;

      if (ddr_cmd == CMD_ACT)
        open_row[ddr_bank] = ddr_addr;

      if (ddr_cmd == CMD_WR) begin
        wq[wq_tail % DEPTH] = {ddr_bank, open_row[ddr_bank], ddr_addr};
        wq_tail = wq_tail + 1;
      end

      // a write burst: beat k is on dq during the k-th cycle of dq_oe.
      // The burst belongs to the oldest WR whose data has not started.
      if (ddr_dq_oe) begin
        if (!oe_q) begin
          widx = 0;
          wcap = (wq_head != wq_tail);
          if (wcap) begin
            wkey    = wq[wq_head % DEPTH];
            wq_head = wq_head + 1;
          end
        end
        if (wcap && widx < BURST_CTRL_CYC) begin
          wtmp = mem.exists(wkey) ? mem[wkey] : '0;
          wtmp[widx*DQ_W +: DQ_W] = ddr_dq_o;
          mem[wkey] = wtmp;
          widx = widx + 1;
        end
      end
      oe_q = ddr_dq_oe;

      if (ddr_cmd == CMD_RD) begin
        for (int i = 0; i < DEPTH; i++) begin
          if (!rvalid[i]) begin
            rvalid[i] = 1'b1;
            // JEDEC: data CL nCK after the DRAM samples RD, i.e. the first
            // controller cycle at which the whole of CL has elapsed. Not the
            // design's counter (see the header).
            rstart[i] = cyc + (int'(cfg_CL_nCK) + CLK_RATIO - 1) / CLK_RATIO;
            rdata[i]  = mem.exists({ddr_bank, open_row[ddr_bank], ddr_addr})
                        ? mem[{ddr_bank, open_row[ddr_bank], ddr_addr}]
                        : unwritten({ddr_bank, open_row[ddr_bank], ddr_addr});
            break;
          end
        end
      end

      // retire replies whose window has passed
      for (int i = 0; i < DEPTH; i++)
        if (rvalid[i] && cyc >= rstart[i] + BURST_CTRL_CYC)
          rvalid[i] = 1'b0;
    end
  end

  // Drive the active reply (windows are separated by the sequence's idle
  // spacing; on overlap the oldest wins).
  always_comb begin
    int unsigned best;
    logic        found;
    ddr_dq_i  = '0;
    ddr_dqs_i = 1'b0;
    found = 1'b0;
    best  = 0;
    for (int i = 0; i < DEPTH; i++) begin
      if (rvalid[i] && cyc >= rstart[i] && cyc < rstart[i] + BURST_CTRL_CYC
          && (!found || rstart[i] < rstart[best])) begin
        best  = i;
        found = 1'b1;
      end
    end
    if (found) begin
      ddr_dq_i  = rdata[best][(cyc - rstart[best])*DQ_W +: DQ_W];
      ddr_dqs_i = 1'b1;
    end
  end

endmodule
