`timescale 1ns/1ps
// dram_stub.sv — minimal DRAM behavioral model for the integration harness.
//
// The chain harness needs something on the far side of the DDR pins, or
// every read returns the tied-off bus. This is the smallest honest model of
// the current drop's simplified pin protocol (controller-domain, one dq bus,
// level dqs):
//
//   ACT  opens a row per bank (ddr_addr carries the row)
//   WR   after CWL controller cycles the data path drives dq for
//        BURST_CTRL_CYC cycles with ONE word (both beats identical); the
//        stub stores that word at {bank, open row, column}
//   RD   after CL controller cycles the stub drives the stored word on
//        dq_i and raises dqs_i for BURST_CTRL_CYC cycles
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
    parameter BURST_CTRL_CYC = 2,
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

  logic [DQ_W-1:0]   mem [key_t];                 // sparse storage
  logic [ADDR_W-1:0] open_row [0:(1<<BANK_W)-1];

  int unsigned cyc;
  logic oe_q;

  // pending writes: addresses issued but whose data burst has not started
  key_t        wq [0:DEPTH-1];
  int unsigned wq_head, wq_tail;

  // scheduled read replies: reply i drives the bus on cycles
  // [rstart[i], rstart[i]+BURST_CTRL_CYC)
  logic              rvalid [0:DEPTH-1];
  int unsigned       rstart [0:DEPTH-1];
  logic [DQ_W-1:0]   rdata  [0:DEPTH-1];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cyc     = 0;
      oe_q    = 1'b0;
      wq_head = 0;
      wq_tail = 0;
      for (int i = 0; i < DEPTH; i++) rvalid[i] = 1'b0;
    end else begin
      cyc = cyc + 1;

      if (ddr_cmd == CMD_ACT)
        open_row[ddr_bank] = ddr_addr;

      if (ddr_cmd == CMD_WR) begin
        wq[wq_tail % DEPTH] = {ddr_bank, open_row[ddr_bank], ddr_addr};
        wq_tail = wq_tail + 1;
      end

      // first cycle of a drive burst: capture the (single) burst word
      if (ddr_dq_oe && !oe_q && wq_head != wq_tail) begin
        mem[wq[wq_head % DEPTH]] = ddr_dq_o;
        wq_head = wq_head + 1;
      end
      oe_q = ddr_dq_oe;

      if (ddr_cmd == CMD_RD) begin
        for (int i = 0; i < DEPTH; i++) begin
          if (!rvalid[i]) begin
            rvalid[i] = 1'b1;
            // The data path registers the rd command one pin-cycle later and
            // counts (CL>>2)-1 before its 2-cycle capture window; starting
            // the reply at +CL_ctrl+1 and holding BURST_CTRL_CYC covers it.
            rstart[i] = cyc + (cfg_CL_nCK >> 2) + 1;
            rdata[i]  = mem.exists({ddr_bank, open_row[ddr_bank], ddr_addr})
                        ? mem[{ddr_bank, open_row[ddr_bank], ddr_addr}]
                        : '0;
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
      ddr_dq_i  = rdata[best];
      ddr_dqs_i = 1'b1;
    end
  end

endmodule
