module init_fsm #(
  parameter DDR_ADDR_W = 15,
  parameter DDR_BANK_W = 3
) (
  input  logic                    clk,
  input  logic                    rst_n,
  input  logic                    enable,
  output logic                    init_done,
  output logic                    init_fail,
  output logic                    init_cmd_valid,
  output logic [3:0]              init_cmd,
  output logic [DDR_ADDR_W-1:0]   init_addr,
  output logic [DDR_BANK_W-1:0]   init_bank,
  output logic                    init_cke,
  output logic                    init_reset_n,
  output logic [3:0]              init_state
);

  // Wait count parameters
  localparam WAIT_RESET = 40000;
  localparam WAIT_CKE   = 100000;
  localparam WAIT_TXPR  = 34;
  localparam WAIT_ZQCL  = 128;

  // Mode register values
  localparam [14:0] MR0_VAL = 15'h1D34;
  localparam [14:0] MR1_VAL = 15'h0004;
  localparam [14:0] MR2_VAL = 15'h0218;
  localparam [14:0] MR3_VAL = 15'h0000;

  // DDR3 command encodings
  localparam [3:0] CMD_MRS  = 4'b0000;
  localparam [3:0] CMD_ZQCL = 4'b0110;
  localparam [3:0] CMD_NOP  = 4'b0111;
  localparam [3:0] CMD_DES  = 4'b1111;

  // FSM states (order matters per spec)
  typedef enum logic [3:0] {
    S_RESET      = 4'd0,
    S_CKE_WAIT   = 4'd1,
    S_TXPR_WAIT  = 4'd2,
    S_MR2        = 4'd3,
    S_MR3        = 4'd4,
    S_MR1        = 4'd5,
    S_MR0        = 4'd6,
    S_ZQCL       = 4'd7,
    S_ZQCL_WAIT  = 4'd8,
    S_DONE       = 4'd9
  } state_t;

  state_t state, next_state;
  logic [16:0] counter, next_counter;

  // Sequential logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state   <= S_RESET;
      counter <= 17'd0;
    end else begin
      state   <= next_state;
      counter <= next_counter;
    end
  end

  // Next state and counter logic
  always_comb begin
    next_state   = state;
    next_counter = counter;

    case (state)
      S_RESET: begin
        if (enable) begin
          if (counter < WAIT_RESET - 1) begin
            next_counter = counter + 17'd1;
          end else begin
            next_state   = S_CKE_WAIT;
            next_counter = 17'd0;
          end
        end else begin
          next_counter = 17'd0;
        end
      end

      S_CKE_WAIT: begin
        if (counter < WAIT_CKE - 1) begin
          next_counter = counter + 17'd1;
        end else begin
          next_state   = S_TXPR_WAIT;
          next_counter = 17'd0;
        end
      end

      S_TXPR_WAIT: begin
        if (counter < WAIT_TXPR - 1) begin
          next_counter = counter + 17'd1;
        end else begin
          next_state   = S_MR2;
          next_counter = 17'd0;
        end
      end

      S_MR2: begin
        next_state   = S_MR3;
        next_counter = 17'd0;
      end

      S_MR3: begin
        next_state   = S_MR1;
        next_counter = 17'd0;
      end

      S_MR1: begin
        next_state   = S_MR0;
        next_counter = 17'd0;
      end

      S_MR0: begin
        next_state   = S_ZQCL;
        next_counter = 17'd0;
      end

      S_ZQCL: begin
        next_state   = S_ZQCL_WAIT;
        next_counter = 17'd0;
      end

      S_ZQCL_WAIT: begin
        if (counter < WAIT_ZQCL - 1) begin
          next_counter = counter + 17'd1;
        end else begin
          next_state   = S_DONE;
          next_counter = 17'd0;
        end
      end

      S_DONE: begin
        next_state   = S_DONE;
        next_counter = 17'd0;
      end

      default: begin
        next_state   = S_RESET;
        next_counter = 17'd0;
      end
    endcase
  end

  // Output logic
  always_comb begin
    // Defaults
    init_done       = 1'b0;
    init_fail       = 1'b0;
    init_cmd_valid  = 1'b0;
    init_cmd        = CMD_NOP;
    init_addr       = '0;
    init_bank       = '0;
    init_cke        = 1'b0;
    init_reset_n    = 1'b0;
    init_state      = state;

    case (state)
      S_RESET: begin
        init_reset_n = 1'b0;
        init_cke     = 1'b0;
      end

      S_CKE_WAIT: begin
        init_reset_n = 1'b1;
        init_cke     = 1'b0;
      end

      S_TXPR_WAIT: begin
        init_reset_n = 1'b1;
        init_cke     = 1'b1;
      end

      S_MR2: begin
        init_reset_n   = 1'b1;
        init_cke       = 1'b1;
        init_cmd_valid = 1'b1;
        init_cmd       = CMD_MRS;
        init_addr      = MR2_VAL;
        init_bank      = 3'd2;
      end

      S_MR3: begin
        init_reset_n   = 1'b1;
        init_cke       = 1'b1;
        init_cmd_valid = 1'b1;
        init_cmd       = CMD_MRS;
        init_addr      = MR3_VAL;
        init_bank      = 3'd3;
      end

      S_MR1: begin
        init_reset_n   = 1'b1;
        init_cke       = 1'b1;
        init_cmd_valid = 1'b1;
        init_cmd       = CMD_MRS;
        init_addr      = MR1_VAL;
        init_bank      = 3'd1;
      end

      S_MR0: begin
        init_reset_n   = 1'b1;
        init_cke       = 1'b1;
        init_cmd_valid = 1'b1;
        init_cmd       = CMD_MRS;
        init_addr      = MR0_VAL;
        init_bank      = 3'd0;
      end

      S_ZQCL: begin
        init_reset_n   = 1'b1;
        init_cke       = 1'b1;
        init_cmd_valid = 1'b1;
        init_cmd       = CMD_ZQCL;
        init_addr      = 15'h0400;  // A10 = 1 for ZQCL
        init_bank      = 3'd0;
      end

      S_ZQCL_WAIT: begin
        init_reset_n = 1'b1;
        init_cke     = 1'b1;
      end

      S_DONE: begin
        init_reset_n = 1'b1;
        init_cke     = 1'b1;
        init_done    = 1'b1;
      end

      default: begin
        init_reset_n = 1'b0;
        init_cke     = 1'b0;
      end
    endcase
  end

endmodule
