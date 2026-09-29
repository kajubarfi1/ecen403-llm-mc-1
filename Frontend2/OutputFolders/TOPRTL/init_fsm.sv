module init_fsm #(
    parameter int DDR_ADDR_W = 15,
    parameter int DDR_BANK_W = 3,
    parameter int CTR_WIDTH  = 17
) (
    input  logic                    clk,
    input  logic                    rst_n,            // active-low async reset
    input  logic                    enable,           // start init when high
    output logic                    init_done,
    output logic                    init_fail,
    output logic                    init_cmd_valid,
    output logic [3:0]              init_cmd,         // {cs_n, ras_n, cas_n, we_n}
    output logic [DDR_ADDR_W-1:0]   init_addr,        // MR data / row address
    output logic [DDR_BANK_W-1:0]   init_bank,        // MR select for MRS commands
    output logic                    init_cke,
    output logic                    init_reset_n,
    output logic [3:0]              init_state        // for debug
);

    localparam WAIT_RESET = 40000;
    localparam WAIT_CKE   = 100000;
    localparam WAIT_TXPR  = 34;
    localparam WAIT_ZQCL  = 128;

    localparam [DDR_ADDR_W-1:0] MR0_VAL   = 15'h1D34;
    localparam [DDR_ADDR_W-1:0] MR1_VAL   = 15'h0004;
    localparam [DDR_ADDR_W-1:0] MR2_VAL   = 15'h0218;
    localparam [DDR_ADDR_W-1:0] MR3_VAL   = 15'h0000;
    localparam [DDR_ADDR_W-1:0] ZQCL_ADDR = 15'h0400;  // A10=1, long calibration

    localparam logic [3:0] CMD_MRS  = 4'b0000;
    localparam logic [3:0] CMD_ZQCL = 4'b0110;  // ZQCL
    localparam logic [3:0] CMD_NOP  = 4'b0111;

    typedef enum logic [3:0] {
        S_IDLE       = 4'd0,   // before enable; init_reset_n=0, init_cke=0
        S_RESET_LOW  = 4'd1,   // RESET# low for WAIT_RESET cycles
        S_RESET_HIGH = 4'd2,   // RESET# high, CKE low, for WAIT_CKE cycles
        S_TXPR_WAIT  = 4'd3,   // CKE high, wait WAIT_TXPR cycles
        S_MR2        = 4'd4,
        S_MR3        = 4'd5,
        S_MR1        = 4'd6,
        S_MR0        = 4'd7,
        S_ZQCL       = 4'd8,
        S_ZQCL_WAIT  = 4'd9,   // wait WAIT_ZQCL cycles
        S_DONE       = 4'd14  // init_done asserted ONLY here
    } state_t;

    state_t state, next_state;
    logic [CTR_WIDTH-1:0] wait_cnt;

    // State register
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= S_IDLE;
        else        state <= next_state;

    // Wait counter: resets to 0 on every state change, counts cycles spent
    // in the current state (0 .. WAIT_N-1 -- WAIT_N cycles total).
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) wait_cnt <= '0;
        else if (state != next_state) wait_cnt <= '0;
        else wait_cnt <= wait_cnt + 1'b1;

    // Next-state logic
    always_comb begin
        next_state = state;
        case (state)
            S_IDLE:       next_state = enable ? S_RESET_LOW : S_IDLE;
            S_RESET_LOW:  next_state = (wait_cnt == WAIT_RESET-1) ? S_RESET_HIGH : S_RESET_LOW;
            S_RESET_HIGH: next_state = (wait_cnt == WAIT_CKE-1)   ? S_TXPR_WAIT  : S_RESET_HIGH;
            S_TXPR_WAIT:  next_state = (wait_cnt == WAIT_TXPR-1)  ? S_MR2        : S_TXPR_WAIT;
            S_MR2:        next_state = S_MR3;
            S_MR3:        next_state = S_MR1;
            S_MR1:        next_state = S_MR0;
            S_MR0:        next_state = S_ZQCL;
            S_ZQCL:       next_state = S_ZQCL_WAIT;
            S_ZQCL_WAIT:  next_state = (wait_cnt == WAIT_ZQCL-1)  ? S_DONE : S_ZQCL_WAIT;
            S_DONE:       next_state = S_DONE;
            default:      next_state = S_IDLE;
        endcase
    end

    // Combinational command outputs -- high ONLY in the 5 command states,
    // never registered (registering would bleed one cycle into the next
    // wait state).
    always_comb begin
        init_cmd_valid = 1'b0;
        init_cmd  = CMD_NOP;
        init_addr = '0;
        init_bank = '0;
        case (state)
            S_MR2:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR2_VAL;   init_bank = 2; end
            S_MR3:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR3_VAL;   init_bank = 3; end
            S_MR1:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR1_VAL;   init_bank = 1; end
            S_MR0:  begin init_cmd_valid = 1'b1; init_cmd = CMD_MRS;  init_addr = MR0_VAL;   init_bank = 0; end
            S_ZQCL: begin init_cmd_valid = 1'b1; init_cmd = CMD_ZQCL; init_addr = ZQCL_ADDR; init_bank = '0; end
            default: ;
        endcase
    end

    assign init_reset_n = !(state == S_IDLE || state == S_RESET_LOW);
    assign init_cke     = !(state == S_IDLE || state == S_RESET_LOW || state == S_RESET_HIGH);
    assign init_done    = (state == S_DONE);
    assign init_fail    = 1'b0;
    assign init_state   = state;

endmodule
