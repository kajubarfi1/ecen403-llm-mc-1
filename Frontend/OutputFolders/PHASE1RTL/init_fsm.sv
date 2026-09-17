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

    // Wait cycle counts
    localparam WAIT_RESET   = 40000;
    localparam WAIT_CKE     = 100000;
    localparam WAIT_TXPR    = 34;
    localparam WAIT_ZQCL    = 128;

    // Mode register values
    localparam [14:0] MR0_VAL = 15'h1D34;
    localparam [14:0] MR1_VAL = 15'h0004;
    localparam [14:0] MR2_VAL = 15'h0218;
    localparam [14:0] MR3_VAL = 15'h0000;

    // Command encodings
    localparam [3:0] CMD_MRS  = 4'b0000;
    localparam [3:0] CMD_ZQCL = 4'b0110;
    localparam [3:0] CMD_NOP  = 4'b0111;
    localparam [3:0] CMD_DES  = 4'b1111;

    // FSM state encoding
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
        S_DONE       = 4'd14   // init_done asserted ONLY here
    } state_t;

    state_t state, next_state;
    logic [CTR_WIDTH-1:0] counter, next_counter;

    // Sequential logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= S_IDLE;
            counter <= '0;
        end else begin
            state   <= next_state;
            counter <= next_counter;
        end
    end

    // Next state logic
    always_comb begin
        next_state   = state;
        next_counter = counter;

        case (state)
            S_IDLE: begin
                next_counter = '0;
                if (enable) begin
                    next_state = S_RESET_LOW;
                end
            end

            S_RESET_LOW: begin
                if (counter == (WAIT_RESET - 1)) begin
                    next_state   = S_RESET_HIGH;
                    next_counter = '0;
                end else begin
                    next_counter = counter + 1'b1;
                end
            end

            S_RESET_HIGH: begin
                if (counter == (WAIT_CKE - 1)) begin
                    next_state   = S_TXPR_WAIT;
                    next_counter = '0;
                end else begin
                    next_counter = counter + 1'b1;
                end
            end

            S_TXPR_WAIT: begin
                if (counter == (WAIT_TXPR - 1)) begin
                    next_state   = S_MR2;
                    next_counter = '0;
                end else begin
                    next_counter = counter + 1'b1;
                end
            end

            S_MR2: begin
                next_state   = S_MR3;
                next_counter = '0;
            end

            S_MR3: begin
                next_state   = S_MR1;
                next_counter = '0;
            end

            S_MR1: begin
                next_state   = S_MR0;
                next_counter = '0;
            end

            S_MR0: begin
                next_state   = S_ZQCL;
                next_counter = '0;
            end

            S_ZQCL: begin
                next_state   = S_ZQCL_WAIT;
                next_counter = '0;
            end

            S_ZQCL_WAIT: begin
                if (counter == (WAIT_ZQCL - 1)) begin
                    next_state   = S_DONE;
                    next_counter = '0;
                end else begin
                    next_counter = counter + 1'b1;
                end
            end

            S_DONE: begin
                next_state = S_DONE;
                next_counter = '0;
            end

            default: begin
                next_state   = S_IDLE;
                next_counter = '0;
            end
        endcase
    end

    // Output logic - combinational
    always_comb begin
        // Defaults
        init_cmd_valid = 1'b0;
        init_cmd       = CMD_NOP;
        init_addr      = '0;
        init_bank      = '0;
        init_cke       = 1'b0;
        init_reset_n   = 1'b0;
        init_done      = 1'b0;
        init_fail      = 1'b0;
        init_state     = state;

        // init_reset_n: low in S_IDLE and S_RESET_LOW, high otherwise
        if (state != S_IDLE && state != S_RESET_LOW) begin
            init_reset_n = 1'b1;
        end

        // init_cke: low in S_IDLE, S_RESET_LOW, S_RESET_HIGH; high from S_TXPR_WAIT onward
        if (state != S_IDLE && state != S_RESET_LOW && state != S_RESET_HIGH) begin
            init_cke = 1'b1;
        end

        // State-specific outputs
        case (state)
            S_MR2: begin
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR2_VAL;
                init_bank      = 3'd2;
            end

            S_MR3: begin
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR3_VAL;
                init_bank      = 3'd3;
            end

            S_MR1: begin
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR1_VAL;
                init_bank      = 3'd1;
            end

            S_MR0: begin
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR0_VAL;
                init_bank      = 3'd0;
            end

            S_ZQCL: begin
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_ZQCL;
                init_addr      = 15'h0400;  // A10=1 for ZQCL
                init_bank      = 3'd0;
            end

            S_DONE: begin
                init_done = 1'b1;
            end

            default: begin
                // All outputs already set to defaults
            end
        endcase
    end

endmodule
