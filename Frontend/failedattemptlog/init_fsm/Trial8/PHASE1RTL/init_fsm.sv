module init_fsm (
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

    parameter DDR_ADDR_W = 15;
    localparam DDR_BANK_W = 3;

    localparam WAIT_RESET   = 40000;
    localparam WAIT_CKE     = 100000;
    localparam WAIT_TXPR    = 34;
    localparam WAIT_ZQCL    = 128;

    localparam [14:0] MR0_VAL = 15'h1D34;
    localparam [14:0] MR1_VAL = 15'h0004;
    localparam [14:0] MR2_VAL = 15'h0218;
    localparam [14:0] MR3_VAL = 15'h0000;

    localparam [3:0] CMD_MRS  = 4'b0000;
    localparam [3:0] CMD_ZQCL = 4'b0110;
    localparam [3:0] CMD_NOP  = 4'b0111;
    localparam [3:0] CMD_DES  = 4'b1111;

    typedef enum logic [3:0] {
        S_IDLE       = 4'd0,
        S_RESET_LOW  = 4'd1,
        S_RESET_HIGH = 4'd2,
        S_TXPR_WAIT  = 4'd3,
        S_MR2        = 4'd4,
        S_MR3        = 4'd5,
        S_MR1        = 4'd6,
        S_MR0        = 4'd7,
        S_ZQCL       = 4'd8,
        S_ZQCL_WAIT  = 4'd9,
        S_DONE       = 4'd14
    } state_t;

    state_t state, next_state;
    logic [16:0] counter, next_counter;

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE;
            counter <= 17'd0;
        end else begin
            state <= next_state;
            counter <= next_counter;
        end
    end

    // Next state logic
    always_comb begin
        next_state = state;
        next_counter = counter;

        case (state)
            S_IDLE: begin
                if (enable) begin
                    next_state = S_RESET_LOW;
                    next_counter = 17'd0;
                end
            end

            S_RESET_LOW: begin
                if (counter == (WAIT_RESET - 1)) begin
                    next_state = S_RESET_HIGH;
                    next_counter = 17'd0;
                end else begin
                    next_counter = counter + 17'd1;
                end
            end

            S_RESET_HIGH: begin
                if (counter == (WAIT_CKE - 1)) begin
                    next_state = S_TXPR_WAIT;
                    next_counter = 17'd0;
                end else begin
                    next_counter = counter + 17'd1;
                end
            end

            S_TXPR_WAIT: begin
                if (counter == (WAIT_TXPR - 1)) begin
                    next_state = S_MR2;
                    next_counter = 17'd0;
                end else begin
                    next_counter = counter + 17'd1;
                end
            end

            S_MR2: begin
                next_state = S_MR3;
                next_counter = 17'd0;
            end

            S_MR3: begin
                next_state = S_MR1;
                next_counter = 17'd0;
            end

            S_MR1: begin
                next_state = S_MR0;
                next_counter = 17'd0;
            end

            S_MR0: begin
                next_state = S_ZQCL;
                next_counter = 17'd0;
            end

            S_ZQCL: begin
                next_state = S_ZQCL_WAIT;
                next_counter = 17'd0;
            end

            S_ZQCL_WAIT: begin
                if (counter == (WAIT_ZQCL - 1)) begin
                    next_state = S_DONE;
                    next_counter = 17'd0;
                end else begin
                    next_counter = counter + 17'd1;
                end
            end

            S_DONE: begin
                next_state = S_DONE;
                next_counter = 17'd0;
            end

            default: begin
                next_state = S_IDLE;
                next_counter = 17'd0;
            end
        endcase
    end

    // Combinational outputs
    always_comb begin
        init_cmd_valid = 1'b0;
        init_cmd = CMD_NOP;
        init_addr = {DDR_ADDR_W{1'b0}};
        init_bank = 3'd0;
        init_cke = 1'b0;
        init_reset_n = 1'b0;
        init_done = 1'b0;
        init_fail = 1'b0;
        init_state = state;

        case (state)
            S_IDLE: begin
                init_reset_n = 1'b0;
                init_cke = 1'b0;
            end

            S_RESET_LOW: begin
                init_reset_n = 1'b0;
                init_cke = 1'b0;
            end

            S_RESET_HIGH: begin
                init_reset_n = 1'b1;
                init_cke = 1'b0;
            end

            S_TXPR_WAIT: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
            end

            S_MR2: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd = CMD_MRS;
                init_addr = MR2_VAL;
                init_bank = 3'd2;
            end

            S_MR3: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd = CMD_MRS;
                init_addr = MR3_VAL;
                init_bank = 3'd3;
            end

            S_MR1: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd = CMD_MRS;
                init_addr = MR1_VAL;
                init_bank = 3'd1;
            end

            S_MR0: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd = CMD_MRS;
                init_addr = MR0_VAL;
                init_bank = 3'd0;
            end

            S_ZQCL: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd = CMD_ZQCL;
                init_addr = 15'h0400;
                init_bank = 3'd0;
            end

            S_ZQCL_WAIT: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
            end

            S_DONE: begin
                init_reset_n = 1'b1;
                init_cke = 1'b1;
                init_done = 1'b1;
            end

            default: begin
                init_reset_n = 1'b0;
                init_cke = 1'b0;
            end
        endcase
    end

endmodule
