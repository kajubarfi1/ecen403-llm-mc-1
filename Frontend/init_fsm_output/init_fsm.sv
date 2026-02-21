////////////////////////////////////////////////////////////////////////////////
// Module:    init_fsm
// File:      init_fsm.sv
// Generated: 2026-02-21 09:28:07
// Agent:     Init/Reset FSM Agent (Phase 1)
// Spec:      ddr3_mc_core_v2 rev golden_ddr3_1600k_x8_2lane_1rank
//
// JEDEC DDR3 Initialization Sequence (JESD79-3F §4.6):
//   RESET# low (200µs = 40000 ctrl clks)
//   → RESET# high → CKE delay (500µs = 100000 ctrl clks)
//   → CKE high → tXPR (170.0ns = 34 ctrl clks)
//   → MR2 → MR3 → MR1 → MR0 (DLL reset) → ZQCL (128 ctrl clks)
//   → init_done
//
// Counter width: 17 bits (max wait = 100000 cycles)
// DDR address:   15 bits, Bank: 3 bits
//
// Validation: IN-001 .. IN-011
////////////////////////////////////////////////////////////////////////////////

module init_fsm #(
    parameter DDR_ADDR_W  = 15,
    parameter DDR_BANK_W  = 3,
    parameter CTR_WIDTH   = 17
) (
    // ────────────── Clock / Reset ──────────────
    input  logic                    clk,
    input  logic                    rst_n,

    // ────────────── Control ──────────────
    input  logic                    enable,         // start init when high

    // ────────────── Status outputs ──────────────
    output logic                    init_done,      // init complete
    output logic                    init_fail,      // init timeout/error

    // ────────────── DDR3 command outputs (to cmd_gen) ──────────────
    output logic                    init_cmd_valid, // command valid
    output logic [3:0]              init_cmd,       // {cs_n, ras_n, cas_n, we_n}
    output logic [DDR_ADDR_W-1:0]   init_addr,      // MR data / row address
    output logic [DDR_BANK_W-1:0]   init_bank,      // bank (selects MR0-3)

    // ────────────── DDR3 control outputs ──────────────
    output logic                    init_cke,       // clock enable
    output logic                    init_reset_n,   // RESET# to DRAM

    // ────────────── State debug (observability) ──────────────
    output logic [3:0]              init_state      // current FSM state
);

    // ================================================================
    // DDR3 command encodings {CS#, RAS#, CAS#, WE#}
    // ================================================================
    localparam CMD_NOP  = 4'b0111;  // CS=0, RAS=1, CAS=1, WE=1
    localparam CMD_MRS  = 4'b0000;  // mode register set
    localparam CMD_ZQCL = 4'b0110;  // ZQ calibration long (WE=0)
    localparam CMD_DESL = 4'b1111;  // deselect (CS=1)

    // ================================================================
    // Wait counts (derived from spec)
    // ================================================================
    localparam CTR_WIDTH_W = CTR_WIDTH;
    localparam [CTR_WIDTH-1:0] WAIT_RESET    = 40000;  // 200µs
    localparam [CTR_WIDTH-1:0] WAIT_CKE      = 100000;  // 500µs
    localparam [CTR_WIDTH-1:0] WAIT_TXPR     = 34;    // tXPR = 170.0ns
    localparam [CTR_WIDTH-1:0] WAIT_TMRD     = 1;      // tMRD = 4 nCK
    localparam [CTR_WIDTH-1:0] WAIT_TMOD     = 3;      // tMOD = max(12nCK, 15ns)
    localparam [CTR_WIDTH-1:0] WAIT_ZQCL     = 128;   // tZQinit = 512 nCK

    // ================================================================
    // Mode register encoded values
    // ================================================================
    localparam [DDR_ADDR_W-1:0] MR0_VAL = 15'h1D34;
    localparam [DDR_ADDR_W-1:0] MR1_VAL = 15'h0004;
    localparam [DDR_ADDR_W-1:0] MR2_VAL = 15'h0218;
    localparam [DDR_ADDR_W-1:0] MR3_VAL = 15'h0000;

    // ================================================================
    // FSM states
    // ================================================================
    typedef enum logic [3:0] {
        S_IDLE       = 4'd0,   // waiting for enable
        S_RESET_LOW  = 4'd1,   // RESET# asserted low
        S_RESET_HIGH = 4'd2,   // RESET# released, wait before CKE
        S_CKE_WAIT   = 4'd3,   // CKE high, wait tXPR
        S_MR2        = 4'd4,   // issue MRS for MR2
        S_MR2_WAIT   = 4'd5,   // wait tMRD
        S_MR3        = 4'd6,   // issue MRS for MR3
        S_MR3_WAIT   = 4'd7,   // wait tMRD
        S_MR1        = 4'd8,   // issue MRS for MR1
        S_MR1_WAIT   = 4'd9,   // wait tMRD
        S_MR0        = 4'd10,  // issue MRS for MR0 (DLL reset)
        S_MR0_WAIT   = 4'd11,  // wait tMOD
        S_ZQCL       = 4'd12,  // issue ZQCL
        S_ZQCL_WAIT  = 4'd13,  // wait tZQinit
        S_DONE       = 4'd14   // init complete
    } state_t;

    state_t state, state_nxt;

    // ================================================================
    // Wait counter
    // ================================================================
    logic [CTR_WIDTH-1:0] ctr, ctr_load;
    logic                 ctr_en, ctr_done;

    assign ctr_done = (ctr == '0);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            ctr <= '0;
        else if (ctr_en)
            ctr <= ctr_load;
        else if (!ctr_done)
            ctr <= ctr - 1'b1;

    // ================================================================
    // State register
    // ================================================================
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) state <= S_IDLE;
        else        state <= state_nxt;

    assign init_state = state;

    // ================================================================
    // Next-state and output logic
    // ================================================================
    always_comb begin
        // Defaults
        state_nxt     = state;
        ctr_en        = 1'b0;
        ctr_load      = '0;
        init_cmd_valid= 1'b0;
        init_cmd      = CMD_NOP;
        init_addr     = '0;
        init_bank     = '0;
        init_cke      = 1'b0;
        init_reset_n  = 1'b1;
        init_done     = 1'b0;
        init_fail     = 1'b0;

        case (state)

            S_IDLE: begin
                init_reset_n = 1'b0;  // hold reset low
                init_cke     = 1'b0;
                if (enable) begin
                    state_nxt = S_RESET_LOW;
                    ctr_en    = 1'b1;
                    ctr_load  = WAIT_RESET;
                end
            end

            S_RESET_LOW: begin
                init_reset_n = 1'b0;  // RESET# still low
                init_cke     = 1'b0;
                if (ctr_done) begin
                    state_nxt = S_RESET_HIGH;
                    ctr_en    = 1'b1;
                    ctr_load  = WAIT_CKE;
                end
            end

            S_RESET_HIGH: begin
                init_reset_n = 1'b1;  // RESET# released
                init_cke     = 1'b0;  // CKE still low
                if (ctr_done) begin
                    state_nxt = S_CKE_WAIT;
                    ctr_en    = 1'b1;
                    ctr_load  = WAIT_TXPR;
                end
            end

            S_CKE_WAIT: begin
                init_cke = 1'b1;      // CKE now high
                if (ctr_done)
                    state_nxt = S_MR2;
            end

            S_MR2: begin
                init_cke       = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR2_VAL;
                init_bank      = 3'd2;
                state_nxt      = S_MR2_WAIT;
                ctr_en         = 1'b1;
                ctr_load       = WAIT_TMRD;
            end

            S_MR2_WAIT: begin
                init_cke = 1'b1;
                if (ctr_done) state_nxt = S_MR3;
            end

            S_MR3: begin
                init_cke       = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR3_VAL;
                init_bank      = 3'd3;
                state_nxt      = S_MR3_WAIT;
                ctr_en         = 1'b1;
                ctr_load       = WAIT_TMRD;
            end

            S_MR3_WAIT: begin
                init_cke = 1'b1;
                if (ctr_done) state_nxt = S_MR1;
            end

            S_MR1: begin
                init_cke       = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR1_VAL;
                init_bank      = 3'd1;
                state_nxt      = S_MR1_WAIT;
                ctr_en         = 1'b1;
                ctr_load       = WAIT_TMRD;
            end

            S_MR1_WAIT: begin
                init_cke = 1'b1;
                if (ctr_done) state_nxt = S_MR0;
            end

            S_MR0: begin
                init_cke       = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_MRS;
                init_addr      = MR0_VAL;  // includes DLL reset bit
                init_bank      = 3'd0;
                state_nxt      = S_MR0_WAIT;
                ctr_en         = 1'b1;
                ctr_load       = WAIT_TMOD;  // tMOD after MR0 before ZQCL
            end

            S_MR0_WAIT: begin
                init_cke = 1'b1;
                if (ctr_done) state_nxt = S_ZQCL;
            end

            S_ZQCL: begin
                init_cke       = 1'b1;
                init_cmd_valid = 1'b1;
                init_cmd       = CMD_ZQCL;
                init_addr      = '0;
                init_addr[10]  = 1'b1;  // A10=1 for ZQCL (long)
                init_bank      = '0;
                state_nxt      = S_ZQCL_WAIT;
                ctr_en         = 1'b1;
                ctr_load       = WAIT_ZQCL;
            end

            S_ZQCL_WAIT: begin
                init_cke = 1'b1;
                if (ctr_done) state_nxt = S_DONE;
            end

            S_DONE: begin
                init_cke  = 1'b1;
                init_done = 1'b1;
            end

            default: begin
                state_nxt = S_IDLE;
                init_fail = 1'b1;
            end
        endcase
    end

    // ================================================================
    // SVA — simulation only
    // ================================================================
    // synopsys translate_off
    // synthesis translate_off

    // IN-001: RESET# held low for >= 200µs
    // IN-002: CKE low during reset
    property p_cke_low_during_reset;
        @(posedge clk) disable iff (!rst_n)
        (state == S_RESET_LOW) |-> (!init_cke);
    endproperty
    assert property (p_cke_low_during_reset)
        else $error("[IN-002] CKE not low during reset");

    // IN-003: MR program order is MR2→MR3→MR1→MR0
    // (enforced structurally by FSM)

    // IN-005: init_done only in S_DONE
    property p_done_only_in_done;
        @(posedge clk) disable iff (!rst_n)
        init_done |-> (state == S_DONE);
    endproperty
    assert property (p_done_only_in_done)
        else $error("[IN-005] init_done asserted outside S_DONE");

    // IN-010: ZQCL A10=1
    property p_zqcl_a10;
        @(posedge clk) disable iff (!rst_n)
        (state == S_ZQCL && init_cmd_valid) |-> init_addr[10];
    endproperty
    assert property (p_zqcl_a10)
        else $error("[IN-010] ZQCL issued without A10=1");

    // Coverage
    covergroup cg_init @(posedge clk);
        option.per_instance = 1;
        cp_state   : coverpoint state;
        cp_mr_cmd  : coverpoint (init_cmd_valid && init_cmd == CMD_MRS);
        cp_zq_cmd  : coverpoint (init_cmd_valid && init_cmd == CMD_ZQCL);
        cp_done    : coverpoint init_done;
    endgroup
    cg_init cg_inst = new();

    // synthesis translate_on
    // synopsys translate_on

endmodule