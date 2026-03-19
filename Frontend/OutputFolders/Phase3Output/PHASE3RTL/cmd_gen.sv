////////////////////////////////////////////////////////////////////////////////
// Module:    cmd_gen
// Generated: 2026-03-19 12:01:05
// Agent:     Command Generator Agent (Phase 3)
//
// Translates scheduler command type → DDR3 pin-level encoding.
// Output: {CS#, RAS#, CAS#, WE#} + addr + bank + CKE + reset_n
//
// Command encodings (active-low CS#=0):
//   NOP    = 4'b0111   MRS  = 4'b0000   REF  = 4'b0001
//   PRE    = 4'b0010   ACT  = 4'b0011   WR   = 4'b0100
//   RD     = 4'b0101   ZQCL = 4'b0110   DESL = 4'b1111
////////////////////////////////////////////////////////////////////////////////

module cmd_gen #(
    parameter DDR_ADDR_W = 15,
    parameter DDR_BANK_W = 3,
    parameter ROW_BITS   = 15,
    parameter COL_BITS   = 10,
    parameter BANK_BITS  = 3,
    parameter AUX_WIDTH  = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── From scheduler ──
    input  logic                    sched_valid,
    input  logic [3:0]              sched_type,     // CMD_ACT/RD/WR/PRE/REF/NOP
    input  logic [ROW_BITS-1:0]     sched_row,
    input  logic [COL_BITS-1:0]     sched_col,
    input  logic [BANK_BITS-1:0]    sched_bank,
    input  logic                    sched_we,
    input  logic [AUX_WIDTH-1:0]    sched_aux,

    // ── DDR3 pin-level outputs ──
    output logic [3:0]              ddr_cmd,        // {CS#,RAS#,CAS#,WE#}
    output logic [DDR_ADDR_W-1:0]   ddr_addr,
    output logic [DDR_BANK_W-1:0]   ddr_bank,
    output logic                    ddr_cke,
    output logic                    ddr_reset_n,
    output logic                    ddr_odt,

    // ── Feedback to bank_tracker ──
    output logic                    fb_act_valid,
    output logic [BANK_BITS-1:0]    fb_act_bank,
    output logic [ROW_BITS-1:0]     fb_act_row,
    output logic                    fb_pre_valid,
    output logic [BANK_BITS-1:0]    fb_pre_bank,
    output logic                    fb_pre_all,
    output logic                    fb_rd_valid,
    output logic [BANK_BITS-1:0]    fb_rd_bank,
    output logic                    fb_wr_valid,
    output logic [BANK_BITS-1:0]    fb_wr_bank,
    output logic                    fb_ref_valid,

    // ── Aux passthrough (to data path) ──
    output logic                    cmd_out_valid,
    output logic                    cmd_out_we,
    output logic [AUX_WIDTH-1:0]    cmd_out_aux
);

    // Scheduler command type encoding (must match scheduler)
    localparam SCMD_NOP = 4'd0;
    localparam SCMD_ACT = 4'd1;
    localparam SCMD_RD  = 4'd2;
    localparam SCMD_WR  = 4'd3;
    localparam SCMD_PRE = 4'd4;
    localparam SCMD_REF = 4'd5;

    // DDR3 command encodings {CS#, RAS#, CAS#, WE#}
    localparam DDR_NOP  = 4'b0111;
    localparam DDR_MRS  = 4'b0000;
    localparam DDR_REF  = 4'b0001;
    localparam DDR_PRE  = 4'b0010;
    localparam DDR_ACT  = 4'b0011;
    localparam DDR_WR   = 4'b0100;
    localparam DDR_RD   = 4'b0101;
    localparam DDR_DESL = 4'b1111;

    // ════════════════════════════════════════════════════
    // Command encoding
    // ════════════════════════════════════════════════════
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ddr_cmd      <= DDR_NOP;
            ddr_addr     <= '0;
            ddr_bank     <= '0;
            ddr_cke      <= 1'b1;   // CKE high during normal operation
            ddr_reset_n  <= 1'b1;
            ddr_odt      <= 1'b0;
            fb_act_valid <= 1'b0;
            fb_pre_valid <= 1'b0;
            fb_rd_valid  <= 1'b0;
            fb_wr_valid  <= 1'b0;
            fb_ref_valid <= 1'b0;
            fb_pre_all   <= 1'b0;
            fb_act_bank  <= '0;
            fb_act_row   <= '0;
            fb_pre_bank  <= '0;
            fb_rd_bank   <= '0;
            fb_wr_bank   <= '0;
            cmd_out_valid<= 1'b0;
            cmd_out_we   <= 1'b0;
            cmd_out_aux  <= '0;
        end else begin
            // Default: NOP, all feedback deasserted
            ddr_cmd      <= DDR_NOP;
            ddr_addr     <= '0;
            ddr_bank     <= '0;
            ddr_odt      <= 1'b0;
            fb_act_valid <= 1'b0;
            fb_pre_valid <= 1'b0;
            fb_rd_valid  <= 1'b0;
            fb_wr_valid  <= 1'b0;
            fb_ref_valid <= 1'b0;
            fb_pre_all   <= 1'b0;
            cmd_out_valid<= 1'b0;

            if (sched_valid) begin
                case (sched_type)
                    SCMD_ACT: begin
                        ddr_cmd      <= DDR_ACT;
                        ddr_addr     <= sched_row[DDR_ADDR_W-1:0];
                        ddr_bank     <= sched_bank;
                        fb_act_valid <= 1'b1;
                        fb_act_bank  <= sched_bank;
                        fb_act_row   <= sched_row;
                    end
                    SCMD_RD: begin
                        ddr_cmd      <= DDR_RD;
                        // Column address: col in lower bits, A10=0 (no auto-precharge)
                        ddr_addr     <= {{DDR_ADDR_W-COL_BITS{1'b0}}, sched_col};
                        ddr_bank     <= sched_bank;
                        fb_rd_valid  <= 1'b1;
                        fb_rd_bank   <= sched_bank;
                        cmd_out_valid<= 1'b1;
                        cmd_out_we   <= 1'b0;
                        cmd_out_aux  <= sched_aux;
                    end
                    SCMD_WR: begin
                        ddr_cmd      <= DDR_WR;
                        ddr_addr     <= {{DDR_ADDR_W-COL_BITS{1'b0}}, sched_col};
                        ddr_bank     <= sched_bank;
                        ddr_odt      <= 1'b1;  // ODT on for writes
                        fb_wr_valid  <= 1'b1;
                        fb_wr_bank   <= sched_bank;
                        cmd_out_valid<= 1'b1;
                        cmd_out_we   <= 1'b1;
                        cmd_out_aux  <= sched_aux;
                    end
                    SCMD_PRE: begin
                        ddr_cmd      <= DDR_PRE;
                        ddr_addr[10] <= 1'b0;  // A10=0 → single bank precharge
                        ddr_bank     <= sched_bank;
                        fb_pre_valid <= 1'b1;
                        fb_pre_bank  <= sched_bank;
                        fb_pre_all   <= 1'b0;
                    end
                    SCMD_REF: begin
                        ddr_cmd      <= DDR_REF;
                        fb_ref_valid <= 1'b1;
                    end
                    default: begin
                        ddr_cmd <= DDR_NOP;
                    end
                endcase
            end
        end
    end

endmodule
