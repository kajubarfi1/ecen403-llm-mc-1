`timescale 1ns / 1ps
//==============================================================
// config_regs_tb.sv -- Enhanced testbench (36 tests)
// Generated: 2026-09-24 13:00:47
// Generator: config_regs_gen.py (Phase 1, deterministic script)
//==============================================================
module config_regs_tb;

    localparam real CLK_PERIOD = 5.0;
    logic clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    logic        rst_n;
    logic        csr_cyc_i, csr_stb_i, csr_we_i;
    logic [7:0]  csr_adr_i;
    logic [31:0] csr_dat_i;
    logic [3:0]  csr_sel_i;
    logic        csr_ack_o;
    logic [31:0] csr_dat_o;
    logic        csr_err_o;
    logic        sts_init_done, sts_cal_done, sts_cal_fail;
    logic        sts_bist_done, sts_bist_fail;
    logic [2:0]  sts_ref_pending_cnt;
    logic        sts_self_refresh_active;
    logic [15:0] sts_ecc_ce_count;
    logic        sts_ecc_ue_event, sts_ref_starve_event, sts_init_fail_event;
    logic [12:0] sts_bist_fail_addr;

    logic [7:0]  cfg_tRCD_nCK, cfg_tRP_nCK, cfg_tRAS_nCK, cfg_tRC_nCK;
    logic [7:0]  cfg_tRRD_nCK, cfg_tWTR_nCK, cfg_tFAW_nCK, cfg_tRFC_nCK;
    logic [7:0]  cfg_tWR_nCK, cfg_tRTP_nCK, cfg_CL_nCK, cfg_CWL_nCK;
    logic [7:0]  cfg_tCCD_nCK;  logic [23:0] cfg_tREFI_nCK;
    logic        cfg_sched_policy, cfg_row_policy, cfg_ecc_enable;
    logic [1:0]  cfg_self_ref_mode;
    logic        cfg_bist_start, cfg_force_refresh, cfg_force_self_ref;
    logic [3:0]  cfg_max_postpone, cfg_urgent_threshold;
    logic        cfg_ref_priority;
    logic [2:0]  cfg_bist_pattern; logic cfg_bist_addr_mode;
    logic [28:0] cfg_bist_addr_start, cfg_bist_addr_end;

    config_regs dut (
        .clk(clk), .rst_n(rst_n),
        .csr_cyc_i(csr_cyc_i), .csr_stb_i(csr_stb_i), .csr_we_i(csr_we_i),
        .csr_adr_i(csr_adr_i), .csr_dat_i(csr_dat_i), .csr_sel_i(csr_sel_i),
        .csr_ack_o(csr_ack_o), .csr_dat_o(csr_dat_o), .csr_err_o(csr_err_o),
        .sts_init_done(sts_init_done), .sts_cal_done(sts_cal_done), .sts_cal_fail(sts_cal_fail),
        .sts_bist_done(sts_bist_done), .sts_bist_fail(sts_bist_fail),
        .sts_ref_pending_cnt(sts_ref_pending_cnt), .sts_self_refresh_active(sts_self_refresh_active),
        .sts_ecc_ce_count(sts_ecc_ce_count), .sts_ecc_ue_event(sts_ecc_ue_event),
        .sts_ref_starve_event(sts_ref_starve_event), .sts_init_fail_event(sts_init_fail_event),
        .sts_bist_fail_addr(sts_bist_fail_addr),
        .cfg_tRCD_nCK(cfg_tRCD_nCK), .cfg_tRP_nCK(cfg_tRP_nCK),
        .cfg_tRAS_nCK(cfg_tRAS_nCK), .cfg_tRC_nCK(cfg_tRC_nCK),
        .cfg_tRRD_nCK(cfg_tRRD_nCK), .cfg_tWTR_nCK(cfg_tWTR_nCK),
        .cfg_tFAW_nCK(cfg_tFAW_nCK), .cfg_tRFC_nCK(cfg_tRFC_nCK),
        .cfg_tWR_nCK(cfg_tWR_nCK), .cfg_tRTP_nCK(cfg_tRTP_nCK),
        .cfg_CL_nCK(cfg_CL_nCK), .cfg_CWL_nCK(cfg_CWL_nCK),
        .cfg_tCCD_nCK(cfg_tCCD_nCK), .cfg_tREFI_nCK(cfg_tREFI_nCK),
        .cfg_sched_policy(cfg_sched_policy), .cfg_row_policy(cfg_row_policy),
        .cfg_self_ref_mode(cfg_self_ref_mode), .cfg_ecc_enable(cfg_ecc_enable),
        .cfg_bist_start(cfg_bist_start), .cfg_force_refresh(cfg_force_refresh),
        .cfg_force_self_ref(cfg_force_self_ref),
        .cfg_max_postpone(cfg_max_postpone), .cfg_urgent_threshold(cfg_urgent_threshold),
        .cfg_ref_priority(cfg_ref_priority),
        .cfg_bist_pattern(cfg_bist_pattern), .cfg_bist_addr_mode(cfg_bist_addr_mode),
        .cfg_bist_addr_start(cfg_bist_addr_start), .cfg_bist_addr_end(cfg_bist_addr_end)
    );

    int pass_count=0, fail_count=0, total_tests=0;
    task automatic check(string name, logic condition);
        total_tests++;
        if (condition) begin pass_count++; $display("  [PASS] %0d: %s", total_tests, name); end
        else begin fail_count++; $display("  [FAIL] %0d: %s", total_tests, name); end
    endtask
    logic [31:0] rdata;
    task automatic csr_idle(); csr_cyc_i=0;csr_stb_i=0;csr_we_i=0;csr_adr_i=0;csr_dat_i=0;csr_sel_i=4'hF; endtask
    task automatic csr_write(input [7:0] addr, input [31:0] data);
        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=1;csr_adr_i=addr;csr_dat_i=data;csr_sel_i=4'hF;
        @(posedge clk); wait(csr_ack_o||csr_err_o); @(posedge clk); csr_idle();
    endtask
    task automatic csr_read(input [7:0] addr, output [31:0] data);
        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=addr;csr_sel_i=4'hF;
        @(posedge clk); wait(csr_ack_o||csr_err_o); data=csr_dat_o; @(posedge clk); csr_idle();
    endtask
    task automatic hw_reset();
        rst_n=0; csr_idle();
        sts_init_done=0;sts_cal_done=0;sts_cal_fail=0;sts_bist_done=0;sts_bist_fail=0;
        sts_ref_pending_cnt=0;sts_self_refresh_active=0;sts_ecc_ce_count=0;
        sts_ecc_ue_event=0;sts_ref_starve_event=0;sts_init_fail_event=0;sts_bist_fail_addr=0;
        repeat(5) @(posedge clk); rst_n=1; repeat(2) @(posedge clk);
    endtask

    localparam [31:0] CTRL_CONFIG_WO_MASK = 32'hFFFFFF1F;

    initial begin
        $dumpfile("config_regs_tb.vcd");
        $dumpvars(0, config_regs_tb);
        $display("");
        $display("==========================================================");
        $display("  config_regs_tb -- CSR Register Verification");
        $display("  11 registers, 32-bit data bus");
        $display("==========================================================");
        hw_reset();

        $display(""); $display("  -- Section A: Reset Values --");
        csr_read(8'h00, rdata); check($sformatf("A1: CTRL_STATUS reset = 0x%08X", rdata), rdata == 32'h00000000);
        csr_read(8'h04, rdata); check($sformatf("A2: CTRL_CONFIG reset = 0x%08X", rdata), rdata == 32'h00000009);
        csr_read(8'h08, rdata); check($sformatf("A3: TIMING_0 reset = 0x%08X", rdata), rdata == 32'h271C0B0B);
        csr_read(8'h0C, rdata); check($sformatf("A4: TIMING_1 reset = 0x%08X", rdata), rdata == 32'h80200606);
        csr_read(8'h10, rdata); check($sformatf("A5: TIMING_2 reset = 0x%08X", rdata), rdata == 32'h080B060C);
        csr_read(8'h14, rdata); check($sformatf("A6: TIMING_3 reset = 0x%08X", rdata), rdata == 32'h00186004);
        csr_read(8'h18, rdata); check($sformatf("A7: REFRESH_CONFIG reset = 0x%08X", rdata), rdata == 32'h00000168);
        csr_read(8'h1C, rdata); check($sformatf("A8: ERROR_STATUS reset = 0x%08X", rdata), rdata == 32'h00000000);
        csr_read(8'h20, rdata); check($sformatf("A9: BIST_CONFIG reset = 0x%08X", rdata), rdata == 32'h00000000);
        csr_read(8'h24, rdata); check($sformatf("A10: BIST_ADDR_START reset = 0x%08X", rdata), rdata == 32'h00000000);
        csr_read(8'h28, rdata); check($sformatf("A11: BIST_ADDR_END reset = 0x%08X", rdata), rdata == 32'h1FFFFFFF);

        $display(""); $display("  -- Section B: Write / Readback --");
        csr_write(8'h04, 32'h0000001F); csr_read(8'h04, rdata);
        check($sformatf("B1: CTRL_CONFIG write/readback (0x%08X, WO masked)", rdata),
              (rdata & CTRL_CONFIG_WO_MASK) == (32'h0000001F & CTRL_CONFIG_WO_MASK));
        csr_write(8'h08, 32'h12345678); csr_read(8'h08, rdata);
        check("B2: TIMING_0 write/readback", rdata == 32'h12345678);
        csr_write(8'h0C, 32'hDEADBEEF); csr_read(8'h0C, rdata);
        check("B3: TIMING_1 write/readback", rdata == 32'hDEADBEEF);
        csr_write(8'h10, 32'hCAFEBABE); csr_read(8'h10, rdata);
        check("B4: TIMING_2 write/readback", rdata == 32'hCAFEBABE);
        csr_write(8'h14, 32'hFACEFEED); csr_read(8'h14, rdata);
        check("B5: TIMING_3 write/readback", rdata == 32'hFACEFEED);
        csr_write(8'h18, 32'h000001FF); csr_read(8'h18, rdata);
        check("B6: REFRESH_CONFIG write/readback", rdata == 32'h000001FF);
        csr_write(8'h20, 32'h0000000F); csr_read(8'h20, rdata);
        check("B7: BIST_CONFIG write/readback", rdata == 32'h0000000F);
        csr_write(8'h24, 32'h1ABC0000); csr_read(8'h24, rdata);
        check("B8: BIST_ADDR_START write/readback", rdata == 32'h1ABC0000);
        csr_write(8'h28, 32'h1FFFFFFF); csr_read(8'h28, rdata);
        check("B9: BIST_ADDR_END write/readback", rdata == 32'h1FFFFFFF);

        $display(""); $display("  -- Section C: CTRL_STATUS (RO) --");
        hw_reset();
        sts_init_done=1; sts_cal_done=1; sts_ref_pending_cnt=3'd5;
        repeat(2) @(posedge clk);
        csr_read(8'h00, rdata);
        check($sformatf("C1: CTRL_STATUS reflects inputs (0x%08X)", rdata),
              rdata[0]==1'b1 && rdata[1]==1'b1 && rdata[7:5]==3'd5);
        csr_write(8'h00, 32'hFFFFFFFF); csr_read(8'h00, rdata);
        check("C2: CTRL_STATUS ignores writes", rdata[0]==1'b1 && rdata[1]==1'b1);

        $display(""); $display("  -- Section D: WO Self-Clearing --");
        hw_reset();
        csr_write(8'h04, 32'h00000029); repeat(1) @(posedge clk); csr_read(8'h04, rdata);
        check($sformatf("D1: bist_start self-clears (bit5=%0b)", rdata[5]), rdata[5]==1'b0);
        csr_write(8'h04, 32'h00000049); repeat(1) @(posedge clk); csr_read(8'h04, rdata);
        check($sformatf("D2: force_refresh self-clears (bit6=%0b)", rdata[6]), rdata[6]==1'b0);

        $display(""); $display("  -- Section E: RW1C (ERROR_STATUS) --");
        hw_reset();
        sts_ecc_ue_event=1; @(posedge clk); sts_ecc_ue_event=0; repeat(2) @(posedge clk);
        csr_read(8'h1C, rdata); check($sformatf("E1: ecc_ue latched (0x%08X)", rdata), rdata[16]==1'b1);
        csr_write(8'h1C, 32'h00010000); csr_read(8'h1C, rdata);
        check($sformatf("E2: ecc_ue W1C clears (0x%08X)", rdata), rdata[16]==1'b0);
        csr_read(8'h1C, rdata); check("E3: Flag stays clear", rdata[16]==1'b0);

        $display(""); $display("  -- Section F: Error Handling --");
        hw_reset();
        @(posedge clk); csr_cyc_i=1;csr_stb_i=1;csr_we_i=0;csr_adr_i=8'hFF;csr_sel_i=4'hF;
        begin
            logic saw_err; saw_err=0;
            repeat(10) begin @(posedge clk); if(csr_err_o) begin saw_err=1; break; end end
            check("F1: Invalid addr error", saw_err);
        end
        csr_idle(); repeat(2) @(posedge clk);
        csr_read(8'h04, rdata); check("F2: Valid addr no error", csr_err_o===1'b0);

        $display(""); $display("  -- Section G: cfg_* Outputs --");
        hw_reset();
        csr_write(8'h08, 32'h44332211); repeat(2) @(posedge clk);
        check($sformatf("G1: cfg_tRCD_nCK=0x%02X", cfg_tRCD_nCK), cfg_tRCD_nCK==8'h11);
        csr_write(8'h04, 32'h00000001); repeat(2) @(posedge clk);
        check($sformatf("G2: cfg_sched_policy=%0b", cfg_sched_policy), cfg_sched_policy==1'b1);
        csr_write(8'h18, 32'h0000006A); repeat(2) @(posedge clk);
        check($sformatf("G3: cfg_max_postpone=%0d", cfg_max_postpone), cfg_max_postpone==4'hA);

        $display(""); $display("  -- Section H: Reset --");
        csr_write(8'h08, 32'hFFFFFFFF); csr_write(8'h0C, 32'hFFFFFFFF);
        rst_n=0; repeat(5) @(posedge clk); rst_n=1; csr_idle(); repeat(2) @(posedge clk);
        csr_read(8'h08, rdata); check($sformatf("H1: TIMING_0 reset (0x%08X)", rdata), rdata==32'h271C0B0B);
        csr_write(8'h08, 32'h11223344); csr_read(8'h08, rdata); check("H2: Normal after reset", rdata==32'h11223344);

        $display(""); $display("  -- Section I: Edge Cases --");
        hw_reset();
        csr_write(8'h08, 32'hAAAAAAAA); csr_write(8'h0C, 32'hBBBBBBBB);
        csr_read(8'h08, rdata); check("I1: Back-to-back TIMING_0", rdata==32'hAAAAAAAA);
        csr_read(8'h0C, rdata); check("I2: Back-to-back TIMING_1", rdata==32'hBBBBBBBB);

        $display(""); $display("  -- Section J: Reserved Bits Pinned on Write --");
        hw_reset();
        csr_write(8'h04, 32'hFFFFFFFF); csr_read(8'h04, rdata);
        check($sformatf("J1: CTRL_CONFIG reserved bits pinned (0x%08X)", rdata),
              (rdata & 32'hFFFFFF00) == (32'h00000009 & 32'hFFFFFF00));
        csr_write(8'h18, 32'hFFFFFFFF); csr_read(8'h18, rdata);
        check($sformatf("J2: REFRESH_CONFIG reserved bits pinned (0x%08X)", rdata),
              (rdata & 32'hFFFFFE00) == (32'h00000168 & 32'hFFFFFE00));
        csr_write(8'h20, 32'hFFFFFFFF); csr_read(8'h20, rdata);
        check($sformatf("J3: BIST_CONFIG reserved bits pinned (0x%08X)", rdata),
              (rdata & 32'hFFFFFFF0) == (32'h00000000 & 32'hFFFFFFF0));
        csr_write(8'h24, 32'hFFFFFFFF); csr_read(8'h24, rdata);
        check($sformatf("J4: BIST_ADDR_START reserved bits pinned (0x%08X)", rdata),
              (rdata & 32'hE0000000) == (32'h00000000 & 32'hE0000000));
        csr_write(8'h28, 32'hFFFFFFFF); csr_read(8'h28, rdata);
        check($sformatf("J5: BIST_ADDR_END reserved bits pinned (0x%08X)", rdata),
              (rdata & 32'hE0000000) == (32'h1FFFFFFF & 32'hE0000000));

        $display("");
        $display("==========================================================");
        if (fail_count==0) $display("  ALL %0d TESTS PASSED", total_tests);
        else $display("  %0d of %0d TESTS FAILED", fail_count, total_tests);
        $display("==========================================================");
        $display(""); $finish;
    end
    initial begin #(1_000_000); $display("  [FAIL] GLOBAL TIMEOUT"); $finish; end
endmodule