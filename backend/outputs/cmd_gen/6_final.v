module cmd_gen (clk,
    cmd_out_valid,
    cmd_out_we,
    ddr_cke,
    ddr_odt,
    ddr_reset_n,
    fb_act_valid,
    fb_pre_all,
    fb_pre_valid,
    fb_rd_valid,
    fb_ref_valid,
    fb_wr_valid,
    rst_n,
    sched_valid,
    sched_we,
    cmd_out_aux,
    ddr_addr,
    ddr_bank,
    ddr_cmd,
    fb_act_bank,
    fb_act_row,
    fb_pre_bank,
    fb_rd_bank,
    fb_wr_bank,
    sched_aux,
    sched_bank,
    sched_col,
    sched_row,
    sched_type);
 input clk;
 output cmd_out_valid;
 output cmd_out_we;
 output ddr_cke;
 output ddr_odt;
 output ddr_reset_n;
 output fb_act_valid;
 output fb_pre_all;
 output fb_pre_valid;
 output fb_rd_valid;
 output fb_ref_valid;
 output fb_wr_valid;
 input rst_n;
 input sched_valid;
 input sched_we;
 output [3:0] cmd_out_aux;
 output [14:0] ddr_addr;
 output [2:0] ddr_bank;
 output [3:0] ddr_cmd;
 output [2:0] fb_act_bank;
 output [14:0] fb_act_row;
 output [2:0] fb_pre_bank;
 output [2:0] fb_rd_bank;
 output [2:0] fb_wr_bank;
 input [3:0] sched_aux;
 input [2:0] sched_bank;
 input [9:0] sched_col;
 input [14:0] sched_row;
 input [3:0] sched_type;

 wire _000_;
 wire _001_;
 wire _002_;
 wire _005_;
 wire _006_;
 wire _007_;
 wire _008_;
 wire _009_;
 wire _010_;
 wire _011_;
 wire _012_;
 wire _013_;
 wire _014_;
 wire _015_;
 wire _016_;
 wire _017_;
 wire _018_;
 wire _019_;
 wire _020_;
 wire _021_;
 wire _022_;
 wire _023_;
 wire _024_;
 wire _025_;
 wire _026_;
 wire _027_;
 wire _028_;
 wire _029_;
 wire _030_;
 wire _031_;
 wire _032_;
 wire _033_;
 wire _034_;
 wire _035_;
 wire _036_;
 wire _037_;
 wire _038_;
 wire _039_;
 wire _040_;
 wire _041_;
 wire _042_;
 wire _043_;
 wire _044_;
 wire _045_;
 wire _046_;
 wire _047_;
 wire _048_;
 wire _049_;
 wire _050_;
 wire _051_;
 wire _052_;
 wire _053_;
 wire _054_;
 wire _055_;
 wire _056_;
 wire _057_;
 wire _058_;
 wire _059_;
 wire _061_;
 wire _062_;
 wire _064_;
 wire _065_;
 wire _066_;
 wire _067_;
 wire _068_;
 wire _069_;
 wire _070_;
 wire _071_;
 wire _072_;
 wire _074_;
 wire _075_;
 wire _076_;
 wire net42;
 wire net43;
 wire net44;
 wire net45;
 wire net46;
 wire net47;
 wire net48;
 wire net49;
 wire net50;
 wire net51;
 wire net52;
 wire net53;
 wire net54;
 wire net55;
 wire net56;
 wire net57;
 wire net58;
 wire net59;
 wire net60;
 wire net61;
 wire net62;
 wire net63;
 wire net64;
 wire net65;
 wire net66;
 wire net67;
 wire net68;
 wire net69;
 wire net70;
 wire net71;
 wire net72;
 wire net73;
 wire net74;
 wire net75;
 wire net76;
 wire net77;
 wire net78;
 wire net79;
 wire net80;
 wire net81;
 wire net82;
 wire net83;
 wire net84;
 wire net85;
 wire net86;
 wire net87;
 wire net88;
 wire net89;
 wire net90;
 wire net91;
 wire net92;
 wire net93;
 wire net94;
 wire net95;
 wire net96;
 wire net97;
 wire net98;
 wire net99;
 wire net100;
 wire net4;
 wire net5;
 wire net6;
 wire net7;
 wire net8;
 wire net9;
 wire net10;
 wire net11;
 wire net12;
 wire net13;
 wire net14;
 wire net15;
 wire net16;
 wire net17;
 wire net18;
 wire net19;
 wire net20;
 wire net21;
 wire net22;
 wire net23;
 wire net24;
 wire net25;
 wire net26;
 wire net27;
 wire net28;
 wire net29;
 wire net30;
 wire net31;
 wire net32;
 wire net33;
 wire net34;
 wire net35;
 wire net36;
 wire net37;
 wire net38;
 wire net39;
 wire net40;
 wire net41;
 wire net101;
 wire clknet_3_0__leaf_clk;
 wire clknet_0_clk;
 wire net107;
 wire net108;
 wire clknet_3_1__leaf_clk;
 wire clknet_3_2__leaf_clk;
 wire clknet_3_3__leaf_clk;
 wire clknet_3_4__leaf_clk;
 wire clknet_3_5__leaf_clk;
 wire clknet_3_6__leaf_clk;
 wire clknet_3_7__leaf_clk;

 sky130_fd_sc_hd__nor2b_1 _079_ (.A(net40),
    .B_N(net41),
    .Y(_059_));
 sky130_fd_sc_hd__and3b_2 _081_ (.A_N(net38),
    .B(net39),
    .C(net37),
    .X(_061_));
 sky130_fd_sc_hd__and2_1 _082_ (.A(_059_),
    .B(_061_),
    .X(_026_));
 sky130_fd_sc_hd__and4bb_2 _083_ (.A_N(net40),
    .B_N(net39),
    .C(net41),
    .D(net38),
    .X(_062_));
 sky130_fd_sc_hd__nand2b_4 _086_ (.A_N(net40),
    .B(net41),
    .Y(_064_));
 sky130_fd_sc_hd__nor4b_4 _087_ (.A(net38),
    .B(net39),
    .C(_064_),
    .D_N(net37),
    .Y(_065_));
 sky130_fd_sc_hd__or3b_1 _089_ (.A(net37),
    .B(net38),
    .C_N(net39),
    .X(_066_));
 sky130_fd_sc_hd__or2_4 _090_ (.A(_064_),
    .B(_066_),
    .X(_067_));
 sky130_fd_sc_hd__inv_1 _091_ (.A(_067_),
    .Y(_002_));
 sky130_fd_sc_hd__and2b_4 _092_ (.A_N(net37),
    .B(_062_),
    .X(_001_));
 sky130_fd_sc_hd__nand2_1 _093_ (.A(net37),
    .B(_062_),
    .Y(_068_));
 sky130_fd_sc_hd__inv_1 _094_ (.A(_068_),
    .Y(_000_));
 sky130_fd_sc_hd__nand2_1 _095_ (.A(net37),
    .B(net38),
    .Y(_069_));
 sky130_fd_sc_hd__o21ai_0 _096_ (.A1(net39),
    .A2(_069_),
    .B1(_066_),
    .Y(_070_));
 sky130_fd_sc_hd__nand2_1 _097_ (.A(_059_),
    .B(_070_),
    .Y(_023_));
 sky130_fd_sc_hd__and2b_1 _098_ (.A_N(net39),
    .B(net38),
    .X(_071_));
 sky130_fd_sc_hd__o21ai_0 _099_ (.A1(_061_),
    .A2(_071_),
    .B1(_059_),
    .Y(_024_));
 sky130_fd_sc_hd__nor2_1 _100_ (.A(net38),
    .B(_064_),
    .Y(_072_));
 sky130_fd_sc_hd__o21ai_0 _101_ (.A1(net37),
    .A2(net39),
    .B1(_072_),
    .Y(_025_));
 sky130_fd_sc_hd__a22o_1 _102_ (.A1(net12),
    .A2(_062_),
    .B1(net107),
    .B2(net22),
    .X(_005_));
 sky130_fd_sc_hd__a22o_1 _103_ (.A1(net13),
    .A2(_062_),
    .B1(net107),
    .B2(net28),
    .X(_011_));
 sky130_fd_sc_hd__a22o_1 _104_ (.A1(net14),
    .A2(_062_),
    .B1(net107),
    .B2(net29),
    .X(_012_));
 sky130_fd_sc_hd__a22o_1 _105_ (.A1(net15),
    .A2(_062_),
    .B1(net107),
    .B2(net30),
    .X(_013_));
 sky130_fd_sc_hd__a22o_1 _107_ (.A1(net16),
    .A2(_062_),
    .B1(net107),
    .B2(net31),
    .X(_014_));
 sky130_fd_sc_hd__a22o_1 _108_ (.A1(net17),
    .A2(_062_),
    .B1(net107),
    .B2(net32),
    .X(_015_));
 sky130_fd_sc_hd__a22o_1 _109_ (.A1(net18),
    .A2(_062_),
    .B1(net107),
    .B2(net33),
    .X(_016_));
 sky130_fd_sc_hd__a22o_1 _110_ (.A1(net19),
    .A2(_062_),
    .B1(net107),
    .B2(net34),
    .X(_017_));
 sky130_fd_sc_hd__a22o_1 _111_ (.A1(net20),
    .A2(_062_),
    .B1(net107),
    .B2(net35),
    .X(_018_));
 sky130_fd_sc_hd__a22o_1 _112_ (.A1(net21),
    .A2(_062_),
    .B1(net107),
    .B2(net36),
    .X(_019_));
 sky130_fd_sc_hd__and2_1 _113_ (.A(net23),
    .B(net107),
    .X(_006_));
 sky130_fd_sc_hd__and2_1 _114_ (.A(net24),
    .B(net107),
    .X(_007_));
 sky130_fd_sc_hd__and2_1 _115_ (.A(net25),
    .B(net107),
    .X(_008_));
 sky130_fd_sc_hd__and2_1 _116_ (.A(net26),
    .B(net107),
    .X(_009_));
 sky130_fd_sc_hd__and2_1 _117_ (.A(net27),
    .B(net107),
    .X(_010_));
 sky130_fd_sc_hd__o21bai_1 _118_ (.A1(net37),
    .A2(net38),
    .B1_N(net39),
    .Y(_074_));
 sky130_fd_sc_hd__a21oi_1 _119_ (.A1(_066_),
    .A2(_074_),
    .B1(_064_),
    .Y(_075_));
 sky130_fd_sc_hd__and2_1 _120_ (.A(net9),
    .B(_075_),
    .X(_020_));
 sky130_fd_sc_hd__and2_1 _121_ (.A(net10),
    .B(_075_),
    .X(_021_));
 sky130_fd_sc_hd__and2_1 _122_ (.A(net11),
    .B(_075_),
    .X(_022_));
 sky130_fd_sc_hd__mux2_2 _123_ (.A0(net42),
    .A1(net5),
    .S(_062_),
    .X(_027_));
 sky130_fd_sc_hd__mux2_2 _124_ (.A0(net43),
    .A1(net6),
    .S(_062_),
    .X(_028_));
 sky130_fd_sc_hd__mux2_2 _125_ (.A0(net44),
    .A1(net7),
    .S(_062_),
    .X(_029_));
 sky130_fd_sc_hd__mux2_2 _126_ (.A0(net45),
    .A1(net8),
    .S(_062_),
    .X(_030_));
 sky130_fd_sc_hd__inv_1 _127_ (.A(net47),
    .Y(_076_));
 sky130_fd_sc_hd__o21ai_0 _128_ (.A1(_076_),
    .A2(_062_),
    .B1(_068_),
    .Y(_031_));
 sky130_fd_sc_hd__mux2_2 _129_ (.A0(net70),
    .A1(net9),
    .S(net107),
    .X(_032_));
 sky130_fd_sc_hd__mux2_2 _130_ (.A0(net71),
    .A1(net10),
    .S(net107),
    .X(_033_));
 sky130_fd_sc_hd__mux2_2 _131_ (.A0(net72),
    .A1(net11),
    .S(net107),
    .X(_034_));
 sky130_fd_sc_hd__mux2_2 _132_ (.A0(net73),
    .A1(net22),
    .S(net107),
    .X(_035_));
 sky130_fd_sc_hd__mux2_2 _134_ (.A0(net74),
    .A1(net23),
    .S(net107),
    .X(_036_));
 sky130_fd_sc_hd__mux2_2 _135_ (.A0(net75),
    .A1(net24),
    .S(net107),
    .X(_037_));
 sky130_fd_sc_hd__mux2_2 _136_ (.A0(net76),
    .A1(net25),
    .S(net107),
    .X(_038_));
 sky130_fd_sc_hd__mux2_2 _137_ (.A0(net77),
    .A1(net26),
    .S(net107),
    .X(_039_));
 sky130_fd_sc_hd__mux2_2 _138_ (.A0(net78),
    .A1(net27),
    .S(net107),
    .X(_040_));
 sky130_fd_sc_hd__mux2_2 _139_ (.A0(net79),
    .A1(net28),
    .S(net107),
    .X(_041_));
 sky130_fd_sc_hd__mux2_2 _140_ (.A0(net80),
    .A1(net29),
    .S(net107),
    .X(_042_));
 sky130_fd_sc_hd__mux2_2 _141_ (.A0(net81),
    .A1(net30),
    .S(net107),
    .X(_043_));
 sky130_fd_sc_hd__mux2_2 _142_ (.A0(net82),
    .A1(net31),
    .S(net107),
    .X(_044_));
 sky130_fd_sc_hd__mux2_2 _143_ (.A0(net83),
    .A1(net32),
    .S(net107),
    .X(_045_));
 sky130_fd_sc_hd__mux2_2 _144_ (.A0(net84),
    .A1(net33),
    .S(net107),
    .X(_046_));
 sky130_fd_sc_hd__mux2_2 _145_ (.A0(net85),
    .A1(net34),
    .S(net107),
    .X(_047_));
 sky130_fd_sc_hd__mux2_2 _146_ (.A0(net86),
    .A1(net35),
    .S(net107),
    .X(_048_));
 sky130_fd_sc_hd__mux2_2 _147_ (.A0(net87),
    .A1(net36),
    .S(net107),
    .X(_049_));
 sky130_fd_sc_hd__mux2_4 _148_ (.A0(net9),
    .A1(net89),
    .S(_067_),
    .X(_050_));
 sky130_fd_sc_hd__mux2_4 _149_ (.A0(net10),
    .A1(net90),
    .S(_067_),
    .X(_051_));
 sky130_fd_sc_hd__mux2_4 _150_ (.A0(net11),
    .A1(net91),
    .S(_067_),
    .X(_052_));
 sky130_fd_sc_hd__mux2_2 _151_ (.A0(net93),
    .A1(net9),
    .S(_001_),
    .X(_053_));
 sky130_fd_sc_hd__mux2_2 _152_ (.A0(net94),
    .A1(net10),
    .S(_001_),
    .X(_054_));
 sky130_fd_sc_hd__mux2_2 _153_ (.A0(net95),
    .A1(net11),
    .S(_001_),
    .X(_055_));
 sky130_fd_sc_hd__mux2_2 _154_ (.A0(net9),
    .A1(net98),
    .S(_068_),
    .X(_056_));
 sky130_fd_sc_hd__mux2_2 _155_ (.A0(net10),
    .A1(net99),
    .S(_068_),
    .X(_057_));
 sky130_fd_sc_hd__mux2_2 _156_ (.A0(net11),
    .A1(net100),
    .S(_068_),
    .X(_058_));
 sky130_fd_sc_hd__conb_1 _158__1 (.LO(ddr_cke));
 sky130_fd_sc_hd__conb_1 _159__2 (.LO(ddr_cmd[3]));
 sky130_fd_sc_hd__conb_1 _160__3 (.LO(ddr_reset_n));
 sky130_fd_sc_hd__conb_1 _161__4 (.LO(fb_pre_all));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_0__f_clk (.A(clknet_0_clk),
    .X(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_1__f_clk (.A(clknet_0_clk),
    .X(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_2__f_clk (.A(clknet_0_clk),
    .X(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_3__f_clk (.A(clknet_0_clk),
    .X(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_4__f_clk (.A(clknet_0_clk),
    .X(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_5__f_clk (.A(clknet_0_clk),
    .X(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_6__f_clk (.A(clknet_0_clk),
    .X(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_3_7__f_clk (.A(clknet_0_clk),
    .X(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload0 (.A(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__clkinv_2 clkload1 (.A(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__clkinv_2 clkload2 (.A(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload3 (.A(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__bufinv_16 clkload4 (.A(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__bufinv_16 clkload5 (.A(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload6 (.A(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \cmd_out_aux[0]$_DFFE_PN0P_  (.D(_027_),
    .Q(net42),
    .RESET_B(net108),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \cmd_out_aux[1]$_DFFE_PN0P_  (.D(_028_),
    .Q(net43),
    .RESET_B(net108),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \cmd_out_aux[2]$_DFFE_PN0P_  (.D(_029_),
    .Q(net44),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \cmd_out_aux[3]$_DFFE_PN0P_  (.D(_030_),
    .Q(net45),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \cmd_out_valid$_DFF_PN0_  (.D(_062_),
    .Q(net46),
    .RESET_B(net108),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \cmd_out_we$_DFFE_PN0P_  (.D(_031_),
    .Q(net47),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[0]$_DFF_PN0_  (.D(_005_),
    .Q(net48),
    .RESET_B(net108),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[10]$_DFF_PN0_  (.D(_006_),
    .Q(net49),
    .RESET_B(net108),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[11]$_DFF_PN0_  (.D(_007_),
    .Q(net50),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[12]$_DFF_PN0_  (.D(_008_),
    .Q(net51),
    .RESET_B(net108),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[13]$_DFF_PN0_  (.D(_009_),
    .Q(net52),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[14]$_DFF_PN0_  (.D(_010_),
    .Q(net53),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[1]$_DFF_PN0_  (.D(_011_),
    .Q(net54),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[2]$_DFF_PN0_  (.D(_012_),
    .Q(net55),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[3]$_DFF_PN0_  (.D(_013_),
    .Q(net56),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[4]$_DFF_PN0_  (.D(_014_),
    .Q(net57),
    .RESET_B(net108),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[5]$_DFF_PN0_  (.D(_015_),
    .Q(net58),
    .RESET_B(net108),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[6]$_DFF_PN0_  (.D(_016_),
    .Q(net59),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[7]$_DFF_PN0_  (.D(_017_),
    .Q(net60),
    .RESET_B(net108),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[8]$_DFF_PN0_  (.D(_018_),
    .Q(net61),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_addr[9]$_DFF_PN0_  (.D(_019_),
    .Q(net62),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_bank[0]$_DFF_PN0_  (.D(_020_),
    .Q(net63),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_bank[1]$_DFF_PN0_  (.D(_021_),
    .Q(net64),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_bank[2]$_DFF_PN0_  (.D(_022_),
    .Q(net65),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfstp_2 \ddr_cmd[0]$_DFF_PN1_  (.D(_023_),
    .Q(net66),
    .SET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfstp_2 \ddr_cmd[1]$_DFF_PN1_  (.D(_024_),
    .Q(net67),
    .SET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfstp_2 \ddr_cmd[2]$_DFF_PN1_  (.D(_025_),
    .Q(net68),
    .SET_B(net108),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ddr_odt$_DFF_PN0_  (.D(_000_),
    .Q(net69),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_bank[0]$_DFFE_PN0P_  (.D(_032_),
    .Q(net70),
    .RESET_B(net108),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_bank[1]$_DFFE_PN0P_  (.D(_033_),
    .Q(net71),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_bank[2]$_DFFE_PN0P_  (.D(_034_),
    .Q(net72),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[0]$_DFFE_PN0P_  (.D(_035_),
    .Q(net73),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[10]$_DFFE_PN0P_  (.D(_036_),
    .Q(net74),
    .RESET_B(net108),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[11]$_DFFE_PN0P_  (.D(_037_),
    .Q(net75),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[12]$_DFFE_PN0P_  (.D(_038_),
    .Q(net76),
    .RESET_B(net108),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[13]$_DFFE_PN0P_  (.D(_039_),
    .Q(net77),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[14]$_DFFE_PN0P_  (.D(_040_),
    .Q(net78),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[1]$_DFFE_PN0P_  (.D(_041_),
    .Q(net79),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[2]$_DFFE_PN0P_  (.D(_042_),
    .Q(net80),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[3]$_DFFE_PN0P_  (.D(_043_),
    .Q(net81),
    .RESET_B(net108),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[4]$_DFFE_PN0P_  (.D(_044_),
    .Q(net82),
    .RESET_B(net108),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[5]$_DFFE_PN0P_  (.D(_045_),
    .Q(net83),
    .RESET_B(net108),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[6]$_DFFE_PN0P_  (.D(_046_),
    .Q(net84),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[7]$_DFFE_PN0P_  (.D(_047_),
    .Q(net85),
    .RESET_B(net108),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[8]$_DFFE_PN0P_  (.D(_048_),
    .Q(net86),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_row[9]$_DFFE_PN0P_  (.D(_049_),
    .Q(net87),
    .RESET_B(net108),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_act_valid$_DFF_PN0_  (.D(net107),
    .Q(net88),
    .RESET_B(net108),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_pre_bank[0]$_DFFE_PN0P_  (.D(_050_),
    .Q(net89),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_pre_bank[1]$_DFFE_PN0P_  (.D(_051_),
    .Q(net90),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_pre_bank[2]$_DFFE_PN0P_  (.D(_052_),
    .Q(net91),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_pre_valid$_DFF_PN0_  (.D(_002_),
    .Q(net92),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_rd_bank[0]$_DFFE_PN0P_  (.D(_053_),
    .Q(net93),
    .RESET_B(net108),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_rd_bank[1]$_DFFE_PN0P_  (.D(_054_),
    .Q(net94),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_rd_bank[2]$_DFFE_PN0P_  (.D(_055_),
    .Q(net95),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_rd_valid$_DFF_PN0_  (.D(_001_),
    .Q(net96),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_ref_valid$_DFF_PN0_  (.D(_026_),
    .Q(net97),
    .RESET_B(net108),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_wr_bank[0]$_DFFE_PN0P_  (.D(_056_),
    .Q(net98),
    .RESET_B(net108),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_wr_bank[1]$_DFFE_PN0P_  (.D(_057_),
    .Q(net99),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \fb_wr_bank[2]$_DFFE_PN0P_  (.D(_058_),
    .Q(net100),
    .RESET_B(net108),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(sched_bank[0]),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input11 (.A(sched_bank[1]),
    .X(net10));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input12 (.A(sched_bank[2]),
    .X(net11));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input13 (.A(sched_col[0]),
    .X(net12));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input14 (.A(sched_col[1]),
    .X(net13));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input15 (.A(sched_col[2]),
    .X(net14));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input16 (.A(sched_col[3]),
    .X(net15));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input17 (.A(sched_col[4]),
    .X(net16));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input18 (.A(sched_col[5]),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input19 (.A(sched_col[6]),
    .X(net18));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input20 (.A(sched_col[7]),
    .X(net19));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input21 (.A(sched_col[8]),
    .X(net20));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input22 (.A(sched_col[9]),
    .X(net21));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input23 (.A(sched_row[0]),
    .X(net22));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input24 (.A(sched_row[10]),
    .X(net23));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input25 (.A(sched_row[11]),
    .X(net24));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input26 (.A(sched_row[12]),
    .X(net25));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input27 (.A(sched_row[13]),
    .X(net26));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input28 (.A(sched_row[14]),
    .X(net27));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input29 (.A(sched_row[1]),
    .X(net28));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input30 (.A(sched_row[2]),
    .X(net29));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input31 (.A(sched_row[3]),
    .X(net30));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input32 (.A(sched_row[4]),
    .X(net31));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input33 (.A(sched_row[5]),
    .X(net32));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input34 (.A(sched_row[6]),
    .X(net33));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input35 (.A(sched_row[7]),
    .X(net34));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input36 (.A(sched_row[8]),
    .X(net35));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input37 (.A(sched_row[9]),
    .X(net36));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input38 (.A(sched_type[0]),
    .X(net37));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input39 (.A(sched_type[1]),
    .X(net38));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input40 (.A(sched_type[2]),
    .X(net39));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input41 (.A(sched_type[3]),
    .X(net40));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input42 (.A(sched_valid),
    .X(net41));
 sky130_fd_sc_hd__buf_2 input5 (.A(rst_n),
    .X(net4));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input6 (.A(sched_aux[0]),
    .X(net5));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input7 (.A(sched_aux[1]),
    .X(net6));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input8 (.A(sched_aux[2]),
    .X(net7));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input9 (.A(sched_aux[3]),
    .X(net8));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output100 (.A(net99),
    .X(fb_wr_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output101 (.A(net100),
    .X(fb_wr_bank[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output102 (.A(net69),
    .X(net101));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output43 (.A(net42),
    .X(cmd_out_aux[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output44 (.A(net43),
    .X(cmd_out_aux[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output45 (.A(net44),
    .X(cmd_out_aux[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output46 (.A(net45),
    .X(cmd_out_aux[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output47 (.A(net46),
    .X(cmd_out_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output48 (.A(net47),
    .X(cmd_out_we));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output49 (.A(net48),
    .X(ddr_addr[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output50 (.A(net49),
    .X(ddr_addr[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output51 (.A(net50),
    .X(ddr_addr[11]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output52 (.A(net51),
    .X(ddr_addr[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output53 (.A(net52),
    .X(ddr_addr[13]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output54 (.A(net53),
    .X(ddr_addr[14]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output55 (.A(net54),
    .X(ddr_addr[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output56 (.A(net55),
    .X(ddr_addr[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output57 (.A(net56),
    .X(ddr_addr[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output58 (.A(net57),
    .X(ddr_addr[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output59 (.A(net58),
    .X(ddr_addr[5]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output60 (.A(net59),
    .X(ddr_addr[6]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output61 (.A(net60),
    .X(ddr_addr[7]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output62 (.A(net61),
    .X(ddr_addr[8]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output63 (.A(net62),
    .X(ddr_addr[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output64 (.A(net63),
    .X(ddr_bank[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output65 (.A(net64),
    .X(ddr_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output66 (.A(net65),
    .X(ddr_bank[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output67 (.A(net66),
    .X(ddr_cmd[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output68 (.A(net67),
    .X(ddr_cmd[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output69 (.A(net68),
    .X(ddr_cmd[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output70 (.A(net69),
    .X(ddr_odt));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output71 (.A(net70),
    .X(fb_act_bank[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output72 (.A(net71),
    .X(fb_act_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output73 (.A(net72),
    .X(fb_act_bank[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output74 (.A(net73),
    .X(fb_act_row[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output75 (.A(net74),
    .X(fb_act_row[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output76 (.A(net75),
    .X(fb_act_row[11]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output77 (.A(net76),
    .X(fb_act_row[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output78 (.A(net77),
    .X(fb_act_row[13]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output79 (.A(net78),
    .X(fb_act_row[14]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output80 (.A(net79),
    .X(fb_act_row[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output81 (.A(net80),
    .X(fb_act_row[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output82 (.A(net81),
    .X(fb_act_row[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output83 (.A(net82),
    .X(fb_act_row[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output84 (.A(net83),
    .X(fb_act_row[5]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output85 (.A(net84),
    .X(fb_act_row[6]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output86 (.A(net85),
    .X(fb_act_row[7]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output87 (.A(net86),
    .X(fb_act_row[8]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output88 (.A(net87),
    .X(fb_act_row[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output89 (.A(net88),
    .X(fb_act_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output90 (.A(net89),
    .X(fb_pre_bank[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output91 (.A(net90),
    .X(fb_pre_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output92 (.A(net91),
    .X(fb_pre_bank[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output93 (.A(net92),
    .X(fb_pre_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output94 (.A(net93),
    .X(fb_rd_bank[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output95 (.A(net94),
    .X(fb_rd_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output96 (.A(net95),
    .X(fb_rd_bank[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output97 (.A(net96),
    .X(fb_rd_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output98 (.A(net97),
    .X(fb_ref_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output99 (.A(net98),
    .X(fb_wr_bank[0]));
 sky130_fd_sc_hd__buf_4 place108 (.A(_065_),
    .X(net107));
 sky130_fd_sc_hd__buf_4 place109 (.A(net4),
    .X(net108));
 assign fb_wr_valid = net101;
endmodule
