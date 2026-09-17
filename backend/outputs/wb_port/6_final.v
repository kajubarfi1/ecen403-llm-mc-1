module wb_port (clk,
    req_ready,
    req_valid,
    req_we,
    rsp_valid,
    rst_n,
    wb_ack_o,
    wb_cyc_i,
    wb_err_o,
    wb_stall_o,
    wb_stb_i,
    wb_we_i,
    req_addr,
    req_aux,
    req_wdata,
    req_wmask,
    rsp_aux,
    rsp_rdata,
    wb_adr_i,
    wb_bte_i,
    wb_cti_i,
    wb_dat_i,
    wb_dat_o,
    wb_sel_i);
 input clk;
 input req_ready;
 output req_valid;
 output req_we;
 input rsp_valid;
 input rst_n;
 output wb_ack_o;
 input wb_cyc_i;
 output wb_err_o;
 output wb_stall_o;
 input wb_stb_i;
 input wb_we_i;
 output [28:0] req_addr;
 output [3:0] req_aux;
 output [31:0] req_wdata;
 output [3:0] req_wmask;
 input [3:0] rsp_aux;
 input [31:0] rsp_rdata;
 input [28:0] wb_adr_i;
 input [1:0] wb_bte_i;
 input [2:0] wb_cti_i;
 input [31:0] wb_dat_i;
 output [31:0] wb_dat_o;
 input [3:0] wb_sel_i;

 wire _000_;
 wire _001_;
 wire _002_;
 wire _003_;
 wire _004_;
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
 wire _060_;
 wire _061_;
 wire _062_;
 wire _063_;
 wire _064_;
 wire _065_;
 wire _066_;
 wire _067_;
 wire _068_;
 wire _069_;
 wire _070_;
 wire _071_;
 wire _072_;
 wire _073_;
 wire _074_;
 wire _075_;
 wire _076_;
 wire _077_;
 wire _078_;
 wire _079_;
 wire _080_;
 wire _081_;
 wire _082_;
 wire _083_;
 wire _084_;
 wire _085_;
 wire _086_;
 wire _087_;
 wire _088_;
 wire _089_;
 wire _090_;
 wire _091_;
 wire _092_;
 wire _093_;
 wire _094_;
 wire _095_;
 wire _096_;
 wire _097_;
 wire _098_;
 wire _099_;
 wire _100_;
 wire _101_;
 wire _102_;
 wire _103_;
 wire _104_;
 wire _105_;
 wire _106_;
 wire _107_;
 wire _108_;
 wire _109_;
 wire _110_;
 wire _111_;
 wire _112_;
 wire _113_;
 wire _114_;
 wire _115_;
 wire _116_;
 wire _117_;
 wire _119_;
 wire _120_;
 wire _121_;
 wire _122_;
 wire _123_;
 wire _124_;
 wire _125_;
 wire _126_;
 wire _127_;
 wire _128_;
 wire _129_;
 wire _130_;
 wire _131_;
 wire _132_;
 wire _134_;
 wire _135_;
 wire _137_;
 wire _138_;
 wire _139_;
 wire _140_;
 wire _141_;
 wire _142_;
 wire _143_;
 wire _144_;
 wire _145_;
 wire _146_;
 wire _147_;
 wire _148_;
 wire _149_;
 wire _150_;
 wire _151_;
 wire _152_;
 wire _159_;
 wire _160_;
 wire _161_;
 wire _162_;
 wire _163_;
 wire _164_;
 wire _165_;
 wire _166_;
 wire _167_;
 wire _168_;
 wire _169_;
 wire _170_;
 wire _171_;
 wire _172_;
 wire _173_;
 wire \aux_ctr[0] ;
 wire \aux_ctr[1] ;
 wire \aux_ctr[2] ;
 wire \aux_ctr[3] ;
 wire burst_active;
 wire \burst_cnt[0] ;
 wire \burst_cnt[1] ;
 wire \burst_cnt[2] ;
 wire burst_we;
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
 wire net101;
 wire net102;
 wire net103;
 wire net104;
 wire net105;
 wire net106;
 wire net107;
 wire net1;
 wire net108;
 wire net109;
 wire net110;
 wire net111;
 wire net112;
 wire net113;
 wire net114;
 wire net115;
 wire net116;
 wire net117;
 wire net118;
 wire net119;
 wire net120;
 wire net121;
 wire net122;
 wire net123;
 wire net124;
 wire net125;
 wire net126;
 wire net127;
 wire net128;
 wire net129;
 wire net130;
 wire net131;
 wire net132;
 wire net133;
 wire net134;
 wire net135;
 wire net136;
 wire net137;
 wire net138;
 wire net139;
 wire net140;
 wire net141;
 wire net142;
 wire net143;
 wire net144;
 wire net145;
 wire net2;
 wire net3;
 wire \tag_rd[0] ;
 wire \tag_rd[1] ;
 wire \tag_rd[2] ;
 wire \tag_rd[3] ;
 wire \tag_rd[4] ;
 wire \tag_rd[5] ;
 wire \tag_wr[0] ;
 wire \tag_wr[1] ;
 wire \tag_wr[2] ;
 wire \tag_wr[3] ;
 wire \tag_wr[4] ;
 wire \tag_wr[5] ;
 wire net146;
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
 wire net147;
 wire net69;
 wire net70;
 wire net71;
 wire net72;
 wire net148;
 wire net73;
 wire net74;
 wire wr_ack_r;
 wire clknet_0_clk;
 wire clknet_3_0__leaf_clk;
 wire net156;
 wire net155;
 wire net157;
 wire clknet_3_1__leaf_clk;
 wire clknet_3_2__leaf_clk;
 wire clknet_3_3__leaf_clk;
 wire clknet_3_4__leaf_clk;
 wire clknet_3_5__leaf_clk;
 wire clknet_3_6__leaf_clk;
 wire clknet_3_7__leaf_clk;

 sky130_fd_sc_hd__inv_1 _174_ (.A(net73),
    .Y(_117_));
 sky130_fd_sc_hd__nand2_1 _176_ (.A(_004_),
    .B(_007_),
    .Y(_119_));
 sky130_fd_sc_hd__xor2_1 _177_ (.A(\tag_rd[5] ),
    .B(_015_),
    .X(_120_));
 sky130_fd_sc_hd__xnor2_1 _178_ (.A(\tag_wr[5] ),
    .B(_120_),
    .Y(_121_));
 sky130_fd_sc_hd__o41ai_1 _179_ (.A1(_117_),
    .A2(net74),
    .A3(_119_),
    .A4(_121_),
    .B1(net1),
    .Y(_122_));
 sky130_fd_sc_hd__nor2b_1 _180_ (.A(_003_),
    .B_N(_007_),
    .Y(_123_));
 sky130_fd_sc_hd__xor2_1 _181_ (.A(_010_),
    .B(_012_),
    .X(_124_));
 sky130_fd_sc_hd__or4_1 _182_ (.A(_013_),
    .B(_006_),
    .C(_123_),
    .D(_124_),
    .X(_125_));
 sky130_fd_sc_hd__inv_1 _183_ (.A(_016_),
    .Y(_126_));
 sky130_fd_sc_hd__a21oi_1 _184_ (.A1(_010_),
    .A2(_012_),
    .B1(_009_),
    .Y(_127_));
 sky130_fd_sc_hd__xnor2_1 _185_ (.A(_126_),
    .B(_127_),
    .Y(_128_));
 sky130_fd_sc_hd__o2111ai_1 _186_ (.A1(_006_),
    .A2(_123_),
    .B1(_013_),
    .C1(_126_),
    .D1(_010_),
    .Y(_129_));
 sky130_fd_sc_hd__o211ai_2 _187_ (.A1(_125_),
    .A2(_128_),
    .B1(_129_),
    .C1(net1),
    .Y(_130_));
 sky130_fd_sc_hd__nand2_1 _188_ (.A(net73),
    .B(net36),
    .Y(_131_));
 sky130_fd_sc_hd__a21oi_4 _189_ (.A1(_122_),
    .A2(_130_),
    .B1(_131_),
    .Y(_132_));
 sky130_fd_sc_hd__and2_1 _192_ (.A(net74),
    .B(net156),
    .X(_001_));
 sky130_fd_sc_hd__xor2_1 _193_ (.A(net74),
    .B(burst_we),
    .X(_134_));
 sky130_fd_sc_hd__a211oi_1 _194_ (.A1(burst_active),
    .A2(_134_),
    .B1(net4),
    .C1(net15),
    .Y(_135_));
 sky130_fd_sc_hd__nor2_1 _195_ (.A(_131_),
    .B(_135_),
    .Y(_000_));
 sky130_fd_sc_hd__inv_1 _196_ (.A(\tag_wr[0] ),
    .Y(_002_));
 sky130_fd_sc_hd__inv_1 _197_ (.A(\tag_rd[1] ),
    .Y(_005_));
 sky130_fd_sc_hd__inv_1 _198_ (.A(\tag_rd[3] ),
    .Y(_008_));
 sky130_fd_sc_hd__inv_1 _199_ (.A(\tag_rd[2] ),
    .Y(_011_));
 sky130_fd_sc_hd__inv_1 _200_ (.A(\tag_rd[4] ),
    .Y(_014_));
 sky130_fd_sc_hd__xor2_1 _201_ (.A(\aux_ctr[0] ),
    .B(net155),
    .X(_026_));
 sky130_fd_sc_hd__mux2_4 _203_ (.A0(\aux_ctr[1] ),
    .A1(_018_),
    .S(net155),
    .X(_027_));
 sky130_fd_sc_hd__nand2_1 _204_ (.A(_017_),
    .B(net155),
    .Y(_137_));
 sky130_fd_sc_hd__xnor2_1 _205_ (.A(\aux_ctr[2] ),
    .B(_137_),
    .Y(_028_));
 sky130_fd_sc_hd__nand4_1 _206_ (.A(\aux_ctr[2] ),
    .B(\aux_ctr[1] ),
    .C(\aux_ctr[0] ),
    .D(net155),
    .Y(_138_));
 sky130_fd_sc_hd__xnor2_1 _207_ (.A(\aux_ctr[3] ),
    .B(_138_),
    .Y(_029_));
 sky130_fd_sc_hd__nor3b_1 _208_ (.A(net33),
    .B(net35),
    .C_N(net34),
    .Y(_139_));
 sky130_fd_sc_hd__nand3b_1 _209_ (.A_N(burst_active),
    .B(net156),
    .C(_139_),
    .Y(_140_));
 sky130_fd_sc_hd__and2_1 _210_ (.A(_122_),
    .B(_130_),
    .X(net148));
 sky130_fd_sc_hd__a31oi_1 _211_ (.A1(net34),
    .A2(net33),
    .A3(net35),
    .B1(_024_),
    .Y(_141_));
 sky130_fd_sc_hd__o311ai_0 _212_ (.A1(_117_),
    .A2(net148),
    .A3(_141_),
    .B1(net36),
    .C1(burst_active),
    .Y(_142_));
 sky130_fd_sc_hd__nand2_1 _213_ (.A(_140_),
    .B(_142_),
    .Y(_030_));
 sky130_fd_sc_hd__nand2_1 _214_ (.A(net36),
    .B(\burst_cnt[0] ),
    .Y(_143_));
 sky130_fd_sc_hd__inv_1 _215_ (.A(_141_),
    .Y(_144_));
 sky130_fd_sc_hd__o21ai_0 _216_ (.A1(\burst_cnt[0] ),
    .A2(_144_),
    .B1(burst_active),
    .Y(_145_));
 sky130_fd_sc_hd__o311ai_0 _217_ (.A1(burst_active),
    .A2(\burst_cnt[0] ),
    .A3(_139_),
    .B1(_145_),
    .C1(net156),
    .Y(_146_));
 sky130_fd_sc_hd__o21ai_0 _218_ (.A1(net156),
    .A2(_143_),
    .B1(_146_),
    .Y(_031_));
 sky130_fd_sc_hd__inv_1 _219_ (.A(\burst_cnt[1] ),
    .Y(_147_));
 sky130_fd_sc_hd__o21ai_0 _220_ (.A1(burst_active),
    .A2(_139_),
    .B1(net73),
    .Y(_148_));
 sky130_fd_sc_hd__o21ai_0 _221_ (.A1(net148),
    .A2(_148_),
    .B1(net36),
    .Y(_149_));
 sky130_fd_sc_hd__nand4_1 _222_ (.A(burst_active),
    .B(_023_),
    .C(net156),
    .D(_141_),
    .Y(_150_));
 sky130_fd_sc_hd__o21ai_0 _223_ (.A1(_147_),
    .A2(_149_),
    .B1(_150_),
    .Y(_032_));
 sky130_fd_sc_hd__inv_1 _224_ (.A(\burst_cnt[2] ),
    .Y(_151_));
 sky130_fd_sc_hd__nand4_1 _225_ (.A(burst_active),
    .B(_025_),
    .C(net156),
    .D(_141_),
    .Y(_152_));
 sky130_fd_sc_hd__o21ai_0 _226_ (.A1(_151_),
    .A2(_149_),
    .B1(_152_),
    .Y(_033_));
 sky130_fd_sc_hd__mux2_2 _227_ (.A0(net74),
    .A1(burst_we),
    .S(_140_),
    .X(_034_));
 sky130_fd_sc_hd__mux2_4 _228_ (.A0(net75),
    .A1(net4),
    .S(net155),
    .X(_035_));
 sky130_fd_sc_hd__mux2_4 _229_ (.A0(net76),
    .A1(net5),
    .S(net155),
    .X(_036_));
 sky130_fd_sc_hd__mux2_4 _230_ (.A0(net77),
    .A1(net6),
    .S(net155),
    .X(_037_));
 sky130_fd_sc_hd__mux2_4 _231_ (.A0(net78),
    .A1(net7),
    .S(net155),
    .X(_038_));
 sky130_fd_sc_hd__mux2_4 _232_ (.A0(net79),
    .A1(net8),
    .S(net155),
    .X(_039_));
 sky130_fd_sc_hd__mux2_4 _233_ (.A0(net80),
    .A1(net9),
    .S(net155),
    .X(_040_));
 sky130_fd_sc_hd__mux2_4 _234_ (.A0(net81),
    .A1(net10),
    .S(net155),
    .X(_041_));
 sky130_fd_sc_hd__mux2_4 _236_ (.A0(net82),
    .A1(net11),
    .S(net156),
    .X(_042_));
 sky130_fd_sc_hd__mux2_4 _237_ (.A0(net83),
    .A1(net12),
    .S(net156),
    .X(_043_));
 sky130_fd_sc_hd__mux2_4 _238_ (.A0(net84),
    .A1(net13),
    .S(net156),
    .X(_044_));
 sky130_fd_sc_hd__mux2_4 _239_ (.A0(net85),
    .A1(net14),
    .S(net156),
    .X(_045_));
 sky130_fd_sc_hd__mux2_4 _240_ (.A0(net86),
    .A1(net15),
    .S(net155),
    .X(_046_));
 sky130_fd_sc_hd__mux2_4 _241_ (.A0(net87),
    .A1(net16),
    .S(net155),
    .X(_047_));
 sky130_fd_sc_hd__mux2_4 _242_ (.A0(net88),
    .A1(net17),
    .S(net155),
    .X(_048_));
 sky130_fd_sc_hd__mux2_4 _243_ (.A0(net89),
    .A1(net18),
    .S(net155),
    .X(_049_));
 sky130_fd_sc_hd__mux2_4 _244_ (.A0(net90),
    .A1(net19),
    .S(net156),
    .X(_050_));
 sky130_fd_sc_hd__mux2_4 _245_ (.A0(net91),
    .A1(net20),
    .S(net156),
    .X(_051_));
 sky130_fd_sc_hd__mux2_4 _247_ (.A0(net92),
    .A1(net21),
    .S(net156),
    .X(_052_));
 sky130_fd_sc_hd__mux2_4 _248_ (.A0(net93),
    .A1(net22),
    .S(net156),
    .X(_053_));
 sky130_fd_sc_hd__mux2_4 _249_ (.A0(net94),
    .A1(net23),
    .S(net156),
    .X(_054_));
 sky130_fd_sc_hd__mux2_4 _250_ (.A0(net95),
    .A1(net24),
    .S(net156),
    .X(_055_));
 sky130_fd_sc_hd__mux2_4 _251_ (.A0(net96),
    .A1(net25),
    .S(net156),
    .X(_056_));
 sky130_fd_sc_hd__mux2_4 _252_ (.A0(net97),
    .A1(net26),
    .S(net156),
    .X(_057_));
 sky130_fd_sc_hd__mux2_4 _253_ (.A0(net98),
    .A1(net27),
    .S(net156),
    .X(_058_));
 sky130_fd_sc_hd__mux2_4 _254_ (.A0(net99),
    .A1(net28),
    .S(net156),
    .X(_059_));
 sky130_fd_sc_hd__mux2_4 _255_ (.A0(net100),
    .A1(net29),
    .S(net156),
    .X(_060_));
 sky130_fd_sc_hd__mux2_4 _256_ (.A0(net101),
    .A1(net30),
    .S(net156),
    .X(_061_));
 sky130_fd_sc_hd__mux2_4 _258_ (.A0(net102),
    .A1(net31),
    .S(net155),
    .X(_062_));
 sky130_fd_sc_hd__mux2_4 _259_ (.A0(net103),
    .A1(net32),
    .S(net155),
    .X(_063_));
 sky130_fd_sc_hd__mux2_4 _260_ (.A0(net104),
    .A1(\aux_ctr[0] ),
    .S(net155),
    .X(_064_));
 sky130_fd_sc_hd__mux2_4 _261_ (.A0(net105),
    .A1(\aux_ctr[1] ),
    .S(net155),
    .X(_065_));
 sky130_fd_sc_hd__mux2_4 _262_ (.A0(net106),
    .A1(\aux_ctr[2] ),
    .S(net155),
    .X(_066_));
 sky130_fd_sc_hd__mux2_4 _263_ (.A0(net107),
    .A1(\aux_ctr[3] ),
    .S(net155),
    .X(_067_));
 sky130_fd_sc_hd__mux2_4 _264_ (.A0(net109),
    .A1(net37),
    .S(net155),
    .X(_068_));
 sky130_fd_sc_hd__mux2_4 _265_ (.A0(net110),
    .A1(net38),
    .S(net155),
    .X(_069_));
 sky130_fd_sc_hd__mux2_4 _266_ (.A0(net111),
    .A1(net39),
    .S(net155),
    .X(_070_));
 sky130_fd_sc_hd__mux2_4 _267_ (.A0(net112),
    .A1(net40),
    .S(net155),
    .X(_071_));
 sky130_fd_sc_hd__mux2_2 _269_ (.A0(net113),
    .A1(net41),
    .S(net156),
    .X(_072_));
 sky130_fd_sc_hd__mux2_2 _270_ (.A0(net114),
    .A1(net42),
    .S(net156),
    .X(_073_));
 sky130_fd_sc_hd__mux2_2 _271_ (.A0(net115),
    .A1(net43),
    .S(net156),
    .X(_074_));
 sky130_fd_sc_hd__mux2_2 _272_ (.A0(net116),
    .A1(net44),
    .S(net156),
    .X(_075_));
 sky130_fd_sc_hd__mux2_2 _273_ (.A0(net117),
    .A1(net45),
    .S(net156),
    .X(_076_));
 sky130_fd_sc_hd__mux2_2 _274_ (.A0(net118),
    .A1(net46),
    .S(net156),
    .X(_077_));
 sky130_fd_sc_hd__mux2_2 _275_ (.A0(net119),
    .A1(net47),
    .S(net156),
    .X(_078_));
 sky130_fd_sc_hd__mux2_2 _276_ (.A0(net120),
    .A1(net48),
    .S(net156),
    .X(_079_));
 sky130_fd_sc_hd__mux2_2 _277_ (.A0(net121),
    .A1(net49),
    .S(net156),
    .X(_080_));
 sky130_fd_sc_hd__mux2_2 _278_ (.A0(net122),
    .A1(net50),
    .S(net156),
    .X(_081_));
 sky130_fd_sc_hd__mux2_2 _280_ (.A0(net123),
    .A1(net51),
    .S(net156),
    .X(_082_));
 sky130_fd_sc_hd__mux2_2 _281_ (.A0(net124),
    .A1(net52),
    .S(net156),
    .X(_083_));
 sky130_fd_sc_hd__mux2_2 _282_ (.A0(net125),
    .A1(net53),
    .S(net156),
    .X(_084_));
 sky130_fd_sc_hd__mux2_2 _283_ (.A0(net126),
    .A1(net54),
    .S(net156),
    .X(_085_));
 sky130_fd_sc_hd__mux2_2 _284_ (.A0(net127),
    .A1(net55),
    .S(net156),
    .X(_086_));
 sky130_fd_sc_hd__mux2_2 _285_ (.A0(net128),
    .A1(net56),
    .S(net156),
    .X(_087_));
 sky130_fd_sc_hd__mux2_2 _286_ (.A0(net129),
    .A1(net57),
    .S(net156),
    .X(_088_));
 sky130_fd_sc_hd__mux2_2 _287_ (.A0(net130),
    .A1(net58),
    .S(net156),
    .X(_089_));
 sky130_fd_sc_hd__mux2_2 _288_ (.A0(net131),
    .A1(net59),
    .S(net156),
    .X(_090_));
 sky130_fd_sc_hd__mux2_2 _289_ (.A0(net132),
    .A1(net60),
    .S(net156),
    .X(_091_));
 sky130_fd_sc_hd__mux2_2 _291_ (.A0(net133),
    .A1(net61),
    .S(net156),
    .X(_092_));
 sky130_fd_sc_hd__mux2_2 _292_ (.A0(net134),
    .A1(net62),
    .S(net156),
    .X(_093_));
 sky130_fd_sc_hd__mux2_2 _293_ (.A0(net135),
    .A1(net63),
    .S(net156),
    .X(_094_));
 sky130_fd_sc_hd__mux2_2 _294_ (.A0(net136),
    .A1(net64),
    .S(net156),
    .X(_095_));
 sky130_fd_sc_hd__mux2_2 _295_ (.A0(net137),
    .A1(net65),
    .S(net156),
    .X(_096_));
 sky130_fd_sc_hd__mux2_2 _296_ (.A0(net138),
    .A1(net66),
    .S(net156),
    .X(_097_));
 sky130_fd_sc_hd__mux2_2 _297_ (.A0(net139),
    .A1(net67),
    .S(net156),
    .X(_098_));
 sky130_fd_sc_hd__mux2_2 _298_ (.A0(net140),
    .A1(net68),
    .S(net156),
    .X(_099_));
 sky130_fd_sc_hd__mux2_2 _299_ (.A0(net141),
    .A1(net74),
    .S(net156),
    .X(_100_));
 sky130_fd_sc_hd__mux2_2 _300_ (.A0(net142),
    .A1(net69),
    .S(net156),
    .X(_101_));
 sky130_fd_sc_hd__mux2_2 _301_ (.A0(net143),
    .A1(net70),
    .S(net156),
    .X(_102_));
 sky130_fd_sc_hd__mux2_2 _302_ (.A0(net144),
    .A1(net71),
    .S(net156),
    .X(_103_));
 sky130_fd_sc_hd__mux2_2 _303_ (.A0(net145),
    .A1(net72),
    .S(net156),
    .X(_104_));
 sky130_fd_sc_hd__xor2_1 _304_ (.A(\tag_rd[0] ),
    .B(net2),
    .X(_105_));
 sky130_fd_sc_hd__nand2_1 _305_ (.A(net2),
    .B(_020_),
    .Y(_159_));
 sky130_fd_sc_hd__o21ai_0 _306_ (.A1(_005_),
    .A2(net2),
    .B1(_159_),
    .Y(_106_));
 sky130_fd_sc_hd__nand2_1 _307_ (.A(_019_),
    .B(net2),
    .Y(_160_));
 sky130_fd_sc_hd__xnor2_1 _308_ (.A(\tag_rd[2] ),
    .B(_160_),
    .Y(_107_));
 sky130_fd_sc_hd__nand4_1 _309_ (.A(\tag_rd[0] ),
    .B(\tag_rd[2] ),
    .C(\tag_rd[1] ),
    .D(net2),
    .Y(_161_));
 sky130_fd_sc_hd__xnor2_1 _310_ (.A(\tag_rd[3] ),
    .B(_161_),
    .Y(_108_));
 sky130_fd_sc_hd__nand4_1 _311_ (.A(_019_),
    .B(\tag_rd[2] ),
    .C(\tag_rd[3] ),
    .D(net2),
    .Y(_162_));
 sky130_fd_sc_hd__xnor2_1 _312_ (.A(\tag_rd[4] ),
    .B(_162_),
    .Y(_109_));
 sky130_fd_sc_hd__nor3_1 _313_ (.A(_008_),
    .B(_014_),
    .C(_161_),
    .Y(_163_));
 sky130_fd_sc_hd__xor2_1 _314_ (.A(\tag_rd[5] ),
    .B(_163_),
    .X(_110_));
 sky130_fd_sc_hd__nor3_1 _315_ (.A(net74),
    .B(_131_),
    .C(net148),
    .Y(_164_));
 sky130_fd_sc_hd__xnor2_1 _316_ (.A(_002_),
    .B(_164_),
    .Y(_111_));
 sky130_fd_sc_hd__mux2_2 _317_ (.A0(\tag_wr[1] ),
    .A1(_022_),
    .S(_164_),
    .X(_112_));
 sky130_fd_sc_hd__nor2b_1 _318_ (.A(net74),
    .B_N(_021_),
    .Y(_165_));
 sky130_fd_sc_hd__nand2_1 _319_ (.A(net156),
    .B(_165_),
    .Y(_166_));
 sky130_fd_sc_hd__xnor2_1 _320_ (.A(\tag_wr[2] ),
    .B(_166_),
    .Y(_113_));
 sky130_fd_sc_hd__nand2_1 _321_ (.A(\tag_wr[1] ),
    .B(\tag_wr[0] ),
    .Y(_167_));
 sky130_fd_sc_hd__nor2_1 _322_ (.A(net74),
    .B(_167_),
    .Y(_168_));
 sky130_fd_sc_hd__nand3_1 _323_ (.A(\tag_wr[2] ),
    .B(net156),
    .C(_168_),
    .Y(_169_));
 sky130_fd_sc_hd__xnor2_1 _324_ (.A(\tag_wr[3] ),
    .B(_169_),
    .Y(_114_));
 sky130_fd_sc_hd__and2_1 _325_ (.A(\tag_wr[2] ),
    .B(\tag_wr[3] ),
    .X(_170_));
 sky130_fd_sc_hd__nand3_1 _326_ (.A(net156),
    .B(_165_),
    .C(_170_),
    .Y(_171_));
 sky130_fd_sc_hd__xnor2_1 _327_ (.A(\tag_wr[4] ),
    .B(_171_),
    .Y(_115_));
 sky130_fd_sc_hd__and4_1 _328_ (.A(\tag_wr[4] ),
    .B(net156),
    .C(_168_),
    .D(_170_),
    .X(_172_));
 sky130_fd_sc_hd__xor2_1 _329_ (.A(\tag_wr[5] ),
    .B(_172_),
    .X(_116_));
 sky130_fd_sc_hd__or2_2 _330_ (.A(net2),
    .B(wr_ack_r),
    .X(net146));
 sky130_fd_sc_hd__ha_1 _331_ (.A(_002_),
    .B(\tag_rd[0] ),
    .COUT(_003_),
    .SUM(_004_));
 sky130_fd_sc_hd__ha_1 _332_ (.A(\tag_wr[1] ),
    .B(_005_),
    .COUT(_006_),
    .SUM(_007_));
 sky130_fd_sc_hd__ha_1 _333_ (.A(\tag_wr[3] ),
    .B(_008_),
    .COUT(_009_),
    .SUM(_010_));
 sky130_fd_sc_hd__ha_1 _334_ (.A(\tag_wr[2] ),
    .B(_011_),
    .COUT(_012_),
    .SUM(_013_));
 sky130_fd_sc_hd__ha_1 _335_ (.A(\tag_wr[4] ),
    .B(_014_),
    .COUT(_015_),
    .SUM(_016_));
 sky130_fd_sc_hd__ha_1 _336_ (.A(\aux_ctr[0] ),
    .B(\aux_ctr[1] ),
    .COUT(_017_),
    .SUM(_018_));
 sky130_fd_sc_hd__ha_1 _337_ (.A(\tag_rd[0] ),
    .B(\tag_rd[1] ),
    .COUT(_019_),
    .SUM(_020_));
 sky130_fd_sc_hd__ha_1 _338_ (.A(\tag_wr[0] ),
    .B(\tag_wr[1] ),
    .COUT(_021_),
    .SUM(_022_));
 sky130_fd_sc_hd__ha_1 _339_ (.A(\burst_cnt[0] ),
    .B(\burst_cnt[1] ),
    .COUT(_173_),
    .SUM(_023_));
 sky130_fd_sc_hd__ha_1 _340_ (.A(\burst_cnt[2] ),
    .B(_173_),
    .COUT(_024_),
    .SUM(_025_));
 sky130_fd_sc_hd__dfrtp_1 \aux_ctr[0]$_DFFE_PN0P_  (.D(_026_),
    .Q(\aux_ctr[0] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \aux_ctr[1]$_DFFE_PN0P_  (.D(_027_),
    .Q(\aux_ctr[1] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \aux_ctr[2]$_DFFE_PN0P_  (.D(_028_),
    .Q(\aux_ctr[2] ),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \aux_ctr[3]$_DFFE_PN0P_  (.D(_029_),
    .Q(\aux_ctr[3] ),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \burst_active$_DFFE_PN0P_  (.D(_030_),
    .Q(burst_active),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \burst_cnt[0]$_DFFE_PN0P_  (.D(_031_),
    .Q(\burst_cnt[0] ),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \burst_cnt[1]$_DFFE_PN0P_  (.D(_032_),
    .Q(\burst_cnt[1] ),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \burst_cnt[2]$_DFFE_PN0P_  (.D(_033_),
    .Q(\burst_cnt[2] ),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \burst_we$_DFFE_PN0P_  (.D(_034_),
    .Q(burst_we),
    .RESET_B(net157),
    .CLK(clknet_3_1__leaf_clk));
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
 sky130_fd_sc_hd__clkinv_2 clkload0 (.A(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__inv_6 clkload1 (.A(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__bufinv_16 clkload2 (.A(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload3 (.A(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload4 (.A(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkload5 (.A(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \err_r$_DFF_PN0_  (.D(_000_),
    .Q(net147),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input1 (.A(req_ready),
    .X(net1));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(wb_adr_i[15]),
    .X(net10));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input11 (.A(wb_adr_i[16]),
    .X(net11));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input12 (.A(wb_adr_i[17]),
    .X(net12));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input13 (.A(wb_adr_i[18]),
    .X(net13));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input14 (.A(wb_adr_i[19]),
    .X(net14));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input15 (.A(wb_adr_i[1]),
    .X(net15));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input16 (.A(wb_adr_i[20]),
    .X(net16));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input17 (.A(wb_adr_i[21]),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input18 (.A(wb_adr_i[22]),
    .X(net18));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input19 (.A(wb_adr_i[23]),
    .X(net19));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input2 (.A(rsp_valid),
    .X(net2));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input20 (.A(wb_adr_i[24]),
    .X(net20));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input21 (.A(wb_adr_i[25]),
    .X(net21));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input22 (.A(wb_adr_i[26]),
    .X(net22));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input23 (.A(wb_adr_i[27]),
    .X(net23));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input24 (.A(wb_adr_i[28]),
    .X(net24));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input25 (.A(wb_adr_i[2]),
    .X(net25));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input26 (.A(wb_adr_i[3]),
    .X(net26));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input27 (.A(wb_adr_i[4]),
    .X(net27));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input28 (.A(wb_adr_i[5]),
    .X(net28));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input29 (.A(wb_adr_i[6]),
    .X(net29));
 sky130_fd_sc_hd__buf_4 input3 (.A(rst_n),
    .X(net3));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input30 (.A(wb_adr_i[7]),
    .X(net30));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input31 (.A(wb_adr_i[8]),
    .X(net31));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input32 (.A(wb_adr_i[9]),
    .X(net32));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input33 (.A(wb_cti_i[0]),
    .X(net33));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input34 (.A(wb_cti_i[1]),
    .X(net34));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input35 (.A(wb_cti_i[2]),
    .X(net35));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input36 (.A(wb_cyc_i),
    .X(net36));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input37 (.A(wb_dat_i[0]),
    .X(net37));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input38 (.A(wb_dat_i[10]),
    .X(net38));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input39 (.A(wb_dat_i[11]),
    .X(net39));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input4 (.A(wb_adr_i[0]),
    .X(net4));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input40 (.A(wb_dat_i[12]),
    .X(net40));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input41 (.A(wb_dat_i[13]),
    .X(net41));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input42 (.A(wb_dat_i[14]),
    .X(net42));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input43 (.A(wb_dat_i[15]),
    .X(net43));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input44 (.A(wb_dat_i[16]),
    .X(net44));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input45 (.A(wb_dat_i[17]),
    .X(net45));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input46 (.A(wb_dat_i[18]),
    .X(net46));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input47 (.A(wb_dat_i[19]),
    .X(net47));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input48 (.A(wb_dat_i[1]),
    .X(net48));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input49 (.A(wb_dat_i[20]),
    .X(net49));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input5 (.A(wb_adr_i[10]),
    .X(net5));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input50 (.A(wb_dat_i[21]),
    .X(net50));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input51 (.A(wb_dat_i[22]),
    .X(net51));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input52 (.A(wb_dat_i[23]),
    .X(net52));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input53 (.A(wb_dat_i[24]),
    .X(net53));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input54 (.A(wb_dat_i[25]),
    .X(net54));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input55 (.A(wb_dat_i[26]),
    .X(net55));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input56 (.A(wb_dat_i[27]),
    .X(net56));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input57 (.A(wb_dat_i[28]),
    .X(net57));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input58 (.A(wb_dat_i[29]),
    .X(net58));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input59 (.A(wb_dat_i[2]),
    .X(net59));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input6 (.A(wb_adr_i[11]),
    .X(net6));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input60 (.A(wb_dat_i[30]),
    .X(net60));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input61 (.A(wb_dat_i[31]),
    .X(net61));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input62 (.A(wb_dat_i[3]),
    .X(net62));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input63 (.A(wb_dat_i[4]),
    .X(net63));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input64 (.A(wb_dat_i[5]),
    .X(net64));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input65 (.A(wb_dat_i[6]),
    .X(net65));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input66 (.A(wb_dat_i[7]),
    .X(net66));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input67 (.A(wb_dat_i[8]),
    .X(net67));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input68 (.A(wb_dat_i[9]),
    .X(net68));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input69 (.A(wb_sel_i[0]),
    .X(net69));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input7 (.A(wb_adr_i[12]),
    .X(net7));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input70 (.A(wb_sel_i[1]),
    .X(net70));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input71 (.A(wb_sel_i[2]),
    .X(net71));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input72 (.A(wb_sel_i[3]),
    .X(net72));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input73 (.A(wb_stb_i),
    .X(net73));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input74 (.A(wb_we_i),
    .X(net74));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input8 (.A(wb_adr_i[13]),
    .X(net8));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input9 (.A(wb_adr_i[14]),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output100 (.A(net100),
    .X(req_addr[6]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output101 (.A(net101),
    .X(req_addr[7]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output102 (.A(net102),
    .X(req_addr[8]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output103 (.A(net103),
    .X(req_addr[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output104 (.A(net104),
    .X(req_aux[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output105 (.A(net105),
    .X(req_aux[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output106 (.A(net106),
    .X(req_aux[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output107 (.A(net107),
    .X(req_aux[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output108 (.A(net108),
    .X(req_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output109 (.A(net109),
    .X(req_wdata[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output110 (.A(net110),
    .X(req_wdata[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output111 (.A(net111),
    .X(req_wdata[11]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output112 (.A(net112),
    .X(req_wdata[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output113 (.A(net113),
    .X(req_wdata[13]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output114 (.A(net114),
    .X(req_wdata[14]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output115 (.A(net115),
    .X(req_wdata[15]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output116 (.A(net116),
    .X(req_wdata[16]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output117 (.A(net117),
    .X(req_wdata[17]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output118 (.A(net118),
    .X(req_wdata[18]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output119 (.A(net119),
    .X(req_wdata[19]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output120 (.A(net120),
    .X(req_wdata[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output121 (.A(net121),
    .X(req_wdata[20]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output122 (.A(net122),
    .X(req_wdata[21]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output123 (.A(net123),
    .X(req_wdata[22]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output124 (.A(net124),
    .X(req_wdata[23]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output125 (.A(net125),
    .X(req_wdata[24]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output126 (.A(net126),
    .X(req_wdata[25]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output127 (.A(net127),
    .X(req_wdata[26]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output128 (.A(net128),
    .X(req_wdata[27]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output129 (.A(net129),
    .X(req_wdata[28]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output130 (.A(net130),
    .X(req_wdata[29]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output131 (.A(net131),
    .X(req_wdata[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output132 (.A(net132),
    .X(req_wdata[30]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output133 (.A(net133),
    .X(req_wdata[31]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output134 (.A(net134),
    .X(req_wdata[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output135 (.A(net135),
    .X(req_wdata[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output136 (.A(net136),
    .X(req_wdata[5]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output137 (.A(net137),
    .X(req_wdata[6]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output138 (.A(net138),
    .X(req_wdata[7]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output139 (.A(net139),
    .X(req_wdata[8]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output140 (.A(net140),
    .X(req_wdata[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output141 (.A(net141),
    .X(req_we));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output142 (.A(net142),
    .X(req_wmask[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output143 (.A(net143),
    .X(req_wmask[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output144 (.A(net144),
    .X(req_wmask[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output145 (.A(net145),
    .X(req_wmask[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output146 (.A(net146),
    .X(wb_ack_o));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output147 (.A(net147),
    .X(wb_err_o));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output148 (.A(net148),
    .X(wb_stall_o));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output75 (.A(net75),
    .X(req_addr[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output76 (.A(net76),
    .X(req_addr[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output77 (.A(net77),
    .X(req_addr[11]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output78 (.A(net78),
    .X(req_addr[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output79 (.A(net79),
    .X(req_addr[13]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output80 (.A(net80),
    .X(req_addr[14]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output81 (.A(net81),
    .X(req_addr[15]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output82 (.A(net82),
    .X(req_addr[16]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output83 (.A(net83),
    .X(req_addr[17]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output84 (.A(net84),
    .X(req_addr[18]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output85 (.A(net85),
    .X(req_addr[19]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output86 (.A(net86),
    .X(req_addr[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output87 (.A(net87),
    .X(req_addr[20]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output88 (.A(net88),
    .X(req_addr[21]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output89 (.A(net89),
    .X(req_addr[22]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output90 (.A(net90),
    .X(req_addr[23]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output91 (.A(net91),
    .X(req_addr[24]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output92 (.A(net92),
    .X(req_addr[25]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output93 (.A(net93),
    .X(req_addr[26]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output94 (.A(net94),
    .X(req_addr[27]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output95 (.A(net95),
    .X(req_addr[28]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output96 (.A(net96),
    .X(req_addr[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output97 (.A(net97),
    .X(req_addr[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output98 (.A(net98),
    .X(req_addr[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output99 (.A(net99),
    .X(req_addr[5]));
 sky130_fd_sc_hd__buf_4 place155 (.A(_132_),
    .X(net155));
 sky130_fd_sc_hd__buf_4 place156 (.A(_132_),
    .X(net156));
 sky130_fd_sc_hd__buf_4 place157 (.A(net3),
    .X(net157));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[0]$_DFFE_PN0P_  (.D(_035_),
    .Q(net75),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[10]$_DFFE_PN0P_  (.D(_036_),
    .Q(net76),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[11]$_DFFE_PN0P_  (.D(_037_),
    .Q(net77),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[12]$_DFFE_PN0P_  (.D(_038_),
    .Q(net78),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[13]$_DFFE_PN0P_  (.D(_039_),
    .Q(net79),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[14]$_DFFE_PN0P_  (.D(_040_),
    .Q(net80),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[15]$_DFFE_PN0P_  (.D(_041_),
    .Q(net81),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[16]$_DFFE_PN0P_  (.D(_042_),
    .Q(net82),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[17]$_DFFE_PN0P_  (.D(_043_),
    .Q(net83),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[18]$_DFFE_PN0P_  (.D(_044_),
    .Q(net84),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[19]$_DFFE_PN0P_  (.D(_045_),
    .Q(net85),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[1]$_DFFE_PN0P_  (.D(_046_),
    .Q(net86),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[20]$_DFFE_PN0P_  (.D(_047_),
    .Q(net87),
    .RESET_B(net3),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[21]$_DFFE_PN0P_  (.D(_048_),
    .Q(net88),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[22]$_DFFE_PN0P_  (.D(_049_),
    .Q(net89),
    .RESET_B(net3),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[23]$_DFFE_PN0P_  (.D(_050_),
    .Q(net90),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[24]$_DFFE_PN0P_  (.D(_051_),
    .Q(net91),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[25]$_DFFE_PN0P_  (.D(_052_),
    .Q(net92),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[26]$_DFFE_PN0P_  (.D(_053_),
    .Q(net93),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[27]$_DFFE_PN0P_  (.D(_054_),
    .Q(net94),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[28]$_DFFE_PN0P_  (.D(_055_),
    .Q(net95),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[2]$_DFFE_PN0P_  (.D(_056_),
    .Q(net96),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[3]$_DFFE_PN0P_  (.D(_057_),
    .Q(net97),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[4]$_DFFE_PN0P_  (.D(_058_),
    .Q(net98),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[5]$_DFFE_PN0P_  (.D(_059_),
    .Q(net99),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[6]$_DFFE_PN0P_  (.D(_060_),
    .Q(net100),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[7]$_DFFE_PN0P_  (.D(_061_),
    .Q(net101),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[8]$_DFFE_PN0P_  (.D(_062_),
    .Q(net102),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_addr[9]$_DFFE_PN0P_  (.D(_063_),
    .Q(net103),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_aux[0]$_DFFE_PN0P_  (.D(_064_),
    .Q(net104),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_aux[1]$_DFFE_PN0P_  (.D(_065_),
    .Q(net105),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_aux[2]$_DFFE_PN0P_  (.D(_066_),
    .Q(net106),
    .RESET_B(net3),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_aux[3]$_DFFE_PN0P_  (.D(_067_),
    .Q(net107),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_valid$_DFF_PN0_  (.D(net156),
    .Q(net108),
    .RESET_B(net157),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[0]$_DFFE_PN0P_  (.D(_068_),
    .Q(net109),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[10]$_DFFE_PN0P_  (.D(_069_),
    .Q(net110),
    .RESET_B(net3),
    .CLK(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[11]$_DFFE_PN0P_  (.D(_070_),
    .Q(net111),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[12]$_DFFE_PN0P_  (.D(_071_),
    .Q(net112),
    .RESET_B(net3),
    .CLK(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[13]$_DFFE_PN0P_  (.D(_072_),
    .Q(net113),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[14]$_DFFE_PN0P_  (.D(_073_),
    .Q(net114),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[15]$_DFFE_PN0P_  (.D(_074_),
    .Q(net115),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[16]$_DFFE_PN0P_  (.D(_075_),
    .Q(net116),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[17]$_DFFE_PN0P_  (.D(_076_),
    .Q(net117),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[18]$_DFFE_PN0P_  (.D(_077_),
    .Q(net118),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[19]$_DFFE_PN0P_  (.D(_078_),
    .Q(net119),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[1]$_DFFE_PN0P_  (.D(_079_),
    .Q(net120),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[20]$_DFFE_PN0P_  (.D(_080_),
    .Q(net121),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[21]$_DFFE_PN0P_  (.D(_081_),
    .Q(net122),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[22]$_DFFE_PN0P_  (.D(_082_),
    .Q(net123),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[23]$_DFFE_PN0P_  (.D(_083_),
    .Q(net124),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[24]$_DFFE_PN0P_  (.D(_084_),
    .Q(net125),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[25]$_DFFE_PN0P_  (.D(_085_),
    .Q(net126),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[26]$_DFFE_PN0P_  (.D(_086_),
    .Q(net127),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[27]$_DFFE_PN0P_  (.D(_087_),
    .Q(net128),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[28]$_DFFE_PN0P_  (.D(_088_),
    .Q(net129),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[29]$_DFFE_PN0P_  (.D(_089_),
    .Q(net130),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[2]$_DFFE_PN0P_  (.D(_090_),
    .Q(net131),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[30]$_DFFE_PN0P_  (.D(_091_),
    .Q(net132),
    .RESET_B(net157),
    .CLK(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[31]$_DFFE_PN0P_  (.D(_092_),
    .Q(net133),
    .RESET_B(net157),
    .CLK(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[3]$_DFFE_PN0P_  (.D(_093_),
    .Q(net134),
    .RESET_B(net3),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[4]$_DFFE_PN0P_  (.D(_094_),
    .Q(net135),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[5]$_DFFE_PN0P_  (.D(_095_),
    .Q(net136),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[6]$_DFFE_PN0P_  (.D(_096_),
    .Q(net137),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[7]$_DFFE_PN0P_  (.D(_097_),
    .Q(net138),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[8]$_DFFE_PN0P_  (.D(_098_),
    .Q(net139),
    .RESET_B(net157),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wdata[9]$_DFFE_PN0P_  (.D(_099_),
    .Q(net140),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_we$_DFFE_PN0P_  (.D(_100_),
    .Q(net141),
    .RESET_B(net3),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wmask[0]$_DFFE_PN0P_  (.D(_101_),
    .Q(net142),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wmask[1]$_DFFE_PN0P_  (.D(_102_),
    .Q(net143),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wmask[2]$_DFFE_PN0P_  (.D(_103_),
    .Q(net144),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \req_wmask[3]$_DFFE_PN0P_  (.D(_104_),
    .Q(net145),
    .RESET_B(net157),
    .CLK(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_rd[0]$_DFFE_PN0P_  (.D(_105_),
    .Q(\tag_rd[0] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_rd[1]$_DFFE_PN0P_  (.D(_106_),
    .Q(\tag_rd[1] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_rd[2]$_DFFE_PN0P_  (.D(_107_),
    .Q(\tag_rd[2] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_rd[3]$_DFFE_PN0P_  (.D(_108_),
    .Q(\tag_rd[3] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_rd[4]$_DFFE_PN0P_  (.D(_109_),
    .Q(\tag_rd[4] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_rd[5]$_DFFE_PN0P_  (.D(_110_),
    .Q(\tag_rd[5] ),
    .RESET_B(net3),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_wr[0]$_DFFE_PN0P_  (.D(_111_),
    .Q(\tag_wr[0] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_wr[1]$_DFFE_PN0P_  (.D(_112_),
    .Q(\tag_wr[1] ),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_wr[2]$_DFFE_PN0P_  (.D(_113_),
    .Q(\tag_wr[2] ),
    .RESET_B(net157),
    .CLK(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_wr[3]$_DFFE_PN0P_  (.D(_114_),
    .Q(\tag_wr[3] ),
    .RESET_B(net157),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_wr[4]$_DFFE_PN0P_  (.D(_115_),
    .Q(\tag_wr[4] ),
    .RESET_B(net157),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \tag_wr[5]$_DFFE_PN0P_  (.D(_116_),
    .Q(\tag_wr[5] ),
    .RESET_B(net157),
    .CLK(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_ack_r$_DFF_PN0_  (.D(_001_),
    .Q(wr_ack_r),
    .RESET_B(net3),
    .CLK(clknet_3_0__leaf_clk));
 assign wb_dat_o[0] = rsp_rdata[0];
 assign wb_dat_o[10] = rsp_rdata[10];
 assign wb_dat_o[11] = rsp_rdata[11];
 assign wb_dat_o[12] = rsp_rdata[12];
 assign wb_dat_o[13] = rsp_rdata[13];
 assign wb_dat_o[14] = rsp_rdata[14];
 assign wb_dat_o[15] = rsp_rdata[15];
 assign wb_dat_o[16] = rsp_rdata[16];
 assign wb_dat_o[17] = rsp_rdata[17];
 assign wb_dat_o[18] = rsp_rdata[18];
 assign wb_dat_o[19] = rsp_rdata[19];
 assign wb_dat_o[1] = rsp_rdata[1];
 assign wb_dat_o[20] = rsp_rdata[20];
 assign wb_dat_o[21] = rsp_rdata[21];
 assign wb_dat_o[22] = rsp_rdata[22];
 assign wb_dat_o[23] = rsp_rdata[23];
 assign wb_dat_o[24] = rsp_rdata[24];
 assign wb_dat_o[25] = rsp_rdata[25];
 assign wb_dat_o[26] = rsp_rdata[26];
 assign wb_dat_o[27] = rsp_rdata[27];
 assign wb_dat_o[28] = rsp_rdata[28];
 assign wb_dat_o[29] = rsp_rdata[29];
 assign wb_dat_o[2] = rsp_rdata[2];
 assign wb_dat_o[30] = rsp_rdata[30];
 assign wb_dat_o[31] = rsp_rdata[31];
 assign wb_dat_o[3] = rsp_rdata[3];
 assign wb_dat_o[4] = rsp_rdata[4];
 assign wb_dat_o[5] = rsp_rdata[5];
 assign wb_dat_o[6] = rsp_rdata[6];
 assign wb_dat_o[7] = rsp_rdata[7];
 assign wb_dat_o[8] = rsp_rdata[8];
 assign wb_dat_o[9] = rsp_rdata[9];
endmodule
