module refresh_ctrl (cfg_force_refresh,
    cfg_ref_priority,
    clk,
    init_done,
    ref_ack,
    ref_required,
    ref_starve_flag,
    ref_urgent,
    rst_n,
    cfg_max_postpone,
    cfg_tREFI_nCK,
    cfg_urgent_threshold,
    ref_pending_cnt);
 input cfg_force_refresh;
 input cfg_ref_priority;
 input clk;
 input init_done;
 input ref_ack;
 output ref_required;
 output ref_starve_flag;
 output ref_urgent;
 input rst_n;
 input [3:0] cfg_max_postpone;
 input [23:0] cfg_tREFI_nCK;
 input [3:0] cfg_urgent_threshold;
 output [3:0] ref_pending_cnt;

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
 wire _060_;
 wire _061_;
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
 wire _118_;
 wire _119_;
 wire _120_;
 wire _121_;
 wire _122_;
 wire _123_;
 wire _124_;
 wire _126_;
 wire _127_;
 wire net1;
 wire net2;
 wire net3;
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
 wire net27;
 wire net28;
 wire net29;
 wire net30;
 wire net31;
 wire net32;
 wire net33;
 wire \refi_ctr[0] ;
 wire \refi_ctr[10] ;
 wire \refi_ctr[11] ;
 wire \refi_ctr[12] ;
 wire \refi_ctr[1] ;
 wire \refi_ctr[2] ;
 wire \refi_ctr[3] ;
 wire \refi_ctr[4] ;
 wire \refi_ctr[5] ;
 wire \refi_ctr[6] ;
 wire \refi_ctr[7] ;
 wire \refi_ctr[8] ;
 wire \refi_ctr[9] ;
 wire refi_tick;
 wire net26;
 wire starve_detect;
 wire net34;
 wire clknet_0_clk;
 wire clknet_1_0__leaf_clk;
 wire clknet_1_1__leaf_clk;

 sky130_fd_sc_hd__inv_1 _128_ (.A(net24),
    .Y(_124_));
 sky130_fd_sc_hd__nor4_4 _130_ (.A(\refi_ctr[5] ),
    .B(\refi_ctr[6] ),
    .C(\refi_ctr[7] ),
    .D(\refi_ctr[8] ),
    .Y(_126_));
 sky130_fd_sc_hd__nor2_1 _131_ (.A(\refi_ctr[9] ),
    .B(\refi_ctr[10] ),
    .Y(_052_));
 sky130_fd_sc_hd__nand2_1 _132_ (.A(_126_),
    .B(_052_),
    .Y(_053_));
 sky130_fd_sc_hd__nor3_2 _133_ (.A(\refi_ctr[2] ),
    .B(\refi_ctr[3] ),
    .C(\refi_ctr[4] ),
    .Y(_054_));
 sky130_fd_sc_hd__nor2_1 _134_ (.A(\refi_ctr[11] ),
    .B(\refi_ctr[12] ),
    .Y(_055_));
 sky130_fd_sc_hd__nand3_1 _135_ (.A(_041_),
    .B(_054_),
    .C(_055_),
    .Y(_056_));
 sky130_fd_sc_hd__nor3_1 _136_ (.A(_124_),
    .B(_053_),
    .C(_056_),
    .Y(_000_));
 sky130_fd_sc_hd__and4b_4 _137_ (.A_N(\refi_ctr[11] ),
    .B(_126_),
    .C(_052_),
    .D(_054_),
    .X(_057_));
 sky130_fd_sc_hd__nand3b_4 _138_ (.A_N(\refi_ctr[12] ),
    .B(_057_),
    .C(_041_),
    .Y(_058_));
 sky130_fd_sc_hd__nor2_1 _140_ (.A(net7),
    .B(_058_),
    .Y(_060_));
 sky130_fd_sc_hd__a211oi_2 _141_ (.A1(\refi_ctr[0] ),
    .A2(_058_),
    .B1(_060_),
    .C1(_124_),
    .Y(_001_));
 sky130_fd_sc_hd__nor2_1 _142_ (.A(net11),
    .B(_058_),
    .Y(_061_));
 sky130_fd_sc_hd__a211oi_2 _143_ (.A1(_040_),
    .A2(_058_),
    .B1(_061_),
    .C1(_124_),
    .Y(_005_));
 sky130_fd_sc_hd__xnor2_1 _145_ (.A(\refi_ctr[2] ),
    .B(_039_),
    .Y(_063_));
 sky130_fd_sc_hd__nor2_1 _146_ (.A(net12),
    .B(_058_),
    .Y(_064_));
 sky130_fd_sc_hd__a211oi_2 _147_ (.A1(_058_),
    .A2(_063_),
    .B1(_064_),
    .C1(_124_),
    .Y(_006_));
 sky130_fd_sc_hd__nor3_1 _148_ (.A(\refi_ctr[2] ),
    .B(\refi_ctr[0] ),
    .C(\refi_ctr[1] ),
    .Y(_065_));
 sky130_fd_sc_hd__xnor2_1 _149_ (.A(\refi_ctr[3] ),
    .B(_065_),
    .Y(_066_));
 sky130_fd_sc_hd__nor2_1 _150_ (.A(net13),
    .B(_058_),
    .Y(_067_));
 sky130_fd_sc_hd__a211oi_2 _151_ (.A1(_058_),
    .A2(_066_),
    .B1(_067_),
    .C1(_124_),
    .Y(_007_));
 sky130_fd_sc_hd__nor2_1 _152_ (.A(\refi_ctr[2] ),
    .B(\refi_ctr[3] ),
    .Y(_068_));
 sky130_fd_sc_hd__nand2_1 _153_ (.A(_039_),
    .B(_068_),
    .Y(_069_));
 sky130_fd_sc_hd__nand2_1 _154_ (.A(\refi_ctr[4] ),
    .B(_069_),
    .Y(_070_));
 sky130_fd_sc_hd__nand2_1 _155_ (.A(_039_),
    .B(_054_),
    .Y(_071_));
 sky130_fd_sc_hd__nor2_1 _156_ (.A(net14),
    .B(_058_),
    .Y(_072_));
 sky130_fd_sc_hd__a311oi_2 _157_ (.A1(_058_),
    .A2(_070_),
    .A3(_071_),
    .B1(_072_),
    .C1(_124_),
    .Y(_008_));
 sky130_fd_sc_hd__nor2_1 _158_ (.A(\refi_ctr[0] ),
    .B(\refi_ctr[1] ),
    .Y(_073_));
 sky130_fd_sc_hd__nand2_1 _159_ (.A(_054_),
    .B(_073_),
    .Y(_074_));
 sky130_fd_sc_hd__xor2_1 _160_ (.A(\refi_ctr[5] ),
    .B(_074_),
    .X(_075_));
 sky130_fd_sc_hd__nor2_1 _161_ (.A(net15),
    .B(_058_),
    .Y(_076_));
 sky130_fd_sc_hd__a211oi_2 _162_ (.A1(_058_),
    .A2(_075_),
    .B1(_076_),
    .C1(_124_),
    .Y(_009_));
 sky130_fd_sc_hd__nor2_1 _163_ (.A(\refi_ctr[5] ),
    .B(_071_),
    .Y(_077_));
 sky130_fd_sc_hd__xnor2_1 _164_ (.A(\refi_ctr[6] ),
    .B(_077_),
    .Y(_078_));
 sky130_fd_sc_hd__o21ai_0 _166_ (.A1(net16),
    .A2(_058_),
    .B1(net24),
    .Y(_080_));
 sky130_fd_sc_hd__a21oi_1 _167_ (.A1(_058_),
    .A2(_078_),
    .B1(_080_),
    .Y(_010_));
 sky130_fd_sc_hd__or3_1 _168_ (.A(\refi_ctr[5] ),
    .B(\refi_ctr[6] ),
    .C(_074_),
    .X(_081_));
 sky130_fd_sc_hd__xor2_1 _169_ (.A(\refi_ctr[7] ),
    .B(_081_),
    .X(_082_));
 sky130_fd_sc_hd__o21ai_0 _170_ (.A1(net17),
    .A2(_058_),
    .B1(net24),
    .Y(_083_));
 sky130_fd_sc_hd__a21oi_1 _171_ (.A1(_058_),
    .A2(_082_),
    .B1(_083_),
    .Y(_011_));
 sky130_fd_sc_hd__nor4_1 _172_ (.A(\refi_ctr[5] ),
    .B(\refi_ctr[6] ),
    .C(\refi_ctr[7] ),
    .D(_071_),
    .Y(_084_));
 sky130_fd_sc_hd__xnor2_1 _173_ (.A(\refi_ctr[8] ),
    .B(_084_),
    .Y(_085_));
 sky130_fd_sc_hd__o21ai_0 _174_ (.A1(net18),
    .A2(_058_),
    .B1(net24),
    .Y(_086_));
 sky130_fd_sc_hd__a21oi_1 _175_ (.A1(_058_),
    .A2(_085_),
    .B1(_086_),
    .Y(_012_));
 sky130_fd_sc_hd__nand3_1 _176_ (.A(_126_),
    .B(_054_),
    .C(_073_),
    .Y(_087_));
 sky130_fd_sc_hd__xor2_1 _177_ (.A(\refi_ctr[9] ),
    .B(_087_),
    .X(_088_));
 sky130_fd_sc_hd__o21ai_0 _178_ (.A1(net19),
    .A2(_058_),
    .B1(net24),
    .Y(_089_));
 sky130_fd_sc_hd__a21oi_1 _179_ (.A1(_058_),
    .A2(_088_),
    .B1(_089_),
    .Y(_013_));
 sky130_fd_sc_hd__nand4b_1 _180_ (.A_N(\refi_ctr[9] ),
    .B(_039_),
    .C(_126_),
    .D(_054_),
    .Y(_090_));
 sky130_fd_sc_hd__xor2_1 _181_ (.A(\refi_ctr[10] ),
    .B(_090_),
    .X(_091_));
 sky130_fd_sc_hd__o21ai_0 _182_ (.A1(net8),
    .A2(_058_),
    .B1(net24),
    .Y(_092_));
 sky130_fd_sc_hd__a21oi_1 _183_ (.A1(_058_),
    .A2(_091_),
    .B1(_092_),
    .Y(_002_));
 sky130_fd_sc_hd__nand4_1 _184_ (.A(_126_),
    .B(_052_),
    .C(_054_),
    .D(_073_),
    .Y(_093_));
 sky130_fd_sc_hd__xor2_1 _185_ (.A(\refi_ctr[11] ),
    .B(_093_),
    .X(_094_));
 sky130_fd_sc_hd__o21ai_0 _186_ (.A1(net9),
    .A2(_058_),
    .B1(net24),
    .Y(_095_));
 sky130_fd_sc_hd__a21oi_1 _187_ (.A1(_058_),
    .A2(_094_),
    .B1(_095_),
    .Y(_003_));
 sky130_fd_sc_hd__mux2_2 _188_ (.A0(_039_),
    .A1(net10),
    .S(_041_),
    .X(_096_));
 sky130_fd_sc_hd__a21oi_1 _189_ (.A1(_057_),
    .A2(_096_),
    .B1(\refi_ctr[12] ),
    .Y(_097_));
 sky130_fd_sc_hd__a311oi_1 _190_ (.A1(\refi_ctr[12] ),
    .A2(_039_),
    .A3(_057_),
    .B1(_097_),
    .C1(_124_),
    .Y(_004_));
 sky130_fd_sc_hd__nor3b_2 _191_ (.A(refi_tick),
    .B(net1),
    .C_N(net25),
    .Y(_045_));
 sky130_fd_sc_hd__inv_1 _192_ (.A(net27),
    .Y(_023_));
 sky130_fd_sc_hd__inv_1 _193_ (.A(\refi_ctr[0] ),
    .Y(_037_));
 sky130_fd_sc_hd__inv_1 _194_ (.A(net5),
    .Y(_014_));
 sky130_fd_sc_hd__inv_1 _195_ (.A(net4),
    .Y(_017_));
 sky130_fd_sc_hd__inv_1 _196_ (.A(net3),
    .Y(_020_));
 sky130_fd_sc_hd__inv_1 _197_ (.A(net23),
    .Y(_026_));
 sky130_fd_sc_hd__inv_1 _198_ (.A(net22),
    .Y(_029_));
 sky130_fd_sc_hd__inv_1 _199_ (.A(net21),
    .Y(_032_));
 sky130_fd_sc_hd__inv_1 _200_ (.A(\refi_ctr[1] ),
    .Y(_038_));
 sky130_fd_sc_hd__xor2_1 _201_ (.A(net28),
    .B(_045_),
    .X(_042_));
 sky130_fd_sc_hd__nor2b_1 _202_ (.A(_024_),
    .B_N(_022_),
    .Y(_098_));
 sky130_fd_sc_hd__o211ai_1 _203_ (.A1(_021_),
    .A2(_098_),
    .B1(_016_),
    .C1(_019_),
    .Y(_099_));
 sky130_fd_sc_hd__a21oi_1 _204_ (.A1(_016_),
    .A2(_018_),
    .B1(_015_),
    .Y(_100_));
 sky130_fd_sc_hd__nor2_1 _205_ (.A(refi_tick),
    .B(net1),
    .Y(_101_));
 sky130_fd_sc_hd__nor2_1 _206_ (.A(net25),
    .B(_101_),
    .Y(_102_));
 sky130_fd_sc_hd__or4_4 _207_ (.A(net28),
    .B(net27),
    .C(net30),
    .D(net29),
    .X(_103_));
 sky130_fd_sc_hd__a32oi_4 _208_ (.A1(_099_),
    .A2(_100_),
    .A3(_102_),
    .B1(_103_),
    .B2(_045_),
    .Y(_104_));
 sky130_fd_sc_hd__xnor2_1 _209_ (.A(_023_),
    .B(_104_),
    .Y(_105_));
 sky130_fd_sc_hd__nor2_1 _210_ (.A(_124_),
    .B(_105_),
    .Y(_048_));
 sky130_fd_sc_hd__mux2i_1 _211_ (.A0(_044_),
    .A1(net28),
    .S(_104_),
    .Y(_106_));
 sky130_fd_sc_hd__nor2_1 _212_ (.A(_124_),
    .B(_106_),
    .Y(_049_));
 sky130_fd_sc_hd__a21oi_1 _213_ (.A1(net28),
    .A2(_045_),
    .B1(_043_),
    .Y(_107_));
 sky130_fd_sc_hd__xor2_1 _214_ (.A(_047_),
    .B(_107_),
    .X(_108_));
 sky130_fd_sc_hd__nand3_1 _215_ (.A(net24),
    .B(net29),
    .C(_104_),
    .Y(_109_));
 sky130_fd_sc_hd__o31ai_1 _216_ (.A1(_124_),
    .A2(_104_),
    .A3(_108_),
    .B1(_109_),
    .Y(_050_));
 sky130_fd_sc_hd__inv_1 _217_ (.A(_046_),
    .Y(_110_));
 sky130_fd_sc_hd__o21ai_0 _218_ (.A1(net28),
    .A2(net27),
    .B1(_047_),
    .Y(_111_));
 sky130_fd_sc_hd__nand3_1 _219_ (.A(net28),
    .B(net27),
    .C(_047_),
    .Y(_112_));
 sky130_fd_sc_hd__a21oi_1 _220_ (.A1(_110_),
    .A2(_112_),
    .B1(_045_),
    .Y(_113_));
 sky130_fd_sc_hd__a31oi_1 _221_ (.A1(_110_),
    .A2(_045_),
    .A3(_111_),
    .B1(_113_),
    .Y(_114_));
 sky130_fd_sc_hd__nand2b_1 _222_ (.A_N(net30),
    .B(net24),
    .Y(_115_));
 sky130_fd_sc_hd__o211ai_1 _223_ (.A1(_104_),
    .A2(_114_),
    .B1(net24),
    .C1(net30),
    .Y(_116_));
 sky130_fd_sc_hd__o31ai_1 _224_ (.A1(_104_),
    .A2(_114_),
    .A3(_115_),
    .B1(_116_),
    .Y(_051_));
 sky130_fd_sc_hd__and2_1 _225_ (.A(net24),
    .B(_103_),
    .X(net31));
 sky130_fd_sc_hd__nand2b_1 _226_ (.A_N(_036_),
    .B(_035_),
    .Y(_117_));
 sky130_fd_sc_hd__a21o_1 _227_ (.A1(_034_),
    .A2(_117_),
    .B1(_033_),
    .X(_118_));
 sky130_fd_sc_hd__a21o_1 _228_ (.A1(_031_),
    .A2(_118_),
    .B1(_030_),
    .X(_119_));
 sky130_fd_sc_hd__a21oi_1 _229_ (.A1(_028_),
    .A2(_119_),
    .B1(_027_),
    .Y(_120_));
 sky130_fd_sc_hd__nand2_1 _230_ (.A(net6),
    .B(net31),
    .Y(_121_));
 sky130_fd_sc_hd__nor2_1 _231_ (.A(_120_),
    .B(_121_),
    .Y(net33));
 sky130_fd_sc_hd__nand4_1 _232_ (.A(_016_),
    .B(_025_),
    .C(_022_),
    .D(_019_),
    .Y(_122_));
 sky130_fd_sc_hd__nand2_1 _233_ (.A(net24),
    .B(refi_tick),
    .Y(_123_));
 sky130_fd_sc_hd__a31oi_1 _234_ (.A1(_099_),
    .A2(_100_),
    .A3(_122_),
    .B1(_123_),
    .Y(starve_detect));
 sky130_fd_sc_hd__ha_1 _235_ (.A(net30),
    .B(_014_),
    .COUT(_015_),
    .SUM(_016_));
 sky130_fd_sc_hd__ha_1 _236_ (.A(net29),
    .B(_017_),
    .COUT(_018_),
    .SUM(_019_));
 sky130_fd_sc_hd__ha_1 _237_ (.A(net28),
    .B(_020_),
    .COUT(_021_),
    .SUM(_022_));
 sky130_fd_sc_hd__ha_1 _238_ (.A(_023_),
    .B(net2),
    .COUT(_024_),
    .SUM(_025_));
 sky130_fd_sc_hd__ha_1 _239_ (.A(net30),
    .B(_026_),
    .COUT(_027_),
    .SUM(_028_));
 sky130_fd_sc_hd__ha_1 _240_ (.A(net29),
    .B(_029_),
    .COUT(_030_),
    .SUM(_031_));
 sky130_fd_sc_hd__ha_1 _241_ (.A(net28),
    .B(_032_),
    .COUT(_033_),
    .SUM(_034_));
 sky130_fd_sc_hd__ha_1 _242_ (.A(_023_),
    .B(net20),
    .COUT(_035_),
    .SUM(_036_));
 sky130_fd_sc_hd__ha_1 _243_ (.A(_037_),
    .B(_038_),
    .COUT(_039_),
    .SUM(_040_));
 sky130_fd_sc_hd__ha_1 _244_ (.A(_037_),
    .B(_038_),
    .COUT(_041_),
    .SUM(_127_));
 sky130_fd_sc_hd__ha_1 _245_ (.A(net27),
    .B(_042_),
    .COUT(_043_),
    .SUM(_044_));
 sky130_fd_sc_hd__ha_1 _246_ (.A(net29),
    .B(_045_),
    .COUT(_046_),
    .SUM(_047_));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_0__f_clk (.A(clknet_0_clk),
    .X(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_1__f_clk (.A(clknet_0_clk),
    .X(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload0 (.A(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input1 (.A(cfg_force_refresh),
    .X(net1));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(cfg_tREFI_nCK[12]),
    .X(net10));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input11 (.A(cfg_tREFI_nCK[1]),
    .X(net11));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input12 (.A(cfg_tREFI_nCK[2]),
    .X(net12));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input13 (.A(cfg_tREFI_nCK[3]),
    .X(net13));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input14 (.A(cfg_tREFI_nCK[4]),
    .X(net14));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input15 (.A(cfg_tREFI_nCK[5]),
    .X(net15));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input16 (.A(cfg_tREFI_nCK[6]),
    .X(net16));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input17 (.A(cfg_tREFI_nCK[7]),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input18 (.A(cfg_tREFI_nCK[8]),
    .X(net18));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input19 (.A(cfg_tREFI_nCK[9]),
    .X(net19));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input2 (.A(cfg_max_postpone[0]),
    .X(net2));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input20 (.A(cfg_urgent_threshold[0]),
    .X(net20));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input21 (.A(cfg_urgent_threshold[1]),
    .X(net21));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input22 (.A(cfg_urgent_threshold[2]),
    .X(net22));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input23 (.A(cfg_urgent_threshold[3]),
    .X(net23));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input24 (.A(init_done),
    .X(net24));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input25 (.A(ref_ack),
    .X(net25));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input26 (.A(rst_n),
    .X(net26));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input3 (.A(cfg_max_postpone[1]),
    .X(net3));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input4 (.A(cfg_max_postpone[2]),
    .X(net4));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input5 (.A(cfg_max_postpone[3]),
    .X(net5));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input6 (.A(cfg_ref_priority),
    .X(net6));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input7 (.A(cfg_tREFI_nCK[0]),
    .X(net7));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input8 (.A(cfg_tREFI_nCK[10]),
    .X(net8));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input9 (.A(cfg_tREFI_nCK[11]),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output27 (.A(net27),
    .X(ref_pending_cnt[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output28 (.A(net28),
    .X(ref_pending_cnt[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output29 (.A(net29),
    .X(ref_pending_cnt[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output30 (.A(net30),
    .X(ref_pending_cnt[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output31 (.A(net31),
    .X(ref_required));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output32 (.A(net32),
    .X(ref_starve_flag));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output33 (.A(net33),
    .X(ref_urgent));
 sky130_fd_sc_hd__buf_4 place34 (.A(net26),
    .X(net34));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[0]$_DFFE_PN0P_  (.D(_048_),
    .Q(net27),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[1]$_DFFE_PN0P_  (.D(_049_),
    .Q(net28),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[2]$_DFFE_PN0P_  (.D(_050_),
    .Q(net29),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[3]$_DFFE_PN0P_  (.D(_051_),
    .Q(net30),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_starve_flag$_DFF_PN0_  (.D(starve_detect),
    .Q(net32),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[0]$_DFF_PN0_  (.D(_001_),
    .Q(\refi_ctr[0] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[10]$_DFF_PN0_  (.D(_002_),
    .Q(\refi_ctr[10] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[11]$_DFF_PN0_  (.D(_003_),
    .Q(\refi_ctr[11] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[12]$_DFF_PN0_  (.D(_004_),
    .Q(\refi_ctr[12] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[1]$_DFF_PN0_  (.D(_005_),
    .Q(\refi_ctr[1] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[2]$_DFF_PN0_  (.D(_006_),
    .Q(\refi_ctr[2] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[3]$_DFF_PN0_  (.D(_007_),
    .Q(\refi_ctr[3] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[4]$_DFF_PN0_  (.D(_008_),
    .Q(\refi_ctr[4] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[5]$_DFF_PN0_  (.D(_009_),
    .Q(\refi_ctr[5] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[6]$_DFF_PN0_  (.D(_010_),
    .Q(\refi_ctr[6] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[7]$_DFF_PN0_  (.D(_011_),
    .Q(\refi_ctr[7] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[8]$_DFF_PN0_  (.D(_012_),
    .Q(\refi_ctr[8] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[9]$_DFF_PN0_  (.D(_013_),
    .Q(\refi_ctr[9] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_tick$_DFF_PN0_  (.D(_000_),
    .Q(refi_tick),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
endmodule
