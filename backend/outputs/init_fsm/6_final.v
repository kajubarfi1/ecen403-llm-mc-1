module init_fsm (clk,
    enable,
    init_cke,
    init_cmd_valid,
    init_done,
    init_fail,
    init_reset_n,
    rst_n,
    init_addr,
    init_bank,
    init_cmd,
    init_state);
 input clk;
 input enable;
 output init_cke;
 output init_cmd_valid;
 output init_done;
 output init_fail;
 output init_reset_n;
 input rst_n;
 output [14:0] init_addr;
 output [2:0] init_bank;
 output [3:0] init_cmd;
 output [3:0] init_state;

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
 wire _105_;
 wire net23;
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
 wire _123_;
 wire _124_;
 wire _125_;
 wire _126_;
 wire _127_;
 wire _129_;
 wire \ctr[0] ;
 wire \ctr[10] ;
 wire \ctr[11] ;
 wire \ctr[12] ;
 wire \ctr[13] ;
 wire \ctr[14] ;
 wire \ctr[15] ;
 wire \ctr[16] ;
 wire \ctr[1] ;
 wire \ctr[2] ;
 wire \ctr[3] ;
 wire \ctr[4] ;
 wire \ctr[5] ;
 wire \ctr[6] ;
 wire \ctr[7] ;
 wire \ctr[8] ;
 wire \ctr[9] ;
 wire net8;
 wire net10;
 wire net12;
 wire net13;
 wire net15;
 wire net17;
 wire net14;
 wire net18;
 wire net19;
 wire net20;
 wire net21;
 wire net22;
 wire net24;
 wire net25;
 wire net26;
 wire net27;
 wire net28;
 wire net29;
 wire net30;
 wire net31;
 wire net32;
 wire net9;
 wire net16;
 wire net11;
 wire clknet_0_clk;
 wire net34;
 wire clknet_1_0__leaf_clk;
 wire clknet_1_1__leaf_clk;

 sky130_fd_sc_hd__nand2b_1 _133_ (.A_N(net31),
    .B(net32),
    .Y(_105_));
 sky130_fd_sc_hd__nor2_1 _134_ (.A(net29),
    .B(_105_),
    .Y(net13));
 sky130_fd_sc_hd__and2_1 _138_ (.A(net31),
    .B(net32),
    .X(_109_));
 sky130_fd_sc_hd__a21oi_1 _139_ (.A1(net30),
    .A2(_109_),
    .B1(net29),
    .Y(_110_));
 sky130_fd_sc_hd__o21ai_0 _140_ (.A1(net31),
    .A2(net32),
    .B1(_110_),
    .Y(net22));
 sky130_fd_sc_hd__inv_1 _141_ (.A(net22),
    .Y(net25));
 sky130_fd_sc_hd__nand2_1 _142_ (.A(net31),
    .B(net32),
    .Y(_111_));
 sky130_fd_sc_hd__nand2b_1 _143_ (.A_N(net29),
    .B(net30),
    .Y(_112_));
 sky130_fd_sc_hd__nor2_1 _144_ (.A(_111_),
    .B(_112_),
    .Y(net26));
 sky130_fd_sc_hd__nor2_1 _145_ (.A(_105_),
    .B(_112_),
    .Y(net12));
 sky130_fd_sc_hd__xnor2_1 _146_ (.A(net30),
    .B(net31),
    .Y(_113_));
 sky130_fd_sc_hd__nor3b_1 _147_ (.A(net29),
    .B(_113_),
    .C_N(net32),
    .Y(net10));
 sky130_fd_sc_hd__inv_1 _148_ (.A(\ctr[0] ),
    .Y(_000_));
 sky130_fd_sc_hd__inv_1 _149_ (.A(\ctr[1] ),
    .Y(_001_));
 sky130_fd_sc_hd__nand2b_1 _150_ (.A_N(net32),
    .B(net31),
    .Y(_114_));
 sky130_fd_sc_hd__nor3_1 _151_ (.A(net31),
    .B(net32),
    .C(net8),
    .Y(_115_));
 sky130_fd_sc_hd__a311oi_4 _152_ (.A1(net30),
    .A2(_105_),
    .A3(_114_),
    .B1(_115_),
    .C1(net29),
    .Y(_116_));
 sky130_fd_sc_hd__nor4_2 _153_ (.A(\ctr[8] ),
    .B(\ctr[9] ),
    .C(\ctr[10] ),
    .D(\ctr[11] ),
    .Y(_117_));
 sky130_fd_sc_hd__nor4_1 _154_ (.A(\ctr[12] ),
    .B(\ctr[13] ),
    .C(\ctr[14] ),
    .D(\ctr[15] ),
    .Y(_118_));
 sky130_fd_sc_hd__nor4b_2 _155_ (.A(\ctr[2] ),
    .B(\ctr[3] ),
    .C(\ctr[4] ),
    .D_N(_002_),
    .Y(_119_));
 sky130_fd_sc_hd__nor4_1 _156_ (.A(\ctr[5] ),
    .B(\ctr[6] ),
    .C(\ctr[7] ),
    .D(\ctr[16] ),
    .Y(_120_));
 sky130_fd_sc_hd__and4_1 _157_ (.A(_117_),
    .B(_118_),
    .C(_119_),
    .D(_120_),
    .X(_121_));
 sky130_fd_sc_hd__nor2_1 _159_ (.A(net31),
    .B(net32),
    .Y(_123_));
 sky130_fd_sc_hd__xor2_1 _160_ (.A(net30),
    .B(net29),
    .X(_124_));
 sky130_fd_sc_hd__nand2_1 _161_ (.A(_123_),
    .B(_124_),
    .Y(_125_));
 sky130_fd_sc_hd__a21oi_1 _162_ (.A1(_121_),
    .A2(_125_),
    .B1(_000_),
    .Y(_126_));
 sky130_fd_sc_hd__nand4_1 _163_ (.A(_117_),
    .B(_118_),
    .C(_119_),
    .D(_120_),
    .Y(_127_));
 sky130_fd_sc_hd__nor2_1 _165_ (.A(\ctr[0] ),
    .B(_127_),
    .Y(_129_));
 sky130_fd_sc_hd__nor2_1 _166_ (.A(net29),
    .B(_114_),
    .Y(net20));
 sky130_fd_sc_hd__nor2_1 _167_ (.A(net13),
    .B(net20),
    .Y(net24));
 sky130_fd_sc_hd__o31ai_1 _168_ (.A1(_116_),
    .A2(_126_),
    .A3(_129_),
    .B1(net24),
    .Y(_004_));
 sky130_fd_sc_hd__nor2b_1 _169_ (.A(net29),
    .B_N(net8),
    .Y(_025_));
 sky130_fd_sc_hd__nor3_1 _170_ (.A(net30),
    .B(net31),
    .C(net32),
    .Y(_026_));
 sky130_fd_sc_hd__inv_1 _171_ (.A(_026_),
    .Y(net28));
 sky130_fd_sc_hd__o21ai_1 _172_ (.A1(_110_),
    .A2(_127_),
    .B1(net28),
    .Y(_027_));
 sky130_fd_sc_hd__o21ai_1 _173_ (.A1(_121_),
    .A2(_025_),
    .B1(_027_),
    .Y(_028_));
 sky130_fd_sc_hd__a31oi_2 _174_ (.A1(_123_),
    .A2(_121_),
    .A3(_124_),
    .B1(_116_),
    .Y(_029_));
 sky130_fd_sc_hd__nor2_1 _175_ (.A(\ctr[8] ),
    .B(\ctr[9] ),
    .Y(_030_));
 sky130_fd_sc_hd__nor3_1 _176_ (.A(\ctr[5] ),
    .B(\ctr[6] ),
    .C(\ctr[7] ),
    .Y(_031_));
 sky130_fd_sc_hd__nand3_1 _177_ (.A(_030_),
    .B(_119_),
    .C(_031_),
    .Y(_032_));
 sky130_fd_sc_hd__xnor2_1 _178_ (.A(\ctr[10] ),
    .B(_032_),
    .Y(_033_));
 sky130_fd_sc_hd__nand2_1 _179_ (.A(_029_),
    .B(_033_),
    .Y(_034_));
 sky130_fd_sc_hd__nand2_1 _180_ (.A(_121_),
    .B(_125_),
    .Y(_035_));
 sky130_fd_sc_hd__nor2_2 _181_ (.A(_116_),
    .B(_035_),
    .Y(_036_));
 sky130_fd_sc_hd__a21oi_1 _182_ (.A1(_028_),
    .A2(_034_),
    .B1(_036_),
    .Y(_005_));
 sky130_fd_sc_hd__nor3_1 _183_ (.A(\ctr[8] ),
    .B(\ctr[9] ),
    .C(\ctr[10] ),
    .Y(_037_));
 sky130_fd_sc_hd__nor3_1 _184_ (.A(\ctr[2] ),
    .B(\ctr[3] ),
    .C(\ctr[4] ),
    .Y(_038_));
 sky130_fd_sc_hd__nor2_1 _185_ (.A(\ctr[1] ),
    .B(\ctr[0] ),
    .Y(_039_));
 sky130_fd_sc_hd__nand4_1 _186_ (.A(_037_),
    .B(_038_),
    .C(_031_),
    .D(_039_),
    .Y(_040_));
 sky130_fd_sc_hd__xnor2_1 _187_ (.A(\ctr[11] ),
    .B(_040_),
    .Y(_041_));
 sky130_fd_sc_hd__nor2_1 _188_ (.A(net30),
    .B(net29),
    .Y(_042_));
 sky130_fd_sc_hd__and3_1 _189_ (.A(net8),
    .B(_123_),
    .C(_042_),
    .X(_043_));
 sky130_fd_sc_hd__a21oi_1 _190_ (.A1(_029_),
    .A2(_041_),
    .B1(_043_),
    .Y(_044_));
 sky130_fd_sc_hd__nor2_1 _191_ (.A(_036_),
    .B(_044_),
    .Y(_006_));
 sky130_fd_sc_hd__nand3_1 _192_ (.A(_117_),
    .B(_119_),
    .C(_031_),
    .Y(_045_));
 sky130_fd_sc_hd__xnor2_1 _193_ (.A(\ctr[12] ),
    .B(_045_),
    .Y(_046_));
 sky130_fd_sc_hd__a21oi_1 _194_ (.A1(_029_),
    .A2(_046_),
    .B1(_043_),
    .Y(_047_));
 sky130_fd_sc_hd__nor2_1 _195_ (.A(_036_),
    .B(_047_),
    .Y(_007_));
 sky130_fd_sc_hd__a311o_1 _196_ (.A1(net30),
    .A2(_105_),
    .A3(_114_),
    .B1(_115_),
    .C1(net29),
    .X(_048_));
 sky130_fd_sc_hd__o21ai_1 _197_ (.A1(_127_),
    .A2(_125_),
    .B1(_048_),
    .Y(_049_));
 sky130_fd_sc_hd__or4_4 _198_ (.A(\ctr[8] ),
    .B(\ctr[9] ),
    .C(\ctr[10] ),
    .D(\ctr[11] ),
    .X(_050_));
 sky130_fd_sc_hd__nand3_1 _199_ (.A(_038_),
    .B(_031_),
    .C(_039_),
    .Y(_051_));
 sky130_fd_sc_hd__nor4_1 _200_ (.A(\ctr[12] ),
    .B(_050_),
    .C(_121_),
    .D(_051_),
    .Y(_052_));
 sky130_fd_sc_hd__xnor2_1 _201_ (.A(\ctr[13] ),
    .B(_052_),
    .Y(_053_));
 sky130_fd_sc_hd__nor2_1 _202_ (.A(_049_),
    .B(_053_),
    .Y(_008_));
 sky130_fd_sc_hd__or3_4 _203_ (.A(\ctr[12] ),
    .B(\ctr[13] ),
    .C(_050_),
    .X(_054_));
 sky130_fd_sc_hd__and2_1 _204_ (.A(_119_),
    .B(_031_),
    .X(_055_));
 sky130_fd_sc_hd__nand3b_1 _205_ (.A_N(_054_),
    .B(_127_),
    .C(_055_),
    .Y(_056_));
 sky130_fd_sc_hd__xor2_1 _206_ (.A(\ctr[14] ),
    .B(_056_),
    .X(_057_));
 sky130_fd_sc_hd__nor2_1 _207_ (.A(_049_),
    .B(_057_),
    .Y(_009_));
 sky130_fd_sc_hd__o31a_1 _208_ (.A1(\ctr[14] ),
    .A2(_054_),
    .A3(_051_),
    .B1(\ctr[15] ),
    .X(_058_));
 sky130_fd_sc_hd__nor4_1 _209_ (.A(\ctr[14] ),
    .B(\ctr[15] ),
    .C(_054_),
    .D(_051_),
    .Y(_059_));
 sky130_fd_sc_hd__o21ai_1 _210_ (.A1(_058_),
    .A2(_059_),
    .B1(_029_),
    .Y(_060_));
 sky130_fd_sc_hd__a21oi_1 _211_ (.A1(_028_),
    .A2(_060_),
    .B1(_036_),
    .Y(_010_));
 sky130_fd_sc_hd__nand3_1 _212_ (.A(_117_),
    .B(_118_),
    .C(_055_),
    .Y(_061_));
 sky130_fd_sc_hd__nand2_1 _213_ (.A(\ctr[16] ),
    .B(_061_),
    .Y(_062_));
 sky130_fd_sc_hd__nand3_1 _214_ (.A(net29),
    .B(_121_),
    .C(_026_),
    .Y(_063_));
 sky130_fd_sc_hd__a21oi_1 _215_ (.A1(_062_),
    .A2(_063_),
    .B1(_116_),
    .Y(_011_));
 sky130_fd_sc_hd__nor2_1 _216_ (.A(net32),
    .B(_121_),
    .Y(_064_));
 sky130_fd_sc_hd__nand2_1 _217_ (.A(_048_),
    .B(_127_),
    .Y(_065_));
 sky130_fd_sc_hd__o32ai_1 _218_ (.A1(net31),
    .A2(_112_),
    .A3(_064_),
    .B1(_065_),
    .B2(_003_),
    .Y(_066_));
 sky130_fd_sc_hd__a21o_1 _219_ (.A1(\ctr[1] ),
    .A2(_036_),
    .B1(_066_),
    .X(_012_));
 sky130_fd_sc_hd__nand2_1 _220_ (.A(_002_),
    .B(_127_),
    .Y(_067_));
 sky130_fd_sc_hd__xor2_1 _221_ (.A(\ctr[2] ),
    .B(_067_),
    .X(_068_));
 sky130_fd_sc_hd__nor2_1 _222_ (.A(_049_),
    .B(_068_),
    .Y(_013_));
 sky130_fd_sc_hd__nor4_1 _223_ (.A(\ctr[2] ),
    .B(\ctr[1] ),
    .C(\ctr[0] ),
    .D(_121_),
    .Y(_069_));
 sky130_fd_sc_hd__xnor2_1 _224_ (.A(\ctr[3] ),
    .B(_069_),
    .Y(_070_));
 sky130_fd_sc_hd__nor2_1 _225_ (.A(_049_),
    .B(_070_),
    .Y(_014_));
 sky130_fd_sc_hd__nor2_1 _226_ (.A(\ctr[2] ),
    .B(\ctr[3] ),
    .Y(_071_));
 sky130_fd_sc_hd__nand3_1 _227_ (.A(_002_),
    .B(_071_),
    .C(_127_),
    .Y(_072_));
 sky130_fd_sc_hd__xor2_1 _228_ (.A(\ctr[4] ),
    .B(_072_),
    .X(_073_));
 sky130_fd_sc_hd__nor2_1 _229_ (.A(_049_),
    .B(_073_),
    .Y(_015_));
 sky130_fd_sc_hd__nand2_1 _230_ (.A(_038_),
    .B(_039_),
    .Y(_074_));
 sky130_fd_sc_hd__xor2_1 _231_ (.A(\ctr[5] ),
    .B(_074_),
    .X(_075_));
 sky130_fd_sc_hd__o22ai_1 _232_ (.A1(_127_),
    .A2(_125_),
    .B1(_065_),
    .B2(_075_),
    .Y(_016_));
 sky130_fd_sc_hd__nand2b_1 _233_ (.A_N(\ctr[5] ),
    .B(_119_),
    .Y(_076_));
 sky130_fd_sc_hd__xnor2_1 _234_ (.A(\ctr[6] ),
    .B(_076_),
    .Y(_077_));
 sky130_fd_sc_hd__a21oi_1 _235_ (.A1(_029_),
    .A2(_077_),
    .B1(_043_),
    .Y(_078_));
 sky130_fd_sc_hd__nor2_1 _236_ (.A(_036_),
    .B(_078_),
    .Y(_017_));
 sky130_fd_sc_hd__nand4_1 _237_ (.A(_002_),
    .B(_117_),
    .C(_118_),
    .D(_120_),
    .Y(_079_));
 sky130_fd_sc_hd__nand3_1 _238_ (.A(net29),
    .B(_038_),
    .C(_026_),
    .Y(_080_));
 sky130_fd_sc_hd__nand2_1 _239_ (.A(_109_),
    .B(_042_),
    .Y(_081_));
 sky130_fd_sc_hd__o41ai_1 _240_ (.A1(\ctr[5] ),
    .A2(\ctr[6] ),
    .A3(\ctr[1] ),
    .A4(\ctr[0] ),
    .B1(_079_),
    .Y(_082_));
 sky130_fd_sc_hd__nand2_1 _241_ (.A(\ctr[7] ),
    .B(_048_),
    .Y(_083_));
 sky130_fd_sc_hd__a31o_1 _242_ (.A1(_038_),
    .A2(_035_),
    .A3(_082_),
    .B1(_083_),
    .X(_084_));
 sky130_fd_sc_hd__nor2_1 _243_ (.A(_116_),
    .B(_051_),
    .Y(_085_));
 sky130_fd_sc_hd__nand2_1 _244_ (.A(_079_),
    .B(_085_),
    .Y(_086_));
 sky130_fd_sc_hd__o2111ai_1 _245_ (.A1(_079_),
    .A2(_080_),
    .B1(_081_),
    .C1(_084_),
    .D1(_086_),
    .Y(_018_));
 sky130_fd_sc_hd__nand2_1 _246_ (.A(_127_),
    .B(_055_),
    .Y(_087_));
 sky130_fd_sc_hd__xor2_1 _247_ (.A(\ctr[8] ),
    .B(_087_),
    .X(_088_));
 sky130_fd_sc_hd__nor2_1 _248_ (.A(_049_),
    .B(_088_),
    .Y(_019_));
 sky130_fd_sc_hd__nand4b_1 _249_ (.A_N(\ctr[8] ),
    .B(_038_),
    .C(_031_),
    .D(_039_),
    .Y(_089_));
 sky130_fd_sc_hd__xnor2_1 _250_ (.A(\ctr[9] ),
    .B(_089_),
    .Y(_090_));
 sky130_fd_sc_hd__nand2_1 _251_ (.A(_127_),
    .B(_090_),
    .Y(_091_));
 sky130_fd_sc_hd__a21oi_1 _252_ (.A1(_063_),
    .A2(_091_),
    .B1(_116_),
    .Y(_020_));
 sky130_fd_sc_hd__nand2_1 _253_ (.A(net29),
    .B(_121_),
    .Y(_092_));
 sky130_fd_sc_hd__nor4_1 _254_ (.A(net29),
    .B(net31),
    .C(net32),
    .D(_121_),
    .Y(_093_));
 sky130_fd_sc_hd__o21ai_1 _255_ (.A1(_109_),
    .A2(_093_),
    .B1(net30),
    .Y(_094_));
 sky130_fd_sc_hd__nand2_1 _256_ (.A(_115_),
    .B(_042_),
    .Y(_095_));
 sky130_fd_sc_hd__and3_1 _257_ (.A(_092_),
    .B(_094_),
    .C(_095_),
    .X(_021_));
 sky130_fd_sc_hd__o21ai_1 _258_ (.A1(_109_),
    .A2(_121_),
    .B1(net29),
    .Y(_096_));
 sky130_fd_sc_hd__nand2_1 _259_ (.A(net30),
    .B(_096_),
    .Y(_097_));
 sky130_fd_sc_hd__o21ai_1 _260_ (.A1(net30),
    .A2(_092_),
    .B1(_097_),
    .Y(_022_));
 sky130_fd_sc_hd__nand2_1 _261_ (.A(net30),
    .B(net29),
    .Y(_098_));
 sky130_fd_sc_hd__nor2_1 _262_ (.A(_127_),
    .B(_098_),
    .Y(_099_));
 sky130_fd_sc_hd__nand3_1 _263_ (.A(net30),
    .B(net29),
    .C(net31),
    .Y(_100_));
 sky130_fd_sc_hd__o22a_1 _264_ (.A1(net31),
    .A2(_099_),
    .B1(_100_),
    .B2(_064_),
    .X(_023_));
 sky130_fd_sc_hd__nor3_1 _265_ (.A(net32),
    .B(_127_),
    .C(_100_),
    .Y(_101_));
 sky130_fd_sc_hd__a21o_1 _266_ (.A1(net32),
    .A2(_100_),
    .B1(_101_),
    .X(_024_));
 sky130_fd_sc_hd__nor3_1 _267_ (.A(net30),
    .B(net29),
    .C(_114_),
    .Y(net18));
 sky130_fd_sc_hd__or2_2 _268_ (.A(net12),
    .B(net18),
    .X(net15));
 sky130_fd_sc_hd__mux2_2 _269_ (.A0(_105_),
    .A1(_114_),
    .S(net30),
    .X(_102_));
 sky130_fd_sc_hd__nor2_1 _270_ (.A(net29),
    .B(_102_),
    .Y(net19));
 sky130_fd_sc_hd__nor2_1 _271_ (.A(_111_),
    .B(_098_),
    .Y(net27));
 sky130_fd_sc_hd__a21oi_1 _272_ (.A1(_123_),
    .A2(_098_),
    .B1(net27),
    .Y(net21));
 sky130_fd_sc_hd__ha_1 _273_ (.A(_000_),
    .B(_001_),
    .COUT(_002_),
    .SUM(_003_));
 sky130_fd_sc_hd__conb_1 _275__1 (.LO(init_addr[0]));
 sky130_fd_sc_hd__conb_1 _276__2 (.LO(init_addr[1]));
 sky130_fd_sc_hd__conb_1 _279__3 (.LO(init_addr[6]));
 sky130_fd_sc_hd__conb_1 _280__4 (.LO(init_addr[7]));
 sky130_fd_sc_hd__conb_1 _283__5 (.LO(init_addr[13]));
 sky130_fd_sc_hd__conb_1 _284__6 (.LO(init_addr[14]));
 sky130_fd_sc_hd__conb_1 _285__7 (.LO(init_bank[2]));
 sky130_fd_sc_hd__conb_1 _287__8 (.LO(init_cmd[3]));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_0__f_clk (.A(clknet_0_clk),
    .X(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_1__f_clk (.A(clknet_0_clk),
    .X(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload0 (.A(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[0]$_DFFE_PN0P_  (.D(_004_),
    .Q(\ctr[0] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[10]$_DFFE_PN0P_  (.D(_005_),
    .Q(\ctr[10] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[11]$_DFFE_PN0P_  (.D(_006_),
    .Q(\ctr[11] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[12]$_DFFE_PN0P_  (.D(_007_),
    .Q(\ctr[12] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[13]$_DFFE_PN0P_  (.D(_008_),
    .Q(\ctr[13] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[14]$_DFFE_PN0P_  (.D(_009_),
    .Q(\ctr[14] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[15]$_DFFE_PN0P_  (.D(_010_),
    .Q(\ctr[15] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[16]$_DFFE_PN0P_  (.D(_011_),
    .Q(\ctr[16] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[1]$_DFFE_PN0P_  (.D(_012_),
    .Q(\ctr[1] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[2]$_DFFE_PN0P_  (.D(_013_),
    .Q(\ctr[2] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[3]$_DFFE_PN0P_  (.D(_014_),
    .Q(\ctr[3] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[4]$_DFFE_PN0P_  (.D(_015_),
    .Q(\ctr[4] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[5]$_DFFE_PN0P_  (.D(_016_),
    .Q(\ctr[5] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[6]$_DFFE_PN0P_  (.D(_017_),
    .Q(\ctr[6] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[7]$_DFFE_PN0P_  (.D(_018_),
    .Q(\ctr[7] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[8]$_DFFE_PN0P_  (.D(_019_),
    .Q(\ctr[8] ),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ctr[9]$_DFFE_PN0P_  (.D(_020_),
    .Q(\ctr[9] ),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(rst_n),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input9 (.A(enable),
    .X(net8));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output11 (.A(net10),
    .X(init_addr[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output12 (.A(net12),
    .X(net11));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output13 (.A(net12),
    .X(init_addr[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output14 (.A(net13),
    .X(init_addr[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output15 (.A(net18),
    .X(net14));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output16 (.A(net15),
    .X(init_addr[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output17 (.A(net12),
    .X(net16));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output18 (.A(net12),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output19 (.A(net18),
    .X(init_addr[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output20 (.A(net19),
    .X(init_bank[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output21 (.A(net20),
    .X(init_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output22 (.A(net21),
    .X(init_cke));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output23 (.A(net22),
    .X(init_cmd[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output24 (.A(net24),
    .X(net23));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output25 (.A(net24),
    .X(init_cmd[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output26 (.A(net25),
    .X(init_cmd_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output27 (.A(net26),
    .X(init_done));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output28 (.A(net27),
    .X(init_fail));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output29 (.A(net28),
    .X(init_reset_n));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output30 (.A(net29),
    .X(init_state[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output31 (.A(net30),
    .X(init_state[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output32 (.A(net31),
    .X(init_state[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output33 (.A(net32),
    .X(init_state[3]));
 sky130_fd_sc_hd__buf_4 place35 (.A(net9),
    .X(net34));
 sky130_fd_sc_hd__dfrtp_1 \state[0]$_DFFE_PN0P_  (.D(_021_),
    .Q(net29),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \state[1]$_DFFE_PN0P_  (.D(_022_),
    .Q(net30),
    .RESET_B(net34),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \state[2]$_DFFE_PN0P_  (.D(_023_),
    .Q(net31),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \state[3]$_DFFE_PN0P_  (.D(_024_),
    .Q(net32),
    .RESET_B(net34),
    .CLK(clknet_1_0__leaf_clk));
 assign init_addr[11] = net11;
 assign init_addr[3] = net14;
 assign init_addr[5] = net16;
 assign init_addr[8] = net17;
 assign init_cmd[1] = net23;
endmodule
