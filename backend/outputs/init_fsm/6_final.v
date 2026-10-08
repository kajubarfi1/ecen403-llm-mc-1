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
 wire net24;
 wire _046_;
 wire _047_;
 wire _048_;
 wire _049_;
 wire _050_;
 wire _051_;
 wire _052_;
 wire _053_;
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
 wire clknet_0_clk;
 wire _093_;
 wire _096_;
 wire _097_;
 wire _098_;
 wire _100_;
 wire _101_;
 wire _102_;
 wire _103_;
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
 wire _125_;
 wire _126_;
 wire _127_;
 wire _128_;
 wire net9;
 wire net11;
 wire net15;
 wire net13;
 wire net14;
 wire net16;
 wire net19;
 wire net20;
 wire net21;
 wire net22;
 wire net23;
 wire net25;
 wire net26;
 wire net27;
 wire net28;
 wire net29;
 wire net30;
 wire net31;
 wire net32;
 wire \next_state[0] ;
 wire \next_state[1] ;
 wire \next_state[2] ;
 wire \next_state[3] ;
 wire net10;
 wire \wait_cnt[0] ;
 wire \wait_cnt[10] ;
 wire \wait_cnt[11] ;
 wire \wait_cnt[12] ;
 wire \wait_cnt[13] ;
 wire \wait_cnt[14] ;
 wire \wait_cnt[15] ;
 wire \wait_cnt[16] ;
 wire \wait_cnt[1] ;
 wire \wait_cnt[2] ;
 wire \wait_cnt[3] ;
 wire \wait_cnt[4] ;
 wire \wait_cnt[5] ;
 wire \wait_cnt[6] ;
 wire \wait_cnt[7] ;
 wire \wait_cnt[8] ;
 wire \wait_cnt[9] ;
 wire net18;
 wire net17;
 wire net12;
 wire net34;
 wire net35;
 wire net36;
 wire clknet_1_0__leaf_clk;
 wire clknet_1_1__leaf_clk;

 sky130_fd_sc_hd__inv_1 _132_ (.A(net32),
    .Y(_093_));
 sky130_fd_sc_hd__nand2_1 _133_ (.A(net31),
    .B(_093_),
    .Y(net25));
 sky130_fd_sc_hd__nor2b_1 _136_ (.A(net29),
    .B_N(net30),
    .Y(_096_));
 sky130_fd_sc_hd__and3_1 _137_ (.A(net31),
    .B(net32),
    .C(_096_),
    .X(net27));
 sky130_fd_sc_hd__inv_1 _138_ (.A(net29),
    .Y(_097_));
 sky130_fd_sc_hd__nand2b_1 _139_ (.A_N(\wait_cnt[6] ),
    .B(_018_),
    .Y(_098_));
 sky130_fd_sc_hd__or4b_1 _141_ (.A(\wait_cnt[2] ),
    .B(\wait_cnt[3] ),
    .C(\wait_cnt[4] ),
    .D_N(\wait_cnt[5] ),
    .X(_100_));
 sky130_fd_sc_hd__nor2_1 _142_ (.A(_098_),
    .B(_100_),
    .Y(_101_));
 sky130_fd_sc_hd__nor3_2 _143_ (.A(\wait_cnt[8] ),
    .B(\wait_cnt[13] ),
    .C(\wait_cnt[14] ),
    .Y(_102_));
 sky130_fd_sc_hd__nor3_4 _144_ (.A(\wait_cnt[16] ),
    .B(\wait_cnt[7] ),
    .C(\wait_cnt[9] ),
    .Y(_103_));
 sky130_fd_sc_hd__nor4_1 _148_ (.A(\wait_cnt[10] ),
    .B(\wait_cnt[11] ),
    .C(\wait_cnt[12] ),
    .D(\wait_cnt[15] ),
    .Y(_107_));
 sky130_fd_sc_hd__and3_1 _149_ (.A(_102_),
    .B(_103_),
    .C(_107_),
    .X(_108_));
 sky130_fd_sc_hd__a311oi_1 _150_ (.A1(net30),
    .A2(_101_),
    .A3(_108_),
    .B1(net31),
    .C1(net32),
    .Y(_109_));
 sky130_fd_sc_hd__nand3b_1 _151_ (.A_N(\wait_cnt[6] ),
    .B(\wait_cnt[15] ),
    .C(_102_),
    .Y(_110_));
 sky130_fd_sc_hd__nand4_1 _152_ (.A(\wait_cnt[5] ),
    .B(\wait_cnt[10] ),
    .C(\wait_cnt[11] ),
    .D(\wait_cnt[12] ),
    .Y(_111_));
 sky130_fd_sc_hd__and4_1 _153_ (.A(\wait_cnt[2] ),
    .B(\wait_cnt[3] ),
    .C(_020_),
    .D(\wait_cnt[4] ),
    .X(_112_));
 sky130_fd_sc_hd__nand2_1 _154_ (.A(_112_),
    .B(_103_),
    .Y(_113_));
 sky130_fd_sc_hd__or4_4 _155_ (.A(net30),
    .B(_110_),
    .C(_111_),
    .D(_113_),
    .X(_114_));
 sky130_fd_sc_hd__nand4_1 _156_ (.A(\wait_cnt[2] ),
    .B(\wait_cnt[3] ),
    .C(_020_),
    .D(\wait_cnt[4] ),
    .Y(_115_));
 sky130_fd_sc_hd__nand2_1 _157_ (.A(\wait_cnt[5] ),
    .B(\wait_cnt[6] ),
    .Y(_116_));
 sky130_fd_sc_hd__nor2_1 _158_ (.A(_115_),
    .B(_116_),
    .Y(_117_));
 sky130_fd_sc_hd__nand2b_1 _159_ (.A_N(net31),
    .B(net32),
    .Y(_118_));
 sky130_fd_sc_hd__or2_2 _160_ (.A(net30),
    .B(_118_),
    .X(_119_));
 sky130_fd_sc_hd__a21oi_1 _161_ (.A1(_108_),
    .A2(_117_),
    .B1(_119_),
    .Y(_120_));
 sky130_fd_sc_hd__a21oi_1 _162_ (.A1(_109_),
    .A2(_114_),
    .B1(_120_),
    .Y(_121_));
 sky130_fd_sc_hd__and4b_1 _163_ (.A_N(\wait_cnt[5] ),
    .B(\wait_cnt[7] ),
    .C(\wait_cnt[10] ),
    .D(\wait_cnt[16] ),
    .X(_122_));
 sky130_fd_sc_hd__nor2_1 _164_ (.A(net31),
    .B(net32),
    .Y(_123_));
 sky130_fd_sc_hd__nor2_1 _165_ (.A(\wait_cnt[11] ),
    .B(\wait_cnt[12] ),
    .Y(_124_));
 sky130_fd_sc_hd__nand4_1 _166_ (.A(_096_),
    .B(_122_),
    .C(_123_),
    .D(_124_),
    .Y(_125_));
 sky130_fd_sc_hd__nand2_1 _167_ (.A(\wait_cnt[9] ),
    .B(_112_),
    .Y(_126_));
 sky130_fd_sc_hd__o21ba_2 _168_ (.A1(net32),
    .A2(net9),
    .B1_N(net30),
    .X(_127_));
 sky130_fd_sc_hd__a21oi_1 _169_ (.A1(net31),
    .A2(net32),
    .B1(net29),
    .Y(_021_));
 sky130_fd_sc_hd__o21ai_0 _170_ (.A1(net31),
    .A2(_127_),
    .B1(_021_),
    .Y(_022_));
 sky130_fd_sc_hd__o31a_1 _171_ (.A1(_125_),
    .A2(_110_),
    .A3(_126_),
    .B1(_022_),
    .X(_023_));
 sky130_fd_sc_hd__o21ai_0 _172_ (.A1(_097_),
    .A2(_121_),
    .B1(_023_),
    .Y(\next_state[0] ));
 sky130_fd_sc_hd__or3_1 _174_ (.A(\wait_cnt[8] ),
    .B(\wait_cnt[13] ),
    .C(\wait_cnt[14] ),
    .X(_025_));
 sky130_fd_sc_hd__or4_4 _175_ (.A(\wait_cnt[10] ),
    .B(\wait_cnt[11] ),
    .C(\wait_cnt[12] ),
    .D(\wait_cnt[15] ),
    .X(_026_));
 sky130_fd_sc_hd__nor4_1 _176_ (.A(_025_),
    .B(_026_),
    .C(_098_),
    .D(_100_),
    .Y(_027_));
 sky130_fd_sc_hd__and2_1 _177_ (.A(_103_),
    .B(_027_),
    .X(_028_));
 sky130_fd_sc_hd__o21ai_0 _178_ (.A1(net31),
    .A2(_028_),
    .B1(net29),
    .Y(_029_));
 sky130_fd_sc_hd__nor2_1 _179_ (.A(_097_),
    .B(net30),
    .Y(_030_));
 sky130_fd_sc_hd__nand3_1 _180_ (.A(_102_),
    .B(_103_),
    .C(_107_),
    .Y(_031_));
 sky130_fd_sc_hd__nand3_1 _181_ (.A(\wait_cnt[5] ),
    .B(\wait_cnt[6] ),
    .C(_112_),
    .Y(_032_));
 sky130_fd_sc_hd__o31ai_1 _182_ (.A1(net31),
    .A2(_031_),
    .A3(_032_),
    .B1(net32),
    .Y(_033_));
 sky130_fd_sc_hd__nand2_1 _183_ (.A(\wait_cnt[5] ),
    .B(_112_),
    .Y(_034_));
 sky130_fd_sc_hd__nand4_1 _184_ (.A(\wait_cnt[10] ),
    .B(\wait_cnt[11] ),
    .C(\wait_cnt[12] ),
    .D(_103_),
    .Y(_035_));
 sky130_fd_sc_hd__o31ai_1 _185_ (.A1(_110_),
    .A2(_034_),
    .A3(_035_),
    .B1(_123_),
    .Y(_036_));
 sky130_fd_sc_hd__and3_1 _186_ (.A(_030_),
    .B(_033_),
    .C(_036_),
    .X(_037_));
 sky130_fd_sc_hd__a31o_1 _187_ (.A1(net30),
    .A2(_118_),
    .A3(_029_),
    .B1(_037_),
    .X(\next_state[1] ));
 sky130_fd_sc_hd__nor4_1 _188_ (.A(net30),
    .B(_093_),
    .C(_031_),
    .D(_032_),
    .Y(_038_));
 sky130_fd_sc_hd__a31oi_1 _189_ (.A1(net30),
    .A2(_093_),
    .A3(_028_),
    .B1(_038_),
    .Y(_039_));
 sky130_fd_sc_hd__nor2_1 _190_ (.A(net30),
    .B(net32),
    .Y(_040_));
 sky130_fd_sc_hd__o21ai_0 _191_ (.A1(_096_),
    .A2(_040_),
    .B1(net31),
    .Y(_041_));
 sky130_fd_sc_hd__o31ai_1 _192_ (.A1(_097_),
    .A2(net31),
    .A3(_039_),
    .B1(_041_),
    .Y(\next_state[2] ));
 sky130_fd_sc_hd__xor2_1 _193_ (.A(net29),
    .B(net32),
    .X(_042_));
 sky130_fd_sc_hd__nand3_1 _194_ (.A(net30),
    .B(net31),
    .C(_042_),
    .Y(_043_));
 sky130_fd_sc_hd__nand2_1 _195_ (.A(_119_),
    .B(_043_),
    .Y(\next_state[3] ));
 sky130_fd_sc_hd__a211oi_4 _196_ (.A1(_109_),
    .A2(_114_),
    .B1(_120_),
    .C1(_097_),
    .Y(_044_));
 sky130_fd_sc_hd__nor3_2 _198_ (.A(_025_),
    .B(_026_),
    .C(_116_),
    .Y(_046_));
 sky130_fd_sc_hd__nand4_1 _199_ (.A(net32),
    .B(_112_),
    .C(_103_),
    .D(_046_),
    .Y(_047_));
 sky130_fd_sc_hd__a21boi_0 _200_ (.A1(_097_),
    .A2(_118_),
    .B1_N(net30),
    .Y(_048_));
 sky130_fd_sc_hd__nand2_1 _201_ (.A(net29),
    .B(net31),
    .Y(_049_));
 sky130_fd_sc_hd__a21oi_1 _202_ (.A1(net31),
    .A2(net32),
    .B1(net30),
    .Y(_050_));
 sky130_fd_sc_hd__a31oi_1 _203_ (.A1(net30),
    .A2(_118_),
    .A3(_049_),
    .B1(_050_),
    .Y(_051_));
 sky130_fd_sc_hd__a31oi_1 _204_ (.A1(_103_),
    .A2(_027_),
    .A3(_048_),
    .B1(_051_),
    .Y(_052_));
 sky130_fd_sc_hd__o311ai_4 _205_ (.A1(_097_),
    .A2(net30),
    .A3(_047_),
    .B1(_052_),
    .C1(_023_),
    .Y(_053_));
 sky130_fd_sc_hd__nor3_2 _207_ (.A(\wait_cnt[0] ),
    .B(net35),
    .C(net34),
    .Y(_000_));
 sky130_fd_sc_hd__nor3_2 _208_ (.A(_019_),
    .B(net35),
    .C(net34),
    .Y(_008_));
 sky130_fd_sc_hd__xnor2_1 _209_ (.A(\wait_cnt[2] ),
    .B(_020_),
    .Y(_055_));
 sky130_fd_sc_hd__nor3_2 _210_ (.A(net35),
    .B(net34),
    .C(_055_),
    .Y(_009_));
 sky130_fd_sc_hd__nand3_1 _211_ (.A(\wait_cnt[2] ),
    .B(\wait_cnt[0] ),
    .C(\wait_cnt[1] ),
    .Y(_056_));
 sky130_fd_sc_hd__xor2_1 _212_ (.A(\wait_cnt[3] ),
    .B(_056_),
    .X(_057_));
 sky130_fd_sc_hd__nor3_2 _213_ (.A(net35),
    .B(net34),
    .C(_057_),
    .Y(_010_));
 sky130_fd_sc_hd__nand3_1 _214_ (.A(\wait_cnt[2] ),
    .B(\wait_cnt[3] ),
    .C(_020_),
    .Y(_058_));
 sky130_fd_sc_hd__xor2_1 _215_ (.A(\wait_cnt[4] ),
    .B(_058_),
    .X(_059_));
 sky130_fd_sc_hd__nor3_2 _216_ (.A(net35),
    .B(net34),
    .C(_059_),
    .Y(_011_));
 sky130_fd_sc_hd__and3_1 _217_ (.A(\wait_cnt[4] ),
    .B(\wait_cnt[0] ),
    .C(\wait_cnt[1] ),
    .X(_060_));
 sky130_fd_sc_hd__nand3_1 _218_ (.A(\wait_cnt[2] ),
    .B(\wait_cnt[3] ),
    .C(_060_),
    .Y(_061_));
 sky130_fd_sc_hd__xor2_1 _219_ (.A(\wait_cnt[5] ),
    .B(_061_),
    .X(_062_));
 sky130_fd_sc_hd__nor3_2 _220_ (.A(net35),
    .B(net34),
    .C(_062_),
    .Y(_012_));
 sky130_fd_sc_hd__xor2_1 _221_ (.A(\wait_cnt[6] ),
    .B(_034_),
    .X(_063_));
 sky130_fd_sc_hd__nor3_2 _222_ (.A(net35),
    .B(net34),
    .C(_063_),
    .Y(_013_));
 sky130_fd_sc_hd__nor2_1 _223_ (.A(_116_),
    .B(_061_),
    .Y(_064_));
 sky130_fd_sc_hd__xnor2_1 _224_ (.A(\wait_cnt[7] ),
    .B(_064_),
    .Y(_065_));
 sky130_fd_sc_hd__nor3_2 _225_ (.A(net35),
    .B(net34),
    .C(_065_),
    .Y(_014_));
 sky130_fd_sc_hd__nand2_1 _226_ (.A(\wait_cnt[7] ),
    .B(_117_),
    .Y(_066_));
 sky130_fd_sc_hd__xor2_1 _227_ (.A(\wait_cnt[8] ),
    .B(_066_),
    .X(_067_));
 sky130_fd_sc_hd__nor3_2 _228_ (.A(net35),
    .B(net34),
    .C(_067_),
    .Y(_015_));
 sky130_fd_sc_hd__nand4_1 _229_ (.A(\wait_cnt[5] ),
    .B(\wait_cnt[7] ),
    .C(\wait_cnt[6] ),
    .D(\wait_cnt[8] ),
    .Y(_068_));
 sky130_fd_sc_hd__nor2_1 _230_ (.A(_061_),
    .B(_068_),
    .Y(_069_));
 sky130_fd_sc_hd__xnor2_1 _231_ (.A(\wait_cnt[9] ),
    .B(_069_),
    .Y(_070_));
 sky130_fd_sc_hd__nor3_2 _232_ (.A(net35),
    .B(net34),
    .C(_070_),
    .Y(_016_));
 sky130_fd_sc_hd__nor2_1 _233_ (.A(_126_),
    .B(_068_),
    .Y(_071_));
 sky130_fd_sc_hd__xnor2_1 _234_ (.A(\wait_cnt[10] ),
    .B(_071_),
    .Y(_072_));
 sky130_fd_sc_hd__nor3_1 _235_ (.A(net35),
    .B(net34),
    .C(_072_),
    .Y(_001_));
 sky130_fd_sc_hd__nand2_1 _236_ (.A(\wait_cnt[9] ),
    .B(\wait_cnt[10] ),
    .Y(_073_));
 sky130_fd_sc_hd__or3_1 _237_ (.A(_073_),
    .B(_061_),
    .C(_068_),
    .X(_074_));
 sky130_fd_sc_hd__xor2_1 _238_ (.A(\wait_cnt[11] ),
    .B(_074_),
    .X(_075_));
 sky130_fd_sc_hd__nor3_1 _239_ (.A(net35),
    .B(net34),
    .C(_075_),
    .Y(_002_));
 sky130_fd_sc_hd__nand3_1 _240_ (.A(\wait_cnt[9] ),
    .B(\wait_cnt[10] ),
    .C(\wait_cnt[11] ),
    .Y(_076_));
 sky130_fd_sc_hd__nor3_1 _241_ (.A(_115_),
    .B(_068_),
    .C(_076_),
    .Y(_077_));
 sky130_fd_sc_hd__xnor2_1 _242_ (.A(\wait_cnt[12] ),
    .B(_077_),
    .Y(_078_));
 sky130_fd_sc_hd__nor3_1 _243_ (.A(net35),
    .B(net34),
    .C(_078_),
    .Y(_003_));
 sky130_fd_sc_hd__inv_1 _244_ (.A(\wait_cnt[12] ),
    .Y(_079_));
 sky130_fd_sc_hd__nor4_1 _245_ (.A(_079_),
    .B(_061_),
    .C(_068_),
    .D(_076_),
    .Y(_080_));
 sky130_fd_sc_hd__xnor2_1 _246_ (.A(\wait_cnt[13] ),
    .B(_080_),
    .Y(_081_));
 sky130_fd_sc_hd__nor3_1 _247_ (.A(net35),
    .B(net34),
    .C(_081_),
    .Y(_004_));
 sky130_fd_sc_hd__nand3_1 _248_ (.A(\wait_cnt[13] ),
    .B(\wait_cnt[12] ),
    .C(_077_),
    .Y(_082_));
 sky130_fd_sc_hd__xor2_1 _249_ (.A(\wait_cnt[14] ),
    .B(_082_),
    .X(_083_));
 sky130_fd_sc_hd__nor3_1 _250_ (.A(net35),
    .B(net34),
    .C(_083_),
    .Y(_005_));
 sky130_fd_sc_hd__nand3_1 _251_ (.A(\wait_cnt[13] ),
    .B(\wait_cnt[12] ),
    .C(\wait_cnt[14] ),
    .Y(_084_));
 sky130_fd_sc_hd__nor4_1 _252_ (.A(_061_),
    .B(_068_),
    .C(_076_),
    .D(_084_),
    .Y(_085_));
 sky130_fd_sc_hd__xnor2_1 _253_ (.A(\wait_cnt[15] ),
    .B(_085_),
    .Y(_086_));
 sky130_fd_sc_hd__nor3_1 _254_ (.A(net35),
    .B(net34),
    .C(_086_),
    .Y(_006_));
 sky130_fd_sc_hd__nand4_1 _255_ (.A(\wait_cnt[13] ),
    .B(\wait_cnt[12] ),
    .C(\wait_cnt[14] ),
    .D(\wait_cnt[15] ),
    .Y(_087_));
 sky130_fd_sc_hd__nor4_1 _256_ (.A(_115_),
    .B(_068_),
    .C(_076_),
    .D(_087_),
    .Y(_088_));
 sky130_fd_sc_hd__xnor2_1 _257_ (.A(\wait_cnt[16] ),
    .B(_088_),
    .Y(_089_));
 sky130_fd_sc_hd__nor3_1 _258_ (.A(net35),
    .B(net34),
    .C(_089_),
    .Y(_007_));
 sky130_fd_sc_hd__inv_1 _259_ (.A(\wait_cnt[1] ),
    .Y(_017_));
 sky130_fd_sc_hd__nand2_1 _260_ (.A(net29),
    .B(net30),
    .Y(_090_));
 sky130_fd_sc_hd__o22ai_1 _261_ (.A1(net29),
    .A2(_119_),
    .B1(_090_),
    .B2(net25),
    .Y(net11));
 sky130_fd_sc_hd__nor2_1 _262_ (.A(net25),
    .B(_090_),
    .Y(net13));
 sky130_fd_sc_hd__and3_1 _263_ (.A(net30),
    .B(net31),
    .C(_093_),
    .X(net14));
 sky130_fd_sc_hd__nor3_1 _264_ (.A(net25),
    .B(_096_),
    .C(_030_),
    .Y(net16));
 sky130_fd_sc_hd__nor3_1 _265_ (.A(net29),
    .B(net30),
    .C(net25),
    .Y(net19));
 sky130_fd_sc_hd__o21ba_2 _266_ (.A1(_096_),
    .A2(_030_),
    .B1_N(net25),
    .X(net20));
 sky130_fd_sc_hd__nor2_1 _267_ (.A(net30),
    .B(net25),
    .Y(net21));
 sky130_fd_sc_hd__or3_1 _268_ (.A(net30),
    .B(net31),
    .C(net32),
    .X(net28));
 sky130_fd_sc_hd__nand2_1 _269_ (.A(_123_),
    .B(_090_),
    .Y(net22));
 sky130_fd_sc_hd__o21ai_0 _270_ (.A1(net29),
    .A2(_119_),
    .B1(net25),
    .Y(net26));
 sky130_fd_sc_hd__inv_1 _271_ (.A(net26),
    .Y(net23));
 sky130_fd_sc_hd__ha_1 _272_ (.A(\wait_cnt[0] ),
    .B(_017_),
    .COUT(_018_),
    .SUM(_019_));
 sky130_fd_sc_hd__ha_1 _273_ (.A(\wait_cnt[0] ),
    .B(\wait_cnt[1] ),
    .COUT(_020_),
    .SUM(_128_));
 sky130_fd_sc_hd__conb_1 _275__1 (.LO(init_addr[0]));
 sky130_fd_sc_hd__conb_1 _276__2 (.LO(init_addr[1]));
 sky130_fd_sc_hd__conb_1 _279__3 (.LO(init_addr[6]));
 sky130_fd_sc_hd__conb_1 _280__4 (.LO(init_addr[7]));
 sky130_fd_sc_hd__conb_1 _283__5 (.LO(init_addr[13]));
 sky130_fd_sc_hd__conb_1 _284__6 (.LO(init_addr[14]));
 sky130_fd_sc_hd__conb_1 _285__7 (.LO(init_bank[2]));
 sky130_fd_sc_hd__conb_1 _287__8 (.LO(init_cmd[3]));
 sky130_fd_sc_hd__conb_1 _288__9 (.LO(init_fail));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_0__f_clk (.A(clknet_0_clk),
    .X(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_1__f_clk (.A(clknet_0_clk),
    .X(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload0 (.A(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \init_state[0]$_DFF_PN0_  (.D(\next_state[0] ),
    .Q(net29),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \init_state[1]$_DFF_PN0_  (.D(\next_state[1] ),
    .Q(net30),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \init_state[2]$_DFF_PN0_  (.D(\next_state[2] ),
    .Q(net31),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \init_state[3]$_DFF_PN0_  (.D(\next_state[3] ),
    .Q(net32),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(enable),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input11 (.A(rst_n),
    .X(net10));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output12 (.A(net11),
    .X(init_addr[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output13 (.A(net13),
    .X(net12));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output14 (.A(net13),
    .X(init_addr[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output15 (.A(net14),
    .X(init_addr[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output16 (.A(net19),
    .X(net15));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output17 (.A(net16),
    .X(init_addr[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output18 (.A(net13),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output19 (.A(net13),
    .X(net18));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output20 (.A(net19),
    .X(init_addr[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output21 (.A(net20),
    .X(init_bank[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output22 (.A(net21),
    .X(init_bank[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output23 (.A(net22),
    .X(init_cke));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output24 (.A(net23),
    .X(init_cmd[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output25 (.A(net25),
    .X(net24));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output26 (.A(net25),
    .X(init_cmd[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output27 (.A(net26),
    .X(init_cmd_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output28 (.A(net27),
    .X(init_done));
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
 sky130_fd_sc_hd__buf_4 place35 (.A(_053_),
    .X(net34));
 sky130_fd_sc_hd__buf_4 place36 (.A(_044_),
    .X(net35));
 sky130_fd_sc_hd__buf_4 place37 (.A(net10),
    .X(net36));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[0]$_DFF_PN0_  (.D(_000_),
    .Q(\wait_cnt[0] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[10]$_DFF_PN0_  (.D(_001_),
    .Q(\wait_cnt[10] ),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[11]$_DFF_PN0_  (.D(_002_),
    .Q(\wait_cnt[11] ),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[12]$_DFF_PN0_  (.D(_003_),
    .Q(\wait_cnt[12] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[13]$_DFF_PN0_  (.D(_004_),
    .Q(\wait_cnt[13] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[14]$_DFF_PN0_  (.D(_005_),
    .Q(\wait_cnt[14] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[15]$_DFF_PN0_  (.D(_006_),
    .Q(\wait_cnt[15] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[16]$_DFF_PN0_  (.D(_007_),
    .Q(\wait_cnt[16] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[1]$_DFF_PN0_  (.D(_008_),
    .Q(\wait_cnt[1] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[2]$_DFF_PN0_  (.D(_009_),
    .Q(\wait_cnt[2] ),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[3]$_DFF_PN0_  (.D(_010_),
    .Q(\wait_cnt[3] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[4]$_DFF_PN0_  (.D(_011_),
    .Q(\wait_cnt[4] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[5]$_DFF_PN0_  (.D(_012_),
    .Q(\wait_cnt[5] ),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[6]$_DFF_PN0_  (.D(_013_),
    .Q(\wait_cnt[6] ),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[7]$_DFF_PN0_  (.D(_014_),
    .Q(\wait_cnt[7] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[8]$_DFF_PN0_  (.D(_015_),
    .Q(\wait_cnt[8] ),
    .RESET_B(net36),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \wait_cnt[9]$_DFF_PN0_  (.D(_016_),
    .Q(\wait_cnt[9] ),
    .RESET_B(net36),
    .CLK(clknet_1_1__leaf_clk));
 assign init_addr[11] = net12;
 assign init_addr[3] = net15;
 assign init_addr[5] = net17;
 assign init_addr[8] = net18;
 assign init_cmd[1] = net24;
endmodule
