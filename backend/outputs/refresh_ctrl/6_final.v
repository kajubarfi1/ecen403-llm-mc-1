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
 wire _105_;
 wire _106_;
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
 wire _129_;
 wire _130_;
 wire _131_;
 wire _132_;
 wire _133_;
 wire _134_;
 wire _135_;
 wire _136_;
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
 wire _153_;
 wire _154_;
 wire _155_;
 wire _156_;
 wire _157_;
 wire _158_;
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
 wire _174_;
 wire _175_;
 wire _176_;
 wire _177_;
 wire _178_;
 wire _179_;
 wire _180_;
 wire _181_;
 wire _182_;
 wire _183_;
 wire _184_;
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
 wire net26;
 wire net27;
 wire net28;
 wire net29;
 wire net30;
 wire net31;
 wire net32;
 wire net33;
 wire net34;
 wire net36;
 wire net37;
 wire net38;
 wire net39;
 wire net40;
 wire net41;
 wire net42;
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
 wire net35;
 wire starve_detect;
 wire net46;
 wire net47;
 wire net45;
 wire clknet_0_clk;
 wire clknet_1_0__leaf_clk;
 wire clknet_1_1__leaf_clk;
 wire net48;

 sky130_fd_sc_hd__nor3b_4 _186_ (.A(\refi_ctr[2] ),
    .B(\refi_ctr[3] ),
    .C_N(_057_),
    .Y(_069_));
 sky130_fd_sc_hd__nor2_1 _187_ (.A(\refi_ctr[4] ),
    .B(\refi_ctr[5] ),
    .Y(_070_));
 sky130_fd_sc_hd__nand3b_4 _188_ (.A_N(\refi_ctr[6] ),
    .B(_069_),
    .C(_070_),
    .Y(_071_));
 sky130_fd_sc_hd__nor2_1 _189_ (.A(\refi_ctr[7] ),
    .B(\refi_ctr[8] ),
    .Y(_072_));
 sky130_fd_sc_hd__nor2_1 _190_ (.A(\refi_ctr[9] ),
    .B(\refi_ctr[10] ),
    .Y(_073_));
 sky130_fd_sc_hd__nand2_1 _191_ (.A(_072_),
    .B(_073_),
    .Y(_074_));
 sky130_fd_sc_hd__nor4_1 _192_ (.A(\refi_ctr[12] ),
    .B(\refi_ctr[11] ),
    .C(_071_),
    .D(_074_),
    .Y(_075_));
 sky130_fd_sc_hd__and2_1 _193_ (.A(net33),
    .B(_075_),
    .X(_000_));
 sky130_fd_sc_hd__inv_2 _194_ (.A(net3),
    .Y(_025_));
 sky130_fd_sc_hd__nor2b_1 _195_ (.A(_037_),
    .B_N(_035_),
    .Y(_076_));
 sky130_fd_sc_hd__o21a_1 _196_ (.A1(_034_),
    .A2(_076_),
    .B1(_033_),
    .X(_077_));
 sky130_fd_sc_hd__o21a_1 _197_ (.A1(_032_),
    .A2(_077_),
    .B1(_031_),
    .X(_078_));
 sky130_fd_sc_hd__nand4_1 _198_ (.A(_031_),
    .B(_033_),
    .C(net48),
    .D(_038_),
    .Y(_079_));
 sky130_fd_sc_hd__o21ai_2 _199_ (.A1(_030_),
    .A2(_078_),
    .B1(_079_),
    .Y(_080_));
 sky130_fd_sc_hd__mux2i_1 _200_ (.A0(net3),
    .A1(net30),
    .S(net45),
    .Y(_045_));
 sky130_fd_sc_hd__inv_1 _201_ (.A(net29),
    .Y(_036_));
 sky130_fd_sc_hd__inv_1 _202_ (.A(net33),
    .Y(_081_));
 sky130_fd_sc_hd__nor4_1 _203_ (.A(net37),
    .B(net36),
    .C(net39),
    .D(net38),
    .Y(_082_));
 sky130_fd_sc_hd__nor2_1 _204_ (.A(_081_),
    .B(_082_),
    .Y(net40));
 sky130_fd_sc_hd__or3b_2 _205_ (.A(refi_tick),
    .B(net1),
    .C_N(net34),
    .X(_083_));
 sky130_fd_sc_hd__inv_1 _207_ (.A(_083_),
    .Y(_059_));
 sky130_fd_sc_hd__nor4_1 _208_ (.A(\refi_ctr[12] ),
    .B(\refi_ctr[11] ),
    .C(_071_),
    .D(_074_),
    .Y(_084_));
 sky130_fd_sc_hd__nor2_1 _209_ (.A(\refi_ctr[0] ),
    .B(_084_),
    .Y(_085_));
 sky130_fd_sc_hd__or4_4 _210_ (.A(\refi_ctr[12] ),
    .B(\refi_ctr[11] ),
    .C(_071_),
    .D(_074_),
    .X(_086_));
 sky130_fd_sc_hd__nor4_2 _212_ (.A(net25),
    .B(net26),
    .C(net27),
    .D(net28),
    .Y(_088_));
 sky130_fd_sc_hd__nor2_1 _213_ (.A(net8),
    .B(net7),
    .Y(_089_));
 sky130_fd_sc_hd__nor3b_1 _214_ (.A(net23),
    .B(net24),
    .C_N(_053_),
    .Y(_090_));
 sky130_fd_sc_hd__nor2_1 _215_ (.A(net10),
    .B(net9),
    .Y(_091_));
 sky130_fd_sc_hd__nand4_1 _216_ (.A(_088_),
    .B(_089_),
    .C(_090_),
    .D(_091_),
    .Y(_092_));
 sky130_fd_sc_hd__nor2_1 _217_ (.A(net20),
    .B(net19),
    .Y(_093_));
 sky130_fd_sc_hd__nor4_1 _218_ (.A(net12),
    .B(net15),
    .C(net18),
    .D(net17),
    .Y(_094_));
 sky130_fd_sc_hd__nor4_1 _219_ (.A(net11),
    .B(net14),
    .C(net13),
    .D(net16),
    .Y(_095_));
 sky130_fd_sc_hd__nand3_1 _220_ (.A(_093_),
    .B(_094_),
    .C(_095_),
    .Y(_096_));
 sky130_fd_sc_hd__nor2_1 _221_ (.A(_092_),
    .B(_096_),
    .Y(_097_));
 sky130_fd_sc_hd__nor3_2 _222_ (.A(net21),
    .B(_086_),
    .C(_097_),
    .Y(_098_));
 sky130_fd_sc_hd__o21a_1 _223_ (.A1(_085_),
    .A2(_098_),
    .B1(net33),
    .X(_001_));
 sky130_fd_sc_hd__nor2_1 _224_ (.A(_058_),
    .B(_084_),
    .Y(_099_));
 sky130_fd_sc_hd__nor3_1 _225_ (.A(_054_),
    .B(_086_),
    .C(_097_),
    .Y(_100_));
 sky130_fd_sc_hd__o21a_1 _226_ (.A1(_099_),
    .A2(_100_),
    .B1(net33),
    .X(_005_));
 sky130_fd_sc_hd__xor2_1 _227_ (.A(\refi_ctr[2] ),
    .B(_057_),
    .X(_101_));
 sky130_fd_sc_hd__nand2_1 _228_ (.A(_086_),
    .B(_101_),
    .Y(_102_));
 sky130_fd_sc_hd__or2_0 _229_ (.A(_092_),
    .B(_096_),
    .X(_103_));
 sky130_fd_sc_hd__xor2_1 _231_ (.A(net23),
    .B(_053_),
    .X(_105_));
 sky130_fd_sc_hd__nand3_1 _232_ (.A(_075_),
    .B(_103_),
    .C(_105_),
    .Y(_106_));
 sky130_fd_sc_hd__a21oi_1 _234_ (.A1(_102_),
    .A2(_106_),
    .B1(_081_),
    .Y(_006_));
 sky130_fd_sc_hd__o31ai_1 _235_ (.A1(net23),
    .A2(net21),
    .A3(net22),
    .B1(net24),
    .Y(_108_));
 sky130_fd_sc_hd__or4_4 _236_ (.A(net23),
    .B(net24),
    .C(net21),
    .D(net22),
    .X(_109_));
 sky130_fd_sc_hd__nand2_1 _237_ (.A(_108_),
    .B(_109_),
    .Y(_110_));
 sky130_fd_sc_hd__a21oi_1 _238_ (.A1(_103_),
    .A2(_110_),
    .B1(_086_),
    .Y(_111_));
 sky130_fd_sc_hd__o31ai_1 _239_ (.A1(\refi_ctr[2] ),
    .A2(\refi_ctr[0] ),
    .A3(\refi_ctr[1] ),
    .B1(\refi_ctr[3] ),
    .Y(_112_));
 sky130_fd_sc_hd__or4_4 _240_ (.A(\refi_ctr[2] ),
    .B(\refi_ctr[3] ),
    .C(\refi_ctr[0] ),
    .D(\refi_ctr[1] ),
    .X(_113_));
 sky130_fd_sc_hd__and3_2 _241_ (.A(_086_),
    .B(_112_),
    .C(_113_),
    .X(_114_));
 sky130_fd_sc_hd__nor3_1 _242_ (.A(_081_),
    .B(_111_),
    .C(_114_),
    .Y(_007_));
 sky130_fd_sc_hd__xnor2_1 _243_ (.A(\refi_ctr[4] ),
    .B(_069_),
    .Y(_115_));
 sky130_fd_sc_hd__xor2_1 _244_ (.A(net25),
    .B(_090_),
    .X(_116_));
 sky130_fd_sc_hd__a21oi_1 _245_ (.A1(_103_),
    .A2(_116_),
    .B1(_086_),
    .Y(_117_));
 sky130_fd_sc_hd__nor3_1 _246_ (.A(_081_),
    .B(_115_),
    .C(_117_),
    .Y(_008_));
 sky130_fd_sc_hd__nor2_1 _247_ (.A(\refi_ctr[4] ),
    .B(_113_),
    .Y(_118_));
 sky130_fd_sc_hd__xor2_1 _248_ (.A(\refi_ctr[5] ),
    .B(_118_),
    .X(_119_));
 sky130_fd_sc_hd__nand2_1 _249_ (.A(_086_),
    .B(_119_),
    .Y(_120_));
 sky130_fd_sc_hd__nor2_1 _250_ (.A(net25),
    .B(_109_),
    .Y(_121_));
 sky130_fd_sc_hd__xor2_1 _251_ (.A(net26),
    .B(_121_),
    .X(_122_));
 sky130_fd_sc_hd__nand3_1 _252_ (.A(_075_),
    .B(_103_),
    .C(_122_),
    .Y(_123_));
 sky130_fd_sc_hd__a21oi_1 _253_ (.A1(_120_),
    .A2(_123_),
    .B1(_081_),
    .Y(_009_));
 sky130_fd_sc_hd__nand2_1 _254_ (.A(_069_),
    .B(_070_),
    .Y(_124_));
 sky130_fd_sc_hd__xor2_1 _255_ (.A(\refi_ctr[6] ),
    .B(_124_),
    .X(_125_));
 sky130_fd_sc_hd__nor2_1 _256_ (.A(net25),
    .B(net26),
    .Y(_126_));
 sky130_fd_sc_hd__nand2_1 _257_ (.A(_126_),
    .B(_090_),
    .Y(_127_));
 sky130_fd_sc_hd__xnor2_1 _258_ (.A(net27),
    .B(_127_),
    .Y(_128_));
 sky130_fd_sc_hd__a21oi_1 _259_ (.A1(_103_),
    .A2(_128_),
    .B1(_086_),
    .Y(_129_));
 sky130_fd_sc_hd__nor3_1 _260_ (.A(_081_),
    .B(_125_),
    .C(_129_),
    .Y(_010_));
 sky130_fd_sc_hd__nor4_2 _261_ (.A(\refi_ctr[4] ),
    .B(\refi_ctr[5] ),
    .C(\refi_ctr[6] ),
    .D(_113_),
    .Y(_130_));
 sky130_fd_sc_hd__xnor2_1 _262_ (.A(\refi_ctr[7] ),
    .B(_130_),
    .Y(_131_));
 sky130_fd_sc_hd__nor4_1 _263_ (.A(net25),
    .B(net26),
    .C(net27),
    .D(_109_),
    .Y(_132_));
 sky130_fd_sc_hd__xor2_1 _264_ (.A(net28),
    .B(_132_),
    .X(_133_));
 sky130_fd_sc_hd__a21oi_1 _265_ (.A1(_103_),
    .A2(_133_),
    .B1(_086_),
    .Y(_134_));
 sky130_fd_sc_hd__a211oi_1 _266_ (.A1(_086_),
    .A2(_131_),
    .B1(_134_),
    .C1(_081_),
    .Y(_011_));
 sky130_fd_sc_hd__nor2_1 _267_ (.A(\refi_ctr[7] ),
    .B(_071_),
    .Y(_135_));
 sky130_fd_sc_hd__xnor2_1 _268_ (.A(\refi_ctr[8] ),
    .B(_135_),
    .Y(_136_));
 sky130_fd_sc_hd__nand2_1 _269_ (.A(_088_),
    .B(_090_),
    .Y(_137_));
 sky130_fd_sc_hd__xnor2_1 _270_ (.A(net7),
    .B(_137_),
    .Y(_138_));
 sky130_fd_sc_hd__a21oi_1 _271_ (.A1(_103_),
    .A2(_138_),
    .B1(_086_),
    .Y(_139_));
 sky130_fd_sc_hd__nor3_1 _272_ (.A(_081_),
    .B(_136_),
    .C(_139_),
    .Y(_012_));
 sky130_fd_sc_hd__nand2_1 _273_ (.A(_072_),
    .B(_130_),
    .Y(_140_));
 sky130_fd_sc_hd__xor2_1 _274_ (.A(\refi_ctr[9] ),
    .B(_140_),
    .X(_141_));
 sky130_fd_sc_hd__nor3b_1 _275_ (.A(_109_),
    .B(net7),
    .C_N(_088_),
    .Y(_142_));
 sky130_fd_sc_hd__xnor2_1 _276_ (.A(net8),
    .B(_142_),
    .Y(_143_));
 sky130_fd_sc_hd__nand3_1 _277_ (.A(net33),
    .B(_084_),
    .C(_103_),
    .Y(_144_));
 sky130_fd_sc_hd__o32ai_1 _278_ (.A1(_081_),
    .A2(_084_),
    .A3(_141_),
    .B1(_143_),
    .B2(_144_),
    .Y(_013_));
 sky130_fd_sc_hd__or4_1 _279_ (.A(\refi_ctr[7] ),
    .B(\refi_ctr[9] ),
    .C(\refi_ctr[8] ),
    .D(_071_),
    .X(_145_));
 sky130_fd_sc_hd__xor2_1 _280_ (.A(\refi_ctr[10] ),
    .B(_145_),
    .X(_146_));
 sky130_fd_sc_hd__nand3_1 _281_ (.A(_088_),
    .B(_089_),
    .C(_090_),
    .Y(_147_));
 sky130_fd_sc_hd__xnor2_1 _282_ (.A(net9),
    .B(_147_),
    .Y(_148_));
 sky130_fd_sc_hd__a21oi_1 _283_ (.A1(_103_),
    .A2(_148_),
    .B1(_086_),
    .Y(_149_));
 sky130_fd_sc_hd__nor3_1 _284_ (.A(_081_),
    .B(_146_),
    .C(_149_),
    .Y(_002_));
 sky130_fd_sc_hd__inv_1 _285_ (.A(\refi_ctr[12] ),
    .Y(_150_));
 sky130_fd_sc_hd__a21oi_1 _286_ (.A1(_150_),
    .A2(_069_),
    .B1(\refi_ctr[11] ),
    .Y(_151_));
 sky130_fd_sc_hd__and2b_1 _287_ (.A_N(_074_),
    .B(_130_),
    .X(_152_));
 sky130_fd_sc_hd__mux2i_1 _288_ (.A0(\refi_ctr[11] ),
    .A1(_151_),
    .S(_152_),
    .Y(_153_));
 sky130_fd_sc_hd__nand2_1 _289_ (.A(_088_),
    .B(_089_),
    .Y(_154_));
 sky130_fd_sc_hd__nor3_1 _290_ (.A(net9),
    .B(_154_),
    .C(_109_),
    .Y(_155_));
 sky130_fd_sc_hd__xnor2_1 _291_ (.A(net10),
    .B(_155_),
    .Y(_156_));
 sky130_fd_sc_hd__o22ai_1 _292_ (.A1(_081_),
    .A2(_153_),
    .B1(_156_),
    .B2(_144_),
    .Y(_003_));
 sky130_fd_sc_hd__xor2_1 _293_ (.A(net11),
    .B(_092_),
    .X(_157_));
 sky130_fd_sc_hd__o311ai_0 _294_ (.A1(\refi_ctr[11] ),
    .A2(_071_),
    .A3(_074_),
    .B1(\refi_ctr[12] ),
    .C1(net33),
    .Y(_158_));
 sky130_fd_sc_hd__o21ai_0 _295_ (.A1(_144_),
    .A2(_157_),
    .B1(_158_),
    .Y(_004_));
 sky130_fd_sc_hd__inv_1 _296_ (.A(net37),
    .Y(_015_));
 sky130_fd_sc_hd__inv_1 _297_ (.A(net36),
    .Y(_014_));
 sky130_fd_sc_hd__inv_1 _298_ (.A(net21),
    .Y(_051_));
 sky130_fd_sc_hd__inv_1 _299_ (.A(\refi_ctr[0] ),
    .Y(_055_));
 sky130_fd_sc_hd__inv_1 _300_ (.A(net5),
    .Y(_019_));
 sky130_fd_sc_hd__inv_1 _301_ (.A(net4),
    .Y(_022_));
 sky130_fd_sc_hd__mux2i_1 _302_ (.A0(net5),
    .A1(net32),
    .S(net45),
    .Y(_039_));
 sky130_fd_sc_hd__mux2i_1 _303_ (.A0(net4),
    .A1(net31),
    .S(net45),
    .Y(_042_));
 sky130_fd_sc_hd__mux2_4 _304_ (.A0(net2),
    .A1(net29),
    .S(_080_),
    .X(_048_));
 sky130_fd_sc_hd__inv_1 _305_ (.A(net22),
    .Y(_052_));
 sky130_fd_sc_hd__inv_1 _306_ (.A(\refi_ctr[1] ),
    .Y(_056_));
 sky130_fd_sc_hd__nor2b_1 _307_ (.A(_028_),
    .B_N(_027_),
    .Y(_159_));
 sky130_fd_sc_hd__o211ai_1 _308_ (.A1(_026_),
    .A2(_159_),
    .B1(_021_),
    .C1(_024_),
    .Y(_160_));
 sky130_fd_sc_hd__a21oi_1 _309_ (.A1(_021_),
    .A2(_023_),
    .B1(_020_),
    .Y(_161_));
 sky130_fd_sc_hd__nor2_1 _310_ (.A(refi_tick),
    .B(net1),
    .Y(_162_));
 sky130_fd_sc_hd__nor2_1 _311_ (.A(net34),
    .B(_162_),
    .Y(_163_));
 sky130_fd_sc_hd__nor2_1 _312_ (.A(_082_),
    .B(_083_),
    .Y(_164_));
 sky130_fd_sc_hd__a31oi_1 _313_ (.A1(_160_),
    .A2(_161_),
    .A3(_163_),
    .B1(_164_),
    .Y(_165_));
 sky130_fd_sc_hd__xnor2_1 _314_ (.A(_014_),
    .B(_165_),
    .Y(_166_));
 sky130_fd_sc_hd__nor2_1 _315_ (.A(_081_),
    .B(_166_),
    .Y(_064_));
 sky130_fd_sc_hd__nand3_1 _316_ (.A(net33),
    .B(net37),
    .C(_165_),
    .Y(_167_));
 sky130_fd_sc_hd__o31ai_1 _317_ (.A1(_081_),
    .A2(_018_),
    .A3(_165_),
    .B1(_167_),
    .Y(_065_));
 sky130_fd_sc_hd__xor2_1 _318_ (.A(_017_),
    .B(_063_),
    .X(_168_));
 sky130_fd_sc_hd__nand3_1 _319_ (.A(net33),
    .B(net38),
    .C(_083_),
    .Y(_169_));
 sky130_fd_sc_hd__and3_1 _320_ (.A(_160_),
    .B(_161_),
    .C(_163_),
    .X(_170_));
 sky130_fd_sc_hd__o32ai_1 _321_ (.A1(_081_),
    .A2(_165_),
    .A3(_168_),
    .B1(_169_),
    .B2(_170_),
    .Y(_066_));
 sky130_fd_sc_hd__a21o_1 _322_ (.A1(net36),
    .A2(_061_),
    .B1(_060_),
    .X(_171_));
 sky130_fd_sc_hd__a21oi_1 _323_ (.A1(_063_),
    .A2(_171_),
    .B1(_062_),
    .Y(_172_));
 sky130_fd_sc_hd__inv_1 _324_ (.A(net39),
    .Y(_173_));
 sky130_fd_sc_hd__xnor2_1 _325_ (.A(_173_),
    .B(_170_),
    .Y(_174_));
 sky130_fd_sc_hd__xnor2_1 _326_ (.A(_173_),
    .B(_083_),
    .Y(_175_));
 sky130_fd_sc_hd__nand2_1 _327_ (.A(_172_),
    .B(_175_),
    .Y(_176_));
 sky130_fd_sc_hd__a21oi_1 _328_ (.A1(_082_),
    .A2(_059_),
    .B1(_081_),
    .Y(_177_));
 sky130_fd_sc_hd__o211a_1 _329_ (.A1(_172_),
    .A2(_174_),
    .B1(_176_),
    .C1(_177_),
    .X(_067_));
 sky130_fd_sc_hd__nand2b_1 _330_ (.A_N(_050_),
    .B(_049_),
    .Y(_178_));
 sky130_fd_sc_hd__a21o_1 _331_ (.A1(_047_),
    .A2(_178_),
    .B1(_046_),
    .X(_179_));
 sky130_fd_sc_hd__a21o_1 _332_ (.A1(_044_),
    .A2(_179_),
    .B1(_043_),
    .X(_180_));
 sky130_fd_sc_hd__a21oi_1 _333_ (.A1(_180_),
    .A2(_041_),
    .B1(_040_),
    .Y(_181_));
 sky130_fd_sc_hd__nand2_1 _334_ (.A(net6),
    .B(net40),
    .Y(_182_));
 sky130_fd_sc_hd__nor2_1 _335_ (.A(_181_),
    .B(_182_),
    .Y(net42));
 sky130_fd_sc_hd__nand4_1 _336_ (.A(_021_),
    .B(_024_),
    .C(_027_),
    .D(_029_),
    .Y(_183_));
 sky130_fd_sc_hd__nand2_1 _337_ (.A(net33),
    .B(refi_tick),
    .Y(_184_));
 sky130_fd_sc_hd__a31oi_1 _338_ (.A1(_160_),
    .A2(_161_),
    .A3(_183_),
    .B1(_184_),
    .Y(starve_detect));
 sky130_fd_sc_hd__fa_1 _339_ (.A(_014_),
    .B(_015_),
    .CIN(_083_),
    .COUT(_017_),
    .SUM(_018_));
 sky130_fd_sc_hd__ha_1 _340_ (.A(net39),
    .B(_019_),
    .COUT(_020_),
    .SUM(_021_));
 sky130_fd_sc_hd__ha_1 _341_ (.A(net38),
    .B(_022_),
    .COUT(_023_),
    .SUM(_024_));
 sky130_fd_sc_hd__ha_1 _342_ (.A(net37),
    .B(net46),
    .COUT(_026_),
    .SUM(_027_));
 sky130_fd_sc_hd__ha_1 _343_ (.A(_014_),
    .B(net2),
    .COUT(_028_),
    .SUM(_029_));
 sky130_fd_sc_hd__ha_1 _344_ (.A(net32),
    .B(_019_),
    .COUT(_030_),
    .SUM(_031_));
 sky130_fd_sc_hd__ha_4 _345_ (.A(net31),
    .B(_022_),
    .COUT(_032_),
    .SUM(_033_));
 sky130_fd_sc_hd__ha_4 _346_ (.A(_025_),
    .B(net30),
    .COUT(_034_),
    .SUM(_035_));
 sky130_fd_sc_hd__ha_1 _347_ (.A(_036_),
    .B(net2),
    .COUT(_037_),
    .SUM(_038_));
 sky130_fd_sc_hd__ha_1 _348_ (.A(net39),
    .B(_039_),
    .COUT(_040_),
    .SUM(_041_));
 sky130_fd_sc_hd__ha_1 _349_ (.A(net38),
    .B(_042_),
    .COUT(_043_),
    .SUM(_044_));
 sky130_fd_sc_hd__ha_1 _350_ (.A(net37),
    .B(_045_),
    .COUT(_046_),
    .SUM(_047_));
 sky130_fd_sc_hd__ha_1 _351_ (.A(_014_),
    .B(_048_),
    .COUT(_049_),
    .SUM(_050_));
 sky130_fd_sc_hd__ha_1 _352_ (.A(_051_),
    .B(_052_),
    .COUT(_053_),
    .SUM(_054_));
 sky130_fd_sc_hd__ha_1 _353_ (.A(_055_),
    .B(_056_),
    .COUT(_057_),
    .SUM(_058_));
 sky130_fd_sc_hd__ha_1 _354_ (.A(net37),
    .B(_059_),
    .COUT(_060_),
    .SUM(_061_));
 sky130_fd_sc_hd__ha_1 _355_ (.A(net38),
    .B(_059_),
    .COUT(_062_),
    .SUM(_063_));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_0__f_clk (.A(clknet_0_clk),
    .X(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_1__f_clk (.A(clknet_0_clk),
    .X(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload0 (.A(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input1 (.A(cfg_force_refresh),
    .X(net1));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(cfg_tREFI_nCK[13]),
    .X(net10));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input11 (.A(cfg_tREFI_nCK[14]),
    .X(net11));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input12 (.A(cfg_tREFI_nCK[15]),
    .X(net12));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input13 (.A(cfg_tREFI_nCK[16]),
    .X(net13));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input14 (.A(cfg_tREFI_nCK[17]),
    .X(net14));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input15 (.A(cfg_tREFI_nCK[18]),
    .X(net15));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input16 (.A(cfg_tREFI_nCK[19]),
    .X(net16));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input17 (.A(cfg_tREFI_nCK[20]),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input18 (.A(cfg_tREFI_nCK[21]),
    .X(net18));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input19 (.A(cfg_tREFI_nCK[22]),
    .X(net19));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input2 (.A(cfg_max_postpone[0]),
    .X(net2));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input20 (.A(cfg_tREFI_nCK[23]),
    .X(net20));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input21 (.A(cfg_tREFI_nCK[2]),
    .X(net21));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input22 (.A(cfg_tREFI_nCK[3]),
    .X(net22));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input23 (.A(cfg_tREFI_nCK[4]),
    .X(net23));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input24 (.A(cfg_tREFI_nCK[5]),
    .X(net24));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input25 (.A(cfg_tREFI_nCK[6]),
    .X(net25));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input26 (.A(cfg_tREFI_nCK[7]),
    .X(net26));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input27 (.A(cfg_tREFI_nCK[8]),
    .X(net27));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input28 (.A(cfg_tREFI_nCK[9]),
    .X(net28));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input29 (.A(cfg_urgent_threshold[0]),
    .X(net29));
 sky130_fd_sc_hd__dlygate4sd2_1 input3 (.A(cfg_max_postpone[1]),
    .X(net3));
 sky130_fd_sc_hd__dlymetal6s2s_1 input30 (.A(cfg_urgent_threshold[1]),
    .X(net30));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input31 (.A(cfg_urgent_threshold[2]),
    .X(net31));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input32 (.A(cfg_urgent_threshold[3]),
    .X(net32));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input33 (.A(init_done),
    .X(net33));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input34 (.A(ref_ack),
    .X(net34));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input35 (.A(rst_n),
    .X(net35));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input4 (.A(cfg_max_postpone[2]),
    .X(net4));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input5 (.A(cfg_max_postpone[3]),
    .X(net5));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input6 (.A(cfg_ref_priority),
    .X(net6));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input7 (.A(cfg_tREFI_nCK[10]),
    .X(net7));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input8 (.A(cfg_tREFI_nCK[11]),
    .X(net8));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input9 (.A(cfg_tREFI_nCK[12]),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output36 (.A(net36),
    .X(ref_pending_cnt[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output37 (.A(net37),
    .X(ref_pending_cnt[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output38 (.A(net38),
    .X(ref_pending_cnt[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output39 (.A(net39),
    .X(ref_pending_cnt[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output40 (.A(net40),
    .X(ref_required));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output41 (.A(net41),
    .X(ref_starve_flag));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output42 (.A(net42),
    .X(ref_urgent));
 sky130_fd_sc_hd__buf_4 place45 (.A(_080_),
    .X(net45));
 sky130_fd_sc_hd__buf_4 place46 (.A(_025_),
    .X(net46));
 sky130_fd_sc_hd__buf_4 place47 (.A(net35),
    .X(net47));
 sky130_fd_sc_hd__buf_4 rebuffer48 (.A(_035_),
    .X(net48));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[0]$_DFFE_PN0P_  (.D(_064_),
    .Q(net36),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[1]$_DFFE_PN0P_  (.D(_065_),
    .Q(net37),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[2]$_DFFE_PN0P_  (.D(_066_),
    .Q(net38),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[3]$_DFFE_PN0P_  (.D(_067_),
    .Q(net39),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_starve_flag$_DFF_PN0_  (.D(starve_detect),
    .Q(net41),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[0]$_DFF_PN0_  (.D(_001_),
    .Q(\refi_ctr[0] ),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[10]$_DFF_PN0_  (.D(_002_),
    .Q(\refi_ctr[10] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[11]$_DFF_PN0_  (.D(_003_),
    .Q(\refi_ctr[11] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[12]$_DFF_PN0_  (.D(_004_),
    .Q(\refi_ctr[12] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[1]$_DFF_PN0_  (.D(_005_),
    .Q(\refi_ctr[1] ),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[2]$_DFF_PN0_  (.D(_006_),
    .Q(\refi_ctr[2] ),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[3]$_DFF_PN0_  (.D(_007_),
    .Q(\refi_ctr[3] ),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[4]$_DFF_PN0_  (.D(_008_),
    .Q(\refi_ctr[4] ),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[5]$_DFF_PN0_  (.D(_009_),
    .Q(\refi_ctr[5] ),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[6]$_DFF_PN0_  (.D(_010_),
    .Q(\refi_ctr[6] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[7]$_DFF_PN0_  (.D(_011_),
    .Q(\refi_ctr[7] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[8]$_DFF_PN0_  (.D(_012_),
    .Q(\refi_ctr[8] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[9]$_DFF_PN0_  (.D(_013_),
    .Q(\refi_ctr[9] ),
    .RESET_B(net47),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_tick$_DFF_PN0_  (.D(_000_),
    .Q(refi_tick),
    .RESET_B(net47),
    .CLK(clknet_1_0__leaf_clk));
endmodule
