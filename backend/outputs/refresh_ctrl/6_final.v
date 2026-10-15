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
 wire _059_;
 wire _060_;
 wire _061_;
 wire _062_;
 wire _063_;
 wire _064_;
 wire _065_;
 wire _066_;
 wire _068_;
 wire _069_;
 wire _071_;
 wire _072_;
 wire _073_;
 wire _074_;
 wire _075_;
 wire _076_;
 wire _077_;
 wire _078_;
 wire _080_;
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
 wire net45;
 wire net44;
 wire net46;
 wire clknet_0_clk;
 wire clknet_1_0__leaf_clk;
 wire clknet_1_1__leaf_clk;

 sky130_fd_sc_hd__nor2_1 _166_ (.A(\refi_ctr[2] ),
    .B(\refi_ctr[3] ),
    .Y(_058_));
 sky130_fd_sc_hd__or4bb_1 _167_ (.A(\refi_ctr[11] ),
    .B(\refi_ctr[12] ),
    .C_N(_058_),
    .D_N(_049_),
    .X(_059_));
 sky130_fd_sc_hd__or4_4 _168_ (.A(\refi_ctr[4] ),
    .B(\refi_ctr[5] ),
    .C(\refi_ctr[6] ),
    .D(\refi_ctr[7] ),
    .X(_060_));
 sky130_fd_sc_hd__or3_4 _169_ (.A(\refi_ctr[9] ),
    .B(\refi_ctr[8] ),
    .C(_060_),
    .X(_061_));
 sky130_fd_sc_hd__nor3_1 _170_ (.A(\refi_ctr[10] ),
    .B(_059_),
    .C(_061_),
    .Y(_062_));
 sky130_fd_sc_hd__nand2_1 _171_ (.A(net33),
    .B(_062_),
    .Y(_063_));
 sky130_fd_sc_hd__inv_1 _172_ (.A(_063_),
    .Y(_000_));
 sky130_fd_sc_hd__inv_1 _173_ (.A(net33),
    .Y(_064_));
 sky130_fd_sc_hd__nor4_1 _174_ (.A(net37),
    .B(net36),
    .C(net39),
    .D(net38),
    .Y(_065_));
 sky130_fd_sc_hd__nor2_1 _175_ (.A(_064_),
    .B(_065_),
    .Y(net40));
 sky130_fd_sc_hd__or3b_2 _176_ (.A(refi_tick),
    .B(net1),
    .C_N(net34),
    .X(_066_));
 sky130_fd_sc_hd__inv_1 _177_ (.A(_066_),
    .Y(_014_));
 sky130_fd_sc_hd__nor2_1 _179_ (.A(\refi_ctr[0] ),
    .B(net45),
    .Y(_068_));
 sky130_fd_sc_hd__or3_1 _180_ (.A(\refi_ctr[10] ),
    .B(_059_),
    .C(_061_),
    .X(_069_));
 sky130_fd_sc_hd__nor2_1 _182_ (.A(net23),
    .B(net24),
    .Y(_071_));
 sky130_fd_sc_hd__nor4_1 _183_ (.A(net14),
    .B(net13),
    .C(net16),
    .D(net18),
    .Y(_072_));
 sky130_fd_sc_hd__nor4_1 _184_ (.A(net11),
    .B(net15),
    .C(net17),
    .D(net20),
    .Y(_073_));
 sky130_fd_sc_hd__nor3b_1 _185_ (.A(net12),
    .B(net19),
    .C_N(_044_),
    .Y(_074_));
 sky130_fd_sc_hd__nand4_1 _186_ (.A(_071_),
    .B(_072_),
    .C(_073_),
    .D(_074_),
    .Y(_075_));
 sky130_fd_sc_hd__or4_1 _187_ (.A(net25),
    .B(net26),
    .C(net27),
    .D(net28),
    .X(_076_));
 sky130_fd_sc_hd__or3_1 _188_ (.A(net8),
    .B(net7),
    .C(net9),
    .X(_077_));
 sky130_fd_sc_hd__nor4_1 _189_ (.A(net10),
    .B(_075_),
    .C(_076_),
    .D(_077_),
    .Y(_078_));
 sky130_fd_sc_hd__nor3_1 _191_ (.A(net21),
    .B(_069_),
    .C(net44),
    .Y(_080_));
 sky130_fd_sc_hd__o21a_1 _193_ (.A1(_068_),
    .A2(_080_),
    .B1(net33),
    .X(_001_));
 sky130_fd_sc_hd__nor2_1 _194_ (.A(_048_),
    .B(net45),
    .Y(_082_));
 sky130_fd_sc_hd__nor3_1 _195_ (.A(_043_),
    .B(_069_),
    .C(net44),
    .Y(_083_));
 sky130_fd_sc_hd__o21a_1 _196_ (.A1(_082_),
    .A2(_083_),
    .B1(net33),
    .X(_005_));
 sky130_fd_sc_hd__xnor2_1 _197_ (.A(\refi_ctr[2] ),
    .B(_047_),
    .Y(_084_));
 sky130_fd_sc_hd__nor2_1 _198_ (.A(net45),
    .B(_084_),
    .Y(_085_));
 sky130_fd_sc_hd__xnor2_1 _199_ (.A(net23),
    .B(_042_),
    .Y(_086_));
 sky130_fd_sc_hd__nor3_1 _200_ (.A(_069_),
    .B(net44),
    .C(_086_),
    .Y(_087_));
 sky130_fd_sc_hd__o21a_1 _201_ (.A1(_085_),
    .A2(_087_),
    .B1(net33),
    .X(_006_));
 sky130_fd_sc_hd__o31ai_1 _202_ (.A1(\refi_ctr[2] ),
    .A2(\refi_ctr[0] ),
    .A3(\refi_ctr[1] ),
    .B1(\refi_ctr[3] ),
    .Y(_088_));
 sky130_fd_sc_hd__inv_1 _203_ (.A(\refi_ctr[0] ),
    .Y(_045_));
 sky130_fd_sc_hd__inv_1 _204_ (.A(\refi_ctr[1] ),
    .Y(_046_));
 sky130_fd_sc_hd__nand3_1 _205_ (.A(_045_),
    .B(_046_),
    .C(_058_),
    .Y(_089_));
 sky130_fd_sc_hd__a21oi_1 _206_ (.A1(_088_),
    .A2(_089_),
    .B1(net45),
    .Y(_090_));
 sky130_fd_sc_hd__o31ai_1 _207_ (.A1(net23),
    .A2(net21),
    .A3(net22),
    .B1(net24),
    .Y(_091_));
 sky130_fd_sc_hd__or4_1 _208_ (.A(net23),
    .B(net24),
    .C(net21),
    .D(net22),
    .X(_092_));
 sky130_fd_sc_hd__a211oi_1 _209_ (.A1(_091_),
    .A2(_092_),
    .B1(_069_),
    .C1(net44),
    .Y(_093_));
 sky130_fd_sc_hd__o21a_1 _210_ (.A1(_090_),
    .A2(_093_),
    .B1(net33),
    .X(_007_));
 sky130_fd_sc_hd__nand2_1 _211_ (.A(_042_),
    .B(_071_),
    .Y(_094_));
 sky130_fd_sc_hd__xor2_1 _212_ (.A(net25),
    .B(_094_),
    .X(_095_));
 sky130_fd_sc_hd__o21ai_0 _213_ (.A1(net44),
    .A2(_095_),
    .B1(net45),
    .Y(_096_));
 sky130_fd_sc_hd__and2_1 _214_ (.A(_047_),
    .B(_058_),
    .X(_097_));
 sky130_fd_sc_hd__xnor2_1 _215_ (.A(\refi_ctr[4] ),
    .B(_097_),
    .Y(_098_));
 sky130_fd_sc_hd__nand2_1 _216_ (.A(_069_),
    .B(_098_),
    .Y(_099_));
 sky130_fd_sc_hd__and3_1 _217_ (.A(net33),
    .B(_096_),
    .C(_099_),
    .X(_008_));
 sky130_fd_sc_hd__nor2_1 _218_ (.A(\refi_ctr[4] ),
    .B(_089_),
    .Y(_100_));
 sky130_fd_sc_hd__xor2_1 _219_ (.A(\refi_ctr[5] ),
    .B(_100_),
    .X(_101_));
 sky130_fd_sc_hd__nor2_1 _220_ (.A(net25),
    .B(_092_),
    .Y(_102_));
 sky130_fd_sc_hd__xnor2_1 _221_ (.A(net26),
    .B(_102_),
    .Y(_103_));
 sky130_fd_sc_hd__o21ai_0 _222_ (.A1(net44),
    .A2(_103_),
    .B1(net45),
    .Y(_104_));
 sky130_fd_sc_hd__o211a_1 _223_ (.A1(net45),
    .A2(_101_),
    .B1(_104_),
    .C1(net33),
    .X(_009_));
 sky130_fd_sc_hd__nand2_1 _224_ (.A(_047_),
    .B(_058_),
    .Y(_105_));
 sky130_fd_sc_hd__nor3_1 _225_ (.A(\refi_ctr[4] ),
    .B(\refi_ctr[5] ),
    .C(_105_),
    .Y(_106_));
 sky130_fd_sc_hd__xor2_1 _226_ (.A(\refi_ctr[6] ),
    .B(_106_),
    .X(_107_));
 sky130_fd_sc_hd__nor2_1 _227_ (.A(net25),
    .B(net26),
    .Y(_108_));
 sky130_fd_sc_hd__nand3_1 _228_ (.A(_042_),
    .B(_071_),
    .C(_108_),
    .Y(_109_));
 sky130_fd_sc_hd__xor2_1 _229_ (.A(net27),
    .B(_109_),
    .X(_110_));
 sky130_fd_sc_hd__o21ai_0 _230_ (.A1(net44),
    .A2(_110_),
    .B1(net45),
    .Y(_111_));
 sky130_fd_sc_hd__o211a_1 _231_ (.A1(net45),
    .A2(_107_),
    .B1(_111_),
    .C1(net33),
    .X(_010_));
 sky130_fd_sc_hd__nor4_1 _232_ (.A(net25),
    .B(net26),
    .C(net27),
    .D(_092_),
    .Y(_112_));
 sky130_fd_sc_hd__xnor2_1 _233_ (.A(net28),
    .B(_112_),
    .Y(_113_));
 sky130_fd_sc_hd__nor4_1 _234_ (.A(\refi_ctr[4] ),
    .B(\refi_ctr[5] ),
    .C(\refi_ctr[6] ),
    .D(_089_),
    .Y(_114_));
 sky130_fd_sc_hd__xnor2_1 _235_ (.A(\refi_ctr[7] ),
    .B(_114_),
    .Y(_115_));
 sky130_fd_sc_hd__nand2_1 _236_ (.A(net33),
    .B(_069_),
    .Y(_116_));
 sky130_fd_sc_hd__o32ai_1 _237_ (.A1(_063_),
    .A2(net44),
    .A3(_113_),
    .B1(_115_),
    .B2(_116_),
    .Y(_011_));
 sky130_fd_sc_hd__or4b_1 _238_ (.A(net23),
    .B(_076_),
    .C(net24),
    .D_N(_042_),
    .X(_117_));
 sky130_fd_sc_hd__xor2_1 _239_ (.A(net7),
    .B(_117_),
    .X(_118_));
 sky130_fd_sc_hd__nor2_1 _240_ (.A(_060_),
    .B(_105_),
    .Y(_119_));
 sky130_fd_sc_hd__xnor2_1 _241_ (.A(\refi_ctr[8] ),
    .B(_119_),
    .Y(_120_));
 sky130_fd_sc_hd__o32ai_1 _242_ (.A1(_063_),
    .A2(net44),
    .A3(_118_),
    .B1(_120_),
    .B2(_116_),
    .Y(_012_));
 sky130_fd_sc_hd__nor3_1 _243_ (.A(\refi_ctr[8] ),
    .B(_060_),
    .C(_089_),
    .Y(_121_));
 sky130_fd_sc_hd__xnor2_1 _244_ (.A(\refi_ctr[9] ),
    .B(_121_),
    .Y(_122_));
 sky130_fd_sc_hd__or3_4 _245_ (.A(_064_),
    .B(_069_),
    .C(net44),
    .X(_123_));
 sky130_fd_sc_hd__or2_2 _246_ (.A(_076_),
    .B(_092_),
    .X(_124_));
 sky130_fd_sc_hd__nor2_1 _247_ (.A(net7),
    .B(_124_),
    .Y(_125_));
 sky130_fd_sc_hd__xnor2_1 _248_ (.A(net8),
    .B(_125_),
    .Y(_126_));
 sky130_fd_sc_hd__o22ai_1 _249_ (.A1(_116_),
    .A2(_122_),
    .B1(_123_),
    .B2(_126_),
    .Y(_013_));
 sky130_fd_sc_hd__o31ai_1 _250_ (.A1(net8),
    .A2(net7),
    .A3(_117_),
    .B1(net9),
    .Y(_127_));
 sky130_fd_sc_hd__nor2_1 _251_ (.A(_077_),
    .B(_117_),
    .Y(_128_));
 sky130_fd_sc_hd__nor2_1 _252_ (.A(_069_),
    .B(_128_),
    .Y(_129_));
 sky130_fd_sc_hd__nand2_1 _253_ (.A(\refi_ctr[10] ),
    .B(_097_),
    .Y(_130_));
 sky130_fd_sc_hd__a21oi_1 _254_ (.A1(_059_),
    .A2(_105_),
    .B1(_061_),
    .Y(_131_));
 sky130_fd_sc_hd__o221ai_1 _255_ (.A1(_061_),
    .A2(_130_),
    .B1(_131_),
    .B2(\refi_ctr[10] ),
    .C1(net33),
    .Y(_132_));
 sky130_fd_sc_hd__a221oi_1 _256_ (.A1(net45),
    .A2(net44),
    .B1(_127_),
    .B2(_129_),
    .C1(_132_),
    .Y(_002_));
 sky130_fd_sc_hd__nor2_1 _257_ (.A(_077_),
    .B(_124_),
    .Y(_133_));
 sky130_fd_sc_hd__xnor2_1 _258_ (.A(net10),
    .B(_133_),
    .Y(_134_));
 sky130_fd_sc_hd__or3_1 _259_ (.A(\refi_ctr[10] ),
    .B(_061_),
    .C(_089_),
    .X(_135_));
 sky130_fd_sc_hd__xor2_1 _260_ (.A(\refi_ctr[11] ),
    .B(_135_),
    .X(_136_));
 sky130_fd_sc_hd__o22ai_2 _261_ (.A1(_123_),
    .A2(_134_),
    .B1(_136_),
    .B2(_116_),
    .Y(_003_));
 sky130_fd_sc_hd__a21oi_1 _262_ (.A1(_049_),
    .A2(_058_),
    .B1(\refi_ctr[12] ),
    .Y(_137_));
 sky130_fd_sc_hd__nor4_1 _263_ (.A(\refi_ctr[11] ),
    .B(\refi_ctr[10] ),
    .C(_061_),
    .D(_105_),
    .Y(_138_));
 sky130_fd_sc_hd__mux2i_1 _264_ (.A0(\refi_ctr[12] ),
    .A1(_137_),
    .S(_138_),
    .Y(_139_));
 sky130_fd_sc_hd__nor3_1 _265_ (.A(net10),
    .B(_077_),
    .C(_117_),
    .Y(_140_));
 sky130_fd_sc_hd__xnor2_1 _266_ (.A(net11),
    .B(_140_),
    .Y(_141_));
 sky130_fd_sc_hd__o22ai_1 _267_ (.A1(_064_),
    .A2(_139_),
    .B1(_141_),
    .B2(_123_),
    .Y(_004_));
 sky130_fd_sc_hd__inv_1 _268_ (.A(net36),
    .Y(_026_));
 sky130_fd_sc_hd__inv_1 _269_ (.A(net21),
    .Y(_040_));
 sky130_fd_sc_hd__inv_1 _270_ (.A(net5),
    .Y(_017_));
 sky130_fd_sc_hd__inv_1 _271_ (.A(net4),
    .Y(_020_));
 sky130_fd_sc_hd__inv_1 _272_ (.A(net3),
    .Y(_023_));
 sky130_fd_sc_hd__inv_1 _273_ (.A(net32),
    .Y(_029_));
 sky130_fd_sc_hd__inv_1 _274_ (.A(net31),
    .Y(_032_));
 sky130_fd_sc_hd__inv_1 _275_ (.A(net30),
    .Y(_035_));
 sky130_fd_sc_hd__inv_1 _276_ (.A(net22),
    .Y(_041_));
 sky130_fd_sc_hd__nor2_1 _277_ (.A(refi_tick),
    .B(net1),
    .Y(_142_));
 sky130_fd_sc_hd__nor2_1 _278_ (.A(net34),
    .B(_142_),
    .Y(_143_));
 sky130_fd_sc_hd__nor2b_1 _279_ (.A(_027_),
    .B_N(_025_),
    .Y(_144_));
 sky130_fd_sc_hd__o211ai_1 _280_ (.A1(_024_),
    .A2(_144_),
    .B1(_019_),
    .C1(_022_),
    .Y(_145_));
 sky130_fd_sc_hd__a21oi_1 _281_ (.A1(_019_),
    .A2(_021_),
    .B1(_018_),
    .Y(_146_));
 sky130_fd_sc_hd__nor2_1 _282_ (.A(_065_),
    .B(_066_),
    .Y(_147_));
 sky130_fd_sc_hd__a31oi_1 _283_ (.A1(_143_),
    .A2(_145_),
    .A3(_146_),
    .B1(_147_),
    .Y(_148_));
 sky130_fd_sc_hd__xnor2_1 _284_ (.A(_026_),
    .B(_148_),
    .Y(_149_));
 sky130_fd_sc_hd__nor2_1 _285_ (.A(_064_),
    .B(_149_),
    .Y(_054_));
 sky130_fd_sc_hd__mux2i_1 _286_ (.A0(_016_),
    .A1(net37),
    .S(_148_),
    .Y(_150_));
 sky130_fd_sc_hd__nor2_1 _287_ (.A(_064_),
    .B(_150_),
    .Y(_055_));
 sky130_fd_sc_hd__xor2_1 _288_ (.A(_053_),
    .B(_015_),
    .X(_151_));
 sky130_fd_sc_hd__mux2i_1 _289_ (.A0(_151_),
    .A1(net38),
    .S(_148_),
    .Y(_152_));
 sky130_fd_sc_hd__nor2_1 _290_ (.A(_064_),
    .B(_152_),
    .Y(_056_));
 sky130_fd_sc_hd__a21o_1 _291_ (.A1(net36),
    .A2(_051_),
    .B1(_050_),
    .X(_153_));
 sky130_fd_sc_hd__a21oi_1 _292_ (.A1(_053_),
    .A2(_153_),
    .B1(_052_),
    .Y(_154_));
 sky130_fd_sc_hd__xnor2_1 _293_ (.A(_066_),
    .B(_154_),
    .Y(_155_));
 sky130_fd_sc_hd__o21ai_0 _294_ (.A1(_148_),
    .A2(_155_),
    .B1(net39),
    .Y(_156_));
 sky130_fd_sc_hd__or3_1 _295_ (.A(net39),
    .B(_148_),
    .C(_155_),
    .X(_157_));
 sky130_fd_sc_hd__a21oi_1 _296_ (.A1(_156_),
    .A2(_157_),
    .B1(_064_),
    .Y(_057_));
 sky130_fd_sc_hd__nand2b_1 _297_ (.A_N(_039_),
    .B(_038_),
    .Y(_158_));
 sky130_fd_sc_hd__a21o_1 _298_ (.A1(_037_),
    .A2(_158_),
    .B1(_036_),
    .X(_159_));
 sky130_fd_sc_hd__a21o_1 _299_ (.A1(_034_),
    .A2(_159_),
    .B1(_033_),
    .X(_160_));
 sky130_fd_sc_hd__a21oi_1 _300_ (.A1(_031_),
    .A2(_160_),
    .B1(_030_),
    .Y(_161_));
 sky130_fd_sc_hd__and3b_1 _301_ (.A_N(_161_),
    .B(net40),
    .C(net6),
    .X(net42));
 sky130_fd_sc_hd__nand4_1 _302_ (.A(_019_),
    .B(_028_),
    .C(_025_),
    .D(_022_),
    .Y(_162_));
 sky130_fd_sc_hd__nand2_1 _303_ (.A(net33),
    .B(refi_tick),
    .Y(_163_));
 sky130_fd_sc_hd__a31oi_1 _304_ (.A1(_145_),
    .A2(_146_),
    .A3(_162_),
    .B1(_163_),
    .Y(starve_detect));
 sky130_fd_sc_hd__fa_1 _305_ (.A(net36),
    .B(net37),
    .CIN(_014_),
    .COUT(_015_),
    .SUM(_016_));
 sky130_fd_sc_hd__ha_1 _306_ (.A(net39),
    .B(_017_),
    .COUT(_018_),
    .SUM(_019_));
 sky130_fd_sc_hd__ha_1 _307_ (.A(net38),
    .B(_020_),
    .COUT(_021_),
    .SUM(_022_));
 sky130_fd_sc_hd__ha_1 _308_ (.A(net37),
    .B(_023_),
    .COUT(_024_),
    .SUM(_025_));
 sky130_fd_sc_hd__ha_1 _309_ (.A(_026_),
    .B(net2),
    .COUT(_027_),
    .SUM(_028_));
 sky130_fd_sc_hd__ha_1 _310_ (.A(net39),
    .B(_029_),
    .COUT(_030_),
    .SUM(_031_));
 sky130_fd_sc_hd__ha_1 _311_ (.A(net38),
    .B(_032_),
    .COUT(_033_),
    .SUM(_034_));
 sky130_fd_sc_hd__ha_1 _312_ (.A(net37),
    .B(_035_),
    .COUT(_036_),
    .SUM(_037_));
 sky130_fd_sc_hd__ha_1 _313_ (.A(_026_),
    .B(net29),
    .COUT(_038_),
    .SUM(_039_));
 sky130_fd_sc_hd__ha_1 _314_ (.A(_040_),
    .B(_041_),
    .COUT(_042_),
    .SUM(_043_));
 sky130_fd_sc_hd__ha_1 _315_ (.A(_040_),
    .B(_041_),
    .COUT(_044_),
    .SUM(_164_));
 sky130_fd_sc_hd__ha_1 _316_ (.A(_045_),
    .B(_046_),
    .COUT(_047_),
    .SUM(_048_));
 sky130_fd_sc_hd__ha_1 _317_ (.A(_045_),
    .B(_046_),
    .COUT(_049_),
    .SUM(_165_));
 sky130_fd_sc_hd__ha_1 _318_ (.A(net37),
    .B(_014_),
    .COUT(_050_),
    .SUM(_051_));
 sky130_fd_sc_hd__ha_1 _319_ (.A(net38),
    .B(_014_),
    .COUT(_052_),
    .SUM(_053_));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_0__f_clk (.A(clknet_0_clk),
    .X(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_1__f_clk (.A(clknet_0_clk),
    .X(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkinv_2 clkload0 (.A(clknet_1_0__leaf_clk));
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
 sky130_fd_sc_hd__clkdlybuf4s50_1 input3 (.A(cfg_max_postpone[1]),
    .X(net3));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input30 (.A(cfg_urgent_threshold[1]),
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
 sky130_fd_sc_hd__buf_4 place44 (.A(_078_),
    .X(net44));
 sky130_fd_sc_hd__buf_4 place45 (.A(_062_),
    .X(net45));
 sky130_fd_sc_hd__buf_4 place46 (.A(net35),
    .X(net46));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[0]$_DFFE_PN0P_  (.D(_054_),
    .Q(net36),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[1]$_DFFE_PN0P_  (.D(_055_),
    .Q(net37),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[2]$_DFFE_PN0P_  (.D(_056_),
    .Q(net38),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_pending_cnt[3]$_DFFE_PN0P_  (.D(_057_),
    .Q(net39),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \ref_starve_flag$_DFF_PN0_  (.D(starve_detect),
    .Q(net41),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[0]$_DFF_PN0_  (.D(_001_),
    .Q(\refi_ctr[0] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[10]$_DFF_PN0_  (.D(_002_),
    .Q(\refi_ctr[10] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[11]$_DFF_PN0_  (.D(_003_),
    .Q(\refi_ctr[11] ),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[12]$_DFF_PN0_  (.D(_004_),
    .Q(\refi_ctr[12] ),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[1]$_DFF_PN0_  (.D(_005_),
    .Q(\refi_ctr[1] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[2]$_DFF_PN0_  (.D(_006_),
    .Q(\refi_ctr[2] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[3]$_DFF_PN0_  (.D(_007_),
    .Q(\refi_ctr[3] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[4]$_DFF_PN0_  (.D(_008_),
    .Q(\refi_ctr[4] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[5]$_DFF_PN0_  (.D(_009_),
    .Q(\refi_ctr[5] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[6]$_DFF_PN0_  (.D(_010_),
    .Q(\refi_ctr[6] ),
    .RESET_B(net46),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[7]$_DFF_PN0_  (.D(_011_),
    .Q(\refi_ctr[7] ),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[8]$_DFF_PN0_  (.D(_012_),
    .Q(\refi_ctr[8] ),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_ctr[9]$_DFF_PN0_  (.D(_013_),
    .Q(\refi_ctr[9] ),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \refi_tick$_DFF_PN0_  (.D(_000_),
    .Q(refi_tick),
    .RESET_B(net46),
    .CLK(clknet_1_1__leaf_clk));
endmodule
