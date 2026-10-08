module calibration (cal_done,
    cal_fail,
    clk,
    init_done,
    rst_n,
    zqcs_ack,
    zqcs_req);
 output cal_done;
 output cal_fail;
 input clk;
 input init_done;
 input rst_n;
 input zqcs_ack;
 output zqcs_req;

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
 wire net4;
 wire net1;
 wire net2;
 wire net3;
 wire \zqcs_ctr[0] ;
 wire \zqcs_ctr[10] ;
 wire \zqcs_ctr[11] ;
 wire \zqcs_ctr[12] ;
 wire \zqcs_ctr[13] ;
 wire \zqcs_ctr[14] ;
 wire \zqcs_ctr[15] ;
 wire \zqcs_ctr[16] ;
 wire \zqcs_ctr[1] ;
 wire \zqcs_ctr[2] ;
 wire \zqcs_ctr[3] ;
 wire \zqcs_ctr[4] ;
 wire \zqcs_ctr[5] ;
 wire \zqcs_ctr[6] ;
 wire \zqcs_ctr[7] ;
 wire \zqcs_ctr[8] ;
 wire \zqcs_ctr[9] ;
 wire zqcs_pending;
 wire net5;
 wire net8;
 wire net7;
 wire clknet_0_clk;
 wire clknet_1_0__leaf_clk;
 wire clknet_1_1__leaf_clk;

 sky130_fd_sc_hd__nor4_1 _074_ (.A(\zqcs_ctr[8] ),
    .B(\zqcs_ctr[9] ),
    .C(\zqcs_ctr[10] ),
    .D(\zqcs_ctr[11] ),
    .Y(_033_));
 sky130_fd_sc_hd__nor3_1 _075_ (.A(\zqcs_ctr[12] ),
    .B(\zqcs_ctr[13] ),
    .C(\zqcs_ctr[14] ),
    .Y(_034_));
 sky130_fd_sc_hd__nor4b_1 _076_ (.A(\zqcs_ctr[2] ),
    .B(\zqcs_ctr[3] ),
    .C(\zqcs_ctr[4] ),
    .D_N(_019_),
    .Y(_035_));
 sky130_fd_sc_hd__nor4_1 _077_ (.A(\zqcs_ctr[5] ),
    .B(\zqcs_ctr[6] ),
    .C(\zqcs_ctr[7] ),
    .D(\zqcs_ctr[15] ),
    .Y(_036_));
 sky130_fd_sc_hd__nand4_1 _078_ (.A(_033_),
    .B(_034_),
    .C(_035_),
    .D(_036_),
    .Y(_037_));
 sky130_fd_sc_hd__o21ai_0 _079_ (.A1(\zqcs_ctr[16] ),
    .A2(_037_),
    .B1(net4),
    .Y(_038_));
 sky130_fd_sc_hd__nor2_1 _081_ (.A(\zqcs_ctr[0] ),
    .B(net7),
    .Y(_000_));
 sky130_fd_sc_hd__nor2_1 _082_ (.A(_020_),
    .B(net7),
    .Y(_008_));
 sky130_fd_sc_hd__xnor2_1 _083_ (.A(\zqcs_ctr[2] ),
    .B(_019_),
    .Y(_040_));
 sky130_fd_sc_hd__nor2_1 _084_ (.A(net7),
    .B(_040_),
    .Y(_009_));
 sky130_fd_sc_hd__o31ai_1 _085_ (.A1(\zqcs_ctr[2] ),
    .A2(\zqcs_ctr[0] ),
    .A3(\zqcs_ctr[1] ),
    .B1(\zqcs_ctr[3] ),
    .Y(_041_));
 sky130_fd_sc_hd__nor2_1 _086_ (.A(\zqcs_ctr[2] ),
    .B(\zqcs_ctr[3] ),
    .Y(_042_));
 sky130_fd_sc_hd__nor2_1 _087_ (.A(\zqcs_ctr[0] ),
    .B(\zqcs_ctr[1] ),
    .Y(_043_));
 sky130_fd_sc_hd__nand2_1 _088_ (.A(_042_),
    .B(_043_),
    .Y(_044_));
 sky130_fd_sc_hd__a21oi_1 _089_ (.A1(_041_),
    .A2(_044_),
    .B1(net7),
    .Y(_010_));
 sky130_fd_sc_hd__nor3_1 _090_ (.A(\zqcs_ctr[2] ),
    .B(\zqcs_ctr[3] ),
    .C(\zqcs_ctr[4] ),
    .Y(_045_));
 sky130_fd_sc_hd__nand2_1 _091_ (.A(_019_),
    .B(_045_),
    .Y(_046_));
 sky130_fd_sc_hd__nand2_1 _092_ (.A(_019_),
    .B(_042_),
    .Y(_047_));
 sky130_fd_sc_hd__nand2_1 _093_ (.A(\zqcs_ctr[4] ),
    .B(_047_),
    .Y(_048_));
 sky130_fd_sc_hd__a21oi_1 _094_ (.A1(_046_),
    .A2(_048_),
    .B1(net7),
    .Y(_011_));
 sky130_fd_sc_hd__nand2_1 _095_ (.A(_045_),
    .B(_043_),
    .Y(_049_));
 sky130_fd_sc_hd__xor2_1 _096_ (.A(\zqcs_ctr[5] ),
    .B(_049_),
    .X(_050_));
 sky130_fd_sc_hd__nor2_1 _097_ (.A(net7),
    .B(_050_),
    .Y(_012_));
 sky130_fd_sc_hd__o21ai_0 _098_ (.A1(\zqcs_ctr[5] ),
    .A2(_046_),
    .B1(\zqcs_ctr[6] ),
    .Y(_051_));
 sky130_fd_sc_hd__or3_1 _099_ (.A(\zqcs_ctr[5] ),
    .B(\zqcs_ctr[6] ),
    .C(_046_),
    .X(_052_));
 sky130_fd_sc_hd__a21oi_1 _100_ (.A1(_051_),
    .A2(_052_),
    .B1(net7),
    .Y(_013_));
 sky130_fd_sc_hd__o31ai_1 _101_ (.A1(\zqcs_ctr[5] ),
    .A2(\zqcs_ctr[6] ),
    .A3(_049_),
    .B1(\zqcs_ctr[7] ),
    .Y(_053_));
 sky130_fd_sc_hd__nor3_1 _102_ (.A(\zqcs_ctr[5] ),
    .B(\zqcs_ctr[6] ),
    .C(\zqcs_ctr[7] ),
    .Y(_054_));
 sky130_fd_sc_hd__nand3_1 _103_ (.A(_045_),
    .B(_054_),
    .C(_043_),
    .Y(_055_));
 sky130_fd_sc_hd__a21oi_1 _104_ (.A1(_053_),
    .A2(_055_),
    .B1(net7),
    .Y(_014_));
 sky130_fd_sc_hd__nand2_1 _105_ (.A(_035_),
    .B(_054_),
    .Y(_056_));
 sky130_fd_sc_hd__xor2_1 _106_ (.A(\zqcs_ctr[8] ),
    .B(_056_),
    .X(_057_));
 sky130_fd_sc_hd__nor2_1 _107_ (.A(net7),
    .B(_057_),
    .Y(_015_));
 sky130_fd_sc_hd__nand4b_1 _108_ (.A_N(\zqcs_ctr[8] ),
    .B(_045_),
    .C(_054_),
    .D(_043_),
    .Y(_058_));
 sky130_fd_sc_hd__xor2_1 _109_ (.A(\zqcs_ctr[9] ),
    .B(_058_),
    .X(_059_));
 sky130_fd_sc_hd__nor2_1 _110_ (.A(net7),
    .B(_059_),
    .Y(_016_));
 sky130_fd_sc_hd__nor2_1 _112_ (.A(\zqcs_ctr[8] ),
    .B(\zqcs_ctr[9] ),
    .Y(_061_));
 sky130_fd_sc_hd__nand3_1 _113_ (.A(_061_),
    .B(_035_),
    .C(_054_),
    .Y(_062_));
 sky130_fd_sc_hd__xnor2_1 _114_ (.A(\zqcs_ctr[10] ),
    .B(_062_),
    .Y(_063_));
 sky130_fd_sc_hd__and2_1 _115_ (.A(net4),
    .B(_063_),
    .X(_001_));
 sky130_fd_sc_hd__nor3_1 _116_ (.A(\zqcs_ctr[8] ),
    .B(\zqcs_ctr[9] ),
    .C(\zqcs_ctr[10] ),
    .Y(_064_));
 sky130_fd_sc_hd__nand4_1 _117_ (.A(_064_),
    .B(_045_),
    .C(_054_),
    .D(_043_),
    .Y(_065_));
 sky130_fd_sc_hd__xor2_1 _118_ (.A(\zqcs_ctr[11] ),
    .B(_065_),
    .X(_066_));
 sky130_fd_sc_hd__nor2_1 _119_ (.A(net7),
    .B(_066_),
    .Y(_002_));
 sky130_fd_sc_hd__nand3_1 _120_ (.A(_033_),
    .B(_035_),
    .C(_054_),
    .Y(_067_));
 sky130_fd_sc_hd__xnor2_1 _121_ (.A(\zqcs_ctr[12] ),
    .B(_067_),
    .Y(_068_));
 sky130_fd_sc_hd__and2_1 _122_ (.A(net4),
    .B(_068_),
    .X(_003_));
 sky130_fd_sc_hd__nor2_1 _123_ (.A(\zqcs_ctr[16] ),
    .B(_037_),
    .Y(_069_));
 sky130_fd_sc_hd__or4_4 _124_ (.A(\zqcs_ctr[8] ),
    .B(\zqcs_ctr[9] ),
    .C(\zqcs_ctr[10] ),
    .D(\zqcs_ctr[11] ),
    .X(_070_));
 sky130_fd_sc_hd__nor4_1 _125_ (.A(\zqcs_ctr[12] ),
    .B(\zqcs_ctr[13] ),
    .C(_070_),
    .D(_055_),
    .Y(_071_));
 sky130_fd_sc_hd__o31a_2 _126_ (.A1(\zqcs_ctr[12] ),
    .A2(_070_),
    .A3(_055_),
    .B1(\zqcs_ctr[13] ),
    .X(_072_));
 sky130_fd_sc_hd__o31a_1 _127_ (.A1(_069_),
    .A2(_071_),
    .A3(_072_),
    .B1(net4),
    .X(_004_));
 sky130_fd_sc_hd__or3_1 _128_ (.A(\zqcs_ctr[12] ),
    .B(\zqcs_ctr[13] ),
    .C(_070_),
    .X(_023_));
 sky130_fd_sc_hd__o21ai_0 _129_ (.A1(_023_),
    .A2(_056_),
    .B1(\zqcs_ctr[14] ),
    .Y(_024_));
 sky130_fd_sc_hd__or3_1 _130_ (.A(\zqcs_ctr[14] ),
    .B(_023_),
    .C(_056_),
    .X(_025_));
 sky130_fd_sc_hd__a21boi_1 _131_ (.A1(_024_),
    .A2(_025_),
    .B1_N(net4),
    .Y(_005_));
 sky130_fd_sc_hd__nand3_1 _132_ (.A(_033_),
    .B(_034_),
    .C(_036_),
    .Y(_026_));
 sky130_fd_sc_hd__nor2b_1 _133_ (.A(\zqcs_ctr[16] ),
    .B_N(_019_),
    .Y(_027_));
 sky130_fd_sc_hd__inv_1 _134_ (.A(\zqcs_ctr[4] ),
    .Y(_028_));
 sky130_fd_sc_hd__o2111ai_1 _135_ (.A1(_043_),
    .A2(_027_),
    .B1(net4),
    .C1(_028_),
    .D1(_042_),
    .Y(_029_));
 sky130_fd_sc_hd__o311ai_0 _136_ (.A1(\zqcs_ctr[14] ),
    .A2(_023_),
    .A3(_055_),
    .B1(\zqcs_ctr[15] ),
    .C1(net4),
    .Y(_030_));
 sky130_fd_sc_hd__o21ai_0 _137_ (.A1(_026_),
    .A2(_029_),
    .B1(_030_),
    .Y(_006_));
 sky130_fd_sc_hd__and2_1 _138_ (.A(\zqcs_ctr[16] ),
    .B(_037_),
    .X(_031_));
 sky130_fd_sc_hd__o21a_1 _139_ (.A1(_069_),
    .A2(_031_),
    .B1(net4),
    .X(_007_));
 sky130_fd_sc_hd__inv_1 _140_ (.A(\zqcs_ctr[0] ),
    .Y(_017_));
 sky130_fd_sc_hd__inv_1 _141_ (.A(\zqcs_ctr[1] ),
    .Y(_018_));
 sky130_fd_sc_hd__or2_2 _142_ (.A(net4),
    .B(net1),
    .X(_021_));
 sky130_fd_sc_hd__inv_1 _143_ (.A(net3),
    .Y(_032_));
 sky130_fd_sc_hd__o211a_1 _144_ (.A1(zqcs_pending),
    .A2(_069_),
    .B1(net4),
    .C1(_032_),
    .X(_022_));
 sky130_fd_sc_hd__and2_1 _145_ (.A(net4),
    .B(zqcs_pending),
    .X(net5));
 sky130_fd_sc_hd__ha_1 _146_ (.A(_017_),
    .B(_018_),
    .COUT(_019_),
    .SUM(_020_));
 sky130_fd_sc_hd__conb_1 _148__1 (.LO(cal_fail));
 sky130_fd_sc_hd__dfrtp_1 \cal_done$_DFFE_PN0P_  (.D(_021_),
    .Q(net4),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_0__f_clk (.A(clknet_0_clk),
    .X(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_8 clkbuf_1_1__f_clk (.A(clknet_0_clk),
    .X(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload0 (.A(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input2 (.A(init_done),
    .X(net1));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input3 (.A(rst_n),
    .X(net2));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input4 (.A(zqcs_ack),
    .X(net3));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output5 (.A(net4),
    .X(cal_done));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output6 (.A(net5),
    .X(zqcs_req));
 sky130_fd_sc_hd__buf_4 place8 (.A(_038_),
    .X(net7));
 sky130_fd_sc_hd__buf_4 place9 (.A(net2),
    .X(net8));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[0]$_DFF_PN0_  (.D(_000_),
    .Q(\zqcs_ctr[0] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[10]$_DFF_PN0_  (.D(_001_),
    .Q(\zqcs_ctr[10] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[11]$_DFF_PN0_  (.D(_002_),
    .Q(\zqcs_ctr[11] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[12]$_DFF_PN0_  (.D(_003_),
    .Q(\zqcs_ctr[12] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[13]$_DFF_PN0_  (.D(_004_),
    .Q(\zqcs_ctr[13] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[14]$_DFF_PN0_  (.D(_005_),
    .Q(\zqcs_ctr[14] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[15]$_DFF_PN0_  (.D(_006_),
    .Q(\zqcs_ctr[15] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[16]$_DFF_PN0_  (.D(_007_),
    .Q(\zqcs_ctr[16] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[1]$_DFF_PN0_  (.D(_008_),
    .Q(\zqcs_ctr[1] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[2]$_DFF_PN0_  (.D(_009_),
    .Q(\zqcs_ctr[2] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[3]$_DFF_PN0_  (.D(_010_),
    .Q(\zqcs_ctr[3] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[4]$_DFF_PN0_  (.D(_011_),
    .Q(\zqcs_ctr[4] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[5]$_DFF_PN0_  (.D(_012_),
    .Q(\zqcs_ctr[5] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[6]$_DFF_PN0_  (.D(_013_),
    .Q(\zqcs_ctr[6] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[7]$_DFF_PN0_  (.D(_014_),
    .Q(\zqcs_ctr[7] ),
    .RESET_B(net8),
    .CLK(clknet_1_0__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[8]$_DFF_PN0_  (.D(_015_),
    .Q(\zqcs_ctr[8] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_ctr[9]$_DFF_PN0_  (.D(_016_),
    .Q(\zqcs_ctr[9] ),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
 sky130_fd_sc_hd__dfrtp_1 \zqcs_pending$_DFFE_PN0P_  (.D(_022_),
    .Q(zqcs_pending),
    .RESET_B(net8),
    .CLK(clknet_1_1__leaf_clk));
endmodule
