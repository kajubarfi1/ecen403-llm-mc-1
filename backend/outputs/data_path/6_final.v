module data_path (clk,
    cmd_rd_valid,
    cmd_wr_valid,
    ddr_dq_oe,
    ddr_dqs_i,
    ddr_dqs_o,
    ddr_dqs_oe,
    rd_rsp_valid,
    rst_n,
    wr_data_ready,
    wr_data_valid,
    cfg_CL_nCK,
    cfg_CWL_nCK,
    cmd_aux,
    ddr_dm_o,
    ddr_dq_i,
    ddr_dq_o,
    rd_rsp_aux,
    rd_rsp_data,
    wr_data,
    wr_mask);
 input clk;
 input cmd_rd_valid;
 input cmd_wr_valid;
 output ddr_dq_oe;
 input ddr_dqs_i;
 output ddr_dqs_o;
 output ddr_dqs_oe;
 output rd_rsp_valid;
 input rst_n;
 output wr_data_ready;
 input wr_data_valid;
 input [7:0] cfg_CL_nCK;
 input [7:0] cfg_CWL_nCK;
 input [3:0] cmd_aux;
 output [1:0] ddr_dm_o;
 input [15:0] ddr_dq_i;
 output [15:0] ddr_dq_o;
 output [3:0] rd_rsp_aux;
 output [31:0] rd_rsp_data;
 input [31:0] wr_data;
 input [3:0] wr_mask;

 wire _0000_;
 wire _0001_;
 wire _0002_;
 wire _0003_;
 wire _0004_;
 wire _0005_;
 wire _0006_;
 wire _0007_;
 wire _0008_;
 wire _0009_;
 wire _0010_;
 wire _0011_;
 wire _0012_;
 wire _0013_;
 wire _0014_;
 wire _0015_;
 wire _0016_;
 wire _0017_;
 wire _0018_;
 wire _0019_;
 wire _0020_;
 wire _0021_;
 wire _0022_;
 wire _0023_;
 wire _0024_;
 wire _0025_;
 wire _0026_;
 wire _0027_;
 wire _0028_;
 wire _0029_;
 wire _0030_;
 wire _0031_;
 wire _0032_;
 wire _0033_;
 wire _0034_;
 wire _0035_;
 wire _0036_;
 wire _0037_;
 wire _0038_;
 wire _0039_;
 wire _0040_;
 wire _0041_;
 wire _0042_;
 wire _0043_;
 wire _0044_;
 wire _0045_;
 wire _0046_;
 wire _0047_;
 wire _0048_;
 wire _0049_;
 wire _0050_;
 wire _0051_;
 wire _0052_;
 wire _0053_;
 wire _0054_;
 wire _0055_;
 wire _0056_;
 wire _0057_;
 wire _0058_;
 wire _0059_;
 wire _0060_;
 wire _0062_;
 wire _0063_;
 wire _0064_;
 wire _0065_;
 wire _0066_;
 wire _0067_;
 wire _0068_;
 wire _0069_;
 wire _0070_;
 wire _0071_;
 wire _0072_;
 wire _0073_;
 wire _0074_;
 wire _0076_;
 wire _0077_;
 wire _0078_;
 wire _0079_;
 wire _0080_;
 wire _0081_;
 wire _0082_;
 wire _0083_;
 wire _0084_;
 wire _0085_;
 wire _0086_;
 wire _0087_;
 wire _0088_;
 wire _0089_;
 wire _0090_;
 wire _0091_;
 wire _0092_;
 wire _0093_;
 wire _0094_;
 wire _0095_;
 wire _0096_;
 wire _0097_;
 wire _0098_;
 wire _0099_;
 wire _0100_;
 wire _0101_;
 wire _0102_;
 wire _0103_;
 wire _0104_;
 wire _0105_;
 wire _0106_;
 wire _0107_;
 wire _0108_;
 wire _0109_;
 wire _0110_;
 wire _0111_;
 wire _0112_;
 wire _0113_;
 wire _0114_;
 wire _0115_;
 wire _0116_;
 wire _0117_;
 wire _0118_;
 wire _0119_;
 wire _0120_;
 wire _0121_;
 wire _0122_;
 wire _0123_;
 wire _0124_;
 wire _0125_;
 wire _0126_;
 wire _0127_;
 wire _0128_;
 wire _0129_;
 wire _0130_;
 wire _0131_;
 wire _0132_;
 wire _0133_;
 wire _0134_;
 wire _0135_;
 wire _0136_;
 wire _0137_;
 wire _0138_;
 wire _0139_;
 wire _0140_;
 wire _0141_;
 wire _0142_;
 wire _0143_;
 wire _0144_;
 wire _0145_;
 wire _0146_;
 wire _0147_;
 wire _0148_;
 wire _0149_;
 wire _0150_;
 wire _0151_;
 wire _0152_;
 wire _0153_;
 wire _0154_;
 wire _0155_;
 wire _0156_;
 wire _0157_;
 wire _0158_;
 wire _0159_;
 wire _0160_;
 wire _0161_;
 wire _0162_;
 wire _0163_;
 wire _0164_;
 wire _0165_;
 wire _0166_;
 wire _0167_;
 wire _0168_;
 wire _0169_;
 wire _0170_;
 wire _0171_;
 wire _0172_;
 wire _0173_;
 wire _0174_;
 wire _0175_;
 wire _0176_;
 wire _0177_;
 wire _0178_;
 wire _0179_;
 wire _0180_;
 wire _0181_;
 wire _0182_;
 wire _0183_;
 wire _0184_;
 wire _0185_;
 wire _0186_;
 wire _0187_;
 wire _0188_;
 wire _0189_;
 wire _0190_;
 wire _0191_;
 wire _0192_;
 wire _0193_;
 wire _0194_;
 wire _0195_;
 wire _0196_;
 wire _0197_;
 wire _0198_;
 wire _0199_;
 wire _0200_;
 wire _0201_;
 wire _0203_;
 wire _0204_;
 wire _0205_;
 wire _0206_;
 wire _0207_;
 wire _0208_;
 wire _0209_;
 wire _0210_;
 wire _0211_;
 wire _0212_;
 wire _0213_;
 wire _0214_;
 wire _0215_;
 wire _0216_;
 wire _0217_;
 wire _0218_;
 wire _0220_;
 wire _0221_;
 wire _0222_;
 wire _0226_;
 wire _0227_;
 wire _0228_;
 wire _0229_;
 wire _0230_;
 wire _0231_;
 wire _0232_;
 wire _0233_;
 wire _0234_;
 wire _0235_;
 wire _0236_;
 wire _0237_;
 wire _0238_;
 wire _0239_;
 wire _0240_;
 wire _0241_;
 wire _0242_;
 wire _0243_;
 wire _0244_;
 wire _0245_;
 wire _0246_;
 wire _0247_;
 wire _0248_;
 wire net97;
 wire net96;
 wire _0252_;
 wire _0253_;
 wire _0255_;
 wire _0256_;
 wire _0257_;
 wire _0259_;
 wire _0260_;
 wire _0261_;
 wire _0262_;
 wire _0263_;
 wire _0264_;
 wire _0265_;
 wire _0266_;
 wire _0267_;
 wire _0268_;
 wire _0269_;
 wire _0272_;
 wire _0273_;
 wire _0274_;
 wire _0275_;
 wire _0276_;
 wire _0277_;
 wire _0278_;
 wire _0281_;
 wire _0286_;
 wire _0287_;
 wire _0288_;
 wire _0289_;
 wire _0290_;
 wire _0291_;
 wire _0292_;
 wire _0293_;
 wire _0294_;
 wire _0295_;
 wire _0296_;
 wire _0297_;
 wire _0298_;
 wire _0299_;
 wire _0300_;
 wire _0301_;
 wire _0302_;
 wire _0303_;
 wire _0304_;
 wire _0305_;
 wire _0306_;
 wire _0307_;
 wire _0308_;
 wire _0309_;
 wire _0310_;
 wire _0311_;
 wire _0312_;
 wire _0313_;
 wire _0314_;
 wire _0315_;
 wire _0316_;
 wire _0317_;
 wire _0318_;
 wire _0319_;
 wire _0320_;
 wire _0321_;
 wire _0322_;
 wire _0323_;
 wire _0324_;
 wire _0325_;
 wire _0326_;
 wire _0327_;
 wire _0328_;
 wire _0329_;
 wire _0330_;
 wire _0331_;
 wire _0332_;
 wire _0333_;
 wire _0334_;
 wire _0335_;
 wire _0336_;
 wire _0337_;
 wire _0338_;
 wire _0339_;
 wire _0340_;
 wire _0341_;
 wire _0342_;
 wire _0343_;
 wire _0344_;
 wire _0345_;
 wire _0346_;
 wire _0347_;
 wire _0351_;
 wire _0352_;
 wire _0353_;
 wire _0354_;
 wire _0355_;
 wire _0357_;
 wire _0358_;
 wire _0360_;
 wire _0361_;
 wire _0362_;
 wire _0363_;
 wire _0364_;
 wire _0365_;
 wire _0367_;
 wire _0368_;
 wire _0369_;
 wire _0370_;
 wire _0371_;
 wire _0372_;
 wire _0373_;
 wire _0374_;
 wire _0375_;
 wire _0376_;
 wire _0380_;
 wire _0385_;
 wire _0388_;
 wire _0390_;
 wire _0391_;
 wire _0392_;
 wire _0395_;
 wire _0396_;
 wire _0397_;
 wire _0398_;
 wire _0399_;
 wire _0402_;
 wire _0403_;
 wire _0404_;
 wire _0405_;
 wire _0406_;
 wire _0407_;
 wire _0408_;
 wire _0409_;
 wire _0410_;
 wire _0411_;
 wire _0412_;
 wire _0413_;
 wire _0414_;
 wire _0415_;
 wire _0416_;
 wire _0417_;
 wire _0418_;
 wire _0419_;
 wire _0420_;
 wire _0421_;
 wire _0423_;
 wire _0424_;
 wire _0427_;
 wire _0428_;
 wire _0430_;
 wire _0431_;
 wire _0432_;
 wire _0433_;
 wire _0434_;
 wire _0435_;
 wire _0436_;
 wire _0437_;
 wire _0438_;
 wire _0441_;
 wire _0442_;
 wire _0443_;
 wire _0444_;
 wire _0445_;
 wire _0446_;
 wire _0448_;
 wire _0449_;
 wire _0452_;
 wire _0453_;
 wire _0454_;
 wire _0455_;
 wire _0456_;
 wire _0457_;
 wire _0458_;
 wire _0459_;
 wire _0460_;
 wire _0463_;
 wire _0464_;
 wire _0465_;
 wire _0466_;
 wire _0467_;
 wire _0468_;
 wire _0469_;
 wire _0470_;
 wire _0471_;
 wire _0472_;
 wire _0473_;
 wire _0474_;
 wire _0475_;
 wire _0476_;
 wire _0477_;
 wire _0478_;
 wire _0479_;
 wire _0480_;
 wire _0481_;
 wire _0482_;
 wire _0484_;
 wire _0485_;
 wire _0488_;
 wire _0489_;
 wire _0491_;
 wire _0492_;
 wire _0493_;
 wire _0494_;
 wire _0495_;
 wire _0496_;
 wire _0497_;
 wire _0498_;
 wire _0499_;
 wire _0502_;
 wire _0503_;
 wire _0504_;
 wire _0505_;
 wire _0506_;
 wire _0507_;
 wire _0509_;
 wire _0510_;
 wire _0513_;
 wire _0514_;
 wire _0515_;
 wire _0516_;
 wire _0517_;
 wire _0518_;
 wire _0519_;
 wire _0520_;
 wire _0521_;
 wire _0524_;
 wire _0525_;
 wire _0526_;
 wire _0527_;
 wire _0528_;
 wire _0529_;
 wire _0530_;
 wire _0531_;
 wire _0532_;
 wire _0533_;
 wire _0534_;
 wire _0535_;
 wire _0536_;
 wire _0537_;
 wire _0538_;
 wire _0539_;
 wire _0540_;
 wire _0541_;
 wire _0542_;
 wire _0543_;
 wire _0545_;
 wire _0546_;
 wire _0549_;
 wire _0550_;
 wire _0552_;
 wire _0553_;
 wire _0554_;
 wire _0555_;
 wire _0556_;
 wire _0557_;
 wire _0558_;
 wire _0559_;
 wire _0560_;
 wire _0561_;
 wire _0562_;
 wire _0563_;
 wire _0564_;
 wire _0565_;
 wire _0566_;
 wire _0567_;
 wire _0568_;
 wire _0569_;
 wire _0570_;
 wire _0571_;
 wire _0572_;
 wire _0573_;
 wire _0574_;
 wire _0575_;
 wire _0576_;
 wire _0577_;
 wire _0578_;
 wire _0579_;
 wire _0580_;
 wire _0581_;
 wire _0583_;
 wire _0584_;
 wire _0585_;
 wire _0586_;
 wire _0587_;
 wire _0588_;
 wire _0589_;
 wire _0590_;
 wire _0591_;
 wire _0592_;
 wire _0593_;
 wire _0594_;
 wire _0595_;
 wire _0596_;
 wire _0597_;
 wire _0598_;
 wire _0599_;
 wire _0600_;
 wire _0601_;
 wire _0602_;
 wire _0603_;
 wire _0604_;
 wire _0605_;
 wire _0606_;
 wire _0607_;
 wire _0608_;
 wire _0609_;
 wire _0610_;
 wire _0611_;
 wire _0612_;
 wire _0613_;
 wire _0614_;
 wire _0615_;
 wire _0616_;
 wire _0617_;
 wire _0618_;
 wire _0619_;
 wire _0620_;
 wire _0621_;
 wire _0622_;
 wire _0623_;
 wire _0624_;
 wire _0625_;
 wire _0626_;
 wire _0627_;
 wire _0628_;
 wire _0629_;
 wire _0630_;
 wire _0631_;
 wire _0632_;
 wire _0633_;
 wire _0634_;
 wire _0635_;
 wire _0636_;
 wire _0637_;
 wire _0638_;
 wire _0639_;
 wire _0640_;
 wire _0641_;
 wire _0642_;
 wire _0643_;
 wire _0644_;
 wire _0645_;
 wire _0646_;
 wire _0647_;
 wire _0648_;
 wire _0649_;
 wire _0650_;
 wire _0651_;
 wire _0652_;
 wire _0653_;
 wire _0654_;
 wire _0655_;
 wire _0656_;
 wire _0657_;
 wire _0661_;
 wire _0666_;
 wire _0669_;
 wire _0670_;
 wire _0671_;
 wire _0672_;
 wire _0673_;
 wire _0674_;
 wire _0677_;
 wire _0678_;
 wire _0679_;
 wire _0680_;
 wire _0681_;
 wire _0682_;
 wire _0683_;
 wire _0684_;
 wire _0685_;
 wire _0686_;
 wire _0687_;
 wire _0688_;
 wire _0689_;
 wire _0690_;
 wire _0691_;
 wire _0692_;
 wire _0693_;
 wire _0694_;
 wire _0697_;
 wire _0698_;
 wire _0700_;
 wire _0701_;
 wire _0702_;
 wire _0703_;
 wire _0704_;
 wire _0705_;
 wire _0706_;
 wire _0709_;
 wire _0710_;
 wire _0711_;
 wire _0712_;
 wire _0713_;
 wire _0715_;
 wire _0718_;
 wire _0719_;
 wire _0720_;
 wire _0721_;
 wire _0722_;
 wire _0723_;
 wire _0724_;
 wire _0727_;
 wire _0728_;
 wire _0729_;
 wire _0730_;
 wire _0731_;
 wire _0732_;
 wire _0733_;
 wire _0734_;
 wire _0735_;
 wire _0736_;
 wire _0737_;
 wire _0738_;
 wire _0739_;
 wire _0740_;
 wire _0741_;
 wire _0742_;
 wire _0743_;
 wire _0744_;
 wire _0747_;
 wire _0748_;
 wire _0750_;
 wire _0751_;
 wire _0752_;
 wire _0753_;
 wire _0754_;
 wire _0755_;
 wire _0756_;
 wire _0759_;
 wire _0760_;
 wire _0761_;
 wire _0762_;
 wire _0763_;
 wire _0765_;
 wire _0768_;
 wire _0769_;
 wire _0770_;
 wire _0771_;
 wire _0772_;
 wire _0773_;
 wire _0774_;
 wire _0777_;
 wire _0778_;
 wire _0779_;
 wire _0780_;
 wire _0781_;
 wire _0782_;
 wire _0783_;
 wire _0784_;
 wire _0785_;
 wire _0786_;
 wire _0787_;
 wire _0788_;
 wire _0789_;
 wire _0790_;
 wire _0791_;
 wire _0792_;
 wire _0793_;
 wire _0794_;
 wire _0797_;
 wire _0798_;
 wire _0800_;
 wire _0801_;
 wire _0802_;
 wire _0803_;
 wire _0804_;
 wire _0805_;
 wire _0806_;
 wire _0807_;
 wire _0808_;
 wire _0809_;
 wire _0810_;
 wire _0811_;
 wire _0812_;
 wire _0813_;
 wire _0814_;
 wire _0815_;
 wire _0816_;
 wire _0817_;
 wire _0818_;
 wire _0819_;
 wire _0820_;
 wire _0821_;
 wire _0822_;
 wire _0823_;
 wire _0824_;
 wire _0825_;
 wire _0826_;
 wire _0827_;
 wire _0828_;
 wire _0829_;
 wire _0830_;
 wire _0831_;
 wire _0832_;
 wire _0833_;
 wire _0834_;
 wire _0835_;
 wire _0836_;
 wire _0837_;
 wire _0838_;
 wire _0839_;
 wire _0840_;
 wire _0841_;
 wire _0842_;
 wire _0843_;
 wire _0844_;
 wire _0845_;
 wire _0846_;
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
 wire net77;
 wire net78;
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
 wire \rd_aux_r[0] ;
 wire \rd_aux_r[1] ;
 wire \rd_aux_r[2] ;
 wire \rd_aux_r[3] ;
 wire \rd_burst_ctr[0] ;
 wire \rd_burst_ctr[1] ;
 wire rd_capture_valid;
 wire \rd_fifo[0][0] ;
 wire \rd_fifo[0][10] ;
 wire \rd_fifo[0][11] ;
 wire \rd_fifo[0][12] ;
 wire \rd_fifo[0][13] ;
 wire \rd_fifo[0][14] ;
 wire \rd_fifo[0][15] ;
 wire \rd_fifo[0][16] ;
 wire \rd_fifo[0][17] ;
 wire \rd_fifo[0][18] ;
 wire \rd_fifo[0][19] ;
 wire \rd_fifo[0][1] ;
 wire \rd_fifo[0][20] ;
 wire \rd_fifo[0][21] ;
 wire \rd_fifo[0][22] ;
 wire \rd_fifo[0][23] ;
 wire \rd_fifo[0][24] ;
 wire \rd_fifo[0][25] ;
 wire \rd_fifo[0][26] ;
 wire \rd_fifo[0][27] ;
 wire \rd_fifo[0][28] ;
 wire \rd_fifo[0][29] ;
 wire \rd_fifo[0][2] ;
 wire \rd_fifo[0][30] ;
 wire \rd_fifo[0][31] ;
 wire \rd_fifo[0][32] ;
 wire \rd_fifo[0][33] ;
 wire \rd_fifo[0][34] ;
 wire \rd_fifo[0][35] ;
 wire \rd_fifo[0][3] ;
 wire \rd_fifo[0][4] ;
 wire \rd_fifo[0][5] ;
 wire \rd_fifo[0][6] ;
 wire \rd_fifo[0][7] ;
 wire \rd_fifo[0][8] ;
 wire \rd_fifo[0][9] ;
 wire \rd_fifo[10][0] ;
 wire \rd_fifo[10][10] ;
 wire \rd_fifo[10][11] ;
 wire \rd_fifo[10][12] ;
 wire \rd_fifo[10][13] ;
 wire \rd_fifo[10][14] ;
 wire \rd_fifo[10][15] ;
 wire \rd_fifo[10][16] ;
 wire \rd_fifo[10][17] ;
 wire \rd_fifo[10][18] ;
 wire \rd_fifo[10][19] ;
 wire \rd_fifo[10][1] ;
 wire \rd_fifo[10][20] ;
 wire \rd_fifo[10][21] ;
 wire \rd_fifo[10][22] ;
 wire \rd_fifo[10][23] ;
 wire \rd_fifo[10][24] ;
 wire \rd_fifo[10][25] ;
 wire \rd_fifo[10][26] ;
 wire \rd_fifo[10][27] ;
 wire \rd_fifo[10][28] ;
 wire \rd_fifo[10][29] ;
 wire \rd_fifo[10][2] ;
 wire \rd_fifo[10][30] ;
 wire \rd_fifo[10][31] ;
 wire \rd_fifo[10][32] ;
 wire \rd_fifo[10][33] ;
 wire \rd_fifo[10][34] ;
 wire \rd_fifo[10][35] ;
 wire \rd_fifo[10][3] ;
 wire \rd_fifo[10][4] ;
 wire \rd_fifo[10][5] ;
 wire \rd_fifo[10][6] ;
 wire \rd_fifo[10][7] ;
 wire \rd_fifo[10][8] ;
 wire \rd_fifo[10][9] ;
 wire \rd_fifo[11][0] ;
 wire \rd_fifo[11][10] ;
 wire \rd_fifo[11][11] ;
 wire \rd_fifo[11][12] ;
 wire \rd_fifo[11][13] ;
 wire \rd_fifo[11][14] ;
 wire \rd_fifo[11][15] ;
 wire \rd_fifo[11][16] ;
 wire \rd_fifo[11][17] ;
 wire \rd_fifo[11][18] ;
 wire \rd_fifo[11][19] ;
 wire \rd_fifo[11][1] ;
 wire \rd_fifo[11][20] ;
 wire \rd_fifo[11][21] ;
 wire \rd_fifo[11][22] ;
 wire \rd_fifo[11][23] ;
 wire \rd_fifo[11][24] ;
 wire \rd_fifo[11][25] ;
 wire \rd_fifo[11][26] ;
 wire \rd_fifo[11][27] ;
 wire \rd_fifo[11][28] ;
 wire \rd_fifo[11][29] ;
 wire \rd_fifo[11][2] ;
 wire \rd_fifo[11][30] ;
 wire \rd_fifo[11][31] ;
 wire \rd_fifo[11][32] ;
 wire \rd_fifo[11][33] ;
 wire \rd_fifo[11][34] ;
 wire \rd_fifo[11][35] ;
 wire \rd_fifo[11][3] ;
 wire \rd_fifo[11][4] ;
 wire \rd_fifo[11][5] ;
 wire \rd_fifo[11][6] ;
 wire \rd_fifo[11][7] ;
 wire \rd_fifo[11][8] ;
 wire \rd_fifo[11][9] ;
 wire \rd_fifo[12][0] ;
 wire \rd_fifo[12][10] ;
 wire \rd_fifo[12][11] ;
 wire \rd_fifo[12][12] ;
 wire \rd_fifo[12][13] ;
 wire \rd_fifo[12][14] ;
 wire \rd_fifo[12][15] ;
 wire \rd_fifo[12][16] ;
 wire \rd_fifo[12][17] ;
 wire \rd_fifo[12][18] ;
 wire \rd_fifo[12][19] ;
 wire \rd_fifo[12][1] ;
 wire \rd_fifo[12][20] ;
 wire \rd_fifo[12][21] ;
 wire \rd_fifo[12][22] ;
 wire \rd_fifo[12][23] ;
 wire \rd_fifo[12][24] ;
 wire \rd_fifo[12][25] ;
 wire \rd_fifo[12][26] ;
 wire \rd_fifo[12][27] ;
 wire \rd_fifo[12][28] ;
 wire \rd_fifo[12][29] ;
 wire \rd_fifo[12][2] ;
 wire \rd_fifo[12][30] ;
 wire \rd_fifo[12][31] ;
 wire \rd_fifo[12][32] ;
 wire \rd_fifo[12][33] ;
 wire \rd_fifo[12][34] ;
 wire \rd_fifo[12][35] ;
 wire \rd_fifo[12][3] ;
 wire \rd_fifo[12][4] ;
 wire \rd_fifo[12][5] ;
 wire \rd_fifo[12][6] ;
 wire \rd_fifo[12][7] ;
 wire \rd_fifo[12][8] ;
 wire \rd_fifo[12][9] ;
 wire \rd_fifo[13][0] ;
 wire \rd_fifo[13][10] ;
 wire \rd_fifo[13][11] ;
 wire \rd_fifo[13][12] ;
 wire \rd_fifo[13][13] ;
 wire \rd_fifo[13][14] ;
 wire \rd_fifo[13][15] ;
 wire \rd_fifo[13][16] ;
 wire \rd_fifo[13][17] ;
 wire \rd_fifo[13][18] ;
 wire \rd_fifo[13][19] ;
 wire \rd_fifo[13][1] ;
 wire \rd_fifo[13][20] ;
 wire \rd_fifo[13][21] ;
 wire \rd_fifo[13][22] ;
 wire \rd_fifo[13][23] ;
 wire \rd_fifo[13][24] ;
 wire \rd_fifo[13][25] ;
 wire \rd_fifo[13][26] ;
 wire \rd_fifo[13][27] ;
 wire \rd_fifo[13][28] ;
 wire \rd_fifo[13][29] ;
 wire \rd_fifo[13][2] ;
 wire \rd_fifo[13][30] ;
 wire \rd_fifo[13][31] ;
 wire \rd_fifo[13][32] ;
 wire \rd_fifo[13][33] ;
 wire \rd_fifo[13][34] ;
 wire \rd_fifo[13][35] ;
 wire \rd_fifo[13][3] ;
 wire \rd_fifo[13][4] ;
 wire \rd_fifo[13][5] ;
 wire \rd_fifo[13][6] ;
 wire \rd_fifo[13][7] ;
 wire \rd_fifo[13][8] ;
 wire \rd_fifo[13][9] ;
 wire \rd_fifo[14][0] ;
 wire \rd_fifo[14][10] ;
 wire \rd_fifo[14][11] ;
 wire \rd_fifo[14][12] ;
 wire \rd_fifo[14][13] ;
 wire \rd_fifo[14][14] ;
 wire \rd_fifo[14][15] ;
 wire \rd_fifo[14][16] ;
 wire \rd_fifo[14][17] ;
 wire \rd_fifo[14][18] ;
 wire \rd_fifo[14][19] ;
 wire \rd_fifo[14][1] ;
 wire \rd_fifo[14][20] ;
 wire \rd_fifo[14][21] ;
 wire \rd_fifo[14][22] ;
 wire \rd_fifo[14][23] ;
 wire \rd_fifo[14][24] ;
 wire \rd_fifo[14][25] ;
 wire \rd_fifo[14][26] ;
 wire \rd_fifo[14][27] ;
 wire \rd_fifo[14][28] ;
 wire \rd_fifo[14][29] ;
 wire \rd_fifo[14][2] ;
 wire \rd_fifo[14][30] ;
 wire \rd_fifo[14][31] ;
 wire \rd_fifo[14][32] ;
 wire \rd_fifo[14][33] ;
 wire \rd_fifo[14][34] ;
 wire \rd_fifo[14][35] ;
 wire \rd_fifo[14][3] ;
 wire \rd_fifo[14][4] ;
 wire \rd_fifo[14][5] ;
 wire \rd_fifo[14][6] ;
 wire \rd_fifo[14][7] ;
 wire \rd_fifo[14][8] ;
 wire \rd_fifo[14][9] ;
 wire \rd_fifo[15][0] ;
 wire \rd_fifo[15][10] ;
 wire \rd_fifo[15][11] ;
 wire \rd_fifo[15][12] ;
 wire \rd_fifo[15][13] ;
 wire \rd_fifo[15][14] ;
 wire \rd_fifo[15][15] ;
 wire \rd_fifo[15][16] ;
 wire \rd_fifo[15][17] ;
 wire \rd_fifo[15][18] ;
 wire \rd_fifo[15][19] ;
 wire \rd_fifo[15][1] ;
 wire \rd_fifo[15][20] ;
 wire \rd_fifo[15][21] ;
 wire \rd_fifo[15][22] ;
 wire \rd_fifo[15][23] ;
 wire \rd_fifo[15][24] ;
 wire \rd_fifo[15][25] ;
 wire \rd_fifo[15][26] ;
 wire \rd_fifo[15][27] ;
 wire \rd_fifo[15][28] ;
 wire \rd_fifo[15][29] ;
 wire \rd_fifo[15][2] ;
 wire \rd_fifo[15][30] ;
 wire \rd_fifo[15][31] ;
 wire \rd_fifo[15][32] ;
 wire \rd_fifo[15][33] ;
 wire \rd_fifo[15][34] ;
 wire \rd_fifo[15][35] ;
 wire \rd_fifo[15][3] ;
 wire \rd_fifo[15][4] ;
 wire \rd_fifo[15][5] ;
 wire \rd_fifo[15][6] ;
 wire \rd_fifo[15][7] ;
 wire \rd_fifo[15][8] ;
 wire \rd_fifo[15][9] ;
 wire \rd_fifo[1][0] ;
 wire \rd_fifo[1][10] ;
 wire \rd_fifo[1][11] ;
 wire \rd_fifo[1][12] ;
 wire \rd_fifo[1][13] ;
 wire \rd_fifo[1][14] ;
 wire \rd_fifo[1][15] ;
 wire \rd_fifo[1][16] ;
 wire \rd_fifo[1][17] ;
 wire \rd_fifo[1][18] ;
 wire \rd_fifo[1][19] ;
 wire \rd_fifo[1][1] ;
 wire \rd_fifo[1][20] ;
 wire \rd_fifo[1][21] ;
 wire \rd_fifo[1][22] ;
 wire \rd_fifo[1][23] ;
 wire \rd_fifo[1][24] ;
 wire \rd_fifo[1][25] ;
 wire \rd_fifo[1][26] ;
 wire \rd_fifo[1][27] ;
 wire \rd_fifo[1][28] ;
 wire \rd_fifo[1][29] ;
 wire \rd_fifo[1][2] ;
 wire \rd_fifo[1][30] ;
 wire \rd_fifo[1][31] ;
 wire \rd_fifo[1][32] ;
 wire \rd_fifo[1][33] ;
 wire \rd_fifo[1][34] ;
 wire \rd_fifo[1][35] ;
 wire \rd_fifo[1][3] ;
 wire \rd_fifo[1][4] ;
 wire \rd_fifo[1][5] ;
 wire \rd_fifo[1][6] ;
 wire \rd_fifo[1][7] ;
 wire \rd_fifo[1][8] ;
 wire \rd_fifo[1][9] ;
 wire \rd_fifo[2][0] ;
 wire \rd_fifo[2][10] ;
 wire \rd_fifo[2][11] ;
 wire \rd_fifo[2][12] ;
 wire \rd_fifo[2][13] ;
 wire \rd_fifo[2][14] ;
 wire \rd_fifo[2][15] ;
 wire \rd_fifo[2][16] ;
 wire \rd_fifo[2][17] ;
 wire \rd_fifo[2][18] ;
 wire \rd_fifo[2][19] ;
 wire \rd_fifo[2][1] ;
 wire \rd_fifo[2][20] ;
 wire \rd_fifo[2][21] ;
 wire \rd_fifo[2][22] ;
 wire \rd_fifo[2][23] ;
 wire \rd_fifo[2][24] ;
 wire \rd_fifo[2][25] ;
 wire \rd_fifo[2][26] ;
 wire \rd_fifo[2][27] ;
 wire \rd_fifo[2][28] ;
 wire \rd_fifo[2][29] ;
 wire \rd_fifo[2][2] ;
 wire \rd_fifo[2][30] ;
 wire \rd_fifo[2][31] ;
 wire \rd_fifo[2][32] ;
 wire \rd_fifo[2][33] ;
 wire \rd_fifo[2][34] ;
 wire \rd_fifo[2][35] ;
 wire \rd_fifo[2][3] ;
 wire \rd_fifo[2][4] ;
 wire \rd_fifo[2][5] ;
 wire \rd_fifo[2][6] ;
 wire \rd_fifo[2][7] ;
 wire \rd_fifo[2][8] ;
 wire \rd_fifo[2][9] ;
 wire \rd_fifo[3][0] ;
 wire \rd_fifo[3][10] ;
 wire \rd_fifo[3][11] ;
 wire \rd_fifo[3][12] ;
 wire \rd_fifo[3][13] ;
 wire \rd_fifo[3][14] ;
 wire \rd_fifo[3][15] ;
 wire \rd_fifo[3][16] ;
 wire \rd_fifo[3][17] ;
 wire \rd_fifo[3][18] ;
 wire \rd_fifo[3][19] ;
 wire \rd_fifo[3][1] ;
 wire \rd_fifo[3][20] ;
 wire \rd_fifo[3][21] ;
 wire \rd_fifo[3][22] ;
 wire \rd_fifo[3][23] ;
 wire \rd_fifo[3][24] ;
 wire \rd_fifo[3][25] ;
 wire \rd_fifo[3][26] ;
 wire \rd_fifo[3][27] ;
 wire \rd_fifo[3][28] ;
 wire \rd_fifo[3][29] ;
 wire \rd_fifo[3][2] ;
 wire \rd_fifo[3][30] ;
 wire \rd_fifo[3][31] ;
 wire \rd_fifo[3][32] ;
 wire \rd_fifo[3][33] ;
 wire \rd_fifo[3][34] ;
 wire \rd_fifo[3][35] ;
 wire \rd_fifo[3][3] ;
 wire \rd_fifo[3][4] ;
 wire \rd_fifo[3][5] ;
 wire \rd_fifo[3][6] ;
 wire \rd_fifo[3][7] ;
 wire \rd_fifo[3][8] ;
 wire \rd_fifo[3][9] ;
 wire \rd_fifo[4][0] ;
 wire \rd_fifo[4][10] ;
 wire \rd_fifo[4][11] ;
 wire \rd_fifo[4][12] ;
 wire \rd_fifo[4][13] ;
 wire \rd_fifo[4][14] ;
 wire \rd_fifo[4][15] ;
 wire \rd_fifo[4][16] ;
 wire \rd_fifo[4][17] ;
 wire \rd_fifo[4][18] ;
 wire \rd_fifo[4][19] ;
 wire \rd_fifo[4][1] ;
 wire \rd_fifo[4][20] ;
 wire \rd_fifo[4][21] ;
 wire \rd_fifo[4][22] ;
 wire \rd_fifo[4][23] ;
 wire \rd_fifo[4][24] ;
 wire \rd_fifo[4][25] ;
 wire \rd_fifo[4][26] ;
 wire \rd_fifo[4][27] ;
 wire \rd_fifo[4][28] ;
 wire \rd_fifo[4][29] ;
 wire \rd_fifo[4][2] ;
 wire \rd_fifo[4][30] ;
 wire \rd_fifo[4][31] ;
 wire \rd_fifo[4][32] ;
 wire \rd_fifo[4][33] ;
 wire \rd_fifo[4][34] ;
 wire \rd_fifo[4][35] ;
 wire \rd_fifo[4][3] ;
 wire \rd_fifo[4][4] ;
 wire \rd_fifo[4][5] ;
 wire \rd_fifo[4][6] ;
 wire \rd_fifo[4][7] ;
 wire \rd_fifo[4][8] ;
 wire \rd_fifo[4][9] ;
 wire \rd_fifo[5][0] ;
 wire \rd_fifo[5][10] ;
 wire \rd_fifo[5][11] ;
 wire \rd_fifo[5][12] ;
 wire \rd_fifo[5][13] ;
 wire \rd_fifo[5][14] ;
 wire \rd_fifo[5][15] ;
 wire \rd_fifo[5][16] ;
 wire \rd_fifo[5][17] ;
 wire \rd_fifo[5][18] ;
 wire \rd_fifo[5][19] ;
 wire \rd_fifo[5][1] ;
 wire \rd_fifo[5][20] ;
 wire \rd_fifo[5][21] ;
 wire \rd_fifo[5][22] ;
 wire \rd_fifo[5][23] ;
 wire \rd_fifo[5][24] ;
 wire \rd_fifo[5][25] ;
 wire \rd_fifo[5][26] ;
 wire \rd_fifo[5][27] ;
 wire \rd_fifo[5][28] ;
 wire \rd_fifo[5][29] ;
 wire \rd_fifo[5][2] ;
 wire \rd_fifo[5][30] ;
 wire \rd_fifo[5][31] ;
 wire \rd_fifo[5][32] ;
 wire \rd_fifo[5][33] ;
 wire \rd_fifo[5][34] ;
 wire \rd_fifo[5][35] ;
 wire \rd_fifo[5][3] ;
 wire \rd_fifo[5][4] ;
 wire \rd_fifo[5][5] ;
 wire \rd_fifo[5][6] ;
 wire \rd_fifo[5][7] ;
 wire \rd_fifo[5][8] ;
 wire \rd_fifo[5][9] ;
 wire \rd_fifo[6][0] ;
 wire \rd_fifo[6][10] ;
 wire \rd_fifo[6][11] ;
 wire \rd_fifo[6][12] ;
 wire \rd_fifo[6][13] ;
 wire \rd_fifo[6][14] ;
 wire \rd_fifo[6][15] ;
 wire \rd_fifo[6][16] ;
 wire \rd_fifo[6][17] ;
 wire \rd_fifo[6][18] ;
 wire \rd_fifo[6][19] ;
 wire \rd_fifo[6][1] ;
 wire \rd_fifo[6][20] ;
 wire \rd_fifo[6][21] ;
 wire \rd_fifo[6][22] ;
 wire \rd_fifo[6][23] ;
 wire \rd_fifo[6][24] ;
 wire \rd_fifo[6][25] ;
 wire \rd_fifo[6][26] ;
 wire \rd_fifo[6][27] ;
 wire \rd_fifo[6][28] ;
 wire \rd_fifo[6][29] ;
 wire \rd_fifo[6][2] ;
 wire \rd_fifo[6][30] ;
 wire \rd_fifo[6][31] ;
 wire \rd_fifo[6][32] ;
 wire \rd_fifo[6][33] ;
 wire \rd_fifo[6][34] ;
 wire \rd_fifo[6][35] ;
 wire \rd_fifo[6][3] ;
 wire \rd_fifo[6][4] ;
 wire \rd_fifo[6][5] ;
 wire \rd_fifo[6][6] ;
 wire \rd_fifo[6][7] ;
 wire \rd_fifo[6][8] ;
 wire \rd_fifo[6][9] ;
 wire \rd_fifo[7][0] ;
 wire \rd_fifo[7][10] ;
 wire \rd_fifo[7][11] ;
 wire \rd_fifo[7][12] ;
 wire \rd_fifo[7][13] ;
 wire \rd_fifo[7][14] ;
 wire \rd_fifo[7][15] ;
 wire \rd_fifo[7][16] ;
 wire \rd_fifo[7][17] ;
 wire \rd_fifo[7][18] ;
 wire \rd_fifo[7][19] ;
 wire \rd_fifo[7][1] ;
 wire \rd_fifo[7][20] ;
 wire \rd_fifo[7][21] ;
 wire \rd_fifo[7][22] ;
 wire \rd_fifo[7][23] ;
 wire \rd_fifo[7][24] ;
 wire \rd_fifo[7][25] ;
 wire \rd_fifo[7][26] ;
 wire \rd_fifo[7][27] ;
 wire \rd_fifo[7][28] ;
 wire \rd_fifo[7][29] ;
 wire \rd_fifo[7][2] ;
 wire \rd_fifo[7][30] ;
 wire \rd_fifo[7][31] ;
 wire \rd_fifo[7][32] ;
 wire \rd_fifo[7][33] ;
 wire \rd_fifo[7][34] ;
 wire \rd_fifo[7][35] ;
 wire \rd_fifo[7][3] ;
 wire \rd_fifo[7][4] ;
 wire \rd_fifo[7][5] ;
 wire \rd_fifo[7][6] ;
 wire \rd_fifo[7][7] ;
 wire \rd_fifo[7][8] ;
 wire \rd_fifo[7][9] ;
 wire \rd_fifo[8][0] ;
 wire \rd_fifo[8][10] ;
 wire \rd_fifo[8][11] ;
 wire \rd_fifo[8][12] ;
 wire \rd_fifo[8][13] ;
 wire \rd_fifo[8][14] ;
 wire \rd_fifo[8][15] ;
 wire \rd_fifo[8][16] ;
 wire \rd_fifo[8][17] ;
 wire \rd_fifo[8][18] ;
 wire \rd_fifo[8][19] ;
 wire \rd_fifo[8][1] ;
 wire \rd_fifo[8][20] ;
 wire \rd_fifo[8][21] ;
 wire \rd_fifo[8][22] ;
 wire \rd_fifo[8][23] ;
 wire \rd_fifo[8][24] ;
 wire \rd_fifo[8][25] ;
 wire \rd_fifo[8][26] ;
 wire \rd_fifo[8][27] ;
 wire \rd_fifo[8][28] ;
 wire \rd_fifo[8][29] ;
 wire \rd_fifo[8][2] ;
 wire \rd_fifo[8][30] ;
 wire \rd_fifo[8][31] ;
 wire \rd_fifo[8][32] ;
 wire \rd_fifo[8][33] ;
 wire \rd_fifo[8][34] ;
 wire \rd_fifo[8][35] ;
 wire \rd_fifo[8][3] ;
 wire \rd_fifo[8][4] ;
 wire \rd_fifo[8][5] ;
 wire \rd_fifo[8][6] ;
 wire \rd_fifo[8][7] ;
 wire \rd_fifo[8][8] ;
 wire \rd_fifo[8][9] ;
 wire \rd_fifo[9][0] ;
 wire \rd_fifo[9][10] ;
 wire \rd_fifo[9][11] ;
 wire \rd_fifo[9][12] ;
 wire \rd_fifo[9][13] ;
 wire \rd_fifo[9][14] ;
 wire \rd_fifo[9][15] ;
 wire \rd_fifo[9][16] ;
 wire \rd_fifo[9][17] ;
 wire \rd_fifo[9][18] ;
 wire \rd_fifo[9][19] ;
 wire \rd_fifo[9][1] ;
 wire \rd_fifo[9][20] ;
 wire \rd_fifo[9][21] ;
 wire \rd_fifo[9][22] ;
 wire \rd_fifo[9][23] ;
 wire \rd_fifo[9][24] ;
 wire \rd_fifo[9][25] ;
 wire \rd_fifo[9][26] ;
 wire \rd_fifo[9][27] ;
 wire \rd_fifo[9][28] ;
 wire \rd_fifo[9][29] ;
 wire \rd_fifo[9][2] ;
 wire \rd_fifo[9][30] ;
 wire \rd_fifo[9][31] ;
 wire \rd_fifo[9][32] ;
 wire \rd_fifo[9][33] ;
 wire \rd_fifo[9][34] ;
 wire \rd_fifo[9][35] ;
 wire \rd_fifo[9][3] ;
 wire \rd_fifo[9][4] ;
 wire \rd_fifo[9][5] ;
 wire \rd_fifo[9][6] ;
 wire \rd_fifo[9][7] ;
 wire \rd_fifo[9][8] ;
 wire \rd_fifo[9][9] ;
 wire \rd_lat_ctr[0] ;
 wire \rd_lat_ctr[1] ;
 wire \rd_lat_ctr[2] ;
 wire \rd_lat_ctr[3] ;
 wire \rd_lat_ctr[4] ;
 wire \rd_lat_ctr[5] ;
 wire \rd_lat_ctr[6] ;
 wire \rd_lat_ctr[7] ;
 wire \rd_rptr[0] ;
 wire \rd_rptr[1] ;
 wire \rd_rptr[2] ;
 wire \rd_rptr[3] ;
 wire \rd_rptr[4] ;
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
 wire \rd_shift_r[0] ;
 wire \rd_shift_r[10] ;
 wire \rd_shift_r[11] ;
 wire \rd_shift_r[12] ;
 wire \rd_shift_r[13] ;
 wire \rd_shift_r[14] ;
 wire \rd_shift_r[15] ;
 wire \rd_shift_r[1] ;
 wire \rd_shift_r[2] ;
 wire \rd_shift_r[3] ;
 wire \rd_shift_r[4] ;
 wire \rd_shift_r[5] ;
 wire \rd_shift_r[6] ;
 wire \rd_shift_r[7] ;
 wire \rd_shift_r[8] ;
 wire \rd_shift_r[9] ;
 wire \rd_state[0] ;
 wire \rd_state[2] ;
 wire \rd_wptr[0] ;
 wire \rd_wptr[1] ;
 wire \rd_wptr[2] ;
 wire \rd_wptr[3] ;
 wire \rd_wptr[4] ;
 wire net39;
 wire \wr_buf[0][0] ;
 wire \wr_buf[0][10] ;
 wire \wr_buf[0][11] ;
 wire \wr_buf[0][12] ;
 wire \wr_buf[0][13] ;
 wire \wr_buf[0][14] ;
 wire \wr_buf[0][15] ;
 wire \wr_buf[0][16] ;
 wire \wr_buf[0][17] ;
 wire \wr_buf[0][18] ;
 wire \wr_buf[0][19] ;
 wire \wr_buf[0][1] ;
 wire \wr_buf[0][20] ;
 wire \wr_buf[0][21] ;
 wire \wr_buf[0][22] ;
 wire \wr_buf[0][23] ;
 wire \wr_buf[0][24] ;
 wire \wr_buf[0][25] ;
 wire \wr_buf[0][26] ;
 wire \wr_buf[0][27] ;
 wire \wr_buf[0][28] ;
 wire \wr_buf[0][29] ;
 wire \wr_buf[0][2] ;
 wire \wr_buf[0][30] ;
 wire \wr_buf[0][31] ;
 wire \wr_buf[0][32] ;
 wire \wr_buf[0][33] ;
 wire \wr_buf[0][34] ;
 wire \wr_buf[0][35] ;
 wire \wr_buf[0][3] ;
 wire \wr_buf[0][4] ;
 wire \wr_buf[0][5] ;
 wire \wr_buf[0][6] ;
 wire \wr_buf[0][7] ;
 wire \wr_buf[0][8] ;
 wire \wr_buf[0][9] ;
 wire \wr_buf[10][0] ;
 wire \wr_buf[10][10] ;
 wire \wr_buf[10][11] ;
 wire \wr_buf[10][12] ;
 wire \wr_buf[10][13] ;
 wire \wr_buf[10][14] ;
 wire \wr_buf[10][15] ;
 wire \wr_buf[10][16] ;
 wire \wr_buf[10][17] ;
 wire \wr_buf[10][18] ;
 wire \wr_buf[10][19] ;
 wire \wr_buf[10][1] ;
 wire \wr_buf[10][20] ;
 wire \wr_buf[10][21] ;
 wire \wr_buf[10][22] ;
 wire \wr_buf[10][23] ;
 wire \wr_buf[10][24] ;
 wire \wr_buf[10][25] ;
 wire \wr_buf[10][26] ;
 wire \wr_buf[10][27] ;
 wire \wr_buf[10][28] ;
 wire \wr_buf[10][29] ;
 wire \wr_buf[10][2] ;
 wire \wr_buf[10][30] ;
 wire \wr_buf[10][31] ;
 wire \wr_buf[10][32] ;
 wire \wr_buf[10][33] ;
 wire \wr_buf[10][34] ;
 wire \wr_buf[10][35] ;
 wire \wr_buf[10][3] ;
 wire \wr_buf[10][4] ;
 wire \wr_buf[10][5] ;
 wire \wr_buf[10][6] ;
 wire \wr_buf[10][7] ;
 wire \wr_buf[10][8] ;
 wire \wr_buf[10][9] ;
 wire \wr_buf[11][0] ;
 wire \wr_buf[11][10] ;
 wire \wr_buf[11][11] ;
 wire \wr_buf[11][12] ;
 wire \wr_buf[11][13] ;
 wire \wr_buf[11][14] ;
 wire \wr_buf[11][15] ;
 wire \wr_buf[11][16] ;
 wire \wr_buf[11][17] ;
 wire \wr_buf[11][18] ;
 wire \wr_buf[11][19] ;
 wire \wr_buf[11][1] ;
 wire \wr_buf[11][20] ;
 wire \wr_buf[11][21] ;
 wire \wr_buf[11][22] ;
 wire \wr_buf[11][23] ;
 wire \wr_buf[11][24] ;
 wire \wr_buf[11][25] ;
 wire \wr_buf[11][26] ;
 wire \wr_buf[11][27] ;
 wire \wr_buf[11][28] ;
 wire \wr_buf[11][29] ;
 wire \wr_buf[11][2] ;
 wire \wr_buf[11][30] ;
 wire \wr_buf[11][31] ;
 wire \wr_buf[11][32] ;
 wire \wr_buf[11][33] ;
 wire \wr_buf[11][34] ;
 wire \wr_buf[11][35] ;
 wire \wr_buf[11][3] ;
 wire \wr_buf[11][4] ;
 wire \wr_buf[11][5] ;
 wire \wr_buf[11][6] ;
 wire \wr_buf[11][7] ;
 wire \wr_buf[11][8] ;
 wire \wr_buf[11][9] ;
 wire \wr_buf[12][0] ;
 wire \wr_buf[12][10] ;
 wire \wr_buf[12][11] ;
 wire \wr_buf[12][12] ;
 wire \wr_buf[12][13] ;
 wire \wr_buf[12][14] ;
 wire \wr_buf[12][15] ;
 wire \wr_buf[12][16] ;
 wire \wr_buf[12][17] ;
 wire \wr_buf[12][18] ;
 wire \wr_buf[12][19] ;
 wire \wr_buf[12][1] ;
 wire \wr_buf[12][20] ;
 wire \wr_buf[12][21] ;
 wire \wr_buf[12][22] ;
 wire \wr_buf[12][23] ;
 wire \wr_buf[12][24] ;
 wire \wr_buf[12][25] ;
 wire \wr_buf[12][26] ;
 wire \wr_buf[12][27] ;
 wire \wr_buf[12][28] ;
 wire \wr_buf[12][29] ;
 wire \wr_buf[12][2] ;
 wire \wr_buf[12][30] ;
 wire \wr_buf[12][31] ;
 wire \wr_buf[12][32] ;
 wire \wr_buf[12][33] ;
 wire \wr_buf[12][34] ;
 wire \wr_buf[12][35] ;
 wire \wr_buf[12][3] ;
 wire \wr_buf[12][4] ;
 wire \wr_buf[12][5] ;
 wire \wr_buf[12][6] ;
 wire \wr_buf[12][7] ;
 wire \wr_buf[12][8] ;
 wire \wr_buf[12][9] ;
 wire \wr_buf[13][0] ;
 wire \wr_buf[13][10] ;
 wire \wr_buf[13][11] ;
 wire \wr_buf[13][12] ;
 wire \wr_buf[13][13] ;
 wire \wr_buf[13][14] ;
 wire \wr_buf[13][15] ;
 wire \wr_buf[13][16] ;
 wire \wr_buf[13][17] ;
 wire \wr_buf[13][18] ;
 wire \wr_buf[13][19] ;
 wire \wr_buf[13][1] ;
 wire \wr_buf[13][20] ;
 wire \wr_buf[13][21] ;
 wire \wr_buf[13][22] ;
 wire \wr_buf[13][23] ;
 wire \wr_buf[13][24] ;
 wire \wr_buf[13][25] ;
 wire \wr_buf[13][26] ;
 wire \wr_buf[13][27] ;
 wire \wr_buf[13][28] ;
 wire \wr_buf[13][29] ;
 wire \wr_buf[13][2] ;
 wire \wr_buf[13][30] ;
 wire \wr_buf[13][31] ;
 wire \wr_buf[13][32] ;
 wire \wr_buf[13][33] ;
 wire \wr_buf[13][34] ;
 wire \wr_buf[13][35] ;
 wire \wr_buf[13][3] ;
 wire \wr_buf[13][4] ;
 wire \wr_buf[13][5] ;
 wire \wr_buf[13][6] ;
 wire \wr_buf[13][7] ;
 wire \wr_buf[13][8] ;
 wire \wr_buf[13][9] ;
 wire \wr_buf[14][0] ;
 wire \wr_buf[14][10] ;
 wire \wr_buf[14][11] ;
 wire \wr_buf[14][12] ;
 wire \wr_buf[14][13] ;
 wire \wr_buf[14][14] ;
 wire \wr_buf[14][15] ;
 wire \wr_buf[14][16] ;
 wire \wr_buf[14][17] ;
 wire \wr_buf[14][18] ;
 wire \wr_buf[14][19] ;
 wire \wr_buf[14][1] ;
 wire \wr_buf[14][20] ;
 wire \wr_buf[14][21] ;
 wire \wr_buf[14][22] ;
 wire \wr_buf[14][23] ;
 wire \wr_buf[14][24] ;
 wire \wr_buf[14][25] ;
 wire \wr_buf[14][26] ;
 wire \wr_buf[14][27] ;
 wire \wr_buf[14][28] ;
 wire \wr_buf[14][29] ;
 wire \wr_buf[14][2] ;
 wire \wr_buf[14][30] ;
 wire \wr_buf[14][31] ;
 wire \wr_buf[14][32] ;
 wire \wr_buf[14][33] ;
 wire \wr_buf[14][34] ;
 wire \wr_buf[14][35] ;
 wire \wr_buf[14][3] ;
 wire \wr_buf[14][4] ;
 wire \wr_buf[14][5] ;
 wire \wr_buf[14][6] ;
 wire \wr_buf[14][7] ;
 wire \wr_buf[14][8] ;
 wire \wr_buf[14][9] ;
 wire \wr_buf[15][0] ;
 wire \wr_buf[15][10] ;
 wire \wr_buf[15][11] ;
 wire \wr_buf[15][12] ;
 wire \wr_buf[15][13] ;
 wire \wr_buf[15][14] ;
 wire \wr_buf[15][15] ;
 wire \wr_buf[15][16] ;
 wire \wr_buf[15][17] ;
 wire \wr_buf[15][18] ;
 wire \wr_buf[15][19] ;
 wire \wr_buf[15][1] ;
 wire \wr_buf[15][20] ;
 wire \wr_buf[15][21] ;
 wire \wr_buf[15][22] ;
 wire \wr_buf[15][23] ;
 wire \wr_buf[15][24] ;
 wire \wr_buf[15][25] ;
 wire \wr_buf[15][26] ;
 wire \wr_buf[15][27] ;
 wire \wr_buf[15][28] ;
 wire \wr_buf[15][29] ;
 wire \wr_buf[15][2] ;
 wire \wr_buf[15][30] ;
 wire \wr_buf[15][31] ;
 wire \wr_buf[15][32] ;
 wire \wr_buf[15][33] ;
 wire \wr_buf[15][34] ;
 wire \wr_buf[15][35] ;
 wire \wr_buf[15][3] ;
 wire \wr_buf[15][4] ;
 wire \wr_buf[15][5] ;
 wire \wr_buf[15][6] ;
 wire \wr_buf[15][7] ;
 wire \wr_buf[15][8] ;
 wire \wr_buf[15][9] ;
 wire \wr_buf[1][0] ;
 wire \wr_buf[1][10] ;
 wire \wr_buf[1][11] ;
 wire \wr_buf[1][12] ;
 wire \wr_buf[1][13] ;
 wire \wr_buf[1][14] ;
 wire \wr_buf[1][15] ;
 wire \wr_buf[1][16] ;
 wire \wr_buf[1][17] ;
 wire \wr_buf[1][18] ;
 wire \wr_buf[1][19] ;
 wire \wr_buf[1][1] ;
 wire \wr_buf[1][20] ;
 wire \wr_buf[1][21] ;
 wire \wr_buf[1][22] ;
 wire \wr_buf[1][23] ;
 wire \wr_buf[1][24] ;
 wire \wr_buf[1][25] ;
 wire \wr_buf[1][26] ;
 wire \wr_buf[1][27] ;
 wire \wr_buf[1][28] ;
 wire \wr_buf[1][29] ;
 wire \wr_buf[1][2] ;
 wire \wr_buf[1][30] ;
 wire \wr_buf[1][31] ;
 wire \wr_buf[1][32] ;
 wire \wr_buf[1][33] ;
 wire \wr_buf[1][34] ;
 wire \wr_buf[1][35] ;
 wire \wr_buf[1][3] ;
 wire \wr_buf[1][4] ;
 wire \wr_buf[1][5] ;
 wire \wr_buf[1][6] ;
 wire \wr_buf[1][7] ;
 wire \wr_buf[1][8] ;
 wire \wr_buf[1][9] ;
 wire \wr_buf[2][0] ;
 wire \wr_buf[2][10] ;
 wire \wr_buf[2][11] ;
 wire \wr_buf[2][12] ;
 wire \wr_buf[2][13] ;
 wire \wr_buf[2][14] ;
 wire \wr_buf[2][15] ;
 wire \wr_buf[2][16] ;
 wire \wr_buf[2][17] ;
 wire \wr_buf[2][18] ;
 wire \wr_buf[2][19] ;
 wire \wr_buf[2][1] ;
 wire \wr_buf[2][20] ;
 wire \wr_buf[2][21] ;
 wire \wr_buf[2][22] ;
 wire \wr_buf[2][23] ;
 wire \wr_buf[2][24] ;
 wire \wr_buf[2][25] ;
 wire \wr_buf[2][26] ;
 wire \wr_buf[2][27] ;
 wire \wr_buf[2][28] ;
 wire \wr_buf[2][29] ;
 wire \wr_buf[2][2] ;
 wire \wr_buf[2][30] ;
 wire \wr_buf[2][31] ;
 wire \wr_buf[2][32] ;
 wire \wr_buf[2][33] ;
 wire \wr_buf[2][34] ;
 wire \wr_buf[2][35] ;
 wire \wr_buf[2][3] ;
 wire \wr_buf[2][4] ;
 wire \wr_buf[2][5] ;
 wire \wr_buf[2][6] ;
 wire \wr_buf[2][7] ;
 wire \wr_buf[2][8] ;
 wire \wr_buf[2][9] ;
 wire \wr_buf[3][0] ;
 wire \wr_buf[3][10] ;
 wire \wr_buf[3][11] ;
 wire \wr_buf[3][12] ;
 wire \wr_buf[3][13] ;
 wire \wr_buf[3][14] ;
 wire \wr_buf[3][15] ;
 wire \wr_buf[3][16] ;
 wire \wr_buf[3][17] ;
 wire \wr_buf[3][18] ;
 wire \wr_buf[3][19] ;
 wire \wr_buf[3][1] ;
 wire \wr_buf[3][20] ;
 wire \wr_buf[3][21] ;
 wire \wr_buf[3][22] ;
 wire \wr_buf[3][23] ;
 wire \wr_buf[3][24] ;
 wire \wr_buf[3][25] ;
 wire \wr_buf[3][26] ;
 wire \wr_buf[3][27] ;
 wire \wr_buf[3][28] ;
 wire \wr_buf[3][29] ;
 wire \wr_buf[3][2] ;
 wire \wr_buf[3][30] ;
 wire \wr_buf[3][31] ;
 wire \wr_buf[3][32] ;
 wire \wr_buf[3][33] ;
 wire \wr_buf[3][34] ;
 wire \wr_buf[3][35] ;
 wire \wr_buf[3][3] ;
 wire \wr_buf[3][4] ;
 wire \wr_buf[3][5] ;
 wire \wr_buf[3][6] ;
 wire \wr_buf[3][7] ;
 wire \wr_buf[3][8] ;
 wire \wr_buf[3][9] ;
 wire \wr_buf[4][0] ;
 wire \wr_buf[4][10] ;
 wire \wr_buf[4][11] ;
 wire \wr_buf[4][12] ;
 wire \wr_buf[4][13] ;
 wire \wr_buf[4][14] ;
 wire \wr_buf[4][15] ;
 wire \wr_buf[4][16] ;
 wire \wr_buf[4][17] ;
 wire \wr_buf[4][18] ;
 wire \wr_buf[4][19] ;
 wire \wr_buf[4][1] ;
 wire \wr_buf[4][20] ;
 wire \wr_buf[4][21] ;
 wire \wr_buf[4][22] ;
 wire \wr_buf[4][23] ;
 wire \wr_buf[4][24] ;
 wire \wr_buf[4][25] ;
 wire \wr_buf[4][26] ;
 wire \wr_buf[4][27] ;
 wire \wr_buf[4][28] ;
 wire \wr_buf[4][29] ;
 wire \wr_buf[4][2] ;
 wire \wr_buf[4][30] ;
 wire \wr_buf[4][31] ;
 wire \wr_buf[4][32] ;
 wire \wr_buf[4][33] ;
 wire \wr_buf[4][34] ;
 wire \wr_buf[4][35] ;
 wire \wr_buf[4][3] ;
 wire \wr_buf[4][4] ;
 wire \wr_buf[4][5] ;
 wire \wr_buf[4][6] ;
 wire \wr_buf[4][7] ;
 wire \wr_buf[4][8] ;
 wire \wr_buf[4][9] ;
 wire \wr_buf[5][0] ;
 wire \wr_buf[5][10] ;
 wire \wr_buf[5][11] ;
 wire \wr_buf[5][12] ;
 wire \wr_buf[5][13] ;
 wire \wr_buf[5][14] ;
 wire \wr_buf[5][15] ;
 wire \wr_buf[5][16] ;
 wire \wr_buf[5][17] ;
 wire \wr_buf[5][18] ;
 wire \wr_buf[5][19] ;
 wire \wr_buf[5][1] ;
 wire \wr_buf[5][20] ;
 wire \wr_buf[5][21] ;
 wire \wr_buf[5][22] ;
 wire \wr_buf[5][23] ;
 wire \wr_buf[5][24] ;
 wire \wr_buf[5][25] ;
 wire \wr_buf[5][26] ;
 wire \wr_buf[5][27] ;
 wire \wr_buf[5][28] ;
 wire \wr_buf[5][29] ;
 wire \wr_buf[5][2] ;
 wire \wr_buf[5][30] ;
 wire \wr_buf[5][31] ;
 wire \wr_buf[5][32] ;
 wire \wr_buf[5][33] ;
 wire \wr_buf[5][34] ;
 wire \wr_buf[5][35] ;
 wire \wr_buf[5][3] ;
 wire \wr_buf[5][4] ;
 wire \wr_buf[5][5] ;
 wire \wr_buf[5][6] ;
 wire \wr_buf[5][7] ;
 wire \wr_buf[5][8] ;
 wire \wr_buf[5][9] ;
 wire \wr_buf[6][0] ;
 wire \wr_buf[6][10] ;
 wire \wr_buf[6][11] ;
 wire \wr_buf[6][12] ;
 wire \wr_buf[6][13] ;
 wire \wr_buf[6][14] ;
 wire \wr_buf[6][15] ;
 wire \wr_buf[6][16] ;
 wire \wr_buf[6][17] ;
 wire \wr_buf[6][18] ;
 wire \wr_buf[6][19] ;
 wire \wr_buf[6][1] ;
 wire \wr_buf[6][20] ;
 wire \wr_buf[6][21] ;
 wire \wr_buf[6][22] ;
 wire \wr_buf[6][23] ;
 wire \wr_buf[6][24] ;
 wire \wr_buf[6][25] ;
 wire \wr_buf[6][26] ;
 wire \wr_buf[6][27] ;
 wire \wr_buf[6][28] ;
 wire \wr_buf[6][29] ;
 wire \wr_buf[6][2] ;
 wire \wr_buf[6][30] ;
 wire \wr_buf[6][31] ;
 wire \wr_buf[6][32] ;
 wire \wr_buf[6][33] ;
 wire \wr_buf[6][34] ;
 wire \wr_buf[6][35] ;
 wire \wr_buf[6][3] ;
 wire \wr_buf[6][4] ;
 wire \wr_buf[6][5] ;
 wire \wr_buf[6][6] ;
 wire \wr_buf[6][7] ;
 wire \wr_buf[6][8] ;
 wire \wr_buf[6][9] ;
 wire \wr_buf[7][0] ;
 wire \wr_buf[7][10] ;
 wire \wr_buf[7][11] ;
 wire \wr_buf[7][12] ;
 wire \wr_buf[7][13] ;
 wire \wr_buf[7][14] ;
 wire \wr_buf[7][15] ;
 wire \wr_buf[7][16] ;
 wire \wr_buf[7][17] ;
 wire \wr_buf[7][18] ;
 wire \wr_buf[7][19] ;
 wire \wr_buf[7][1] ;
 wire \wr_buf[7][20] ;
 wire \wr_buf[7][21] ;
 wire \wr_buf[7][22] ;
 wire \wr_buf[7][23] ;
 wire \wr_buf[7][24] ;
 wire \wr_buf[7][25] ;
 wire \wr_buf[7][26] ;
 wire \wr_buf[7][27] ;
 wire \wr_buf[7][28] ;
 wire \wr_buf[7][29] ;
 wire \wr_buf[7][2] ;
 wire \wr_buf[7][30] ;
 wire \wr_buf[7][31] ;
 wire \wr_buf[7][32] ;
 wire \wr_buf[7][33] ;
 wire \wr_buf[7][34] ;
 wire \wr_buf[7][35] ;
 wire \wr_buf[7][3] ;
 wire \wr_buf[7][4] ;
 wire \wr_buf[7][5] ;
 wire \wr_buf[7][6] ;
 wire \wr_buf[7][7] ;
 wire \wr_buf[7][8] ;
 wire \wr_buf[7][9] ;
 wire \wr_buf[8][0] ;
 wire \wr_buf[8][10] ;
 wire \wr_buf[8][11] ;
 wire \wr_buf[8][12] ;
 wire \wr_buf[8][13] ;
 wire \wr_buf[8][14] ;
 wire \wr_buf[8][15] ;
 wire \wr_buf[8][16] ;
 wire \wr_buf[8][17] ;
 wire \wr_buf[8][18] ;
 wire \wr_buf[8][19] ;
 wire \wr_buf[8][1] ;
 wire \wr_buf[8][20] ;
 wire \wr_buf[8][21] ;
 wire \wr_buf[8][22] ;
 wire \wr_buf[8][23] ;
 wire \wr_buf[8][24] ;
 wire \wr_buf[8][25] ;
 wire \wr_buf[8][26] ;
 wire \wr_buf[8][27] ;
 wire \wr_buf[8][28] ;
 wire \wr_buf[8][29] ;
 wire \wr_buf[8][2] ;
 wire \wr_buf[8][30] ;
 wire \wr_buf[8][31] ;
 wire \wr_buf[8][32] ;
 wire \wr_buf[8][33] ;
 wire \wr_buf[8][34] ;
 wire \wr_buf[8][35] ;
 wire \wr_buf[8][3] ;
 wire \wr_buf[8][4] ;
 wire \wr_buf[8][5] ;
 wire \wr_buf[8][6] ;
 wire \wr_buf[8][7] ;
 wire \wr_buf[8][8] ;
 wire \wr_buf[8][9] ;
 wire \wr_buf[9][0] ;
 wire \wr_buf[9][10] ;
 wire \wr_buf[9][11] ;
 wire \wr_buf[9][12] ;
 wire \wr_buf[9][13] ;
 wire \wr_buf[9][14] ;
 wire \wr_buf[9][15] ;
 wire \wr_buf[9][16] ;
 wire \wr_buf[9][17] ;
 wire \wr_buf[9][18] ;
 wire \wr_buf[9][19] ;
 wire \wr_buf[9][1] ;
 wire \wr_buf[9][20] ;
 wire \wr_buf[9][21] ;
 wire \wr_buf[9][22] ;
 wire \wr_buf[9][23] ;
 wire \wr_buf[9][24] ;
 wire \wr_buf[9][25] ;
 wire \wr_buf[9][26] ;
 wire \wr_buf[9][27] ;
 wire \wr_buf[9][28] ;
 wire \wr_buf[9][29] ;
 wire \wr_buf[9][2] ;
 wire \wr_buf[9][30] ;
 wire \wr_buf[9][31] ;
 wire \wr_buf[9][32] ;
 wire \wr_buf[9][33] ;
 wire \wr_buf[9][34] ;
 wire \wr_buf[9][35] ;
 wire \wr_buf[9][3] ;
 wire \wr_buf[9][4] ;
 wire \wr_buf[9][5] ;
 wire \wr_buf[9][6] ;
 wire \wr_buf[9][7] ;
 wire \wr_buf[9][8] ;
 wire \wr_buf[9][9] ;
 wire \wr_burst_ctr[0] ;
 wire \wr_burst_ctr[1] ;
 wire \wr_dat_r[0] ;
 wire \wr_dat_r[10] ;
 wire \wr_dat_r[11] ;
 wire \wr_dat_r[12] ;
 wire \wr_dat_r[13] ;
 wire \wr_dat_r[14] ;
 wire \wr_dat_r[15] ;
 wire \wr_dat_r[16] ;
 wire \wr_dat_r[17] ;
 wire \wr_dat_r[18] ;
 wire \wr_dat_r[19] ;
 wire \wr_dat_r[1] ;
 wire \wr_dat_r[20] ;
 wire \wr_dat_r[21] ;
 wire \wr_dat_r[22] ;
 wire \wr_dat_r[23] ;
 wire \wr_dat_r[24] ;
 wire \wr_dat_r[25] ;
 wire \wr_dat_r[26] ;
 wire \wr_dat_r[27] ;
 wire \wr_dat_r[28] ;
 wire \wr_dat_r[29] ;
 wire \wr_dat_r[2] ;
 wire \wr_dat_r[30] ;
 wire \wr_dat_r[31] ;
 wire \wr_dat_r[3] ;
 wire \wr_dat_r[4] ;
 wire \wr_dat_r[5] ;
 wire \wr_dat_r[6] ;
 wire \wr_dat_r[7] ;
 wire \wr_dat_r[8] ;
 wire \wr_dat_r[9] ;
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
 wire net69;
 wire net70;
 wire net71;
 wire net135;
 wire net72;
 wire \wr_lat_ctr[0] ;
 wire \wr_lat_ctr[1] ;
 wire \wr_lat_ctr[2] ;
 wire \wr_lat_ctr[3] ;
 wire \wr_lat_ctr[4] ;
 wire \wr_lat_ctr[5] ;
 wire \wr_lat_ctr[6] ;
 wire \wr_lat_ctr[7] ;
 wire net73;
 wire net74;
 wire net75;
 wire net76;
 wire \wr_msk_r[0] ;
 wire \wr_msk_r[1] ;
 wire \wr_msk_r[2] ;
 wire \wr_msk_r[3] ;
 wire \wr_rptr[0] ;
 wire \wr_rptr[1] ;
 wire \wr_rptr[2] ;
 wire \wr_rptr[3] ;
 wire \wr_rptr[4] ;
 wire \wr_state[0] ;
 wire \wr_state[2] ;
 wire \wr_wptr[0] ;
 wire \wr_wptr[1] ;
 wire \wr_wptr[2] ;
 wire \wr_wptr[3] ;
 wire \wr_wptr[4] ;
 wire net271;
 wire net272;
 wire net273;
 wire net274;
 wire net275;
 wire net276;
 wire net277;
 wire net304;
 wire net302;
 wire net281;
 wire net282;
 wire net283;
 wire clknet_leaf_22_clk;
 wire net285;
 wire clknet_leaf_25_clk;
 wire clknet_leaf_23_clk;
 wire clknet_leaf_24_clk;
 wire clknet_leaf_26_clk;
 wire clknet_leaf_17_clk;
 wire net286;
 wire clknet_leaf_20_clk;
 wire clknet_leaf_19_clk;
 wire clknet_leaf_18_clk;
 wire clknet_leaf_21_clk;
 wire clknet_leaf_14_clk;
 wire clknet_leaf_12_clk;
 wire net287;
 wire clknet_leaf_13_clk;
 wire clknet_leaf_15_clk;
 wire clknet_leaf_16_clk;
 wire clknet_leaf_7_clk;
 wire net288;
 wire clknet_leaf_10_clk;
 wire clknet_leaf_9_clk;
 wire clknet_leaf_8_clk;
 wire clknet_leaf_11_clk;
 wire net289;
 wire net290;
 wire clknet_leaf_3_clk;
 wire net291;
 wire clknet_leaf_5_clk;
 wire clknet_leaf_4_clk;
 wire clknet_leaf_6_clk;
 wire net320;
 wire net292;
 wire net323;
 wire net322;
 wire net324;
 wire net319;
 wire net293;
 wire net311;
 wire net308;
 wire net314;
 wire net294;
 wire net295;
 wire net296;
 wire net297;
 wire net298;
 wire net299;
 wire net300;
 wire net301;
 wire net303;
 wire net305;
 wire net306;
 wire net307;
 wire net310;
 wire net309;
 wire net313;
 wire net312;
 wire net316;
 wire net315;
 wire net317;
 wire clknet_leaf_2_clk;
 wire net318;
 wire net326;
 wire net321;
 wire net325;
 wire clknet_leaf_1_clk;
 wire clknet_leaf_0_clk;
 wire net269;
 wire net270;
 wire net278;
 wire net279;
 wire net280;
 wire net284;
 wire clknet_leaf_27_clk;
 wire clknet_leaf_28_clk;
 wire clknet_leaf_29_clk;
 wire clknet_leaf_30_clk;
 wire clknet_leaf_31_clk;
 wire clknet_leaf_32_clk;
 wire clknet_leaf_33_clk;
 wire clknet_leaf_34_clk;
 wire clknet_leaf_35_clk;
 wire clknet_leaf_36_clk;
 wire clknet_leaf_37_clk;
 wire clknet_leaf_38_clk;
 wire clknet_leaf_39_clk;
 wire clknet_leaf_40_clk;
 wire clknet_leaf_41_clk;
 wire clknet_leaf_42_clk;
 wire clknet_leaf_43_clk;
 wire clknet_leaf_44_clk;
 wire clknet_leaf_45_clk;
 wire clknet_leaf_46_clk;
 wire clknet_leaf_47_clk;
 wire clknet_leaf_48_clk;
 wire clknet_leaf_49_clk;
 wire clknet_leaf_50_clk;
 wire clknet_leaf_51_clk;
 wire clknet_leaf_52_clk;
 wire clknet_leaf_53_clk;
 wire clknet_leaf_54_clk;
 wire clknet_leaf_55_clk;
 wire clknet_leaf_56_clk;
 wire clknet_leaf_57_clk;
 wire clknet_leaf_58_clk;
 wire clknet_leaf_59_clk;
 wire clknet_leaf_60_clk;
 wire clknet_leaf_61_clk;
 wire clknet_leaf_62_clk;
 wire clknet_leaf_63_clk;
 wire clknet_leaf_64_clk;
 wire clknet_leaf_65_clk;
 wire clknet_leaf_66_clk;
 wire clknet_leaf_67_clk;
 wire clknet_leaf_68_clk;
 wire clknet_leaf_69_clk;
 wire clknet_leaf_70_clk;
 wire clknet_leaf_71_clk;
 wire clknet_leaf_72_clk;
 wire clknet_leaf_73_clk;
 wire clknet_leaf_74_clk;
 wire clknet_leaf_75_clk;
 wire clknet_leaf_76_clk;
 wire clknet_leaf_77_clk;
 wire clknet_leaf_78_clk;
 wire clknet_leaf_79_clk;
 wire clknet_leaf_80_clk;
 wire clknet_leaf_81_clk;
 wire clknet_leaf_82_clk;
 wire clknet_leaf_83_clk;
 wire clknet_leaf_84_clk;
 wire clknet_leaf_85_clk;
 wire clknet_leaf_86_clk;
 wire clknet_leaf_87_clk;
 wire clknet_leaf_88_clk;
 wire clknet_leaf_89_clk;
 wire clknet_leaf_90_clk;
 wire clknet_leaf_91_clk;
 wire clknet_leaf_92_clk;
 wire clknet_leaf_93_clk;
 wire clknet_leaf_94_clk;
 wire clknet_leaf_95_clk;
 wire clknet_leaf_96_clk;
 wire clknet_leaf_97_clk;
 wire clknet_leaf_98_clk;
 wire clknet_leaf_99_clk;
 wire clknet_leaf_100_clk;
 wire clknet_leaf_101_clk;
 wire clknet_leaf_102_clk;
 wire clknet_leaf_103_clk;
 wire clknet_leaf_104_clk;
 wire clknet_leaf_105_clk;
 wire clknet_leaf_106_clk;
 wire clknet_leaf_107_clk;
 wire clknet_leaf_108_clk;
 wire clknet_0_clk;
 wire clknet_3_0__leaf_clk;
 wire clknet_3_1__leaf_clk;
 wire clknet_3_2__leaf_clk;
 wire clknet_3_3__leaf_clk;
 wire clknet_3_4__leaf_clk;
 wire clknet_3_5__leaf_clk;
 wire clknet_3_6__leaf_clk;
 wire clknet_3_7__leaf_clk;
 wire net;

 sky130_fd_sc_hd__xnor2_1 _0848_ (.A(\wr_rptr[4] ),
    .B(\wr_wptr[4] ),
    .Y(_0203_));
 sky130_fd_sc_hd__a21o_1 _0849_ (.A1(_0063_),
    .A2(_0065_),
    .B1(_0062_),
    .X(_0204_));
 sky130_fd_sc_hd__nor2b_1 _0850_ (.A(_0056_),
    .B_N(_0060_),
    .Y(_0205_));
 sky130_fd_sc_hd__o211a_1 _0851_ (.A1(_0059_),
    .A2(_0205_),
    .B1(_0066_),
    .C1(_0063_),
    .X(_0206_));
 sky130_fd_sc_hd__nor3_1 _0852_ (.A(_0203_),
    .B(_0204_),
    .C(_0206_),
    .Y(_0207_));
 sky130_fd_sc_hd__a21oi_1 _0853_ (.A1(_0063_),
    .A2(_0065_),
    .B1(_0062_),
    .Y(_0208_));
 sky130_fd_sc_hd__o211ai_1 _0854_ (.A1(_0059_),
    .A2(_0205_),
    .B1(_0066_),
    .C1(_0063_),
    .Y(_0209_));
 sky130_fd_sc_hd__xor2_1 _0855_ (.A(\wr_rptr[4] ),
    .B(\wr_wptr[4] ),
    .X(_0210_));
 sky130_fd_sc_hd__a21oi_1 _0856_ (.A1(_0208_),
    .A2(_0209_),
    .B1(_0210_),
    .Y(_0211_));
 sky130_fd_sc_hd__or2_0 _0857_ (.A(_0059_),
    .B(_0065_),
    .X(_0212_));
 sky130_fd_sc_hd__o22ai_1 _0858_ (.A1(_0066_),
    .A2(_0065_),
    .B1(_0205_),
    .B2(_0212_),
    .Y(_0213_));
 sky130_fd_sc_hd__xnor2_1 _0859_ (.A(_0063_),
    .B(_0213_),
    .Y(_0214_));
 sky130_fd_sc_hd__nand2b_1 _0860_ (.A_N(_0059_),
    .B(_0056_),
    .Y(_0215_));
 sky130_fd_sc_hd__xnor2_1 _0861_ (.A(_0066_),
    .B(_0215_),
    .Y(_0216_));
 sky130_fd_sc_hd__nand3_1 _0862_ (.A(_0057_),
    .B(_0060_),
    .C(_0216_),
    .Y(_0217_));
 sky130_fd_sc_hd__o41a_1 _0863_ (.A1(_0207_),
    .A2(_0211_),
    .A3(_0214_),
    .A4(_0217_),
    .B1(net72),
    .X(_0218_));
 sky130_fd_sc_hd__nand3b_1 _0865_ (.A_N(\wr_wptr[3] ),
    .B(_0218_),
    .C(\wr_wptr[2] ),
    .Y(_0220_));
 sky130_fd_sc_hd__nand2_1 _0866_ (.A(_0044_),
    .B(net39),
    .Y(_0221_));
 sky130_fd_sc_hd__nor2_4 _0867_ (.A(_0220_),
    .B(_0221_),
    .Y(_0034_));
 sky130_fd_sc_hd__nand2_1 _0868_ (.A(net39),
    .B(_0045_),
    .Y(_0222_));
 sky130_fd_sc_hd__nor2_4 _0869_ (.A(_0220_),
    .B(_0222_),
    .Y(_0033_));
 sky130_fd_sc_hd__and3_1 _0873_ (.A(net39),
    .B(rd_capture_valid),
    .C(_0082_),
    .X(_0226_));
 sky130_fd_sc_hd__nand2_1 _0874_ (.A(_0051_),
    .B(_0226_),
    .Y(_0227_));
 sky130_fd_sc_hd__nor3_2 _0875_ (.A(\rd_wptr[2] ),
    .B(\rd_wptr[3] ),
    .C(_0227_),
    .Y(_0006_));
 sky130_fd_sc_hd__nand2_1 _0876_ (.A(net39),
    .B(_0042_),
    .Y(_0228_));
 sky130_fd_sc_hd__nor2_4 _0877_ (.A(_0220_),
    .B(_0228_),
    .Y(_0032_));
 sky130_fd_sc_hd__nand2_1 _0878_ (.A(_0053_),
    .B(_0226_),
    .Y(_0229_));
 sky130_fd_sc_hd__nand2b_1 _0879_ (.A_N(\rd_wptr[2] ),
    .B(\rd_wptr[3] ),
    .Y(_0230_));
 sky130_fd_sc_hd__nor2_4 _0880_ (.A(_0229_),
    .B(_0230_),
    .Y(_0007_));
 sky130_fd_sc_hd__o41ai_1 _0881_ (.A1(_0207_),
    .A2(_0211_),
    .A3(_0214_),
    .A4(_0217_),
    .B1(net72),
    .Y(_0231_));
 sky130_fd_sc_hd__nand2_1 _0882_ (.A(_0046_),
    .B(net39),
    .Y(_0232_));
 sky130_fd_sc_hd__nor4_2 _0883_ (.A(\wr_wptr[2] ),
    .B(\wr_wptr[3] ),
    .C(net287),
    .D(_0232_),
    .Y(_0031_));
 sky130_fd_sc_hd__nor4_2 _0884_ (.A(\wr_wptr[2] ),
    .B(\wr_wptr[3] ),
    .C(net287),
    .D(_0221_),
    .Y(_0030_));
 sky130_fd_sc_hd__nor4_2 _0885_ (.A(\wr_wptr[2] ),
    .B(\wr_wptr[3] ),
    .C(net287),
    .D(_0222_),
    .Y(_0029_));
 sky130_fd_sc_hd__nor4_2 _0886_ (.A(\wr_wptr[2] ),
    .B(\wr_wptr[3] ),
    .C(net287),
    .D(_0228_),
    .Y(_0022_));
 sky130_fd_sc_hd__nand2_1 _0887_ (.A(_0054_),
    .B(_0226_),
    .Y(_0233_));
 sky130_fd_sc_hd__nor2_4 _0888_ (.A(_0230_),
    .B(_0233_),
    .Y(_0021_));
 sky130_fd_sc_hd__nor2_4 _0889_ (.A(_0227_),
    .B(_0230_),
    .Y(_0020_));
 sky130_fd_sc_hd__nand2_1 _0890_ (.A(_0055_),
    .B(_0226_),
    .Y(_0234_));
 sky130_fd_sc_hd__nand2b_1 _0891_ (.A_N(\rd_wptr[3] ),
    .B(\rd_wptr[2] ),
    .Y(_0235_));
 sky130_fd_sc_hd__nor2_4 _0892_ (.A(_0234_),
    .B(_0235_),
    .Y(_0019_));
 sky130_fd_sc_hd__nand2_1 _0893_ (.A(\rd_wptr[2] ),
    .B(\rd_wptr[3] ),
    .Y(_0236_));
 sky130_fd_sc_hd__nor2_4 _0894_ (.A(_0234_),
    .B(_0236_),
    .Y(_0012_));
 sky130_fd_sc_hd__nor2_4 _0895_ (.A(_0229_),
    .B(_0236_),
    .Y(_0011_));
 sky130_fd_sc_hd__nor2_4 _0896_ (.A(_0233_),
    .B(_0236_),
    .Y(_0010_));
 sky130_fd_sc_hd__nor2_4 _0897_ (.A(_0227_),
    .B(_0236_),
    .Y(_0009_));
 sky130_fd_sc_hd__nor2_4 _0898_ (.A(_0229_),
    .B(_0235_),
    .Y(_0018_));
 sky130_fd_sc_hd__nor2_4 _0899_ (.A(_0230_),
    .B(_0234_),
    .Y(_0008_));
 sky130_fd_sc_hd__nor2_4 _0900_ (.A(_0233_),
    .B(_0235_),
    .Y(_0017_));
 sky130_fd_sc_hd__nor2_4 _0901_ (.A(_0227_),
    .B(_0235_),
    .Y(_0016_));
 sky130_fd_sc_hd__nor3_2 _0902_ (.A(\rd_wptr[2] ),
    .B(\rd_wptr[3] ),
    .C(_0234_),
    .Y(_0015_));
 sky130_fd_sc_hd__nor3_2 _0903_ (.A(\rd_wptr[2] ),
    .B(\rd_wptr[3] ),
    .C(_0229_),
    .Y(_0014_));
 sky130_fd_sc_hd__nor3_2 _0904_ (.A(\rd_wptr[2] ),
    .B(\rd_wptr[3] ),
    .C(_0233_),
    .Y(_0013_));
 sky130_fd_sc_hd__nor2_1 _0905_ (.A(\wr_wptr[2] ),
    .B(net287),
    .Y(_0237_));
 sky130_fd_sc_hd__nand2_1 _0906_ (.A(\wr_wptr[3] ),
    .B(_0237_),
    .Y(_0238_));
 sky130_fd_sc_hd__nor2_4 _0907_ (.A(_0232_),
    .B(_0238_),
    .Y(_0024_));
 sky130_fd_sc_hd__nor2_4 _0908_ (.A(_0221_),
    .B(_0238_),
    .Y(_0023_));
 sky130_fd_sc_hd__nor2_4 _0909_ (.A(_0222_),
    .B(_0238_),
    .Y(_0037_));
 sky130_fd_sc_hd__nor2_4 _0910_ (.A(_0228_),
    .B(_0238_),
    .Y(_0036_));
 sky130_fd_sc_hd__nor2_4 _0911_ (.A(_0220_),
    .B(_0232_),
    .Y(_0035_));
 sky130_fd_sc_hd__nand3_1 _0912_ (.A(\wr_wptr[2] ),
    .B(\wr_wptr[3] ),
    .C(_0218_),
    .Y(_0239_));
 sky130_fd_sc_hd__nor2_4 _0913_ (.A(_0228_),
    .B(_0239_),
    .Y(_0025_));
 sky130_fd_sc_hd__nor2_4 _0914_ (.A(_0222_),
    .B(_0239_),
    .Y(_0026_));
 sky130_fd_sc_hd__nor2_4 _0915_ (.A(_0221_),
    .B(_0239_),
    .Y(_0027_));
 sky130_fd_sc_hd__nor2_4 _0916_ (.A(_0232_),
    .B(_0239_),
    .Y(_0028_));
 sky130_fd_sc_hd__nor2_1 _0917_ (.A(net9),
    .B(net10),
    .Y(_0240_));
 sky130_fd_sc_hd__a21oi_1 _0918_ (.A1(_0089_),
    .A2(_0240_),
    .B1(_0087_),
    .Y(_0241_));
 sky130_fd_sc_hd__or3_1 _0919_ (.A(net15),
    .B(net14),
    .C(net13),
    .X(_0242_));
 sky130_fd_sc_hd__or3_1 _0920_ (.A(net16),
    .B(_0241_),
    .C(_0242_),
    .X(_0243_));
 sky130_fd_sc_hd__and2_1 _0921_ (.A(\wr_state[0] ),
    .B(_0243_),
    .X(_0244_));
 sky130_fd_sc_hd__a21oi_1 _0922_ (.A1(_0208_),
    .A2(_0209_),
    .B1(_0203_),
    .Y(_0245_));
 sky130_fd_sc_hd__nor3_1 _0923_ (.A(_0210_),
    .B(_0204_),
    .C(_0206_),
    .Y(_0246_));
 sky130_fd_sc_hd__o41a_4 _0924_ (.A1(_0245_),
    .A2(_0246_),
    .A3(_0214_),
    .A4(_0217_),
    .B1(net22),
    .X(_0247_));
 sky130_fd_sc_hd__nand2_1 _0925_ (.A(_0244_),
    .B(_0247_),
    .Y(_0248_));
 sky130_fd_sc_hd__nor4_1 _0929_ (.A(\wr_lat_ctr[3] ),
    .B(\wr_lat_ctr[5] ),
    .C(\wr_lat_ctr[4] ),
    .D(\wr_lat_ctr[6] ),
    .Y(_0252_));
 sky130_fd_sc_hd__nand2b_1 _0930_ (.A_N(\wr_lat_ctr[2] ),
    .B(_0092_),
    .Y(_0253_));
 sky130_fd_sc_hd__nor2_1 _0932_ (.A(\wr_lat_ctr[7] ),
    .B(_0253_),
    .Y(_0255_));
 sky130_fd_sc_hd__nand2_1 _0933_ (.A(_0252_),
    .B(_0255_),
    .Y(_0256_));
 sky130_fd_sc_hd__nand2_1 _0934_ (.A(\wr_state[2] ),
    .B(_0256_),
    .Y(_0257_));
 sky130_fd_sc_hd__nand2_1 _0935_ (.A(_0248_),
    .B(_0257_),
    .Y(_0005_));
 sky130_fd_sc_hd__nand2_1 _0937_ (.A(\wr_state[0] ),
    .B(_0247_),
    .Y(_0259_));
 sky130_fd_sc_hd__nand3_1 _0938_ (.A(\wr_state[2] ),
    .B(_0252_),
    .C(_0255_),
    .Y(_0260_));
 sky130_fd_sc_hd__nand2b_1 _0939_ (.A_N(_0095_),
    .B(net95),
    .Y(_0261_));
 sky130_fd_sc_hd__o211ai_1 _0940_ (.A1(_0243_),
    .A2(_0259_),
    .B1(_0260_),
    .C1(_0261_),
    .Y(_0004_));
 sky130_fd_sc_hd__inv_1 _0941_ (.A(\wr_state[0] ),
    .Y(_0262_));
 sky130_fd_sc_hd__nand2_1 _0942_ (.A(_0095_),
    .B(net95),
    .Y(_0263_));
 sky130_fd_sc_hd__o21ai_0 _0943_ (.A1(_0262_),
    .A2(_0247_),
    .B1(_0263_),
    .Y(_0003_));
 sky130_fd_sc_hd__nor3b_1 _0944_ (.A(net1),
    .B(net2),
    .C_N(_0101_),
    .Y(_0264_));
 sky130_fd_sc_hd__nor4_1 _0945_ (.A(net8),
    .B(net7),
    .C(net5),
    .D(net6),
    .Y(_0265_));
 sky130_fd_sc_hd__o21ai_0 _0946_ (.A1(_0099_),
    .A2(_0264_),
    .B1(_0265_),
    .Y(_0266_));
 sky130_fd_sc_hd__nand3_1 _0947_ (.A(\rd_state[0] ),
    .B(net21),
    .C(_0266_),
    .Y(_0267_));
 sky130_fd_sc_hd__or3b_4 _0948_ (.A(\rd_lat_ctr[2] ),
    .B(\rd_lat_ctr[3] ),
    .C_N(_0104_),
    .X(_0268_));
 sky130_fd_sc_hd__or3_4 _0949_ (.A(\rd_lat_ctr[5] ),
    .B(\rd_lat_ctr[4] ),
    .C(_0268_),
    .X(_0269_));
 sky130_fd_sc_hd__o31ai_1 _0952_ (.A1(\rd_lat_ctr[7] ),
    .A2(\rd_lat_ctr[6] ),
    .A3(_0269_),
    .B1(\rd_state[2] ),
    .Y(_0272_));
 sky130_fd_sc_hd__nand2_1 _0953_ (.A(_0267_),
    .B(_0272_),
    .Y(_0002_));
 sky130_fd_sc_hd__nand2_1 _0954_ (.A(\rd_state[0] ),
    .B(net21),
    .Y(_0273_));
 sky130_fd_sc_hd__inv_1 _0955_ (.A(_0082_),
    .Y(_0274_));
 sky130_fd_sc_hd__nor4b_4 _0956_ (.A(\rd_lat_ctr[7] ),
    .B(\rd_lat_ctr[6] ),
    .C(_0269_),
    .D_N(\rd_state[2] ),
    .Y(_0275_));
 sky130_fd_sc_hd__a21oi_1 _0957_ (.A1(rd_capture_valid),
    .A2(_0274_),
    .B1(_0275_),
    .Y(_0276_));
 sky130_fd_sc_hd__o21ai_0 _0958_ (.A1(_0266_),
    .A2(_0273_),
    .B1(_0276_),
    .Y(_0001_));
 sky130_fd_sc_hd__inv_1 _0959_ (.A(\rd_state[0] ),
    .Y(_0277_));
 sky130_fd_sc_hd__nand2_1 _0960_ (.A(rd_capture_valid),
    .B(_0082_),
    .Y(_0278_));
 sky130_fd_sc_hd__o21ai_0 _0961_ (.A1(_0277_),
    .A2(net21),
    .B1(_0278_),
    .Y(_0000_));
 sky130_fd_sc_hd__inv_1 _0962_ (.A(net11),
    .Y(_0085_));
 sky130_fd_sc_hd__inv_1 _0963_ (.A(\wr_lat_ctr[0] ),
    .Y(_0090_));
 sky130_fd_sc_hd__inv_1 _0964_ (.A(net3),
    .Y(_0097_));
 sky130_fd_sc_hd__inv_1 _0965_ (.A(\rd_lat_ctr[0] ),
    .Y(_0102_));
 sky130_fd_sc_hd__inv_1 _0966_ (.A(\wr_wptr[0] ),
    .Y(_0040_));
 sky130_fd_sc_hd__inv_1 _0967_ (.A(\rd_wptr[0] ),
    .Y(_0049_));
 sky130_fd_sc_hd__inv_1 _0968_ (.A(\rd_burst_ctr[0] ),
    .Y(_0078_));
 sky130_fd_sc_hd__inv_1 _0969_ (.A(\wr_wptr[1] ),
    .Y(_0041_));
 sky130_fd_sc_hd__inv_1 _0970_ (.A(\rd_wptr[1] ),
    .Y(_0050_));
 sky130_fd_sc_hd__inv_1 _0973_ (.A(\wr_rptr[1] ),
    .Y(_0058_));
 sky130_fd_sc_hd__inv_2 _0974_ (.A(\wr_rptr[3] ),
    .Y(_0281_));
 sky130_fd_sc_hd__inv_1 _0977_ (.A(\wr_rptr[2] ),
    .Y(_0064_));
 sky130_fd_sc_hd__inv_1 _0980_ (.A(\rd_rptr[1] ),
    .Y(_0069_));
 sky130_fd_sc_hd__inv_1 _0982_ (.A(\rd_rptr[2] ),
    .Y(_0072_));
 sky130_fd_sc_hd__inv_2 _0983_ (.A(\rd_rptr[3] ),
    .Y(_0286_));
 sky130_fd_sc_hd__inv_1 _0985_ (.A(\rd_burst_ctr[1] ),
    .Y(_0079_));
 sky130_fd_sc_hd__inv_1 _0986_ (.A(net12),
    .Y(_0086_));
 sky130_fd_sc_hd__inv_1 _0987_ (.A(\wr_lat_ctr[1] ),
    .Y(_0091_));
 sky130_fd_sc_hd__inv_1 _0988_ (.A(\wr_burst_ctr[1] ),
    .Y(_0094_));
 sky130_fd_sc_hd__inv_1 _0989_ (.A(net4),
    .Y(_0098_));
 sky130_fd_sc_hd__inv_1 _0990_ (.A(\rd_lat_ctr[1] ),
    .Y(_0103_));
 sky130_fd_sc_hd__mux2_2 _0991_ (.A0(net17),
    .A1(\rd_aux_r[0] ),
    .S(_0273_),
    .X(_0106_));
 sky130_fd_sc_hd__mux2_2 _0992_ (.A0(net18),
    .A1(\rd_aux_r[1] ),
    .S(_0273_),
    .X(_0107_));
 sky130_fd_sc_hd__mux2_2 _0993_ (.A0(net19),
    .A1(\rd_aux_r[2] ),
    .S(_0273_),
    .X(_0108_));
 sky130_fd_sc_hd__mux2_2 _0994_ (.A0(net20),
    .A1(\rd_aux_r[3] ),
    .S(_0273_),
    .X(_0109_));
 sky130_fd_sc_hd__inv_1 _0995_ (.A(net21),
    .Y(_0287_));
 sky130_fd_sc_hd__o21ai_0 _0996_ (.A1(_0287_),
    .A2(_0266_),
    .B1(\rd_state[0] ),
    .Y(_0288_));
 sky130_fd_sc_hd__nand3_1 _0997_ (.A(_0274_),
    .B(_0078_),
    .C(_0288_),
    .Y(_0289_));
 sky130_fd_sc_hd__o21ai_0 _0998_ (.A1(_0274_),
    .A2(_0078_),
    .B1(_0289_),
    .Y(_0290_));
 sky130_fd_sc_hd__o31ai_1 _0999_ (.A1(rd_capture_valid),
    .A2(\rd_state[0] ),
    .A3(\rd_state[2] ),
    .B1(_0288_),
    .Y(_0291_));
 sky130_fd_sc_hd__a22o_1 _1000_ (.A1(rd_capture_valid),
    .A2(_0290_),
    .B1(_0291_),
    .B2(\rd_burst_ctr[0] ),
    .X(_0110_));
 sky130_fd_sc_hd__nand2_1 _1001_ (.A(_0081_),
    .B(_0288_),
    .Y(_0292_));
 sky130_fd_sc_hd__nand2_1 _1002_ (.A(_0082_),
    .B(\rd_burst_ctr[1] ),
    .Y(_0293_));
 sky130_fd_sc_hd__o21ai_0 _1003_ (.A1(_0082_),
    .A2(_0292_),
    .B1(_0293_),
    .Y(_0294_));
 sky130_fd_sc_hd__a22o_1 _1004_ (.A1(\rd_burst_ctr[1] ),
    .A2(_0291_),
    .B1(_0294_),
    .B2(rd_capture_valid),
    .X(_0111_));
 sky130_fd_sc_hd__nand2_1 _1005_ (.A(\rd_state[2] ),
    .B(\rd_lat_ctr[0] ),
    .Y(_0295_));
 sky130_fd_sc_hd__o21ai_0 _1006_ (.A1(\rd_state[2] ),
    .A2(_0097_),
    .B1(_0295_),
    .Y(_0296_));
 sky130_fd_sc_hd__nor2b_1 _1007_ (.A(\rd_state[0] ),
    .B_N(\rd_state[2] ),
    .Y(_0297_));
 sky130_fd_sc_hd__a31oi_1 _1008_ (.A1(\rd_state[0] ),
    .A2(net21),
    .A3(_0266_),
    .B1(_0297_),
    .Y(_0298_));
 sky130_fd_sc_hd__or2_2 _1009_ (.A(_0275_),
    .B(_0298_),
    .X(_0299_));
 sky130_fd_sc_hd__nand2_1 _1010_ (.A(\rd_lat_ctr[0] ),
    .B(_0299_),
    .Y(_0300_));
 sky130_fd_sc_hd__o21ai_0 _1011_ (.A1(_0296_),
    .A2(_0299_),
    .B1(_0300_),
    .Y(_0112_));
 sky130_fd_sc_hd__nor2_1 _1012_ (.A(_0275_),
    .B(_0298_),
    .Y(_0301_));
 sky130_fd_sc_hd__mux2i_1 _1013_ (.A0(_0100_),
    .A1(_0105_),
    .S(\rd_state[2] ),
    .Y(_0302_));
 sky130_fd_sc_hd__nand2_1 _1014_ (.A(_0301_),
    .B(_0302_),
    .Y(_0303_));
 sky130_fd_sc_hd__o21ai_0 _1015_ (.A1(_0103_),
    .A2(_0301_),
    .B1(_0303_),
    .Y(_0113_));
 sky130_fd_sc_hd__xor2_1 _1016_ (.A(net5),
    .B(_0099_),
    .X(_0304_));
 sky130_fd_sc_hd__nand3_1 _1017_ (.A(\rd_state[2] ),
    .B(\rd_lat_ctr[2] ),
    .C(_0104_),
    .Y(_0305_));
 sky130_fd_sc_hd__o21ai_0 _1018_ (.A1(\rd_state[2] ),
    .A2(_0304_),
    .B1(_0305_),
    .Y(_0306_));
 sky130_fd_sc_hd__nand2b_1 _1019_ (.A_N(_0104_),
    .B(\rd_state[2] ),
    .Y(_0307_));
 sky130_fd_sc_hd__a21oi_1 _1020_ (.A1(_0301_),
    .A2(_0307_),
    .B1(\rd_lat_ctr[2] ),
    .Y(_0308_));
 sky130_fd_sc_hd__a21oi_1 _1021_ (.A1(_0301_),
    .A2(_0306_),
    .B1(_0308_),
    .Y(_0114_));
 sky130_fd_sc_hd__nor3_1 _1022_ (.A(\rd_lat_ctr[2] ),
    .B(\rd_lat_ctr[1] ),
    .C(\rd_lat_ctr[0] ),
    .Y(_0309_));
 sky130_fd_sc_hd__nand3_1 _1023_ (.A(\rd_lat_ctr[3] ),
    .B(_0301_),
    .C(_0309_),
    .Y(_0310_));
 sky130_fd_sc_hd__o21ai_0 _1024_ (.A1(\rd_lat_ctr[3] ),
    .A2(_0309_),
    .B1(_0310_),
    .Y(_0311_));
 sky130_fd_sc_hd__nor2_1 _1025_ (.A(\rd_state[2] ),
    .B(_0267_),
    .Y(_0312_));
 sky130_fd_sc_hd__nor3_1 _1026_ (.A(net5),
    .B(net4),
    .C(net3),
    .Y(_0313_));
 sky130_fd_sc_hd__xnor2_1 _1027_ (.A(net6),
    .B(_0313_),
    .Y(_0314_));
 sky130_fd_sc_hd__nor2_1 _1028_ (.A(\rd_lat_ctr[3] ),
    .B(_0301_),
    .Y(_0315_));
 sky130_fd_sc_hd__a221oi_1 _1029_ (.A1(\rd_state[2] ),
    .A2(_0311_),
    .B1(_0312_),
    .B2(_0314_),
    .C1(_0315_),
    .Y(_0115_));
 sky130_fd_sc_hd__nor2_1 _1030_ (.A(_0268_),
    .B(_0299_),
    .Y(_0316_));
 sky130_fd_sc_hd__mux2_2 _1031_ (.A0(_0268_),
    .A1(_0316_),
    .S(\rd_lat_ctr[4] ),
    .X(_0317_));
 sky130_fd_sc_hd__nor2_1 _1032_ (.A(net5),
    .B(net6),
    .Y(_0318_));
 sky130_fd_sc_hd__nand2_1 _1033_ (.A(_0099_),
    .B(_0318_),
    .Y(_0319_));
 sky130_fd_sc_hd__xor2_1 _1034_ (.A(net7),
    .B(_0319_),
    .X(_0320_));
 sky130_fd_sc_hd__nor2_1 _1035_ (.A(\rd_lat_ctr[4] ),
    .B(_0301_),
    .Y(_0321_));
 sky130_fd_sc_hd__a221oi_2 _1036_ (.A1(\rd_state[2] ),
    .A2(_0317_),
    .B1(_0320_),
    .B2(_0312_),
    .C1(_0321_),
    .Y(_0116_));
 sky130_fd_sc_hd__nor3b_1 _1037_ (.A(\rd_lat_ctr[3] ),
    .B(\rd_lat_ctr[4] ),
    .C_N(_0309_),
    .Y(_0322_));
 sky130_fd_sc_hd__nand3_1 _1038_ (.A(\rd_lat_ctr[5] ),
    .B(_0301_),
    .C(_0322_),
    .Y(_0323_));
 sky130_fd_sc_hd__o21ai_0 _1039_ (.A1(\rd_lat_ctr[5] ),
    .A2(_0322_),
    .B1(_0323_),
    .Y(_0324_));
 sky130_fd_sc_hd__nor4b_1 _1040_ (.A(net7),
    .B(net4),
    .C(net3),
    .D_N(_0318_),
    .Y(_0325_));
 sky130_fd_sc_hd__xor2_1 _1041_ (.A(net8),
    .B(_0325_),
    .X(_0326_));
 sky130_fd_sc_hd__or3_1 _1042_ (.A(\rd_state[2] ),
    .B(_0267_),
    .C(_0326_),
    .X(_0327_));
 sky130_fd_sc_hd__o21ai_0 _1043_ (.A1(\rd_lat_ctr[5] ),
    .A2(_0301_),
    .B1(_0327_),
    .Y(_0328_));
 sky130_fd_sc_hd__a21oi_1 _1044_ (.A1(\rd_state[2] ),
    .A2(_0324_),
    .B1(_0328_),
    .Y(_0117_));
 sky130_fd_sc_hd__nor3_1 _1045_ (.A(\rd_lat_ctr[5] ),
    .B(\rd_lat_ctr[4] ),
    .C(_0268_),
    .Y(_0329_));
 sky130_fd_sc_hd__nand2_1 _1046_ (.A(_0329_),
    .B(_0301_),
    .Y(_0330_));
 sky130_fd_sc_hd__nand2_1 _1047_ (.A(\rd_lat_ctr[6] ),
    .B(_0269_),
    .Y(_0331_));
 sky130_fd_sc_hd__o21ai_0 _1048_ (.A1(\rd_lat_ctr[6] ),
    .A2(_0330_),
    .B1(_0331_),
    .Y(_0332_));
 sky130_fd_sc_hd__a22o_1 _1049_ (.A1(\rd_lat_ctr[6] ),
    .A2(_0299_),
    .B1(_0332_),
    .B2(\rd_state[2] ),
    .X(_0118_));
 sky130_fd_sc_hd__nor2_1 _1050_ (.A(\rd_lat_ctr[5] ),
    .B(\rd_lat_ctr[6] ),
    .Y(_0333_));
 sky130_fd_sc_hd__nand2_1 _1051_ (.A(_0322_),
    .B(_0333_),
    .Y(_0334_));
 sky130_fd_sc_hd__a2111oi_0 _1052_ (.A1(\rd_state[0] ),
    .A2(_0267_),
    .B1(_0329_),
    .C1(_0334_),
    .D1(\rd_lat_ctr[7] ),
    .Y(_0335_));
 sky130_fd_sc_hd__a21o_1 _1053_ (.A1(\rd_lat_ctr[7] ),
    .A2(_0334_),
    .B1(_0335_),
    .X(_0336_));
 sky130_fd_sc_hd__a22o_1 _1054_ (.A1(\rd_lat_ctr[7] ),
    .A2(_0298_),
    .B1(_0336_),
    .B2(\rd_state[2] ),
    .X(_0119_));
 sky130_fd_sc_hd__xnor2_1 _1055_ (.A(\rd_rptr[4] ),
    .B(\rd_wptr[4] ),
    .Y(_0337_));
 sky130_fd_sc_hd__nor2b_1 _1056_ (.A(_0077_),
    .B_N(_0076_),
    .Y(_0338_));
 sky130_fd_sc_hd__inv_1 _1057_ (.A(_0067_),
    .Y(_0339_));
 sky130_fd_sc_hd__a21o_1 _1058_ (.A1(_0339_),
    .A2(_0071_),
    .B1(_0070_),
    .X(_0340_));
 sky130_fd_sc_hd__a21oi_1 _1059_ (.A1(_0074_),
    .A2(_0340_),
    .B1(_0073_),
    .Y(_0341_));
 sky130_fd_sc_hd__mux2i_1 _1060_ (.A0(_0077_),
    .A1(_0338_),
    .S(_0341_),
    .Y(_0342_));
 sky130_fd_sc_hd__nor2_1 _1061_ (.A(_0077_),
    .B(_0076_),
    .Y(_0343_));
 sky130_fd_sc_hd__a21oi_1 _1062_ (.A1(_0341_),
    .A2(_0343_),
    .B1(_0337_),
    .Y(_0344_));
 sky130_fd_sc_hd__nand2b_1 _1063_ (.A_N(_0070_),
    .B(_0067_),
    .Y(_0345_));
 sky130_fd_sc_hd__xnor2_1 _1064_ (.A(_0074_),
    .B(_0345_),
    .Y(_0346_));
 sky130_fd_sc_hd__nand3_1 _1065_ (.A(_0068_),
    .B(_0071_),
    .C(_0346_),
    .Y(_0347_));
 sky130_fd_sc_hd__a211o_1 _1066_ (.A1(_0337_),
    .A2(_0342_),
    .B1(_0344_),
    .C1(_0347_),
    .X(net134));
 sky130_fd_sc_hd__xor2_1 _1070_ (.A(net),
    .B(net134),
    .X(_0120_));
 sky130_fd_sc_hd__nand2_1 _1071_ (.A(_0048_),
    .B(net134),
    .Y(_0351_));
 sky130_fd_sc_hd__o21ai_0 _1072_ (.A1(_0069_),
    .A2(net134),
    .B1(_0351_),
    .Y(_0121_));
 sky130_fd_sc_hd__nand2_1 _1073_ (.A(_0047_),
    .B(net134),
    .Y(_0352_));
 sky130_fd_sc_hd__xnor2_1 _1074_ (.A(\rd_rptr[2] ),
    .B(_0352_),
    .Y(_0122_));
 sky130_fd_sc_hd__nand4_1 _1075_ (.A(\rd_rptr[2] ),
    .B(\rd_rptr[1] ),
    .C(net),
    .D(net134),
    .Y(_0353_));
 sky130_fd_sc_hd__xnor2_1 _1076_ (.A(\rd_rptr[3] ),
    .B(_0353_),
    .Y(_0123_));
 sky130_fd_sc_hd__nand4_1 _1077_ (.A(_0047_),
    .B(\rd_rptr[2] ),
    .C(\rd_rptr[3] ),
    .D(net134),
    .Y(_0354_));
 sky130_fd_sc_hd__xnor2_1 _1078_ (.A(\rd_rptr[4] ),
    .B(_0354_),
    .Y(_0124_));
 sky130_fd_sc_hd__nand3_1 _1079_ (.A(rd_capture_valid),
    .B(_0274_),
    .C(_0080_),
    .Y(_0355_));
 sky130_fd_sc_hd__xor2_1 _1081_ (.A(_0084_),
    .B(_0083_),
    .X(_0357_));
 sky130_fd_sc_hd__nor4_2 _1082_ (.A(\rd_burst_ctr[0] ),
    .B(_0081_),
    .C(net307),
    .D(_0357_),
    .Y(_0358_));
 sky130_fd_sc_hd__a22o_1 _1084_ (.A1(\rd_shift_r[0] ),
    .A2(net307),
    .B1(net288),
    .B2(net23),
    .X(_0125_));
 sky130_fd_sc_hd__a22o_1 _1085_ (.A1(\rd_shift_r[10] ),
    .A2(net307),
    .B1(net288),
    .B2(net24),
    .X(_0126_));
 sky130_fd_sc_hd__a22o_1 _1086_ (.A1(\rd_shift_r[11] ),
    .A2(net307),
    .B1(net288),
    .B2(net25),
    .X(_0127_));
 sky130_fd_sc_hd__a22o_1 _1087_ (.A1(\rd_shift_r[12] ),
    .A2(net307),
    .B1(net288),
    .B2(net26),
    .X(_0128_));
 sky130_fd_sc_hd__a22o_1 _1088_ (.A1(\rd_shift_r[13] ),
    .A2(net307),
    .B1(net288),
    .B2(net27),
    .X(_0129_));
 sky130_fd_sc_hd__a22o_1 _1089_ (.A1(\rd_shift_r[14] ),
    .A2(net307),
    .B1(net288),
    .B2(net28),
    .X(_0130_));
 sky130_fd_sc_hd__a22o_1 _1090_ (.A1(\rd_shift_r[15] ),
    .A2(net307),
    .B1(net288),
    .B2(net29),
    .X(_0131_));
 sky130_fd_sc_hd__a22o_1 _1091_ (.A1(\rd_shift_r[1] ),
    .A2(net307),
    .B1(net288),
    .B2(net30),
    .X(_0132_));
 sky130_fd_sc_hd__a22o_1 _1092_ (.A1(\rd_shift_r[2] ),
    .A2(net307),
    .B1(net288),
    .B2(net31),
    .X(_0133_));
 sky130_fd_sc_hd__a22o_1 _1093_ (.A1(\rd_shift_r[3] ),
    .A2(net307),
    .B1(net288),
    .B2(net32),
    .X(_0134_));
 sky130_fd_sc_hd__a22o_1 _1094_ (.A1(\rd_shift_r[4] ),
    .A2(net307),
    .B1(net288),
    .B2(net33),
    .X(_0135_));
 sky130_fd_sc_hd__a22o_1 _1095_ (.A1(\rd_shift_r[5] ),
    .A2(net307),
    .B1(net288),
    .B2(net34),
    .X(_0136_));
 sky130_fd_sc_hd__a22o_1 _1096_ (.A1(\rd_shift_r[6] ),
    .A2(net307),
    .B1(net288),
    .B2(net35),
    .X(_0137_));
 sky130_fd_sc_hd__a22o_1 _1097_ (.A1(\rd_shift_r[7] ),
    .A2(net307),
    .B1(net288),
    .B2(net36),
    .X(_0138_));
 sky130_fd_sc_hd__a22o_1 _1098_ (.A1(\rd_shift_r[8] ),
    .A2(net307),
    .B1(net288),
    .B2(net37),
    .X(_0139_));
 sky130_fd_sc_hd__a22o_1 _1099_ (.A1(\rd_shift_r[9] ),
    .A2(net307),
    .B1(net288),
    .B2(net38),
    .X(_0140_));
 sky130_fd_sc_hd__xnor2_1 _1100_ (.A(\rd_wptr[0] ),
    .B(_0278_),
    .Y(_0141_));
 sky130_fd_sc_hd__mux2_2 _1101_ (.A0(_0052_),
    .A1(\rd_wptr[1] ),
    .S(_0278_),
    .X(_0142_));
 sky130_fd_sc_hd__nand3_1 _1102_ (.A(_0055_),
    .B(rd_capture_valid),
    .C(_0082_),
    .Y(_0360_));
 sky130_fd_sc_hd__xnor2_1 _1103_ (.A(\rd_wptr[2] ),
    .B(_0360_),
    .Y(_0143_));
 sky130_fd_sc_hd__nand3_1 _1104_ (.A(\rd_wptr[2] ),
    .B(\rd_wptr[1] ),
    .C(\rd_wptr[0] ),
    .Y(_0361_));
 sky130_fd_sc_hd__nor2_1 _1105_ (.A(_0278_),
    .B(_0361_),
    .Y(_0362_));
 sky130_fd_sc_hd__xor2_1 _1106_ (.A(\rd_wptr[3] ),
    .B(_0362_),
    .X(_0144_));
 sky130_fd_sc_hd__nor2_1 _1107_ (.A(_0236_),
    .B(_0360_),
    .Y(_0363_));
 sky130_fd_sc_hd__xor2_1 _1108_ (.A(\rd_wptr[4] ),
    .B(_0363_),
    .X(_0145_));
 sky130_fd_sc_hd__nor3_1 _1109_ (.A(net95),
    .B(\wr_state[0] ),
    .C(\wr_state[2] ),
    .Y(_0364_));
 sky130_fd_sc_hd__nand2_1 _1110_ (.A(\wr_burst_ctr[0] ),
    .B(_0364_),
    .Y(_0365_));
 sky130_fd_sc_hd__nand3_1 _1112_ (.A(_0095_),
    .B(net95),
    .C(\wr_burst_ctr[0] ),
    .Y(_0367_));
 sky130_fd_sc_hd__o311ai_0 _1113_ (.A1(\wr_state[0] ),
    .A2(\wr_burst_ctr[0] ),
    .A3(_0261_),
    .B1(_0365_),
    .C1(_0367_),
    .Y(_0368_));
 sky130_fd_sc_hd__nand2b_1 _1114_ (.A_N(_0243_),
    .B(_0247_),
    .Y(_0369_));
 sky130_fd_sc_hd__nor3_1 _1115_ (.A(\wr_burst_ctr[0] ),
    .B(_0261_),
    .C(_0369_),
    .Y(_0370_));
 sky130_fd_sc_hd__nand3_1 _1116_ (.A(\wr_state[0] ),
    .B(\wr_burst_ctr[0] ),
    .C(_0369_),
    .Y(_0371_));
 sky130_fd_sc_hd__or3b_2 _1117_ (.A(_0368_),
    .B(_0370_),
    .C_N(_0371_),
    .X(_0146_));
 sky130_fd_sc_hd__nand4bb_1 _1118_ (.A_N(_0244_),
    .B_N(_0364_),
    .C(_0247_),
    .D(_0263_),
    .Y(_0372_));
 sky130_fd_sc_hd__inv_1 _1119_ (.A(\wr_state[2] ),
    .Y(_0373_));
 sky130_fd_sc_hd__o21ai_0 _1120_ (.A1(net95),
    .A2(_0373_),
    .B1(_0261_),
    .Y(_0374_));
 sky130_fd_sc_hd__a21oi_1 _1121_ (.A1(_0262_),
    .A2(_0374_),
    .B1(_0094_),
    .Y(_0375_));
 sky130_fd_sc_hd__a211oi_1 _1122_ (.A1(\wr_state[0] ),
    .A2(_0369_),
    .B1(_0261_),
    .C1(_0096_),
    .Y(_0376_));
 sky130_fd_sc_hd__a21o_1 _1123_ (.A1(_0372_),
    .A2(_0375_),
    .B1(_0376_),
    .X(_0147_));
 sky130_fd_sc_hd__mux4_2 _1127_ (.A0(\wr_buf[8][4] ),
    .A1(\wr_buf[9][4] ),
    .A2(\wr_buf[10][4] ),
    .A3(\wr_buf[11][4] ),
    .S0(net316),
    .S1(net314),
    .X(_0380_));
 sky130_fd_sc_hd__mux4_2 _1132_ (.A0(\wr_buf[0][4] ),
    .A1(\wr_buf[1][4] ),
    .A2(\wr_buf[2][4] ),
    .A3(\wr_buf[3][4] ),
    .S0(net316),
    .S1(net314),
    .X(_0385_));
 sky130_fd_sc_hd__mux4_2 _1135_ (.A0(\wr_buf[12][4] ),
    .A1(\wr_buf[13][4] ),
    .A2(\wr_buf[14][4] ),
    .A3(\wr_buf[15][4] ),
    .S0(net316),
    .S1(net314),
    .X(_0388_));
 sky130_fd_sc_hd__mux4_2 _1137_ (.A0(\wr_buf[4][4] ),
    .A1(\wr_buf[5][4] ),
    .A2(\wr_buf[6][4] ),
    .A3(\wr_buf[7][4] ),
    .S0(net316),
    .S1(net314),
    .X(_0390_));
 sky130_fd_sc_hd__mux4_2 _1138_ (.A0(_0380_),
    .A1(_0385_),
    .A2(_0388_),
    .A3(_0390_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0391_));
 sky130_fd_sc_hd__and2_4 _1139_ (.A(\wr_state[0] ),
    .B(_0247_),
    .X(_0392_));
 sky130_fd_sc_hd__mux2_4 _1142_ (.A0(\wr_dat_r[0] ),
    .A1(_0391_),
    .S(net282),
    .X(_0148_));
 sky130_fd_sc_hd__mux4_2 _1143_ (.A0(\wr_buf[8][14] ),
    .A1(\wr_buf[9][14] ),
    .A2(\wr_buf[10][14] ),
    .A3(\wr_buf[11][14] ),
    .S0(net315),
    .S1(net314),
    .X(_0395_));
 sky130_fd_sc_hd__mux4_2 _1144_ (.A0(\wr_buf[0][14] ),
    .A1(\wr_buf[1][14] ),
    .A2(\wr_buf[2][14] ),
    .A3(\wr_buf[3][14] ),
    .S0(net315),
    .S1(net314),
    .X(_0396_));
 sky130_fd_sc_hd__mux4_2 _1145_ (.A0(\wr_buf[12][14] ),
    .A1(\wr_buf[13][14] ),
    .A2(\wr_buf[14][14] ),
    .A3(\wr_buf[15][14] ),
    .S0(net315),
    .S1(net314),
    .X(_0397_));
 sky130_fd_sc_hd__mux4_2 _1146_ (.A0(\wr_buf[4][14] ),
    .A1(\wr_buf[5][14] ),
    .A2(\wr_buf[6][14] ),
    .A3(\wr_buf[7][14] ),
    .S0(net315),
    .S1(net314),
    .X(_0398_));
 sky130_fd_sc_hd__mux4_2 _1147_ (.A0(_0395_),
    .A1(_0396_),
    .A2(_0397_),
    .A3(_0398_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0399_));
 sky130_fd_sc_hd__mux2_4 _1148_ (.A0(\wr_dat_r[10] ),
    .A1(_0399_),
    .S(_0392_),
    .X(_0149_));
 sky130_fd_sc_hd__mux4_2 _1151_ (.A0(\wr_buf[8][15] ),
    .A1(\wr_buf[9][15] ),
    .A2(\wr_buf[10][15] ),
    .A3(\wr_buf[11][15] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0402_));
 sky130_fd_sc_hd__mux4_2 _1152_ (.A0(\wr_buf[0][15] ),
    .A1(\wr_buf[1][15] ),
    .A2(\wr_buf[2][15] ),
    .A3(\wr_buf[3][15] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0403_));
 sky130_fd_sc_hd__mux4_2 _1153_ (.A0(\wr_buf[12][15] ),
    .A1(\wr_buf[13][15] ),
    .A2(\wr_buf[14][15] ),
    .A3(\wr_buf[15][15] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0404_));
 sky130_fd_sc_hd__mux4_2 _1154_ (.A0(\wr_buf[4][15] ),
    .A1(\wr_buf[5][15] ),
    .A2(\wr_buf[6][15] ),
    .A3(\wr_buf[7][15] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0405_));
 sky130_fd_sc_hd__mux4_2 _1155_ (.A0(_0402_),
    .A1(_0403_),
    .A2(_0404_),
    .A3(_0405_),
    .S0(net310),
    .S1(net312),
    .X(_0406_));
 sky130_fd_sc_hd__mux2_4 _1156_ (.A0(\wr_dat_r[11] ),
    .A1(_0406_),
    .S(_0392_),
    .X(_0150_));
 sky130_fd_sc_hd__mux4_2 _1157_ (.A0(\wr_buf[8][16] ),
    .A1(\wr_buf[9][16] ),
    .A2(\wr_buf[10][16] ),
    .A3(\wr_buf[11][16] ),
    .S0(net316),
    .S1(net314),
    .X(_0407_));
 sky130_fd_sc_hd__mux4_2 _1158_ (.A0(\wr_buf[0][16] ),
    .A1(\wr_buf[1][16] ),
    .A2(\wr_buf[2][16] ),
    .A3(\wr_buf[3][16] ),
    .S0(net316),
    .S1(net314),
    .X(_0408_));
 sky130_fd_sc_hd__mux4_2 _1159_ (.A0(\wr_buf[12][16] ),
    .A1(\wr_buf[13][16] ),
    .A2(\wr_buf[14][16] ),
    .A3(\wr_buf[15][16] ),
    .S0(net316),
    .S1(net314),
    .X(_0409_));
 sky130_fd_sc_hd__mux4_2 _1160_ (.A0(\wr_buf[4][16] ),
    .A1(\wr_buf[5][16] ),
    .A2(\wr_buf[6][16] ),
    .A3(\wr_buf[7][16] ),
    .S0(net316),
    .S1(net314),
    .X(_0410_));
 sky130_fd_sc_hd__mux4_2 _1161_ (.A0(_0407_),
    .A1(_0408_),
    .A2(_0409_),
    .A3(_0410_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0411_));
 sky130_fd_sc_hd__mux2_4 _1162_ (.A0(\wr_dat_r[12] ),
    .A1(_0411_),
    .S(net282),
    .X(_0151_));
 sky130_fd_sc_hd__mux4_2 _1163_ (.A0(\wr_buf[8][17] ),
    .A1(\wr_buf[9][17] ),
    .A2(\wr_buf[10][17] ),
    .A3(\wr_buf[11][17] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0412_));
 sky130_fd_sc_hd__mux4_2 _1164_ (.A0(\wr_buf[0][17] ),
    .A1(\wr_buf[1][17] ),
    .A2(\wr_buf[2][17] ),
    .A3(\wr_buf[3][17] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0413_));
 sky130_fd_sc_hd__mux4_2 _1165_ (.A0(\wr_buf[12][17] ),
    .A1(\wr_buf[13][17] ),
    .A2(\wr_buf[14][17] ),
    .A3(\wr_buf[15][17] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0414_));
 sky130_fd_sc_hd__mux4_2 _1166_ (.A0(\wr_buf[4][17] ),
    .A1(\wr_buf[5][17] ),
    .A2(\wr_buf[6][17] ),
    .A3(\wr_buf[7][17] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0415_));
 sky130_fd_sc_hd__mux4_2 _1167_ (.A0(_0412_),
    .A1(_0413_),
    .A2(_0414_),
    .A3(_0415_),
    .S0(net310),
    .S1(net312),
    .X(_0416_));
 sky130_fd_sc_hd__mux2_4 _1168_ (.A0(\wr_dat_r[13] ),
    .A1(_0416_),
    .S(_0392_),
    .X(_0152_));
 sky130_fd_sc_hd__mux4_2 _1169_ (.A0(\wr_buf[8][18] ),
    .A1(\wr_buf[9][18] ),
    .A2(\wr_buf[10][18] ),
    .A3(\wr_buf[11][18] ),
    .S0(net316),
    .S1(net313),
    .X(_0417_));
 sky130_fd_sc_hd__mux4_2 _1170_ (.A0(\wr_buf[0][18] ),
    .A1(\wr_buf[1][18] ),
    .A2(\wr_buf[2][18] ),
    .A3(\wr_buf[3][18] ),
    .S0(net316),
    .S1(net313),
    .X(_0418_));
 sky130_fd_sc_hd__mux4_2 _1171_ (.A0(\wr_buf[12][18] ),
    .A1(\wr_buf[13][18] ),
    .A2(\wr_buf[14][18] ),
    .A3(\wr_buf[15][18] ),
    .S0(net316),
    .S1(net313),
    .X(_0419_));
 sky130_fd_sc_hd__mux4_2 _1172_ (.A0(\wr_buf[4][18] ),
    .A1(\wr_buf[5][18] ),
    .A2(\wr_buf[6][18] ),
    .A3(\wr_buf[7][18] ),
    .S0(net316),
    .S1(net313),
    .X(_0420_));
 sky130_fd_sc_hd__mux4_2 _1173_ (.A0(_0417_),
    .A1(_0418_),
    .A2(_0419_),
    .A3(_0420_),
    .S0(net310),
    .S1(net312),
    .X(_0421_));
 sky130_fd_sc_hd__mux2_4 _1175_ (.A0(\wr_dat_r[14] ),
    .A1(_0421_),
    .S(net282),
    .X(_0153_));
 sky130_fd_sc_hd__mux4_2 _1176_ (.A0(\wr_buf[8][19] ),
    .A1(\wr_buf[9][19] ),
    .A2(\wr_buf[10][19] ),
    .A3(\wr_buf[11][19] ),
    .S0(net316),
    .S1(net313),
    .X(_0423_));
 sky130_fd_sc_hd__mux4_2 _1177_ (.A0(\wr_buf[0][19] ),
    .A1(\wr_buf[1][19] ),
    .A2(\wr_buf[2][19] ),
    .A3(\wr_buf[3][19] ),
    .S0(net316),
    .S1(net313),
    .X(_0424_));
 sky130_fd_sc_hd__mux4_2 _1180_ (.A0(\wr_buf[12][19] ),
    .A1(\wr_buf[13][19] ),
    .A2(\wr_buf[14][19] ),
    .A3(\wr_buf[15][19] ),
    .S0(net316),
    .S1(net313),
    .X(_0427_));
 sky130_fd_sc_hd__mux4_2 _1181_ (.A0(\wr_buf[4][19] ),
    .A1(\wr_buf[5][19] ),
    .A2(\wr_buf[6][19] ),
    .A3(\wr_buf[7][19] ),
    .S0(net316),
    .S1(net313),
    .X(_0428_));
 sky130_fd_sc_hd__mux4_2 _1183_ (.A0(_0423_),
    .A1(_0424_),
    .A2(_0427_),
    .A3(_0428_),
    .S0(net310),
    .S1(net312),
    .X(_0430_));
 sky130_fd_sc_hd__mux2_4 _1184_ (.A0(\wr_dat_r[15] ),
    .A1(_0430_),
    .S(_0392_),
    .X(_0154_));
 sky130_fd_sc_hd__mux4_2 _1185_ (.A0(\wr_buf[8][20] ),
    .A1(\wr_buf[9][20] ),
    .A2(\wr_buf[10][20] ),
    .A3(\wr_buf[11][20] ),
    .S0(net316),
    .S1(net313),
    .X(_0431_));
 sky130_fd_sc_hd__mux4_2 _1186_ (.A0(\wr_buf[0][20] ),
    .A1(\wr_buf[1][20] ),
    .A2(\wr_buf[2][20] ),
    .A3(\wr_buf[3][20] ),
    .S0(net316),
    .S1(net313),
    .X(_0432_));
 sky130_fd_sc_hd__mux4_2 _1187_ (.A0(\wr_buf[12][20] ),
    .A1(\wr_buf[13][20] ),
    .A2(\wr_buf[14][20] ),
    .A3(\wr_buf[15][20] ),
    .S0(net316),
    .S1(net313),
    .X(_0433_));
 sky130_fd_sc_hd__mux4_2 _1188_ (.A0(\wr_buf[4][20] ),
    .A1(\wr_buf[5][20] ),
    .A2(\wr_buf[6][20] ),
    .A3(\wr_buf[7][20] ),
    .S0(net316),
    .S1(net313),
    .X(_0434_));
 sky130_fd_sc_hd__mux4_2 _1189_ (.A0(_0431_),
    .A1(_0432_),
    .A2(_0433_),
    .A3(_0434_),
    .S0(net310),
    .S1(net312),
    .X(_0435_));
 sky130_fd_sc_hd__mux2_4 _1190_ (.A0(\wr_dat_r[16] ),
    .A1(_0435_),
    .S(net282),
    .X(_0155_));
 sky130_fd_sc_hd__mux4_2 _1191_ (.A0(\wr_buf[8][21] ),
    .A1(\wr_buf[9][21] ),
    .A2(\wr_buf[10][21] ),
    .A3(\wr_buf[11][21] ),
    .S0(net316),
    .S1(net313),
    .X(_0436_));
 sky130_fd_sc_hd__mux4_2 _1192_ (.A0(\wr_buf[0][21] ),
    .A1(\wr_buf[1][21] ),
    .A2(\wr_buf[2][21] ),
    .A3(\wr_buf[3][21] ),
    .S0(net316),
    .S1(net313),
    .X(_0437_));
 sky130_fd_sc_hd__mux4_2 _1193_ (.A0(\wr_buf[12][21] ),
    .A1(\wr_buf[13][21] ),
    .A2(\wr_buf[14][21] ),
    .A3(\wr_buf[15][21] ),
    .S0(net316),
    .S1(net313),
    .X(_0438_));
 sky130_fd_sc_hd__mux4_2 _1196_ (.A0(\wr_buf[4][21] ),
    .A1(\wr_buf[5][21] ),
    .A2(\wr_buf[6][21] ),
    .A3(\wr_buf[7][21] ),
    .S0(net316),
    .S1(net313),
    .X(_0441_));
 sky130_fd_sc_hd__mux4_2 _1197_ (.A0(_0436_),
    .A1(_0437_),
    .A2(_0438_),
    .A3(_0441_),
    .S0(net310),
    .S1(net312),
    .X(_0442_));
 sky130_fd_sc_hd__mux2_4 _1198_ (.A0(\wr_dat_r[17] ),
    .A1(_0442_),
    .S(net282),
    .X(_0156_));
 sky130_fd_sc_hd__mux4_2 _1199_ (.A0(\wr_buf[8][22] ),
    .A1(\wr_buf[9][22] ),
    .A2(\wr_buf[10][22] ),
    .A3(\wr_buf[11][22] ),
    .S0(net316),
    .S1(net313),
    .X(_0443_));
 sky130_fd_sc_hd__mux4_2 _1200_ (.A0(\wr_buf[0][22] ),
    .A1(\wr_buf[1][22] ),
    .A2(\wr_buf[2][22] ),
    .A3(\wr_buf[3][22] ),
    .S0(net316),
    .S1(net313),
    .X(_0444_));
 sky130_fd_sc_hd__mux4_2 _1201_ (.A0(\wr_buf[12][22] ),
    .A1(\wr_buf[13][22] ),
    .A2(\wr_buf[14][22] ),
    .A3(\wr_buf[15][22] ),
    .S0(net316),
    .S1(net313),
    .X(_0445_));
 sky130_fd_sc_hd__mux4_2 _1202_ (.A0(\wr_buf[4][22] ),
    .A1(\wr_buf[5][22] ),
    .A2(\wr_buf[6][22] ),
    .A3(\wr_buf[7][22] ),
    .S0(net316),
    .S1(net313),
    .X(_0446_));
 sky130_fd_sc_hd__mux4_2 _1204_ (.A0(_0443_),
    .A1(_0444_),
    .A2(_0445_),
    .A3(_0446_),
    .S0(net310),
    .S1(net312),
    .X(_0448_));
 sky130_fd_sc_hd__mux2_4 _1205_ (.A0(\wr_dat_r[18] ),
    .A1(_0448_),
    .S(net282),
    .X(_0157_));
 sky130_fd_sc_hd__mux4_2 _1206_ (.A0(\wr_buf[8][23] ),
    .A1(\wr_buf[9][23] ),
    .A2(\wr_buf[10][23] ),
    .A3(\wr_buf[11][23] ),
    .S0(net316),
    .S1(net313),
    .X(_0449_));
 sky130_fd_sc_hd__mux4_2 _1209_ (.A0(\wr_buf[0][23] ),
    .A1(\wr_buf[1][23] ),
    .A2(\wr_buf[2][23] ),
    .A3(\wr_buf[3][23] ),
    .S0(net316),
    .S1(net314),
    .X(_0452_));
 sky130_fd_sc_hd__mux4_2 _1210_ (.A0(\wr_buf[12][23] ),
    .A1(\wr_buf[13][23] ),
    .A2(\wr_buf[14][23] ),
    .A3(\wr_buf[15][23] ),
    .S0(net316),
    .S1(net314),
    .X(_0453_));
 sky130_fd_sc_hd__mux4_2 _1211_ (.A0(\wr_buf[4][23] ),
    .A1(\wr_buf[5][23] ),
    .A2(\wr_buf[6][23] ),
    .A3(\wr_buf[7][23] ),
    .S0(net316),
    .S1(net313),
    .X(_0454_));
 sky130_fd_sc_hd__mux4_2 _1212_ (.A0(_0449_),
    .A1(_0452_),
    .A2(_0453_),
    .A3(_0454_),
    .S0(net310),
    .S1(net312),
    .X(_0455_));
 sky130_fd_sc_hd__mux2_4 _1213_ (.A0(\wr_dat_r[19] ),
    .A1(_0455_),
    .S(_0392_),
    .X(_0158_));
 sky130_fd_sc_hd__mux4_2 _1214_ (.A0(\wr_buf[8][5] ),
    .A1(\wr_buf[9][5] ),
    .A2(\wr_buf[10][5] ),
    .A3(\wr_buf[11][5] ),
    .S0(net316),
    .S1(net314),
    .X(_0456_));
 sky130_fd_sc_hd__mux4_2 _1215_ (.A0(\wr_buf[0][5] ),
    .A1(\wr_buf[1][5] ),
    .A2(\wr_buf[2][5] ),
    .A3(\wr_buf[3][5] ),
    .S0(net316),
    .S1(net314),
    .X(_0457_));
 sky130_fd_sc_hd__mux4_2 _1216_ (.A0(\wr_buf[12][5] ),
    .A1(\wr_buf[13][5] ),
    .A2(\wr_buf[14][5] ),
    .A3(\wr_buf[15][5] ),
    .S0(net316),
    .S1(net314),
    .X(_0458_));
 sky130_fd_sc_hd__mux4_2 _1217_ (.A0(\wr_buf[4][5] ),
    .A1(\wr_buf[5][5] ),
    .A2(\wr_buf[6][5] ),
    .A3(\wr_buf[7][5] ),
    .S0(net316),
    .S1(net314),
    .X(_0459_));
 sky130_fd_sc_hd__mux4_2 _1218_ (.A0(_0456_),
    .A1(_0457_),
    .A2(_0458_),
    .A3(_0459_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0460_));
 sky130_fd_sc_hd__mux2_4 _1219_ (.A0(\wr_dat_r[1] ),
    .A1(_0460_),
    .S(net282),
    .X(_0159_));
 sky130_fd_sc_hd__mux4_2 _1222_ (.A0(\wr_buf[8][24] ),
    .A1(\wr_buf[9][24] ),
    .A2(\wr_buf[10][24] ),
    .A3(\wr_buf[11][24] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0463_));
 sky130_fd_sc_hd__mux4_2 _1223_ (.A0(\wr_buf[0][24] ),
    .A1(\wr_buf[1][24] ),
    .A2(\wr_buf[2][24] ),
    .A3(\wr_buf[3][24] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0464_));
 sky130_fd_sc_hd__mux4_2 _1224_ (.A0(\wr_buf[12][24] ),
    .A1(\wr_buf[13][24] ),
    .A2(\wr_buf[14][24] ),
    .A3(\wr_buf[15][24] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0465_));
 sky130_fd_sc_hd__mux4_2 _1225_ (.A0(\wr_buf[4][24] ),
    .A1(\wr_buf[5][24] ),
    .A2(\wr_buf[6][24] ),
    .A3(\wr_buf[7][24] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0466_));
 sky130_fd_sc_hd__mux4_2 _1226_ (.A0(_0463_),
    .A1(_0464_),
    .A2(_0465_),
    .A3(_0466_),
    .S0(net310),
    .S1(net312),
    .X(_0467_));
 sky130_fd_sc_hd__mux2_4 _1227_ (.A0(\wr_dat_r[20] ),
    .A1(_0467_),
    .S(_0392_),
    .X(_0160_));
 sky130_fd_sc_hd__mux4_2 _1228_ (.A0(\wr_buf[8][25] ),
    .A1(\wr_buf[9][25] ),
    .A2(\wr_buf[10][25] ),
    .A3(\wr_buf[11][25] ),
    .S0(net316),
    .S1(net313),
    .X(_0468_));
 sky130_fd_sc_hd__mux4_2 _1229_ (.A0(\wr_buf[0][25] ),
    .A1(\wr_buf[1][25] ),
    .A2(\wr_buf[2][25] ),
    .A3(\wr_buf[3][25] ),
    .S0(net316),
    .S1(net313),
    .X(_0469_));
 sky130_fd_sc_hd__mux4_2 _1230_ (.A0(\wr_buf[12][25] ),
    .A1(\wr_buf[13][25] ),
    .A2(\wr_buf[14][25] ),
    .A3(\wr_buf[15][25] ),
    .S0(net316),
    .S1(net313),
    .X(_0470_));
 sky130_fd_sc_hd__mux4_2 _1231_ (.A0(\wr_buf[4][25] ),
    .A1(\wr_buf[5][25] ),
    .A2(\wr_buf[6][25] ),
    .A3(\wr_buf[7][25] ),
    .S0(net316),
    .S1(net313),
    .X(_0471_));
 sky130_fd_sc_hd__mux4_2 _1232_ (.A0(_0468_),
    .A1(_0469_),
    .A2(_0470_),
    .A3(_0471_),
    .S0(net310),
    .S1(net312),
    .X(_0472_));
 sky130_fd_sc_hd__mux2_4 _1233_ (.A0(\wr_dat_r[21] ),
    .A1(_0472_),
    .S(net282),
    .X(_0161_));
 sky130_fd_sc_hd__mux4_2 _1234_ (.A0(\wr_buf[8][26] ),
    .A1(\wr_buf[9][26] ),
    .A2(\wr_buf[10][26] ),
    .A3(\wr_buf[11][26] ),
    .S0(net316),
    .S1(net314),
    .X(_0473_));
 sky130_fd_sc_hd__mux4_2 _1235_ (.A0(\wr_buf[0][26] ),
    .A1(\wr_buf[1][26] ),
    .A2(\wr_buf[2][26] ),
    .A3(\wr_buf[3][26] ),
    .S0(net316),
    .S1(net314),
    .X(_0474_));
 sky130_fd_sc_hd__mux4_2 _1236_ (.A0(\wr_buf[12][26] ),
    .A1(\wr_buf[13][26] ),
    .A2(\wr_buf[14][26] ),
    .A3(\wr_buf[15][26] ),
    .S0(net315),
    .S1(net314),
    .X(_0475_));
 sky130_fd_sc_hd__mux4_2 _1237_ (.A0(\wr_buf[4][26] ),
    .A1(\wr_buf[5][26] ),
    .A2(\wr_buf[6][26] ),
    .A3(\wr_buf[7][26] ),
    .S0(net315),
    .S1(net314),
    .X(_0476_));
 sky130_fd_sc_hd__mux4_2 _1238_ (.A0(_0473_),
    .A1(_0474_),
    .A2(_0475_),
    .A3(_0476_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0477_));
 sky130_fd_sc_hd__mux2_4 _1239_ (.A0(\wr_dat_r[22] ),
    .A1(_0477_),
    .S(net282),
    .X(_0162_));
 sky130_fd_sc_hd__mux4_2 _1240_ (.A0(\wr_buf[8][27] ),
    .A1(\wr_buf[9][27] ),
    .A2(\wr_buf[10][27] ),
    .A3(\wr_buf[11][27] ),
    .S0(net315),
    .S1(net314),
    .X(_0478_));
 sky130_fd_sc_hd__mux4_2 _1241_ (.A0(\wr_buf[0][27] ),
    .A1(\wr_buf[1][27] ),
    .A2(\wr_buf[2][27] ),
    .A3(\wr_buf[3][27] ),
    .S0(net315),
    .S1(net314),
    .X(_0479_));
 sky130_fd_sc_hd__mux4_2 _1242_ (.A0(\wr_buf[12][27] ),
    .A1(\wr_buf[13][27] ),
    .A2(\wr_buf[14][27] ),
    .A3(\wr_buf[15][27] ),
    .S0(net315),
    .S1(net314),
    .X(_0480_));
 sky130_fd_sc_hd__mux4_2 _1243_ (.A0(\wr_buf[4][27] ),
    .A1(\wr_buf[5][27] ),
    .A2(\wr_buf[6][27] ),
    .A3(\wr_buf[7][27] ),
    .S0(net315),
    .S1(net314),
    .X(_0481_));
 sky130_fd_sc_hd__mux4_2 _1244_ (.A0(_0478_),
    .A1(_0479_),
    .A2(_0480_),
    .A3(_0481_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0482_));
 sky130_fd_sc_hd__mux2_4 _1246_ (.A0(\wr_dat_r[23] ),
    .A1(_0482_),
    .S(_0392_),
    .X(_0163_));
 sky130_fd_sc_hd__mux4_2 _1247_ (.A0(\wr_buf[8][28] ),
    .A1(\wr_buf[9][28] ),
    .A2(\wr_buf[10][28] ),
    .A3(\wr_buf[11][28] ),
    .S0(net316),
    .S1(net313),
    .X(_0484_));
 sky130_fd_sc_hd__mux4_2 _1248_ (.A0(\wr_buf[0][28] ),
    .A1(\wr_buf[1][28] ),
    .A2(\wr_buf[2][28] ),
    .A3(\wr_buf[3][28] ),
    .S0(net316),
    .S1(net313),
    .X(_0485_));
 sky130_fd_sc_hd__mux4_2 _1251_ (.A0(\wr_buf[12][28] ),
    .A1(\wr_buf[13][28] ),
    .A2(\wr_buf[14][28] ),
    .A3(\wr_buf[15][28] ),
    .S0(net316),
    .S1(net313),
    .X(_0488_));
 sky130_fd_sc_hd__mux4_2 _1252_ (.A0(\wr_buf[4][28] ),
    .A1(\wr_buf[5][28] ),
    .A2(\wr_buf[6][28] ),
    .A3(\wr_buf[7][28] ),
    .S0(net316),
    .S1(net313),
    .X(_0489_));
 sky130_fd_sc_hd__mux4_2 _1254_ (.A0(_0484_),
    .A1(_0485_),
    .A2(_0488_),
    .A3(_0489_),
    .S0(net310),
    .S1(net312),
    .X(_0491_));
 sky130_fd_sc_hd__mux2_4 _1255_ (.A0(\wr_dat_r[24] ),
    .A1(_0491_),
    .S(net282),
    .X(_0164_));
 sky130_fd_sc_hd__mux4_2 _1256_ (.A0(\wr_buf[8][29] ),
    .A1(\wr_buf[9][29] ),
    .A2(\wr_buf[10][29] ),
    .A3(\wr_buf[11][29] ),
    .S0(net315),
    .S1(net314),
    .X(_0492_));
 sky130_fd_sc_hd__mux4_2 _1257_ (.A0(\wr_buf[0][29] ),
    .A1(\wr_buf[1][29] ),
    .A2(\wr_buf[2][29] ),
    .A3(\wr_buf[3][29] ),
    .S0(net315),
    .S1(net314),
    .X(_0493_));
 sky130_fd_sc_hd__mux4_2 _1258_ (.A0(\wr_buf[12][29] ),
    .A1(\wr_buf[13][29] ),
    .A2(\wr_buf[14][29] ),
    .A3(\wr_buf[15][29] ),
    .S0(net315),
    .S1(net314),
    .X(_0494_));
 sky130_fd_sc_hd__mux4_2 _1259_ (.A0(\wr_buf[4][29] ),
    .A1(\wr_buf[5][29] ),
    .A2(\wr_buf[6][29] ),
    .A3(\wr_buf[7][29] ),
    .S0(net315),
    .S1(net314),
    .X(_0495_));
 sky130_fd_sc_hd__mux4_2 _1260_ (.A0(_0492_),
    .A1(_0493_),
    .A2(_0494_),
    .A3(_0495_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0496_));
 sky130_fd_sc_hd__mux2_4 _1261_ (.A0(\wr_dat_r[25] ),
    .A1(_0496_),
    .S(_0392_),
    .X(_0165_));
 sky130_fd_sc_hd__mux4_2 _1262_ (.A0(\wr_buf[8][30] ),
    .A1(\wr_buf[9][30] ),
    .A2(\wr_buf[10][30] ),
    .A3(\wr_buf[11][30] ),
    .S0(net315),
    .S1(net314),
    .X(_0497_));
 sky130_fd_sc_hd__mux4_2 _1263_ (.A0(\wr_buf[0][30] ),
    .A1(\wr_buf[1][30] ),
    .A2(\wr_buf[2][30] ),
    .A3(\wr_buf[3][30] ),
    .S0(net315),
    .S1(net314),
    .X(_0498_));
 sky130_fd_sc_hd__mux4_2 _1264_ (.A0(\wr_buf[12][30] ),
    .A1(\wr_buf[13][30] ),
    .A2(\wr_buf[14][30] ),
    .A3(\wr_buf[15][30] ),
    .S0(net315),
    .S1(net314),
    .X(_0499_));
 sky130_fd_sc_hd__mux4_2 _1267_ (.A0(\wr_buf[4][30] ),
    .A1(\wr_buf[5][30] ),
    .A2(\wr_buf[6][30] ),
    .A3(\wr_buf[7][30] ),
    .S0(net315),
    .S1(net314),
    .X(_0502_));
 sky130_fd_sc_hd__mux4_2 _1268_ (.A0(_0497_),
    .A1(_0498_),
    .A2(_0499_),
    .A3(_0502_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0503_));
 sky130_fd_sc_hd__mux2_4 _1269_ (.A0(\wr_dat_r[26] ),
    .A1(_0503_),
    .S(net282),
    .X(_0166_));
 sky130_fd_sc_hd__mux4_2 _1270_ (.A0(\wr_buf[8][31] ),
    .A1(\wr_buf[9][31] ),
    .A2(\wr_buf[10][31] ),
    .A3(\wr_buf[11][31] ),
    .S0(net316),
    .S1(net313),
    .X(_0504_));
 sky130_fd_sc_hd__mux4_2 _1271_ (.A0(\wr_buf[0][31] ),
    .A1(\wr_buf[1][31] ),
    .A2(\wr_buf[2][31] ),
    .A3(\wr_buf[3][31] ),
    .S0(net316),
    .S1(net313),
    .X(_0505_));
 sky130_fd_sc_hd__mux4_2 _1272_ (.A0(\wr_buf[12][31] ),
    .A1(\wr_buf[13][31] ),
    .A2(\wr_buf[14][31] ),
    .A3(\wr_buf[15][31] ),
    .S0(net316),
    .S1(net313),
    .X(_0506_));
 sky130_fd_sc_hd__mux4_2 _1273_ (.A0(\wr_buf[4][31] ),
    .A1(\wr_buf[5][31] ),
    .A2(\wr_buf[6][31] ),
    .A3(\wr_buf[7][31] ),
    .S0(net316),
    .S1(net313),
    .X(_0507_));
 sky130_fd_sc_hd__mux4_2 _1275_ (.A0(_0504_),
    .A1(_0505_),
    .A2(_0506_),
    .A3(_0507_),
    .S0(net310),
    .S1(net312),
    .X(_0509_));
 sky130_fd_sc_hd__mux2_4 _1276_ (.A0(\wr_dat_r[27] ),
    .A1(_0509_),
    .S(_0392_),
    .X(_0167_));
 sky130_fd_sc_hd__mux4_2 _1277_ (.A0(\wr_buf[8][32] ),
    .A1(\wr_buf[9][32] ),
    .A2(\wr_buf[10][32] ),
    .A3(\wr_buf[11][32] ),
    .S0(net316),
    .S1(net314),
    .X(_0510_));
 sky130_fd_sc_hd__mux4_2 _1280_ (.A0(\wr_buf[0][32] ),
    .A1(\wr_buf[1][32] ),
    .A2(\wr_buf[2][32] ),
    .A3(\wr_buf[3][32] ),
    .S0(net316),
    .S1(net314),
    .X(_0513_));
 sky130_fd_sc_hd__mux4_2 _1281_ (.A0(\wr_buf[12][32] ),
    .A1(\wr_buf[13][32] ),
    .A2(\wr_buf[14][32] ),
    .A3(\wr_buf[15][32] ),
    .S0(net316),
    .S1(net314),
    .X(_0514_));
 sky130_fd_sc_hd__mux4_2 _1282_ (.A0(\wr_buf[4][32] ),
    .A1(\wr_buf[5][32] ),
    .A2(\wr_buf[6][32] ),
    .A3(\wr_buf[7][32] ),
    .S0(net316),
    .S1(net314),
    .X(_0515_));
 sky130_fd_sc_hd__mux4_2 _1283_ (.A0(_0510_),
    .A1(_0513_),
    .A2(_0514_),
    .A3(_0515_),
    .S0(net311),
    .S1(net312),
    .X(_0516_));
 sky130_fd_sc_hd__mux2_4 _1284_ (.A0(\wr_dat_r[28] ),
    .A1(_0516_),
    .S(net282),
    .X(_0168_));
 sky130_fd_sc_hd__mux4_2 _1285_ (.A0(\wr_buf[8][33] ),
    .A1(\wr_buf[9][33] ),
    .A2(\wr_buf[10][33] ),
    .A3(\wr_buf[11][33] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0517_));
 sky130_fd_sc_hd__mux4_2 _1286_ (.A0(\wr_buf[0][33] ),
    .A1(\wr_buf[1][33] ),
    .A2(\wr_buf[2][33] ),
    .A3(\wr_buf[3][33] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0518_));
 sky130_fd_sc_hd__mux4_2 _1287_ (.A0(\wr_buf[12][33] ),
    .A1(\wr_buf[13][33] ),
    .A2(\wr_buf[14][33] ),
    .A3(\wr_buf[15][33] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0519_));
 sky130_fd_sc_hd__mux4_2 _1288_ (.A0(\wr_buf[4][33] ),
    .A1(\wr_buf[5][33] ),
    .A2(\wr_buf[6][33] ),
    .A3(\wr_buf[7][33] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0520_));
 sky130_fd_sc_hd__mux4_2 _1289_ (.A0(_0517_),
    .A1(_0518_),
    .A2(_0519_),
    .A3(_0520_),
    .S0(net310),
    .S1(net312),
    .X(_0521_));
 sky130_fd_sc_hd__mux2_4 _1290_ (.A0(\wr_dat_r[29] ),
    .A1(_0521_),
    .S(_0392_),
    .X(_0169_));
 sky130_fd_sc_hd__mux4_2 _1293_ (.A0(\wr_buf[8][6] ),
    .A1(\wr_buf[9][6] ),
    .A2(\wr_buf[10][6] ),
    .A3(\wr_buf[11][6] ),
    .S0(net316),
    .S1(net313),
    .X(_0524_));
 sky130_fd_sc_hd__mux4_2 _1294_ (.A0(\wr_buf[0][6] ),
    .A1(\wr_buf[1][6] ),
    .A2(\wr_buf[2][6] ),
    .A3(\wr_buf[3][6] ),
    .S0(net316),
    .S1(net313),
    .X(_0525_));
 sky130_fd_sc_hd__mux4_2 _1295_ (.A0(\wr_buf[12][6] ),
    .A1(\wr_buf[13][6] ),
    .A2(\wr_buf[14][6] ),
    .A3(\wr_buf[15][6] ),
    .S0(net316),
    .S1(net313),
    .X(_0526_));
 sky130_fd_sc_hd__mux4_2 _1296_ (.A0(\wr_buf[4][6] ),
    .A1(\wr_buf[5][6] ),
    .A2(\wr_buf[6][6] ),
    .A3(\wr_buf[7][6] ),
    .S0(net316),
    .S1(net313),
    .X(_0527_));
 sky130_fd_sc_hd__mux4_2 _1297_ (.A0(_0524_),
    .A1(_0525_),
    .A2(_0526_),
    .A3(_0527_),
    .S0(net310),
    .S1(net312),
    .X(_0528_));
 sky130_fd_sc_hd__mux2_4 _1298_ (.A0(\wr_dat_r[2] ),
    .A1(_0528_),
    .S(net282),
    .X(_0170_));
 sky130_fd_sc_hd__mux4_2 _1299_ (.A0(\wr_buf[8][34] ),
    .A1(\wr_buf[9][34] ),
    .A2(\wr_buf[10][34] ),
    .A3(\wr_buf[11][34] ),
    .S0(net315),
    .S1(net314),
    .X(_0529_));
 sky130_fd_sc_hd__mux4_2 _1300_ (.A0(\wr_buf[0][34] ),
    .A1(\wr_buf[1][34] ),
    .A2(\wr_buf[2][34] ),
    .A3(\wr_buf[3][34] ),
    .S0(net315),
    .S1(net314),
    .X(_0530_));
 sky130_fd_sc_hd__mux4_2 _1301_ (.A0(\wr_buf[12][34] ),
    .A1(\wr_buf[13][34] ),
    .A2(\wr_buf[14][34] ),
    .A3(\wr_buf[15][34] ),
    .S0(net315),
    .S1(net314),
    .X(_0531_));
 sky130_fd_sc_hd__mux4_2 _1302_ (.A0(\wr_buf[4][34] ),
    .A1(\wr_buf[5][34] ),
    .A2(\wr_buf[6][34] ),
    .A3(\wr_buf[7][34] ),
    .S0(net316),
    .S1(net313),
    .X(_0532_));
 sky130_fd_sc_hd__mux4_2 _1303_ (.A0(_0529_),
    .A1(_0530_),
    .A2(_0531_),
    .A3(_0532_),
    .S0(net310),
    .S1(net312),
    .X(_0533_));
 sky130_fd_sc_hd__mux2_4 _1304_ (.A0(\wr_dat_r[30] ),
    .A1(_0533_),
    .S(_0392_),
    .X(_0171_));
 sky130_fd_sc_hd__mux4_2 _1305_ (.A0(\wr_buf[8][35] ),
    .A1(\wr_buf[9][35] ),
    .A2(\wr_buf[10][35] ),
    .A3(\wr_buf[11][35] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0534_));
 sky130_fd_sc_hd__mux4_2 _1306_ (.A0(\wr_buf[0][35] ),
    .A1(\wr_buf[1][35] ),
    .A2(\wr_buf[2][35] ),
    .A3(\wr_buf[3][35] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0535_));
 sky130_fd_sc_hd__mux4_2 _1307_ (.A0(\wr_buf[12][35] ),
    .A1(\wr_buf[13][35] ),
    .A2(\wr_buf[14][35] ),
    .A3(\wr_buf[15][35] ),
    .S0(net316),
    .S1(net314),
    .X(_0536_));
 sky130_fd_sc_hd__mux4_2 _1308_ (.A0(\wr_buf[4][35] ),
    .A1(\wr_buf[5][35] ),
    .A2(\wr_buf[6][35] ),
    .A3(\wr_buf[7][35] ),
    .S0(net316),
    .S1(net314),
    .X(_0537_));
 sky130_fd_sc_hd__mux4_2 _1309_ (.A0(_0534_),
    .A1(_0535_),
    .A2(_0536_),
    .A3(_0537_),
    .S0(net310),
    .S1(net312),
    .X(_0538_));
 sky130_fd_sc_hd__mux2_4 _1310_ (.A0(\wr_dat_r[31] ),
    .A1(_0538_),
    .S(_0392_),
    .X(_0172_));
 sky130_fd_sc_hd__mux4_2 _1311_ (.A0(\wr_buf[8][7] ),
    .A1(\wr_buf[9][7] ),
    .A2(\wr_buf[10][7] ),
    .A3(\wr_buf[11][7] ),
    .S0(\wr_rptr[0] ),
    .S1(net314),
    .X(_0539_));
 sky130_fd_sc_hd__mux4_2 _1312_ (.A0(\wr_buf[0][7] ),
    .A1(\wr_buf[1][7] ),
    .A2(\wr_buf[2][7] ),
    .A3(\wr_buf[3][7] ),
    .S0(net316),
    .S1(net314),
    .X(_0540_));
 sky130_fd_sc_hd__mux4_2 _1313_ (.A0(\wr_buf[12][7] ),
    .A1(\wr_buf[13][7] ),
    .A2(\wr_buf[14][7] ),
    .A3(\wr_buf[15][7] ),
    .S0(net316),
    .S1(net314),
    .X(_0541_));
 sky130_fd_sc_hd__mux4_2 _1314_ (.A0(\wr_buf[4][7] ),
    .A1(\wr_buf[5][7] ),
    .A2(\wr_buf[6][7] ),
    .A3(\wr_buf[7][7] ),
    .S0(net316),
    .S1(net314),
    .X(_0542_));
 sky130_fd_sc_hd__mux4_2 _1315_ (.A0(_0539_),
    .A1(_0540_),
    .A2(_0541_),
    .A3(_0542_),
    .S0(net310),
    .S1(net312),
    .X(_0543_));
 sky130_fd_sc_hd__mux2_4 _1317_ (.A0(\wr_dat_r[3] ),
    .A1(_0543_),
    .S(_0392_),
    .X(_0173_));
 sky130_fd_sc_hd__mux4_2 _1318_ (.A0(\wr_buf[8][8] ),
    .A1(\wr_buf[9][8] ),
    .A2(\wr_buf[10][8] ),
    .A3(\wr_buf[11][8] ),
    .S0(net315),
    .S1(net314),
    .X(_0545_));
 sky130_fd_sc_hd__mux4_2 _1319_ (.A0(\wr_buf[0][8] ),
    .A1(\wr_buf[1][8] ),
    .A2(\wr_buf[2][8] ),
    .A3(\wr_buf[3][8] ),
    .S0(net315),
    .S1(net314),
    .X(_0546_));
 sky130_fd_sc_hd__mux4_2 _1322_ (.A0(\wr_buf[12][8] ),
    .A1(\wr_buf[13][8] ),
    .A2(\wr_buf[14][8] ),
    .A3(\wr_buf[15][8] ),
    .S0(net315),
    .S1(net314),
    .X(_0549_));
 sky130_fd_sc_hd__mux4_2 _1323_ (.A0(\wr_buf[4][8] ),
    .A1(\wr_buf[5][8] ),
    .A2(\wr_buf[6][8] ),
    .A3(\wr_buf[7][8] ),
    .S0(net315),
    .S1(net314),
    .X(_0550_));
 sky130_fd_sc_hd__mux4_2 _1325_ (.A0(_0545_),
    .A1(_0546_),
    .A2(_0549_),
    .A3(_0550_),
    .S0(net310),
    .S1(net312),
    .X(_0552_));
 sky130_fd_sc_hd__mux2_4 _1326_ (.A0(\wr_dat_r[4] ),
    .A1(_0552_),
    .S(_0392_),
    .X(_0174_));
 sky130_fd_sc_hd__mux4_2 _1327_ (.A0(\wr_buf[8][9] ),
    .A1(\wr_buf[9][9] ),
    .A2(\wr_buf[10][9] ),
    .A3(\wr_buf[11][9] ),
    .S0(net315),
    .S1(net314),
    .X(_0553_));
 sky130_fd_sc_hd__mux4_2 _1328_ (.A0(\wr_buf[0][9] ),
    .A1(\wr_buf[1][9] ),
    .A2(\wr_buf[2][9] ),
    .A3(\wr_buf[3][9] ),
    .S0(net315),
    .S1(net314),
    .X(_0554_));
 sky130_fd_sc_hd__mux4_2 _1329_ (.A0(\wr_buf[12][9] ),
    .A1(\wr_buf[13][9] ),
    .A2(\wr_buf[14][9] ),
    .A3(\wr_buf[15][9] ),
    .S0(net315),
    .S1(net314),
    .X(_0555_));
 sky130_fd_sc_hd__mux4_2 _1330_ (.A0(\wr_buf[4][9] ),
    .A1(\wr_buf[5][9] ),
    .A2(\wr_buf[6][9] ),
    .A3(\wr_buf[7][9] ),
    .S0(net315),
    .S1(net314),
    .X(_0556_));
 sky130_fd_sc_hd__mux4_2 _1331_ (.A0(_0553_),
    .A1(_0554_),
    .A2(_0555_),
    .A3(_0556_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0557_));
 sky130_fd_sc_hd__mux2_4 _1332_ (.A0(\wr_dat_r[5] ),
    .A1(_0557_),
    .S(_0392_),
    .X(_0175_));
 sky130_fd_sc_hd__mux4_2 _1333_ (.A0(\wr_buf[8][10] ),
    .A1(\wr_buf[9][10] ),
    .A2(\wr_buf[10][10] ),
    .A3(\wr_buf[11][10] ),
    .S0(net315),
    .S1(net314),
    .X(_0558_));
 sky130_fd_sc_hd__mux4_2 _1334_ (.A0(\wr_buf[0][10] ),
    .A1(\wr_buf[1][10] ),
    .A2(\wr_buf[2][10] ),
    .A3(\wr_buf[3][10] ),
    .S0(net315),
    .S1(net314),
    .X(_0559_));
 sky130_fd_sc_hd__mux4_2 _1335_ (.A0(\wr_buf[12][10] ),
    .A1(\wr_buf[13][10] ),
    .A2(\wr_buf[14][10] ),
    .A3(\wr_buf[15][10] ),
    .S0(net315),
    .S1(net314),
    .X(_0560_));
 sky130_fd_sc_hd__mux4_2 _1336_ (.A0(\wr_buf[4][10] ),
    .A1(\wr_buf[5][10] ),
    .A2(\wr_buf[6][10] ),
    .A3(\wr_buf[7][10] ),
    .S0(net315),
    .S1(net314),
    .X(_0561_));
 sky130_fd_sc_hd__mux4_2 _1337_ (.A0(_0558_),
    .A1(_0559_),
    .A2(_0560_),
    .A3(_0561_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0562_));
 sky130_fd_sc_hd__mux2_4 _1338_ (.A0(\wr_dat_r[6] ),
    .A1(_0562_),
    .S(_0392_),
    .X(_0176_));
 sky130_fd_sc_hd__mux4_2 _1339_ (.A0(\wr_buf[8][11] ),
    .A1(\wr_buf[9][11] ),
    .A2(\wr_buf[10][11] ),
    .A3(\wr_buf[11][11] ),
    .S0(net315),
    .S1(net314),
    .X(_0563_));
 sky130_fd_sc_hd__mux4_2 _1340_ (.A0(\wr_buf[0][11] ),
    .A1(\wr_buf[1][11] ),
    .A2(\wr_buf[2][11] ),
    .A3(\wr_buf[3][11] ),
    .S0(net315),
    .S1(net314),
    .X(_0564_));
 sky130_fd_sc_hd__mux4_2 _1341_ (.A0(\wr_buf[12][11] ),
    .A1(\wr_buf[13][11] ),
    .A2(\wr_buf[14][11] ),
    .A3(\wr_buf[15][11] ),
    .S0(net315),
    .S1(net314),
    .X(_0565_));
 sky130_fd_sc_hd__mux4_2 _1342_ (.A0(\wr_buf[4][11] ),
    .A1(\wr_buf[5][11] ),
    .A2(\wr_buf[6][11] ),
    .A3(\wr_buf[7][11] ),
    .S0(net315),
    .S1(net314),
    .X(_0566_));
 sky130_fd_sc_hd__mux4_2 _1343_ (.A0(_0563_),
    .A1(_0564_),
    .A2(_0565_),
    .A3(_0566_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0567_));
 sky130_fd_sc_hd__mux2_4 _1344_ (.A0(\wr_dat_r[7] ),
    .A1(_0567_),
    .S(_0392_),
    .X(_0177_));
 sky130_fd_sc_hd__mux4_2 _1345_ (.A0(\wr_buf[8][12] ),
    .A1(\wr_buf[9][12] ),
    .A2(\wr_buf[10][12] ),
    .A3(\wr_buf[11][12] ),
    .S0(net315),
    .S1(net314),
    .X(_0568_));
 sky130_fd_sc_hd__mux4_2 _1346_ (.A0(\wr_buf[0][12] ),
    .A1(\wr_buf[1][12] ),
    .A2(\wr_buf[2][12] ),
    .A3(\wr_buf[3][12] ),
    .S0(net315),
    .S1(net314),
    .X(_0569_));
 sky130_fd_sc_hd__mux4_2 _1347_ (.A0(\wr_buf[12][12] ),
    .A1(\wr_buf[13][12] ),
    .A2(\wr_buf[14][12] ),
    .A3(\wr_buf[15][12] ),
    .S0(net315),
    .S1(net314),
    .X(_0570_));
 sky130_fd_sc_hd__mux4_2 _1348_ (.A0(\wr_buf[4][12] ),
    .A1(\wr_buf[5][12] ),
    .A2(\wr_buf[6][12] ),
    .A3(\wr_buf[7][12] ),
    .S0(net315),
    .S1(net314),
    .X(_0571_));
 sky130_fd_sc_hd__mux4_2 _1349_ (.A0(_0568_),
    .A1(_0569_),
    .A2(_0570_),
    .A3(_0571_),
    .S0(net311),
    .S1(net312),
    .X(_0572_));
 sky130_fd_sc_hd__mux2_4 _1350_ (.A0(\wr_dat_r[8] ),
    .A1(_0572_),
    .S(_0392_),
    .X(_0178_));
 sky130_fd_sc_hd__mux4_2 _1351_ (.A0(\wr_buf[8][13] ),
    .A1(\wr_buf[9][13] ),
    .A2(\wr_buf[10][13] ),
    .A3(\wr_buf[11][13] ),
    .S0(net315),
    .S1(net314),
    .X(_0573_));
 sky130_fd_sc_hd__mux4_2 _1352_ (.A0(\wr_buf[0][13] ),
    .A1(\wr_buf[1][13] ),
    .A2(\wr_buf[2][13] ),
    .A3(\wr_buf[3][13] ),
    .S0(net315),
    .S1(net314),
    .X(_0574_));
 sky130_fd_sc_hd__mux4_2 _1353_ (.A0(\wr_buf[12][13] ),
    .A1(\wr_buf[13][13] ),
    .A2(\wr_buf[14][13] ),
    .A3(\wr_buf[15][13] ),
    .S0(net315),
    .S1(net314),
    .X(_0575_));
 sky130_fd_sc_hd__mux4_2 _1354_ (.A0(\wr_buf[4][13] ),
    .A1(\wr_buf[5][13] ),
    .A2(\wr_buf[6][13] ),
    .A3(\wr_buf[7][13] ),
    .S0(net315),
    .S1(net314),
    .X(_0576_));
 sky130_fd_sc_hd__mux4_2 _1355_ (.A0(_0573_),
    .A1(_0574_),
    .A2(_0575_),
    .A3(_0576_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0577_));
 sky130_fd_sc_hd__mux2_4 _1356_ (.A0(\wr_dat_r[9] ),
    .A1(_0577_),
    .S(_0392_),
    .X(_0179_));
 sky130_fd_sc_hd__nand2_1 _1357_ (.A(\wr_state[2] ),
    .B(\wr_lat_ctr[0] ),
    .Y(_0578_));
 sky130_fd_sc_hd__o21ai_0 _1358_ (.A1(\wr_state[2] ),
    .A2(_0085_),
    .B1(_0578_),
    .Y(_0579_));
 sky130_fd_sc_hd__a22oi_1 _1359_ (.A1(_0262_),
    .A2(\wr_state[2] ),
    .B1(_0244_),
    .B2(_0247_),
    .Y(_0580_));
 sky130_fd_sc_hd__a31o_2 _1360_ (.A1(\wr_state[2] ),
    .A2(_0252_),
    .A3(_0255_),
    .B1(_0580_),
    .X(_0581_));
 sky130_fd_sc_hd__mux2i_1 _1362_ (.A0(_0579_),
    .A1(_0090_),
    .S(_0581_),
    .Y(_0180_));
 sky130_fd_sc_hd__mux2_2 _1363_ (.A0(_0088_),
    .A1(_0093_),
    .S(\wr_state[2] ),
    .X(_0583_));
 sky130_fd_sc_hd__mux2i_1 _1364_ (.A0(_0583_),
    .A1(_0091_),
    .S(_0581_),
    .Y(_0181_));
 sky130_fd_sc_hd__xor2_1 _1365_ (.A(net13),
    .B(_0087_),
    .X(_0584_));
 sky130_fd_sc_hd__nand2_1 _1366_ (.A(\wr_state[2] ),
    .B(_0253_),
    .Y(_0585_));
 sky130_fd_sc_hd__o21ai_0 _1367_ (.A1(\wr_state[2] ),
    .A2(_0584_),
    .B1(_0585_),
    .Y(_0586_));
 sky130_fd_sc_hd__mux2i_1 _1368_ (.A0(\wr_state[0] ),
    .A1(_0092_),
    .S(\wr_state[2] ),
    .Y(_0587_));
 sky130_fd_sc_hd__a21oi_1 _1369_ (.A1(_0243_),
    .A2(_0247_),
    .B1(_0262_),
    .Y(_0588_));
 sky130_fd_sc_hd__o21ai_0 _1370_ (.A1(_0587_),
    .A2(_0588_),
    .B1(\wr_lat_ctr[2] ),
    .Y(_0589_));
 sky130_fd_sc_hd__o21ai_0 _1371_ (.A1(_0581_),
    .A2(_0586_),
    .B1(_0589_),
    .Y(_0182_));
 sky130_fd_sc_hd__inv_1 _1372_ (.A(\wr_lat_ctr[3] ),
    .Y(_0590_));
 sky130_fd_sc_hd__nor3_1 _1373_ (.A(\wr_lat_ctr[2] ),
    .B(\wr_lat_ctr[1] ),
    .C(\wr_lat_ctr[0] ),
    .Y(_0591_));
 sky130_fd_sc_hd__nand3_1 _1374_ (.A(\wr_state[2] ),
    .B(\wr_lat_ctr[3] ),
    .C(_0591_),
    .Y(_0592_));
 sky130_fd_sc_hd__nor2_1 _1375_ (.A(_0580_),
    .B(_0592_),
    .Y(_0593_));
 sky130_fd_sc_hd__nand2_1 _1376_ (.A(\wr_state[2] ),
    .B(_0590_),
    .Y(_0594_));
 sky130_fd_sc_hd__nor3_1 _1377_ (.A(net13),
    .B(net12),
    .C(net11),
    .Y(_0595_));
 sky130_fd_sc_hd__xor2_1 _1378_ (.A(net14),
    .B(_0595_),
    .X(_0596_));
 sky130_fd_sc_hd__nor2_1 _1379_ (.A(\wr_state[2] ),
    .B(_0596_),
    .Y(_0597_));
 sky130_fd_sc_hd__nand3_1 _1380_ (.A(_0244_),
    .B(_0247_),
    .C(_0597_),
    .Y(_0598_));
 sky130_fd_sc_hd__o21ai_0 _1381_ (.A1(_0594_),
    .A2(_0591_),
    .B1(_0598_),
    .Y(_0599_));
 sky130_fd_sc_hd__a211oi_1 _1382_ (.A1(_0590_),
    .A2(_0581_),
    .B1(_0593_),
    .C1(_0599_),
    .Y(_0183_));
 sky130_fd_sc_hd__inv_1 _1383_ (.A(\wr_lat_ctr[4] ),
    .Y(_0600_));
 sky130_fd_sc_hd__nand2_1 _1384_ (.A(\wr_state[2] ),
    .B(\wr_lat_ctr[4] ),
    .Y(_0601_));
 sky130_fd_sc_hd__nor2_1 _1385_ (.A(net14),
    .B(net13),
    .Y(_0602_));
 sky130_fd_sc_hd__nand2_1 _1386_ (.A(_0087_),
    .B(_0602_),
    .Y(_0603_));
 sky130_fd_sc_hd__xnor2_1 _1387_ (.A(net15),
    .B(_0603_),
    .Y(_0604_));
 sky130_fd_sc_hd__o32a_1 _1388_ (.A1(\wr_lat_ctr[3] ),
    .A2(_0253_),
    .A3(_0601_),
    .B1(_0604_),
    .B2(\wr_state[2] ),
    .X(_0605_));
 sky130_fd_sc_hd__o31ai_1 _1389_ (.A1(\wr_state[0] ),
    .A2(\wr_lat_ctr[3] ),
    .A3(_0253_),
    .B1(\wr_lat_ctr[4] ),
    .Y(_0606_));
 sky130_fd_sc_hd__o311ai_0 _1390_ (.A1(\wr_lat_ctr[3] ),
    .A2(\wr_lat_ctr[4] ),
    .A3(_0253_),
    .B1(_0606_),
    .C1(\wr_state[2] ),
    .Y(_0607_));
 sky130_fd_sc_hd__o21ai_0 _1391_ (.A1(_0248_),
    .A2(_0605_),
    .B1(_0607_),
    .Y(_0608_));
 sky130_fd_sc_hd__a21oi_1 _1392_ (.A1(_0600_),
    .A2(_0581_),
    .B1(_0608_),
    .Y(_0184_));
 sky130_fd_sc_hd__inv_1 _1393_ (.A(\wr_lat_ctr[5] ),
    .Y(_0609_));
 sky130_fd_sc_hd__and3_1 _1394_ (.A(_0590_),
    .B(_0600_),
    .C(_0591_),
    .X(_0610_));
 sky130_fd_sc_hd__nand3_1 _1395_ (.A(\wr_state[2] ),
    .B(\wr_lat_ctr[5] ),
    .C(_0610_),
    .Y(_0611_));
 sky130_fd_sc_hd__nor2_1 _1396_ (.A(_0588_),
    .B(_0611_),
    .Y(_0612_));
 sky130_fd_sc_hd__nor3_1 _1397_ (.A(net12),
    .B(net11),
    .C(_0242_),
    .Y(_0613_));
 sky130_fd_sc_hd__xor2_1 _1398_ (.A(net16),
    .B(_0613_),
    .X(_0614_));
 sky130_fd_sc_hd__nand2_1 _1399_ (.A(\wr_state[2] ),
    .B(_0609_),
    .Y(_0615_));
 sky130_fd_sc_hd__o32ai_1 _1400_ (.A1(\wr_state[2] ),
    .A2(_0248_),
    .A3(_0614_),
    .B1(_0615_),
    .B2(_0610_),
    .Y(_0616_));
 sky130_fd_sc_hd__a211oi_1 _1401_ (.A1(_0609_),
    .A2(_0581_),
    .B1(_0612_),
    .C1(_0616_),
    .Y(_0185_));
 sky130_fd_sc_hd__inv_1 _1402_ (.A(\wr_lat_ctr[7] ),
    .Y(_0617_));
 sky130_fd_sc_hd__or4_1 _1403_ (.A(\wr_lat_ctr[5] ),
    .B(\wr_lat_ctr[4] ),
    .C(_0617_),
    .D(\wr_lat_ctr[6] ),
    .X(_0618_));
 sky130_fd_sc_hd__o41ai_1 _1404_ (.A1(\wr_lat_ctr[3] ),
    .A2(\wr_lat_ctr[5] ),
    .A3(\wr_lat_ctr[4] ),
    .A4(_0253_),
    .B1(\wr_lat_ctr[6] ),
    .Y(_0619_));
 sky130_fd_sc_hd__o41ai_1 _1405_ (.A1(\wr_state[0] ),
    .A2(\wr_lat_ctr[3] ),
    .A3(_0253_),
    .A4(_0618_),
    .B1(_0619_),
    .Y(_0620_));
 sky130_fd_sc_hd__nand2_1 _1406_ (.A(\wr_state[2] ),
    .B(_0252_),
    .Y(_0621_));
 sky130_fd_sc_hd__nor4_1 _1407_ (.A(_0617_),
    .B(_0248_),
    .C(_0253_),
    .D(_0621_),
    .Y(_0622_));
 sky130_fd_sc_hd__a221o_1 _1408_ (.A1(\wr_lat_ctr[6] ),
    .A2(_0581_),
    .B1(_0620_),
    .B2(\wr_state[2] ),
    .C1(_0622_),
    .X(_0186_));
 sky130_fd_sc_hd__nand2_1 _1409_ (.A(_0252_),
    .B(_0591_),
    .Y(_0623_));
 sky130_fd_sc_hd__a21oi_1 _1410_ (.A1(\wr_state[2] ),
    .A2(_0623_),
    .B1(_0580_),
    .Y(_0624_));
 sky130_fd_sc_hd__nand2_1 _1411_ (.A(_0253_),
    .B(_0591_),
    .Y(_0625_));
 sky130_fd_sc_hd__or4_1 _1412_ (.A(\wr_lat_ctr[7] ),
    .B(_0621_),
    .C(_0588_),
    .D(_0625_),
    .X(_0626_));
 sky130_fd_sc_hd__o21ai_0 _1413_ (.A1(_0617_),
    .A2(_0624_),
    .B1(_0626_),
    .Y(_0187_));
 sky130_fd_sc_hd__mux4_2 _1414_ (.A0(\wr_buf[8][0] ),
    .A1(\wr_buf[9][0] ),
    .A2(\wr_buf[10][0] ),
    .A3(\wr_buf[11][0] ),
    .S0(net315),
    .S1(net314),
    .X(_0627_));
 sky130_fd_sc_hd__mux4_2 _1415_ (.A0(\wr_buf[0][0] ),
    .A1(\wr_buf[1][0] ),
    .A2(\wr_buf[2][0] ),
    .A3(\wr_buf[3][0] ),
    .S0(net315),
    .S1(net314),
    .X(_0628_));
 sky130_fd_sc_hd__mux4_2 _1416_ (.A0(\wr_buf[12][0] ),
    .A1(\wr_buf[13][0] ),
    .A2(\wr_buf[14][0] ),
    .A3(\wr_buf[15][0] ),
    .S0(net315),
    .S1(net314),
    .X(_0629_));
 sky130_fd_sc_hd__mux4_2 _1417_ (.A0(\wr_buf[4][0] ),
    .A1(\wr_buf[5][0] ),
    .A2(\wr_buf[6][0] ),
    .A3(\wr_buf[7][0] ),
    .S0(net315),
    .S1(net314),
    .X(_0630_));
 sky130_fd_sc_hd__mux4_2 _1418_ (.A0(_0627_),
    .A1(_0628_),
    .A2(_0629_),
    .A3(_0630_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0631_));
 sky130_fd_sc_hd__mux2_4 _1419_ (.A0(\wr_msk_r[0] ),
    .A1(_0631_),
    .S(_0392_),
    .X(_0188_));
 sky130_fd_sc_hd__mux4_2 _1420_ (.A0(\wr_buf[8][1] ),
    .A1(\wr_buf[9][1] ),
    .A2(\wr_buf[10][1] ),
    .A3(\wr_buf[11][1] ),
    .S0(\wr_rptr[0] ),
    .S1(\wr_rptr[1] ),
    .X(_0632_));
 sky130_fd_sc_hd__mux4_2 _1421_ (.A0(\wr_buf[0][1] ),
    .A1(\wr_buf[1][1] ),
    .A2(\wr_buf[2][1] ),
    .A3(\wr_buf[3][1] ),
    .S0(net315),
    .S1(\wr_rptr[1] ),
    .X(_0633_));
 sky130_fd_sc_hd__mux4_2 _1422_ (.A0(\wr_buf[12][1] ),
    .A1(\wr_buf[13][1] ),
    .A2(\wr_buf[14][1] ),
    .A3(\wr_buf[15][1] ),
    .S0(net315),
    .S1(\wr_rptr[1] ),
    .X(_0634_));
 sky130_fd_sc_hd__mux4_2 _1423_ (.A0(\wr_buf[4][1] ),
    .A1(\wr_buf[5][1] ),
    .A2(\wr_buf[6][1] ),
    .A3(\wr_buf[7][1] ),
    .S0(\wr_rptr[0] ),
    .S1(\wr_rptr[1] ),
    .X(_0635_));
 sky130_fd_sc_hd__mux4_2 _1424_ (.A0(_0632_),
    .A1(_0633_),
    .A2(_0634_),
    .A3(_0635_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0636_));
 sky130_fd_sc_hd__mux2_4 _1425_ (.A0(\wr_msk_r[1] ),
    .A1(_0636_),
    .S(_0392_),
    .X(_0189_));
 sky130_fd_sc_hd__mux4_2 _1426_ (.A0(\wr_buf[8][2] ),
    .A1(\wr_buf[9][2] ),
    .A2(\wr_buf[10][2] ),
    .A3(\wr_buf[11][2] ),
    .S0(net315),
    .S1(net314),
    .X(_0637_));
 sky130_fd_sc_hd__mux4_2 _1427_ (.A0(\wr_buf[0][2] ),
    .A1(\wr_buf[1][2] ),
    .A2(\wr_buf[2][2] ),
    .A3(\wr_buf[3][2] ),
    .S0(net315),
    .S1(net314),
    .X(_0638_));
 sky130_fd_sc_hd__mux4_2 _1428_ (.A0(\wr_buf[12][2] ),
    .A1(\wr_buf[13][2] ),
    .A2(\wr_buf[14][2] ),
    .A3(\wr_buf[15][2] ),
    .S0(net315),
    .S1(net314),
    .X(_0639_));
 sky130_fd_sc_hd__mux4_2 _1429_ (.A0(\wr_buf[4][2] ),
    .A1(\wr_buf[5][2] ),
    .A2(\wr_buf[6][2] ),
    .A3(\wr_buf[7][2] ),
    .S0(net315),
    .S1(net314),
    .X(_0640_));
 sky130_fd_sc_hd__mux4_2 _1430_ (.A0(_0637_),
    .A1(_0638_),
    .A2(_0639_),
    .A3(_0640_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0641_));
 sky130_fd_sc_hd__mux2_4 _1431_ (.A0(\wr_msk_r[2] ),
    .A1(_0641_),
    .S(_0392_),
    .X(_0190_));
 sky130_fd_sc_hd__mux4_2 _1432_ (.A0(\wr_buf[8][3] ),
    .A1(\wr_buf[9][3] ),
    .A2(\wr_buf[10][3] ),
    .A3(\wr_buf[11][3] ),
    .S0(net315),
    .S1(\wr_rptr[1] ),
    .X(_0642_));
 sky130_fd_sc_hd__mux4_2 _1433_ (.A0(\wr_buf[0][3] ),
    .A1(\wr_buf[1][3] ),
    .A2(\wr_buf[2][3] ),
    .A3(\wr_buf[3][3] ),
    .S0(net315),
    .S1(\wr_rptr[1] ),
    .X(_0643_));
 sky130_fd_sc_hd__mux4_2 _1434_ (.A0(\wr_buf[12][3] ),
    .A1(\wr_buf[13][3] ),
    .A2(\wr_buf[14][3] ),
    .A3(\wr_buf[15][3] ),
    .S0(net315),
    .S1(\wr_rptr[1] ),
    .X(_0644_));
 sky130_fd_sc_hd__mux4_2 _1435_ (.A0(\wr_buf[4][3] ),
    .A1(\wr_buf[5][3] ),
    .A2(\wr_buf[6][3] ),
    .A3(\wr_buf[7][3] ),
    .S0(net315),
    .S1(net314),
    .X(_0645_));
 sky130_fd_sc_hd__mux4_2 _1436_ (.A0(_0642_),
    .A1(_0643_),
    .A2(_0644_),
    .A3(_0645_),
    .S0(net311),
    .S1(\wr_rptr[2] ),
    .X(_0646_));
 sky130_fd_sc_hd__mux2_2 _1437_ (.A0(\wr_msk_r[3] ),
    .A1(_0646_),
    .S(_0392_),
    .X(_0191_));
 sky130_fd_sc_hd__xnor2_1 _1438_ (.A(net315),
    .B(_0259_),
    .Y(_0192_));
 sky130_fd_sc_hd__nand2_1 _1439_ (.A(_0039_),
    .B(_0392_),
    .Y(_0647_));
 sky130_fd_sc_hd__o21ai_0 _1440_ (.A1(_0058_),
    .A2(_0392_),
    .B1(_0647_),
    .Y(_0193_));
 sky130_fd_sc_hd__nand2_1 _1441_ (.A(_0038_),
    .B(_0392_),
    .Y(_0648_));
 sky130_fd_sc_hd__xnor2_1 _1442_ (.A(net312),
    .B(_0648_),
    .Y(_0194_));
 sky130_fd_sc_hd__nand4_1 _1443_ (.A(\wr_rptr[2] ),
    .B(\wr_rptr[1] ),
    .C(net315),
    .D(_0392_),
    .Y(_0649_));
 sky130_fd_sc_hd__xnor2_1 _1444_ (.A(\wr_rptr[3] ),
    .B(_0649_),
    .Y(_0195_));
 sky130_fd_sc_hd__nand4_1 _1445_ (.A(_0038_),
    .B(\wr_rptr[2] ),
    .C(\wr_rptr[3] ),
    .D(_0392_),
    .Y(_0650_));
 sky130_fd_sc_hd__xnor2_1 _1446_ (.A(\wr_rptr[4] ),
    .B(_0650_),
    .Y(_0196_));
 sky130_fd_sc_hd__xnor2_1 _1447_ (.A(_0040_),
    .B(_0218_),
    .Y(_0197_));
 sky130_fd_sc_hd__nand2_1 _1448_ (.A(_0043_),
    .B(_0218_),
    .Y(_0651_));
 sky130_fd_sc_hd__o21ai_0 _1449_ (.A1(_0041_),
    .A2(_0218_),
    .B1(_0651_),
    .Y(_0198_));
 sky130_fd_sc_hd__nand2_1 _1450_ (.A(_0046_),
    .B(_0218_),
    .Y(_0652_));
 sky130_fd_sc_hd__xnor2_1 _1451_ (.A(\wr_wptr[2] ),
    .B(_0652_),
    .Y(_0199_));
 sky130_fd_sc_hd__nand4_1 _1452_ (.A(\wr_wptr[2] ),
    .B(\wr_wptr[1] ),
    .C(\wr_wptr[0] ),
    .D(_0218_),
    .Y(_0653_));
 sky130_fd_sc_hd__xnor2_1 _1453_ (.A(\wr_wptr[3] ),
    .B(_0653_),
    .Y(_0200_));
 sky130_fd_sc_hd__inv_1 _1454_ (.A(_0046_),
    .Y(_0654_));
 sky130_fd_sc_hd__nor2_1 _1455_ (.A(_0654_),
    .B(_0239_),
    .Y(_0655_));
 sky130_fd_sc_hd__xor2_1 _1456_ (.A(\wr_wptr[4] ),
    .B(_0655_),
    .X(_0201_));
 sky130_fd_sc_hd__mux2i_1 _1457_ (.A0(\wr_msk_r[0] ),
    .A1(\wr_msk_r[2] ),
    .S(net308),
    .Y(_0656_));
 sky130_fd_sc_hd__and2_1 _1458_ (.A(net95),
    .B(_0656_),
    .X(net77));
 sky130_fd_sc_hd__mux2i_1 _1459_ (.A0(\wr_msk_r[1] ),
    .A1(\wr_msk_r[3] ),
    .S(_0095_),
    .Y(_0657_));
 sky130_fd_sc_hd__and2_1 _1460_ (.A(net95),
    .B(_0657_),
    .X(net78));
 sky130_fd_sc_hd__mux2_2 _1462_ (.A0(\wr_dat_r[0] ),
    .A1(\wr_dat_r[16] ),
    .S(net308),
    .X(net79));
 sky130_fd_sc_hd__mux2_2 _1463_ (.A0(\wr_dat_r[10] ),
    .A1(\wr_dat_r[26] ),
    .S(net308),
    .X(net80));
 sky130_fd_sc_hd__mux2_2 _1464_ (.A0(\wr_dat_r[11] ),
    .A1(\wr_dat_r[27] ),
    .S(net308),
    .X(net81));
 sky130_fd_sc_hd__mux2_2 _1465_ (.A0(\wr_dat_r[12] ),
    .A1(\wr_dat_r[28] ),
    .S(net308),
    .X(net82));
 sky130_fd_sc_hd__mux2_2 _1466_ (.A0(\wr_dat_r[13] ),
    .A1(\wr_dat_r[29] ),
    .S(net308),
    .X(net83));
 sky130_fd_sc_hd__mux2_2 _1467_ (.A0(\wr_dat_r[14] ),
    .A1(\wr_dat_r[30] ),
    .S(net308),
    .X(net84));
 sky130_fd_sc_hd__mux2_2 _1468_ (.A0(\wr_dat_r[15] ),
    .A1(\wr_dat_r[31] ),
    .S(net308),
    .X(net85));
 sky130_fd_sc_hd__mux2_2 _1469_ (.A0(\wr_dat_r[1] ),
    .A1(\wr_dat_r[17] ),
    .S(net308),
    .X(net86));
 sky130_fd_sc_hd__mux2_2 _1470_ (.A0(\wr_dat_r[2] ),
    .A1(\wr_dat_r[18] ),
    .S(net308),
    .X(net87));
 sky130_fd_sc_hd__mux2_2 _1471_ (.A0(\wr_dat_r[3] ),
    .A1(\wr_dat_r[19] ),
    .S(net308),
    .X(net88));
 sky130_fd_sc_hd__mux2_2 _1472_ (.A0(\wr_dat_r[4] ),
    .A1(\wr_dat_r[20] ),
    .S(net308),
    .X(net89));
 sky130_fd_sc_hd__mux2_2 _1473_ (.A0(\wr_dat_r[5] ),
    .A1(\wr_dat_r[21] ),
    .S(net308),
    .X(net90));
 sky130_fd_sc_hd__mux2_2 _1474_ (.A0(\wr_dat_r[6] ),
    .A1(\wr_dat_r[22] ),
    .S(net308),
    .X(net91));
 sky130_fd_sc_hd__mux2_2 _1475_ (.A0(\wr_dat_r[7] ),
    .A1(\wr_dat_r[23] ),
    .S(net308),
    .X(net92));
 sky130_fd_sc_hd__mux2_2 _1476_ (.A0(\wr_dat_r[8] ),
    .A1(\wr_dat_r[24] ),
    .S(net308),
    .X(net93));
 sky130_fd_sc_hd__mux2_2 _1477_ (.A0(\wr_dat_r[9] ),
    .A1(\wr_dat_r[25] ),
    .S(net308),
    .X(net94));
 sky130_fd_sc_hd__mux4_2 _1480_ (.A0(\rd_fifo[8][0] ),
    .A1(\rd_fifo[9][0] ),
    .A2(\rd_fifo[10][0] ),
    .A3(\rd_fifo[11][0] ),
    .S0(net324),
    .S1(net320),
    .X(_0661_));
 sky130_fd_sc_hd__mux4_2 _1485_ (.A0(\rd_fifo[0][0] ),
    .A1(\rd_fifo[1][0] ),
    .A2(\rd_fifo[2][0] ),
    .A3(\rd_fifo[3][0] ),
    .S0(net324),
    .S1(net320),
    .X(_0666_));
 sky130_fd_sc_hd__mux4_2 _1488_ (.A0(\rd_fifo[12][0] ),
    .A1(\rd_fifo[13][0] ),
    .A2(\rd_fifo[14][0] ),
    .A3(\rd_fifo[15][0] ),
    .S0(net324),
    .S1(net320),
    .X(_0669_));
 sky130_fd_sc_hd__mux4_2 _1489_ (.A0(\rd_fifo[4][0] ),
    .A1(\rd_fifo[5][0] ),
    .A2(\rd_fifo[6][0] ),
    .A3(\rd_fifo[7][0] ),
    .S0(net324),
    .S1(net320),
    .X(_0670_));
 sky130_fd_sc_hd__mux4_2 _1490_ (.A0(_0661_),
    .A1(_0666_),
    .A2(_0669_),
    .A3(_0670_),
    .S0(_0286_),
    .S1(\rd_rptr[2] ),
    .X(net98));
 sky130_fd_sc_hd__mux4_2 _1491_ (.A0(\rd_fifo[8][1] ),
    .A1(\rd_fifo[9][1] ),
    .A2(\rd_fifo[10][1] ),
    .A3(\rd_fifo[11][1] ),
    .S0(net324),
    .S1(net320),
    .X(_0671_));
 sky130_fd_sc_hd__mux4_2 _1492_ (.A0(\rd_fifo[0][1] ),
    .A1(\rd_fifo[1][1] ),
    .A2(\rd_fifo[2][1] ),
    .A3(\rd_fifo[3][1] ),
    .S0(net324),
    .S1(net320),
    .X(_0672_));
 sky130_fd_sc_hd__mux4_2 _1493_ (.A0(\rd_fifo[12][1] ),
    .A1(\rd_fifo[13][1] ),
    .A2(\rd_fifo[14][1] ),
    .A3(\rd_fifo[15][1] ),
    .S0(net324),
    .S1(net320),
    .X(_0673_));
 sky130_fd_sc_hd__mux4_2 _1494_ (.A0(\rd_fifo[4][1] ),
    .A1(\rd_fifo[5][1] ),
    .A2(\rd_fifo[6][1] ),
    .A3(\rd_fifo[7][1] ),
    .S0(net324),
    .S1(net320),
    .X(_0674_));
 sky130_fd_sc_hd__mux4_2 _1495_ (.A0(_0671_),
    .A1(_0672_),
    .A2(_0673_),
    .A3(_0674_),
    .S0(_0286_),
    .S1(\rd_rptr[2] ),
    .X(net99));
 sky130_fd_sc_hd__mux4_2 _1498_ (.A0(\rd_fifo[8][2] ),
    .A1(\rd_fifo[9][2] ),
    .A2(\rd_fifo[10][2] ),
    .A3(\rd_fifo[11][2] ),
    .S0(net324),
    .S1(net320),
    .X(_0677_));
 sky130_fd_sc_hd__mux4_2 _1499_ (.A0(\rd_fifo[0][2] ),
    .A1(\rd_fifo[1][2] ),
    .A2(\rd_fifo[2][2] ),
    .A3(\rd_fifo[3][2] ),
    .S0(net324),
    .S1(net320),
    .X(_0678_));
 sky130_fd_sc_hd__mux4_2 _1500_ (.A0(\rd_fifo[12][2] ),
    .A1(\rd_fifo[13][2] ),
    .A2(\rd_fifo[14][2] ),
    .A3(\rd_fifo[15][2] ),
    .S0(net324),
    .S1(net320),
    .X(_0679_));
 sky130_fd_sc_hd__mux4_2 _1501_ (.A0(\rd_fifo[4][2] ),
    .A1(\rd_fifo[5][2] ),
    .A2(\rd_fifo[6][2] ),
    .A3(\rd_fifo[7][2] ),
    .S0(net324),
    .S1(net320),
    .X(_0680_));
 sky130_fd_sc_hd__mux4_2 _1502_ (.A0(_0677_),
    .A1(_0678_),
    .A2(_0679_),
    .A3(_0680_),
    .S0(_0286_),
    .S1(net317),
    .X(net100));
 sky130_fd_sc_hd__mux4_2 _1503_ (.A0(\rd_fifo[8][3] ),
    .A1(\rd_fifo[9][3] ),
    .A2(\rd_fifo[10][3] ),
    .A3(\rd_fifo[11][3] ),
    .S0(net324),
    .S1(net320),
    .X(_0681_));
 sky130_fd_sc_hd__mux4_2 _1504_ (.A0(\rd_fifo[0][3] ),
    .A1(\rd_fifo[1][3] ),
    .A2(\rd_fifo[2][3] ),
    .A3(\rd_fifo[3][3] ),
    .S0(net324),
    .S1(net320),
    .X(_0682_));
 sky130_fd_sc_hd__mux4_2 _1505_ (.A0(\rd_fifo[12][3] ),
    .A1(\rd_fifo[13][3] ),
    .A2(\rd_fifo[14][3] ),
    .A3(\rd_fifo[15][3] ),
    .S0(net324),
    .S1(net320),
    .X(_0683_));
 sky130_fd_sc_hd__mux4_2 _1506_ (.A0(\rd_fifo[4][3] ),
    .A1(\rd_fifo[5][3] ),
    .A2(\rd_fifo[6][3] ),
    .A3(\rd_fifo[7][3] ),
    .S0(net324),
    .S1(net320),
    .X(_0684_));
 sky130_fd_sc_hd__mux4_2 _1507_ (.A0(_0681_),
    .A1(_0682_),
    .A2(_0683_),
    .A3(_0684_),
    .S0(_0286_),
    .S1(\rd_rptr[2] ),
    .X(net101));
 sky130_fd_sc_hd__mux4_2 _1508_ (.A0(\rd_fifo[8][4] ),
    .A1(\rd_fifo[9][4] ),
    .A2(\rd_fifo[10][4] ),
    .A3(\rd_fifo[11][4] ),
    .S0(net322),
    .S1(net319),
    .X(_0685_));
 sky130_fd_sc_hd__mux4_2 _1509_ (.A0(\rd_fifo[0][4] ),
    .A1(\rd_fifo[1][4] ),
    .A2(\rd_fifo[2][4] ),
    .A3(\rd_fifo[3][4] ),
    .S0(net322),
    .S1(net319),
    .X(_0686_));
 sky130_fd_sc_hd__mux4_2 _1510_ (.A0(\rd_fifo[12][4] ),
    .A1(\rd_fifo[13][4] ),
    .A2(\rd_fifo[14][4] ),
    .A3(\rd_fifo[15][4] ),
    .S0(net322),
    .S1(net319),
    .X(_0687_));
 sky130_fd_sc_hd__mux4_2 _1511_ (.A0(\rd_fifo[4][4] ),
    .A1(\rd_fifo[5][4] ),
    .A2(\rd_fifo[6][4] ),
    .A3(\rd_fifo[7][4] ),
    .S0(net322),
    .S1(net319),
    .X(_0688_));
 sky130_fd_sc_hd__mux4_2 _1512_ (.A0(_0685_),
    .A1(_0686_),
    .A2(_0687_),
    .A3(_0688_),
    .S0(_0286_),
    .S1(net317),
    .X(net102));
 sky130_fd_sc_hd__mux4_2 _1513_ (.A0(\rd_fifo[8][14] ),
    .A1(\rd_fifo[9][14] ),
    .A2(\rd_fifo[10][14] ),
    .A3(\rd_fifo[11][14] ),
    .S0(net322),
    .S1(net319),
    .X(_0689_));
 sky130_fd_sc_hd__mux4_2 _1514_ (.A0(\rd_fifo[0][14] ),
    .A1(\rd_fifo[1][14] ),
    .A2(\rd_fifo[2][14] ),
    .A3(\rd_fifo[3][14] ),
    .S0(net322),
    .S1(net319),
    .X(_0690_));
 sky130_fd_sc_hd__mux4_2 _1515_ (.A0(\rd_fifo[12][14] ),
    .A1(\rd_fifo[13][14] ),
    .A2(\rd_fifo[14][14] ),
    .A3(\rd_fifo[15][14] ),
    .S0(net322),
    .S1(net319),
    .X(_0691_));
 sky130_fd_sc_hd__mux4_2 _1516_ (.A0(\rd_fifo[4][14] ),
    .A1(\rd_fifo[5][14] ),
    .A2(\rd_fifo[6][14] ),
    .A3(\rd_fifo[7][14] ),
    .S0(net322),
    .S1(net319),
    .X(_0692_));
 sky130_fd_sc_hd__mux4_2 _1517_ (.A0(_0689_),
    .A1(_0690_),
    .A2(_0691_),
    .A3(_0692_),
    .S0(net309),
    .S1(net317),
    .X(net103));
 sky130_fd_sc_hd__mux4_2 _1518_ (.A0(\rd_fifo[8][15] ),
    .A1(\rd_fifo[9][15] ),
    .A2(\rd_fifo[10][15] ),
    .A3(\rd_fifo[11][15] ),
    .S0(net322),
    .S1(net319),
    .X(_0693_));
 sky130_fd_sc_hd__mux4_2 _1519_ (.A0(\rd_fifo[0][15] ),
    .A1(\rd_fifo[1][15] ),
    .A2(\rd_fifo[2][15] ),
    .A3(\rd_fifo[3][15] ),
    .S0(net322),
    .S1(net319),
    .X(_0694_));
 sky130_fd_sc_hd__mux4_2 _1522_ (.A0(\rd_fifo[12][15] ),
    .A1(\rd_fifo[13][15] ),
    .A2(\rd_fifo[14][15] ),
    .A3(\rd_fifo[15][15] ),
    .S0(net322),
    .S1(net319),
    .X(_0697_));
 sky130_fd_sc_hd__mux4_2 _1523_ (.A0(\rd_fifo[4][15] ),
    .A1(\rd_fifo[5][15] ),
    .A2(\rd_fifo[6][15] ),
    .A3(\rd_fifo[7][15] ),
    .S0(net322),
    .S1(net319),
    .X(_0698_));
 sky130_fd_sc_hd__mux4_2 _1525_ (.A0(_0693_),
    .A1(_0694_),
    .A2(_0697_),
    .A3(_0698_),
    .S0(_0286_),
    .S1(net317),
    .X(net104));
 sky130_fd_sc_hd__mux4_2 _1526_ (.A0(\rd_fifo[8][16] ),
    .A1(\rd_fifo[9][16] ),
    .A2(\rd_fifo[10][16] ),
    .A3(\rd_fifo[11][16] ),
    .S0(net323),
    .S1(net319),
    .X(_0700_));
 sky130_fd_sc_hd__mux4_2 _1527_ (.A0(\rd_fifo[0][16] ),
    .A1(\rd_fifo[1][16] ),
    .A2(\rd_fifo[2][16] ),
    .A3(\rd_fifo[3][16] ),
    .S0(net323),
    .S1(net319),
    .X(_0701_));
 sky130_fd_sc_hd__mux4_2 _1528_ (.A0(\rd_fifo[12][16] ),
    .A1(\rd_fifo[13][16] ),
    .A2(\rd_fifo[14][16] ),
    .A3(\rd_fifo[15][16] ),
    .S0(net323),
    .S1(net319),
    .X(_0702_));
 sky130_fd_sc_hd__mux4_2 _1529_ (.A0(\rd_fifo[4][16] ),
    .A1(\rd_fifo[5][16] ),
    .A2(\rd_fifo[6][16] ),
    .A3(\rd_fifo[7][16] ),
    .S0(net323),
    .S1(net319),
    .X(_0703_));
 sky130_fd_sc_hd__mux4_2 _1530_ (.A0(_0700_),
    .A1(_0701_),
    .A2(_0702_),
    .A3(_0703_),
    .S0(net309),
    .S1(net317),
    .X(net105));
 sky130_fd_sc_hd__mux4_2 _1531_ (.A0(\rd_fifo[8][17] ),
    .A1(\rd_fifo[9][17] ),
    .A2(\rd_fifo[10][17] ),
    .A3(\rd_fifo[11][17] ),
    .S0(net322),
    .S1(net319),
    .X(_0704_));
 sky130_fd_sc_hd__mux4_2 _1532_ (.A0(\rd_fifo[0][17] ),
    .A1(\rd_fifo[1][17] ),
    .A2(\rd_fifo[2][17] ),
    .A3(\rd_fifo[3][17] ),
    .S0(net322),
    .S1(net319),
    .X(_0705_));
 sky130_fd_sc_hd__mux4_2 _1533_ (.A0(\rd_fifo[12][17] ),
    .A1(\rd_fifo[13][17] ),
    .A2(\rd_fifo[14][17] ),
    .A3(\rd_fifo[15][17] ),
    .S0(net322),
    .S1(net319),
    .X(_0706_));
 sky130_fd_sc_hd__mux4_2 _1536_ (.A0(\rd_fifo[4][17] ),
    .A1(\rd_fifo[5][17] ),
    .A2(\rd_fifo[6][17] ),
    .A3(\rd_fifo[7][17] ),
    .S0(net322),
    .S1(net319),
    .X(_0709_));
 sky130_fd_sc_hd__mux4_2 _1537_ (.A0(_0704_),
    .A1(_0705_),
    .A2(_0706_),
    .A3(_0709_),
    .S0(net309),
    .S1(net317),
    .X(net106));
 sky130_fd_sc_hd__mux4_2 _1538_ (.A0(\rd_fifo[8][18] ),
    .A1(\rd_fifo[9][18] ),
    .A2(\rd_fifo[10][18] ),
    .A3(\rd_fifo[11][18] ),
    .S0(net322),
    .S1(net319),
    .X(_0710_));
 sky130_fd_sc_hd__mux4_2 _1539_ (.A0(\rd_fifo[0][18] ),
    .A1(\rd_fifo[1][18] ),
    .A2(\rd_fifo[2][18] ),
    .A3(\rd_fifo[3][18] ),
    .S0(net322),
    .S1(net319),
    .X(_0711_));
 sky130_fd_sc_hd__mux4_2 _1540_ (.A0(\rd_fifo[12][18] ),
    .A1(\rd_fifo[13][18] ),
    .A2(\rd_fifo[14][18] ),
    .A3(\rd_fifo[15][18] ),
    .S0(net322),
    .S1(net319),
    .X(_0712_));
 sky130_fd_sc_hd__mux4_2 _1541_ (.A0(\rd_fifo[4][18] ),
    .A1(\rd_fifo[5][18] ),
    .A2(\rd_fifo[6][18] ),
    .A3(\rd_fifo[7][18] ),
    .S0(net322),
    .S1(net319),
    .X(_0713_));
 sky130_fd_sc_hd__mux4_2 _1543_ (.A0(_0710_),
    .A1(_0711_),
    .A2(_0712_),
    .A3(_0713_),
    .S0(net309),
    .S1(net317),
    .X(net107));
 sky130_fd_sc_hd__mux4_2 _1544_ (.A0(\rd_fifo[8][19] ),
    .A1(\rd_fifo[9][19] ),
    .A2(\rd_fifo[10][19] ),
    .A3(\rd_fifo[11][19] ),
    .S0(net322),
    .S1(net319),
    .X(_0715_));
 sky130_fd_sc_hd__mux4_2 _1547_ (.A0(\rd_fifo[0][19] ),
    .A1(\rd_fifo[1][19] ),
    .A2(\rd_fifo[2][19] ),
    .A3(\rd_fifo[3][19] ),
    .S0(net324),
    .S1(net320),
    .X(_0718_));
 sky130_fd_sc_hd__mux4_2 _1548_ (.A0(\rd_fifo[12][19] ),
    .A1(\rd_fifo[13][19] ),
    .A2(\rd_fifo[14][19] ),
    .A3(\rd_fifo[15][19] ),
    .S0(net324),
    .S1(net320),
    .X(_0719_));
 sky130_fd_sc_hd__mux4_2 _1549_ (.A0(\rd_fifo[4][19] ),
    .A1(\rd_fifo[5][19] ),
    .A2(\rd_fifo[6][19] ),
    .A3(\rd_fifo[7][19] ),
    .S0(net324),
    .S1(net320),
    .X(_0720_));
 sky130_fd_sc_hd__mux4_2 _1550_ (.A0(_0715_),
    .A1(_0718_),
    .A2(_0719_),
    .A3(_0720_),
    .S0(_0286_),
    .S1(net317),
    .X(net108));
 sky130_fd_sc_hd__mux4_2 _1551_ (.A0(\rd_fifo[8][20] ),
    .A1(\rd_fifo[9][20] ),
    .A2(\rd_fifo[10][20] ),
    .A3(\rd_fifo[11][20] ),
    .S0(net323),
    .S1(net319),
    .X(_0721_));
 sky130_fd_sc_hd__mux4_2 _1552_ (.A0(\rd_fifo[0][20] ),
    .A1(\rd_fifo[1][20] ),
    .A2(\rd_fifo[2][20] ),
    .A3(\rd_fifo[3][20] ),
    .S0(net323),
    .S1(net319),
    .X(_0722_));
 sky130_fd_sc_hd__mux4_2 _1553_ (.A0(\rd_fifo[12][20] ),
    .A1(\rd_fifo[13][20] ),
    .A2(\rd_fifo[14][20] ),
    .A3(\rd_fifo[15][20] ),
    .S0(net322),
    .S1(net319),
    .X(_0723_));
 sky130_fd_sc_hd__mux4_2 _1554_ (.A0(\rd_fifo[4][20] ),
    .A1(\rd_fifo[5][20] ),
    .A2(\rd_fifo[6][20] ),
    .A3(\rd_fifo[7][20] ),
    .S0(net323),
    .S1(net319),
    .X(_0724_));
 sky130_fd_sc_hd__mux4_2 _1555_ (.A0(_0721_),
    .A1(_0722_),
    .A2(_0723_),
    .A3(_0724_),
    .S0(net309),
    .S1(net317),
    .X(net109));
 sky130_fd_sc_hd__mux4_2 _1558_ (.A0(\rd_fifo[8][21] ),
    .A1(\rd_fifo[9][21] ),
    .A2(\rd_fifo[10][21] ),
    .A3(\rd_fifo[11][21] ),
    .S0(net322),
    .S1(net319),
    .X(_0727_));
 sky130_fd_sc_hd__mux4_2 _1559_ (.A0(\rd_fifo[0][21] ),
    .A1(\rd_fifo[1][21] ),
    .A2(\rd_fifo[2][21] ),
    .A3(\rd_fifo[3][21] ),
    .S0(net322),
    .S1(net319),
    .X(_0728_));
 sky130_fd_sc_hd__mux4_2 _1560_ (.A0(\rd_fifo[12][21] ),
    .A1(\rd_fifo[13][21] ),
    .A2(\rd_fifo[14][21] ),
    .A3(\rd_fifo[15][21] ),
    .S0(net322),
    .S1(net319),
    .X(_0729_));
 sky130_fd_sc_hd__mux4_2 _1561_ (.A0(\rd_fifo[4][21] ),
    .A1(\rd_fifo[5][21] ),
    .A2(\rd_fifo[6][21] ),
    .A3(\rd_fifo[7][21] ),
    .S0(net322),
    .S1(net319),
    .X(_0730_));
 sky130_fd_sc_hd__mux4_2 _1562_ (.A0(_0727_),
    .A1(_0728_),
    .A2(_0729_),
    .A3(_0730_),
    .S0(net309),
    .S1(net317),
    .X(net110));
 sky130_fd_sc_hd__mux4_2 _1563_ (.A0(\rd_fifo[8][22] ),
    .A1(\rd_fifo[9][22] ),
    .A2(\rd_fifo[10][22] ),
    .A3(\rd_fifo[11][22] ),
    .S0(net323),
    .S1(net319),
    .X(_0731_));
 sky130_fd_sc_hd__mux4_2 _1564_ (.A0(\rd_fifo[0][22] ),
    .A1(\rd_fifo[1][22] ),
    .A2(\rd_fifo[2][22] ),
    .A3(\rd_fifo[3][22] ),
    .S0(net323),
    .S1(net319),
    .X(_0732_));
 sky130_fd_sc_hd__mux4_2 _1565_ (.A0(\rd_fifo[12][22] ),
    .A1(\rd_fifo[13][22] ),
    .A2(\rd_fifo[14][22] ),
    .A3(\rd_fifo[15][22] ),
    .S0(net323),
    .S1(net319),
    .X(_0733_));
 sky130_fd_sc_hd__mux4_2 _1566_ (.A0(\rd_fifo[4][22] ),
    .A1(\rd_fifo[5][22] ),
    .A2(\rd_fifo[6][22] ),
    .A3(\rd_fifo[7][22] ),
    .S0(net323),
    .S1(net319),
    .X(_0734_));
 sky130_fd_sc_hd__mux4_2 _1567_ (.A0(_0731_),
    .A1(_0732_),
    .A2(_0733_),
    .A3(_0734_),
    .S0(net309),
    .S1(net317),
    .X(net111));
 sky130_fd_sc_hd__mux4_2 _1568_ (.A0(\rd_fifo[8][23] ),
    .A1(\rd_fifo[9][23] ),
    .A2(\rd_fifo[10][23] ),
    .A3(\rd_fifo[11][23] ),
    .S0(net323),
    .S1(net319),
    .X(_0735_));
 sky130_fd_sc_hd__mux4_2 _1569_ (.A0(\rd_fifo[0][23] ),
    .A1(\rd_fifo[1][23] ),
    .A2(\rd_fifo[2][23] ),
    .A3(\rd_fifo[3][23] ),
    .S0(net323),
    .S1(net319),
    .X(_0736_));
 sky130_fd_sc_hd__mux4_2 _1570_ (.A0(\rd_fifo[12][23] ),
    .A1(\rd_fifo[13][23] ),
    .A2(\rd_fifo[14][23] ),
    .A3(\rd_fifo[15][23] ),
    .S0(net323),
    .S1(net319),
    .X(_0737_));
 sky130_fd_sc_hd__mux4_2 _1571_ (.A0(\rd_fifo[4][23] ),
    .A1(\rd_fifo[5][23] ),
    .A2(\rd_fifo[6][23] ),
    .A3(\rd_fifo[7][23] ),
    .S0(net323),
    .S1(net319),
    .X(_0738_));
 sky130_fd_sc_hd__mux4_2 _1572_ (.A0(_0735_),
    .A1(_0736_),
    .A2(_0737_),
    .A3(_0738_),
    .S0(net309),
    .S1(net317),
    .X(net112));
 sky130_fd_sc_hd__mux4_2 _1573_ (.A0(\rd_fifo[8][5] ),
    .A1(\rd_fifo[9][5] ),
    .A2(\rd_fifo[10][5] ),
    .A3(\rd_fifo[11][5] ),
    .S0(net322),
    .S1(net319),
    .X(_0739_));
 sky130_fd_sc_hd__mux4_2 _1574_ (.A0(\rd_fifo[0][5] ),
    .A1(\rd_fifo[1][5] ),
    .A2(\rd_fifo[2][5] ),
    .A3(\rd_fifo[3][5] ),
    .S0(net322),
    .S1(net319),
    .X(_0740_));
 sky130_fd_sc_hd__mux4_2 _1575_ (.A0(\rd_fifo[12][5] ),
    .A1(\rd_fifo[13][5] ),
    .A2(\rd_fifo[14][5] ),
    .A3(\rd_fifo[15][5] ),
    .S0(net322),
    .S1(net319),
    .X(_0741_));
 sky130_fd_sc_hd__mux4_2 _1576_ (.A0(\rd_fifo[4][5] ),
    .A1(\rd_fifo[5][5] ),
    .A2(\rd_fifo[6][5] ),
    .A3(\rd_fifo[7][5] ),
    .S0(net322),
    .S1(net319),
    .X(_0742_));
 sky130_fd_sc_hd__mux4_2 _1577_ (.A0(_0739_),
    .A1(_0740_),
    .A2(_0741_),
    .A3(_0742_),
    .S0(net309),
    .S1(net317),
    .X(net113));
 sky130_fd_sc_hd__mux4_2 _1578_ (.A0(\rd_fifo[8][24] ),
    .A1(\rd_fifo[9][24] ),
    .A2(\rd_fifo[10][24] ),
    .A3(\rd_fifo[11][24] ),
    .S0(net323),
    .S1(net319),
    .X(_0743_));
 sky130_fd_sc_hd__mux4_2 _1579_ (.A0(\rd_fifo[0][24] ),
    .A1(\rd_fifo[1][24] ),
    .A2(\rd_fifo[2][24] ),
    .A3(\rd_fifo[3][24] ),
    .S0(net323),
    .S1(net319),
    .X(_0744_));
 sky130_fd_sc_hd__mux4_2 _1582_ (.A0(\rd_fifo[12][24] ),
    .A1(\rd_fifo[13][24] ),
    .A2(\rd_fifo[14][24] ),
    .A3(\rd_fifo[15][24] ),
    .S0(net323),
    .S1(net319),
    .X(_0747_));
 sky130_fd_sc_hd__mux4_2 _1583_ (.A0(\rd_fifo[4][24] ),
    .A1(\rd_fifo[5][24] ),
    .A2(\rd_fifo[6][24] ),
    .A3(\rd_fifo[7][24] ),
    .S0(net323),
    .S1(net319),
    .X(_0748_));
 sky130_fd_sc_hd__mux4_2 _1585_ (.A0(_0743_),
    .A1(_0744_),
    .A2(_0747_),
    .A3(_0748_),
    .S0(net309),
    .S1(net317),
    .X(net114));
 sky130_fd_sc_hd__mux4_2 _1586_ (.A0(\rd_fifo[8][25] ),
    .A1(\rd_fifo[9][25] ),
    .A2(\rd_fifo[10][25] ),
    .A3(\rd_fifo[11][25] ),
    .S0(net322),
    .S1(net319),
    .X(_0750_));
 sky130_fd_sc_hd__mux4_2 _1587_ (.A0(\rd_fifo[0][25] ),
    .A1(\rd_fifo[1][25] ),
    .A2(\rd_fifo[2][25] ),
    .A3(\rd_fifo[3][25] ),
    .S0(net322),
    .S1(net319),
    .X(_0751_));
 sky130_fd_sc_hd__mux4_2 _1588_ (.A0(\rd_fifo[12][25] ),
    .A1(\rd_fifo[13][25] ),
    .A2(\rd_fifo[14][25] ),
    .A3(\rd_fifo[15][25] ),
    .S0(net322),
    .S1(net319),
    .X(_0752_));
 sky130_fd_sc_hd__mux4_2 _1589_ (.A0(\rd_fifo[4][25] ),
    .A1(\rd_fifo[5][25] ),
    .A2(\rd_fifo[6][25] ),
    .A3(\rd_fifo[7][25] ),
    .S0(net323),
    .S1(net319),
    .X(_0753_));
 sky130_fd_sc_hd__mux4_2 _1590_ (.A0(_0750_),
    .A1(_0751_),
    .A2(_0752_),
    .A3(_0753_),
    .S0(net309),
    .S1(net317),
    .X(net115));
 sky130_fd_sc_hd__mux4_2 _1591_ (.A0(\rd_fifo[8][26] ),
    .A1(\rd_fifo[9][26] ),
    .A2(\rd_fifo[10][26] ),
    .A3(\rd_fifo[11][26] ),
    .S0(net323),
    .S1(net319),
    .X(_0754_));
 sky130_fd_sc_hd__mux4_2 _1592_ (.A0(\rd_fifo[0][26] ),
    .A1(\rd_fifo[1][26] ),
    .A2(\rd_fifo[2][26] ),
    .A3(\rd_fifo[3][26] ),
    .S0(net323),
    .S1(net319),
    .X(_0755_));
 sky130_fd_sc_hd__mux4_2 _1593_ (.A0(\rd_fifo[12][26] ),
    .A1(\rd_fifo[13][26] ),
    .A2(\rd_fifo[14][26] ),
    .A3(\rd_fifo[15][26] ),
    .S0(net323),
    .S1(net319),
    .X(_0756_));
 sky130_fd_sc_hd__mux4_2 _1596_ (.A0(\rd_fifo[4][26] ),
    .A1(\rd_fifo[5][26] ),
    .A2(\rd_fifo[6][26] ),
    .A3(\rd_fifo[7][26] ),
    .S0(net323),
    .S1(net319),
    .X(_0759_));
 sky130_fd_sc_hd__mux4_2 _1597_ (.A0(_0754_),
    .A1(_0755_),
    .A2(_0756_),
    .A3(_0759_),
    .S0(net309),
    .S1(net317),
    .X(net116));
 sky130_fd_sc_hd__mux4_2 _1598_ (.A0(\rd_fifo[8][27] ),
    .A1(\rd_fifo[9][27] ),
    .A2(\rd_fifo[10][27] ),
    .A3(\rd_fifo[11][27] ),
    .S0(net323),
    .S1(net319),
    .X(_0760_));
 sky130_fd_sc_hd__mux4_2 _1599_ (.A0(\rd_fifo[0][27] ),
    .A1(\rd_fifo[1][27] ),
    .A2(\rd_fifo[2][27] ),
    .A3(\rd_fifo[3][27] ),
    .S0(net323),
    .S1(net319),
    .X(_0761_));
 sky130_fd_sc_hd__mux4_2 _1600_ (.A0(\rd_fifo[12][27] ),
    .A1(\rd_fifo[13][27] ),
    .A2(\rd_fifo[14][27] ),
    .A3(\rd_fifo[15][27] ),
    .S0(net323),
    .S1(net319),
    .X(_0762_));
 sky130_fd_sc_hd__mux4_2 _1601_ (.A0(\rd_fifo[4][27] ),
    .A1(\rd_fifo[5][27] ),
    .A2(\rd_fifo[6][27] ),
    .A3(\rd_fifo[7][27] ),
    .S0(net323),
    .S1(net319),
    .X(_0763_));
 sky130_fd_sc_hd__mux4_2 _1603_ (.A0(_0760_),
    .A1(_0761_),
    .A2(_0762_),
    .A3(_0763_),
    .S0(net309),
    .S1(net317),
    .X(net117));
 sky130_fd_sc_hd__mux4_2 _1604_ (.A0(\rd_fifo[8][28] ),
    .A1(\rd_fifo[9][28] ),
    .A2(\rd_fifo[10][28] ),
    .A3(\rd_fifo[11][28] ),
    .S0(net321),
    .S1(net318),
    .X(_0765_));
 sky130_fd_sc_hd__mux4_2 _1607_ (.A0(\rd_fifo[0][28] ),
    .A1(\rd_fifo[1][28] ),
    .A2(\rd_fifo[2][28] ),
    .A3(\rd_fifo[3][28] ),
    .S0(net321),
    .S1(net318),
    .X(_0768_));
 sky130_fd_sc_hd__mux4_2 _1608_ (.A0(\rd_fifo[12][28] ),
    .A1(\rd_fifo[13][28] ),
    .A2(\rd_fifo[14][28] ),
    .A3(\rd_fifo[15][28] ),
    .S0(net321),
    .S1(net318),
    .X(_0769_));
 sky130_fd_sc_hd__mux4_2 _1609_ (.A0(\rd_fifo[4][28] ),
    .A1(\rd_fifo[5][28] ),
    .A2(\rd_fifo[6][28] ),
    .A3(\rd_fifo[7][28] ),
    .S0(net321),
    .S1(net318),
    .X(_0770_));
 sky130_fd_sc_hd__mux4_2 _1610_ (.A0(_0765_),
    .A1(_0768_),
    .A2(_0769_),
    .A3(_0770_),
    .S0(net309),
    .S1(net317),
    .X(net118));
 sky130_fd_sc_hd__mux4_2 _1611_ (.A0(\rd_fifo[8][29] ),
    .A1(\rd_fifo[9][29] ),
    .A2(\rd_fifo[10][29] ),
    .A3(\rd_fifo[11][29] ),
    .S0(net321),
    .S1(net318),
    .X(_0771_));
 sky130_fd_sc_hd__mux4_2 _1612_ (.A0(\rd_fifo[0][29] ),
    .A1(\rd_fifo[1][29] ),
    .A2(\rd_fifo[2][29] ),
    .A3(\rd_fifo[3][29] ),
    .S0(net321),
    .S1(net318),
    .X(_0772_));
 sky130_fd_sc_hd__mux4_2 _1613_ (.A0(\rd_fifo[12][29] ),
    .A1(\rd_fifo[13][29] ),
    .A2(\rd_fifo[14][29] ),
    .A3(\rd_fifo[15][29] ),
    .S0(net321),
    .S1(net318),
    .X(_0773_));
 sky130_fd_sc_hd__mux4_2 _1614_ (.A0(\rd_fifo[4][29] ),
    .A1(\rd_fifo[5][29] ),
    .A2(\rd_fifo[6][29] ),
    .A3(\rd_fifo[7][29] ),
    .S0(net321),
    .S1(net318),
    .X(_0774_));
 sky130_fd_sc_hd__mux4_2 _1615_ (.A0(_0771_),
    .A1(_0772_),
    .A2(_0773_),
    .A3(_0774_),
    .S0(net309),
    .S1(net317),
    .X(net119));
 sky130_fd_sc_hd__mux4_2 _1618_ (.A0(\rd_fifo[8][30] ),
    .A1(\rd_fifo[9][30] ),
    .A2(\rd_fifo[10][30] ),
    .A3(\rd_fifo[11][30] ),
    .S0(net321),
    .S1(net318),
    .X(_0777_));
 sky130_fd_sc_hd__mux4_2 _1619_ (.A0(\rd_fifo[0][30] ),
    .A1(\rd_fifo[1][30] ),
    .A2(\rd_fifo[2][30] ),
    .A3(\rd_fifo[3][30] ),
    .S0(net321),
    .S1(net318),
    .X(_0778_));
 sky130_fd_sc_hd__mux4_2 _1620_ (.A0(\rd_fifo[12][30] ),
    .A1(\rd_fifo[13][30] ),
    .A2(\rd_fifo[14][30] ),
    .A3(\rd_fifo[15][30] ),
    .S0(net321),
    .S1(net318),
    .X(_0779_));
 sky130_fd_sc_hd__mux4_2 _1621_ (.A0(\rd_fifo[4][30] ),
    .A1(\rd_fifo[5][30] ),
    .A2(\rd_fifo[6][30] ),
    .A3(\rd_fifo[7][30] ),
    .S0(net321),
    .S1(net318),
    .X(_0780_));
 sky130_fd_sc_hd__mux4_2 _1622_ (.A0(_0777_),
    .A1(_0778_),
    .A2(_0779_),
    .A3(_0780_),
    .S0(net309),
    .S1(net317),
    .X(net120));
 sky130_fd_sc_hd__mux4_2 _1623_ (.A0(\rd_fifo[8][31] ),
    .A1(\rd_fifo[9][31] ),
    .A2(\rd_fifo[10][31] ),
    .A3(\rd_fifo[11][31] ),
    .S0(net321),
    .S1(net318),
    .X(_0781_));
 sky130_fd_sc_hd__mux4_2 _1624_ (.A0(\rd_fifo[0][31] ),
    .A1(\rd_fifo[1][31] ),
    .A2(\rd_fifo[2][31] ),
    .A3(\rd_fifo[3][31] ),
    .S0(net321),
    .S1(net318),
    .X(_0782_));
 sky130_fd_sc_hd__mux4_2 _1625_ (.A0(\rd_fifo[12][31] ),
    .A1(\rd_fifo[13][31] ),
    .A2(\rd_fifo[14][31] ),
    .A3(\rd_fifo[15][31] ),
    .S0(net323),
    .S1(net319),
    .X(_0783_));
 sky130_fd_sc_hd__mux4_2 _1626_ (.A0(\rd_fifo[4][31] ),
    .A1(\rd_fifo[5][31] ),
    .A2(\rd_fifo[6][31] ),
    .A3(\rd_fifo[7][31] ),
    .S0(net321),
    .S1(net318),
    .X(_0784_));
 sky130_fd_sc_hd__mux4_2 _1627_ (.A0(_0781_),
    .A1(_0782_),
    .A2(_0783_),
    .A3(_0784_),
    .S0(net309),
    .S1(net317),
    .X(net121));
 sky130_fd_sc_hd__mux4_2 _1628_ (.A0(\rd_fifo[8][32] ),
    .A1(\rd_fifo[9][32] ),
    .A2(\rd_fifo[10][32] ),
    .A3(\rd_fifo[11][32] ),
    .S0(net321),
    .S1(net318),
    .X(_0785_));
 sky130_fd_sc_hd__mux4_2 _1629_ (.A0(\rd_fifo[0][32] ),
    .A1(\rd_fifo[1][32] ),
    .A2(\rd_fifo[2][32] ),
    .A3(\rd_fifo[3][32] ),
    .S0(net321),
    .S1(net318),
    .X(_0786_));
 sky130_fd_sc_hd__mux4_2 _1630_ (.A0(\rd_fifo[12][32] ),
    .A1(\rd_fifo[13][32] ),
    .A2(\rd_fifo[14][32] ),
    .A3(\rd_fifo[15][32] ),
    .S0(net321),
    .S1(net318),
    .X(_0787_));
 sky130_fd_sc_hd__mux4_2 _1631_ (.A0(\rd_fifo[4][32] ),
    .A1(\rd_fifo[5][32] ),
    .A2(\rd_fifo[6][32] ),
    .A3(\rd_fifo[7][32] ),
    .S0(net321),
    .S1(net318),
    .X(_0788_));
 sky130_fd_sc_hd__mux4_2 _1632_ (.A0(_0785_),
    .A1(_0786_),
    .A2(_0787_),
    .A3(_0788_),
    .S0(net309),
    .S1(net317),
    .X(net122));
 sky130_fd_sc_hd__mux4_2 _1633_ (.A0(\rd_fifo[8][33] ),
    .A1(\rd_fifo[9][33] ),
    .A2(\rd_fifo[10][33] ),
    .A3(\rd_fifo[11][33] ),
    .S0(net321),
    .S1(net318),
    .X(_0789_));
 sky130_fd_sc_hd__mux4_2 _1634_ (.A0(\rd_fifo[0][33] ),
    .A1(\rd_fifo[1][33] ),
    .A2(\rd_fifo[2][33] ),
    .A3(\rd_fifo[3][33] ),
    .S0(net321),
    .S1(net318),
    .X(_0790_));
 sky130_fd_sc_hd__mux4_2 _1635_ (.A0(\rd_fifo[12][33] ),
    .A1(\rd_fifo[13][33] ),
    .A2(\rd_fifo[14][33] ),
    .A3(\rd_fifo[15][33] ),
    .S0(net321),
    .S1(net318),
    .X(_0791_));
 sky130_fd_sc_hd__mux4_2 _1636_ (.A0(\rd_fifo[4][33] ),
    .A1(\rd_fifo[5][33] ),
    .A2(\rd_fifo[6][33] ),
    .A3(\rd_fifo[7][33] ),
    .S0(net321),
    .S1(net318),
    .X(_0792_));
 sky130_fd_sc_hd__mux4_2 _1637_ (.A0(_0789_),
    .A1(_0790_),
    .A2(_0791_),
    .A3(_0792_),
    .S0(net309),
    .S1(net317),
    .X(net123));
 sky130_fd_sc_hd__mux4_2 _1638_ (.A0(\rd_fifo[8][6] ),
    .A1(\rd_fifo[9][6] ),
    .A2(\rd_fifo[10][6] ),
    .A3(\rd_fifo[11][6] ),
    .S0(net321),
    .S1(net318),
    .X(_0793_));
 sky130_fd_sc_hd__mux4_2 _1639_ (.A0(\rd_fifo[0][6] ),
    .A1(\rd_fifo[1][6] ),
    .A2(\rd_fifo[2][6] ),
    .A3(\rd_fifo[3][6] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0794_));
 sky130_fd_sc_hd__mux4_2 _1642_ (.A0(\rd_fifo[12][6] ),
    .A1(\rd_fifo[13][6] ),
    .A2(\rd_fifo[14][6] ),
    .A3(\rd_fifo[15][6] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0797_));
 sky130_fd_sc_hd__mux4_2 _1643_ (.A0(\rd_fifo[4][6] ),
    .A1(\rd_fifo[5][6] ),
    .A2(\rd_fifo[6][6] ),
    .A3(\rd_fifo[7][6] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0798_));
 sky130_fd_sc_hd__mux4_2 _1645_ (.A0(_0793_),
    .A1(_0794_),
    .A2(_0797_),
    .A3(_0798_),
    .S0(net309),
    .S1(net317),
    .X(net124));
 sky130_fd_sc_hd__mux4_2 _1646_ (.A0(\rd_fifo[8][34] ),
    .A1(\rd_fifo[9][34] ),
    .A2(\rd_fifo[10][34] ),
    .A3(\rd_fifo[11][34] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0800_));
 sky130_fd_sc_hd__mux4_2 _1647_ (.A0(\rd_fifo[0][34] ),
    .A1(\rd_fifo[1][34] ),
    .A2(\rd_fifo[2][34] ),
    .A3(\rd_fifo[3][34] ),
    .S0(net321),
    .S1(net318),
    .X(_0801_));
 sky130_fd_sc_hd__mux4_2 _1648_ (.A0(\rd_fifo[12][34] ),
    .A1(\rd_fifo[13][34] ),
    .A2(\rd_fifo[14][34] ),
    .A3(\rd_fifo[15][34] ),
    .S0(net321),
    .S1(net318),
    .X(_0802_));
 sky130_fd_sc_hd__mux4_2 _1649_ (.A0(\rd_fifo[4][34] ),
    .A1(\rd_fifo[5][34] ),
    .A2(\rd_fifo[6][34] ),
    .A3(\rd_fifo[7][34] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0803_));
 sky130_fd_sc_hd__mux4_2 _1650_ (.A0(_0800_),
    .A1(_0801_),
    .A2(_0802_),
    .A3(_0803_),
    .S0(net309),
    .S1(net317),
    .X(net125));
 sky130_fd_sc_hd__mux4_2 _1651_ (.A0(\rd_fifo[8][35] ),
    .A1(\rd_fifo[9][35] ),
    .A2(\rd_fifo[10][35] ),
    .A3(\rd_fifo[11][35] ),
    .S0(net321),
    .S1(net318),
    .X(_0804_));
 sky130_fd_sc_hd__mux4_2 _1652_ (.A0(\rd_fifo[0][35] ),
    .A1(\rd_fifo[1][35] ),
    .A2(\rd_fifo[2][35] ),
    .A3(\rd_fifo[3][35] ),
    .S0(net321),
    .S1(net318),
    .X(_0805_));
 sky130_fd_sc_hd__mux4_2 _1653_ (.A0(\rd_fifo[12][35] ),
    .A1(\rd_fifo[13][35] ),
    .A2(\rd_fifo[14][35] ),
    .A3(\rd_fifo[15][35] ),
    .S0(net321),
    .S1(net318),
    .X(_0806_));
 sky130_fd_sc_hd__mux4_2 _1654_ (.A0(\rd_fifo[4][35] ),
    .A1(\rd_fifo[5][35] ),
    .A2(\rd_fifo[6][35] ),
    .A3(\rd_fifo[7][35] ),
    .S0(net321),
    .S1(net318),
    .X(_0807_));
 sky130_fd_sc_hd__mux4_2 _1655_ (.A0(_0804_),
    .A1(_0805_),
    .A2(_0806_),
    .A3(_0807_),
    .S0(net309),
    .S1(net317),
    .X(net126));
 sky130_fd_sc_hd__mux4_2 _1656_ (.A0(\rd_fifo[8][7] ),
    .A1(\rd_fifo[9][7] ),
    .A2(\rd_fifo[10][7] ),
    .A3(\rd_fifo[11][7] ),
    .S0(net321),
    .S1(net318),
    .X(_0808_));
 sky130_fd_sc_hd__mux4_2 _1657_ (.A0(\rd_fifo[0][7] ),
    .A1(\rd_fifo[1][7] ),
    .A2(\rd_fifo[2][7] ),
    .A3(\rd_fifo[3][7] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0809_));
 sky130_fd_sc_hd__mux4_2 _1658_ (.A0(\rd_fifo[12][7] ),
    .A1(\rd_fifo[13][7] ),
    .A2(\rd_fifo[14][7] ),
    .A3(\rd_fifo[15][7] ),
    .S0(net321),
    .S1(net318),
    .X(_0810_));
 sky130_fd_sc_hd__mux4_2 _1659_ (.A0(\rd_fifo[4][7] ),
    .A1(\rd_fifo[5][7] ),
    .A2(\rd_fifo[6][7] ),
    .A3(\rd_fifo[7][7] ),
    .S0(net321),
    .S1(net318),
    .X(_0811_));
 sky130_fd_sc_hd__mux4_2 _1660_ (.A0(_0808_),
    .A1(_0809_),
    .A2(_0810_),
    .A3(_0811_),
    .S0(net309),
    .S1(net317),
    .X(net127));
 sky130_fd_sc_hd__mux4_2 _1661_ (.A0(\rd_fifo[8][8] ),
    .A1(\rd_fifo[9][8] ),
    .A2(\rd_fifo[10][8] ),
    .A3(\rd_fifo[11][8] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0812_));
 sky130_fd_sc_hd__mux4_2 _1662_ (.A0(\rd_fifo[0][8] ),
    .A1(\rd_fifo[1][8] ),
    .A2(\rd_fifo[2][8] ),
    .A3(\rd_fifo[3][8] ),
    .S0(\rd_rptr[0] ),
    .S1(\rd_rptr[1] ),
    .X(_0813_));
 sky130_fd_sc_hd__mux4_2 _1663_ (.A0(\rd_fifo[12][8] ),
    .A1(\rd_fifo[13][8] ),
    .A2(\rd_fifo[14][8] ),
    .A3(\rd_fifo[15][8] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0814_));
 sky130_fd_sc_hd__mux4_2 _1664_ (.A0(\rd_fifo[4][8] ),
    .A1(\rd_fifo[5][8] ),
    .A2(\rd_fifo[6][8] ),
    .A3(\rd_fifo[7][8] ),
    .S0(net),
    .S1(\rd_rptr[1] ),
    .X(_0815_));
 sky130_fd_sc_hd__mux4_2 _1665_ (.A0(_0812_),
    .A1(_0813_),
    .A2(_0814_),
    .A3(_0815_),
    .S0(net309),
    .S1(net317),
    .X(net128));
 sky130_fd_sc_hd__mux4_2 _1666_ (.A0(\rd_fifo[8][9] ),
    .A1(\rd_fifo[9][9] ),
    .A2(\rd_fifo[10][9] ),
    .A3(\rd_fifo[11][9] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0816_));
 sky130_fd_sc_hd__mux4_2 _1667_ (.A0(\rd_fifo[0][9] ),
    .A1(\rd_fifo[1][9] ),
    .A2(\rd_fifo[2][9] ),
    .A3(\rd_fifo[3][9] ),
    .S0(\rd_rptr[0] ),
    .S1(\rd_rptr[1] ),
    .X(_0817_));
 sky130_fd_sc_hd__mux4_2 _1668_ (.A0(\rd_fifo[12][9] ),
    .A1(\rd_fifo[13][9] ),
    .A2(\rd_fifo[14][9] ),
    .A3(\rd_fifo[15][9] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0818_));
 sky130_fd_sc_hd__mux4_2 _1669_ (.A0(\rd_fifo[4][9] ),
    .A1(\rd_fifo[5][9] ),
    .A2(\rd_fifo[6][9] ),
    .A3(\rd_fifo[7][9] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0819_));
 sky130_fd_sc_hd__mux4_2 _1670_ (.A0(_0816_),
    .A1(_0817_),
    .A2(_0818_),
    .A3(_0819_),
    .S0(_0286_),
    .S1(\rd_rptr[2] ),
    .X(net129));
 sky130_fd_sc_hd__mux4_2 _1671_ (.A0(\rd_fifo[8][10] ),
    .A1(\rd_fifo[9][10] ),
    .A2(\rd_fifo[10][10] ),
    .A3(\rd_fifo[11][10] ),
    .S0(net323),
    .S1(net319),
    .X(_0820_));
 sky130_fd_sc_hd__mux4_2 _1672_ (.A0(\rd_fifo[0][10] ),
    .A1(\rd_fifo[1][10] ),
    .A2(\rd_fifo[2][10] ),
    .A3(\rd_fifo[3][10] ),
    .S0(net323),
    .S1(net319),
    .X(_0821_));
 sky130_fd_sc_hd__mux4_2 _1673_ (.A0(\rd_fifo[12][10] ),
    .A1(\rd_fifo[13][10] ),
    .A2(\rd_fifo[14][10] ),
    .A3(\rd_fifo[15][10] ),
    .S0(net),
    .S1(net319),
    .X(_0822_));
 sky130_fd_sc_hd__mux4_2 _1674_ (.A0(\rd_fifo[4][10] ),
    .A1(\rd_fifo[5][10] ),
    .A2(\rd_fifo[6][10] ),
    .A3(\rd_fifo[7][10] ),
    .S0(net323),
    .S1(net319),
    .X(_0823_));
 sky130_fd_sc_hd__mux4_2 _1675_ (.A0(_0820_),
    .A1(_0821_),
    .A2(_0822_),
    .A3(_0823_),
    .S0(net309),
    .S1(net317),
    .X(net130));
 sky130_fd_sc_hd__mux4_2 _1676_ (.A0(\rd_fifo[8][11] ),
    .A1(\rd_fifo[9][11] ),
    .A2(\rd_fifo[10][11] ),
    .A3(\rd_fifo[11][11] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0824_));
 sky130_fd_sc_hd__mux4_2 _1677_ (.A0(\rd_fifo[0][11] ),
    .A1(\rd_fifo[1][11] ),
    .A2(\rd_fifo[2][11] ),
    .A3(\rd_fifo[3][11] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0825_));
 sky130_fd_sc_hd__mux4_2 _1678_ (.A0(\rd_fifo[12][11] ),
    .A1(\rd_fifo[13][11] ),
    .A2(\rd_fifo[14][11] ),
    .A3(\rd_fifo[15][11] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0826_));
 sky130_fd_sc_hd__mux4_2 _1679_ (.A0(\rd_fifo[4][11] ),
    .A1(\rd_fifo[5][11] ),
    .A2(\rd_fifo[6][11] ),
    .A3(\rd_fifo[7][11] ),
    .S0(\rd_rptr[0] ),
    .S1(net320),
    .X(_0827_));
 sky130_fd_sc_hd__mux4_2 _1680_ (.A0(_0824_),
    .A1(_0825_),
    .A2(_0826_),
    .A3(_0827_),
    .S0(_0286_),
    .S1(\rd_rptr[2] ),
    .X(net131));
 sky130_fd_sc_hd__mux4_2 _1681_ (.A0(\rd_fifo[8][12] ),
    .A1(\rd_fifo[9][12] ),
    .A2(\rd_fifo[10][12] ),
    .A3(\rd_fifo[11][12] ),
    .S0(net),
    .S1(net319),
    .X(_0828_));
 sky130_fd_sc_hd__mux4_2 _1682_ (.A0(\rd_fifo[0][12] ),
    .A1(\rd_fifo[1][12] ),
    .A2(\rd_fifo[2][12] ),
    .A3(\rd_fifo[3][12] ),
    .S0(net),
    .S1(net319),
    .X(_0829_));
 sky130_fd_sc_hd__mux4_2 _1683_ (.A0(\rd_fifo[12][12] ),
    .A1(\rd_fifo[13][12] ),
    .A2(\rd_fifo[14][12] ),
    .A3(\rd_fifo[15][12] ),
    .S0(net),
    .S1(net319),
    .X(_0830_));
 sky130_fd_sc_hd__mux4_2 _1684_ (.A0(\rd_fifo[4][12] ),
    .A1(\rd_fifo[5][12] ),
    .A2(\rd_fifo[6][12] ),
    .A3(\rd_fifo[7][12] ),
    .S0(net),
    .S1(net319),
    .X(_0831_));
 sky130_fd_sc_hd__mux4_2 _1685_ (.A0(_0828_),
    .A1(_0829_),
    .A2(_0830_),
    .A3(_0831_),
    .S0(net309),
    .S1(net317),
    .X(net132));
 sky130_fd_sc_hd__mux4_2 _1686_ (.A0(\rd_fifo[8][13] ),
    .A1(\rd_fifo[9][13] ),
    .A2(\rd_fifo[10][13] ),
    .A3(\rd_fifo[11][13] ),
    .S0(\rd_rptr[0] ),
    .S1(\rd_rptr[1] ),
    .X(_0832_));
 sky130_fd_sc_hd__mux4_2 _1687_ (.A0(\rd_fifo[0][13] ),
    .A1(\rd_fifo[1][13] ),
    .A2(\rd_fifo[2][13] ),
    .A3(\rd_fifo[3][13] ),
    .S0(\rd_rptr[0] ),
    .S1(\rd_rptr[1] ),
    .X(_0833_));
 sky130_fd_sc_hd__mux4_2 _1688_ (.A0(\rd_fifo[12][13] ),
    .A1(\rd_fifo[13][13] ),
    .A2(\rd_fifo[14][13] ),
    .A3(\rd_fifo[15][13] ),
    .S0(\rd_rptr[0] ),
    .S1(\rd_rptr[1] ),
    .X(_0834_));
 sky130_fd_sc_hd__mux4_2 _1689_ (.A0(\rd_fifo[4][13] ),
    .A1(\rd_fifo[5][13] ),
    .A2(\rd_fifo[6][13] ),
    .A3(\rd_fifo[7][13] ),
    .S0(\rd_rptr[0] ),
    .S1(\rd_rptr[1] ),
    .X(_0835_));
 sky130_fd_sc_hd__mux4_2 _1690_ (.A0(_0832_),
    .A1(_0833_),
    .A2(_0834_),
    .A3(_0835_),
    .S0(_0286_),
    .S1(\rd_rptr[2] ),
    .X(net133));
 sky130_fd_sc_hd__or4_1 _1691_ (.A(_0207_),
    .B(_0211_),
    .C(_0214_),
    .D(_0217_),
    .X(net135));
 sky130_fd_sc_hd__ha_1 _1692_ (.A(net315),
    .B(\wr_rptr[1] ),
    .COUT(_0038_),
    .SUM(_0039_));
 sky130_fd_sc_hd__ha_1 _1693_ (.A(_0040_),
    .B(_0041_),
    .COUT(_0042_),
    .SUM(_0043_));
 sky130_fd_sc_hd__ha_1 _1694_ (.A(_0040_),
    .B(\wr_wptr[1] ),
    .COUT(_0044_),
    .SUM(_0836_));
 sky130_fd_sc_hd__ha_1 _1695_ (.A(\wr_wptr[0] ),
    .B(_0041_),
    .COUT(_0045_),
    .SUM(_0837_));
 sky130_fd_sc_hd__ha_1 _1696_ (.A(\wr_wptr[0] ),
    .B(\wr_wptr[1] ),
    .COUT(_0046_),
    .SUM(_0838_));
 sky130_fd_sc_hd__ha_1 _1697_ (.A(net),
    .B(\rd_rptr[1] ),
    .COUT(_0047_),
    .SUM(_0048_));
 sky130_fd_sc_hd__ha_1 _1698_ (.A(_0049_),
    .B(_0050_),
    .COUT(_0051_),
    .SUM(_0052_));
 sky130_fd_sc_hd__ha_1 _1699_ (.A(_0049_),
    .B(\rd_wptr[1] ),
    .COUT(_0053_),
    .SUM(_0839_));
 sky130_fd_sc_hd__ha_1 _1700_ (.A(\rd_wptr[0] ),
    .B(_0050_),
    .COUT(_0054_),
    .SUM(_0840_));
 sky130_fd_sc_hd__ha_1 _1701_ (.A(\rd_wptr[0] ),
    .B(\rd_wptr[1] ),
    .COUT(_0055_),
    .SUM(_0841_));
 sky130_fd_sc_hd__ha_1 _1702_ (.A(_0040_),
    .B(\wr_rptr[0] ),
    .COUT(_0056_),
    .SUM(_0057_));
 sky130_fd_sc_hd__ha_1 _1703_ (.A(\wr_wptr[1] ),
    .B(_0058_),
    .COUT(_0059_),
    .SUM(_0060_));
 sky130_fd_sc_hd__ha_1 _1704_ (.A(\wr_wptr[3] ),
    .B(_0281_),
    .COUT(_0062_),
    .SUM(_0063_));
 sky130_fd_sc_hd__ha_1 _1705_ (.A(\wr_wptr[2] ),
    .B(_0064_),
    .COUT(_0065_),
    .SUM(_0066_));
 sky130_fd_sc_hd__ha_1 _1706_ (.A(_0049_),
    .B(\rd_rptr[0] ),
    .COUT(_0067_),
    .SUM(_0068_));
 sky130_fd_sc_hd__ha_1 _1707_ (.A(\rd_wptr[1] ),
    .B(_0069_),
    .COUT(_0070_),
    .SUM(_0071_));
 sky130_fd_sc_hd__ha_1 _1708_ (.A(\rd_wptr[2] ),
    .B(_0072_),
    .COUT(_0073_),
    .SUM(_0074_));
 sky130_fd_sc_hd__ha_1 _1709_ (.A(\rd_wptr[3] ),
    .B(_0286_),
    .COUT(_0076_),
    .SUM(_0077_));
 sky130_fd_sc_hd__ha_1 _1710_ (.A(_0078_),
    .B(_0079_),
    .COUT(_0080_),
    .SUM(_0081_));
 sky130_fd_sc_hd__ha_1 _1711_ (.A(\rd_burst_ctr[0] ),
    .B(_0079_),
    .COUT(_0082_),
    .SUM(_0842_));
 sky130_fd_sc_hd__ha_1 _1712_ (.A(\rd_burst_ctr[0] ),
    .B(\rd_burst_ctr[1] ),
    .COUT(_0083_),
    .SUM(_0843_));
 sky130_fd_sc_hd__ha_1 _1713_ (.A(\rd_burst_ctr[0] ),
    .B(\rd_burst_ctr[1] ),
    .COUT(_0084_),
    .SUM(_0844_));
 sky130_fd_sc_hd__ha_1 _1714_ (.A(_0085_),
    .B(_0086_),
    .COUT(_0087_),
    .SUM(_0088_));
 sky130_fd_sc_hd__ha_1 _1715_ (.A(net11),
    .B(_0086_),
    .COUT(_0089_),
    .SUM(_0845_));
 sky130_fd_sc_hd__ha_1 _1716_ (.A(_0090_),
    .B(_0091_),
    .COUT(_0092_),
    .SUM(_0093_));
 sky130_fd_sc_hd__ha_1 _1717_ (.A(\wr_burst_ctr[0] ),
    .B(_0094_),
    .COUT(_0095_),
    .SUM(_0096_));
 sky130_fd_sc_hd__ha_1 _1718_ (.A(_0097_),
    .B(_0098_),
    .COUT(_0099_),
    .SUM(_0100_));
 sky130_fd_sc_hd__ha_1 _1719_ (.A(net3),
    .B(_0098_),
    .COUT(_0101_),
    .SUM(_0846_));
 sky130_fd_sc_hd__ha_1 _1720_ (.A(_0102_),
    .B(_0103_),
    .COUT(_0104_),
    .SUM(_0105_));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_0_clk (.A(clk),
    .X(clknet_0_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_0__f_clk (.A(clknet_0_clk),
    .X(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_1__f_clk (.A(clknet_0_clk),
    .X(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_2__f_clk (.A(clknet_0_clk),
    .X(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_3__f_clk (.A(clknet_0_clk),
    .X(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_4__f_clk (.A(clknet_0_clk),
    .X(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_5__f_clk (.A(clknet_0_clk),
    .X(clknet_3_5__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_6__f_clk (.A(clknet_0_clk),
    .X(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_3_7__f_clk (.A(clknet_0_clk),
    .X(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_0_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_0_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_100_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_100_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_101_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_101_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_102_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_102_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_103_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_103_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_104_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_104_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_105_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_105_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_106_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_106_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_107_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_107_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_108_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_108_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_10_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_10_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_11_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_11_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_12_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_12_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_13_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_13_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_14_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_14_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_15_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_15_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_16_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_16_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_17_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_17_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_18_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_18_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_19_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_19_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_1_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_1_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_20_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_20_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_21_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_21_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_22_clk (.A(clknet_3_1__leaf_clk),
    .X(clknet_leaf_22_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_23_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_23_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_24_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_24_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_25_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_25_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_26_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_26_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_27_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_27_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_28_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_28_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_29_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_29_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_2_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_2_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_30_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_30_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_31_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_31_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_32_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_32_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_33_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_33_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_34_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_34_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_35_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_35_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_36_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_36_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_37_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_37_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_38_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_38_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_39_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_39_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_3_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_3_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_40_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_40_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_41_clk (.A(clknet_3_2__leaf_clk),
    .X(clknet_leaf_41_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_42_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_42_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_43_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_43_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_44_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_44_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_45_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_45_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_46_clk (.A(clknet_3_3__leaf_clk),
    .X(clknet_leaf_46_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_47_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_47_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_48_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_48_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_49_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_49_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_4_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_4_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_50_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_50_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_51_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_51_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_52_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_52_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_53_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_53_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_54_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_54_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_55_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_55_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_56_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_56_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_57_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_57_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_58_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_58_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_59_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_59_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_5_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_5_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_60_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_60_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_61_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_61_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_62_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_62_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_63_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_63_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_64_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_64_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_65_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_65_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_66_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_66_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_67_clk (.A(clknet_3_6__leaf_clk),
    .X(clknet_leaf_67_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_68_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_68_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_69_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_69_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_6_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_6_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_70_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_70_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_71_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_71_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_72_clk (.A(clknet_3_7__leaf_clk),
    .X(clknet_leaf_72_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_73_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_73_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_74_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_74_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_75_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_75_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_76_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_76_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_77_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_77_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_78_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_78_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_79_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_79_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_7_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_7_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_80_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_80_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_81_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_81_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_82_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_82_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_83_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_83_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_84_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_84_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_85_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_85_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_86_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_86_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_87_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_87_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_88_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_88_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_89_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_89_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_8_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_8_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_90_clk (.A(clknet_3_5__leaf_clk),
    .X(clknet_leaf_90_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_91_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_91_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_92_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_92_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_93_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_93_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_94_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_94_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_95_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_95_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_96_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_96_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_97_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_97_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_98_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_98_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_99_clk (.A(clknet_3_4__leaf_clk),
    .X(clknet_leaf_99_clk));
 sky130_fd_sc_hd__clkbuf_16 clkbuf_leaf_9_clk (.A(clknet_3_0__leaf_clk),
    .X(clknet_leaf_9_clk));
 sky130_fd_sc_hd__clkbuf_16 clkload0 (.A(clknet_3_0__leaf_clk));
 sky130_fd_sc_hd__clkinv_16 clkload1 (.A(clknet_3_1__leaf_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload10 (.A(clknet_leaf_4_clk));
 sky130_fd_sc_hd__clkinv_2 clkload100 (.A(clknet_leaf_52_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload101 (.A(clknet_leaf_53_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload102 (.A(clknet_leaf_55_clk));
 sky130_fd_sc_hd__clkbuf_8 clkload103 (.A(clknet_leaf_68_clk));
 sky130_fd_sc_hd__bufinv_16 clkload104 (.A(clknet_leaf_69_clk));
 sky130_fd_sc_hd__clkinv_2 clkload105 (.A(clknet_leaf_70_clk));
 sky130_fd_sc_hd__clkbuf_8 clkload106 (.A(clknet_leaf_71_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload107 (.A(clknet_leaf_72_clk));
 sky130_fd_sc_hd__clkinv_1 clkload11 (.A(clknet_leaf_5_clk));
 sky130_fd_sc_hd__clkinv_1 clkload12 (.A(clknet_leaf_6_clk));
 sky130_fd_sc_hd__clkinv_2 clkload13 (.A(clknet_leaf_7_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload14 (.A(clknet_leaf_8_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload15 (.A(clknet_leaf_9_clk));
 sky130_fd_sc_hd__clkinv_2 clkload16 (.A(clknet_leaf_10_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload17 (.A(clknet_leaf_11_clk));
 sky130_fd_sc_hd__clkinv_1 clkload18 (.A(clknet_leaf_12_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload19 (.A(clknet_leaf_13_clk));
 sky130_fd_sc_hd__clkinv_16 clkload2 (.A(clknet_3_2__leaf_clk));
 sky130_fd_sc_hd__clkinv_1 clkload20 (.A(clknet_leaf_14_clk));
 sky130_fd_sc_hd__bufinv_16 clkload21 (.A(clknet_leaf_16_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload22 (.A(clknet_leaf_107_clk));
 sky130_fd_sc_hd__clkinv_1 clkload23 (.A(clknet_leaf_108_clk));
 sky130_fd_sc_hd__clkinv_1 clkload24 (.A(clknet_leaf_15_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload25 (.A(clknet_leaf_17_clk));
 sky130_fd_sc_hd__clkinv_1 clkload26 (.A(clknet_leaf_18_clk));
 sky130_fd_sc_hd__clkinv_1 clkload27 (.A(clknet_leaf_19_clk));
 sky130_fd_sc_hd__clkinv_2 clkload28 (.A(clknet_leaf_20_clk));
 sky130_fd_sc_hd__inv_6 clkload29 (.A(clknet_leaf_22_clk));
 sky130_fd_sc_hd__clkinv_16 clkload3 (.A(clknet_3_3__leaf_clk));
 sky130_fd_sc_hd__clkinv_1 clkload30 (.A(clknet_leaf_101_clk));
 sky130_fd_sc_hd__clkinv_2 clkload31 (.A(clknet_leaf_102_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload32 (.A(clknet_leaf_103_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload33 (.A(clknet_leaf_104_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload34 (.A(clknet_leaf_105_clk));
 sky130_fd_sc_hd__clkbuf_8 clkload35 (.A(clknet_leaf_106_clk));
 sky130_fd_sc_hd__clkinv_2 clkload36 (.A(clknet_leaf_28_clk));
 sky130_fd_sc_hd__bufinv_16 clkload37 (.A(clknet_leaf_30_clk));
 sky130_fd_sc_hd__bufinv_16 clkload38 (.A(clknet_leaf_31_clk));
 sky130_fd_sc_hd__bufinv_16 clkload39 (.A(clknet_leaf_32_clk));
 sky130_fd_sc_hd__clkinv_16 clkload4 (.A(clknet_3_4__leaf_clk));
 sky130_fd_sc_hd__clkinv_1 clkload40 (.A(clknet_leaf_33_clk));
 sky130_fd_sc_hd__clkinv_2 clkload41 (.A(clknet_leaf_35_clk));
 sky130_fd_sc_hd__clkinv_2 clkload42 (.A(clknet_leaf_36_clk));
 sky130_fd_sc_hd__clkinv_2 clkload43 (.A(clknet_leaf_37_clk));
 sky130_fd_sc_hd__clkinv_2 clkload44 (.A(clknet_leaf_38_clk));
 sky130_fd_sc_hd__clkinv_2 clkload45 (.A(clknet_leaf_39_clk));
 sky130_fd_sc_hd__inv_6 clkload46 (.A(clknet_leaf_41_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload47 (.A(clknet_leaf_23_clk));
 sky130_fd_sc_hd__clkinv_2 clkload48 (.A(clknet_leaf_24_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload49 (.A(clknet_leaf_25_clk));
 sky130_fd_sc_hd__clkinv_16 clkload5 (.A(clknet_3_6__leaf_clk));
 sky130_fd_sc_hd__clkinv_1 clkload50 (.A(clknet_leaf_26_clk));
 sky130_fd_sc_hd__clkinv_1 clkload51 (.A(clknet_leaf_29_clk));
 sky130_fd_sc_hd__clkinv_4 clkload52 (.A(clknet_leaf_40_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload53 (.A(clknet_leaf_42_clk));
 sky130_fd_sc_hd__inv_6 clkload54 (.A(clknet_leaf_43_clk));
 sky130_fd_sc_hd__clkinv_1 clkload55 (.A(clknet_leaf_44_clk));
 sky130_fd_sc_hd__clkinv_1 clkload56 (.A(clknet_leaf_45_clk));
 sky130_fd_sc_hd__bufinv_16 clkload57 (.A(clknet_leaf_46_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload58 (.A(clknet_leaf_62_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload59 (.A(clknet_leaf_63_clk));
 sky130_fd_sc_hd__clkinv_16 clkload6 (.A(clknet_3_7__leaf_clk));
 sky130_fd_sc_hd__clkinv_2 clkload60 (.A(clknet_leaf_64_clk));
 sky130_fd_sc_hd__clkinv_2 clkload61 (.A(clknet_leaf_91_clk));
 sky130_fd_sc_hd__clkinv_2 clkload62 (.A(clknet_leaf_92_clk));
 sky130_fd_sc_hd__clkbuf_8 clkload63 (.A(clknet_leaf_94_clk));
 sky130_fd_sc_hd__inv_8 clkload64 (.A(clknet_leaf_95_clk));
 sky130_fd_sc_hd__clkinv_2 clkload65 (.A(clknet_leaf_96_clk));
 sky130_fd_sc_hd__bufinv_16 clkload66 (.A(clknet_leaf_97_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload67 (.A(clknet_leaf_98_clk));
 sky130_fd_sc_hd__clkbuf_8 clkload68 (.A(clknet_leaf_99_clk));
 sky130_fd_sc_hd__inv_8 clkload69 (.A(clknet_leaf_100_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload7 (.A(clknet_leaf_1_clk));
 sky130_fd_sc_hd__clkinv_1 clkload70 (.A(clknet_leaf_65_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload71 (.A(clknet_leaf_73_clk));
 sky130_fd_sc_hd__clkinv_2 clkload72 (.A(clknet_leaf_74_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload73 (.A(clknet_leaf_75_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload74 (.A(clknet_leaf_76_clk));
 sky130_fd_sc_hd__clkinv_2 clkload75 (.A(clknet_leaf_77_clk));
 sky130_fd_sc_hd__clkinv_2 clkload76 (.A(clknet_leaf_78_clk));
 sky130_fd_sc_hd__clkinv_1 clkload77 (.A(clknet_leaf_79_clk));
 sky130_fd_sc_hd__clkinv_1 clkload78 (.A(clknet_leaf_80_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload79 (.A(clknet_leaf_81_clk));
 sky130_fd_sc_hd__clkinv_1 clkload8 (.A(clknet_leaf_2_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload80 (.A(clknet_leaf_83_clk));
 sky130_fd_sc_hd__clkinv_1 clkload81 (.A(clknet_leaf_84_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload82 (.A(clknet_leaf_85_clk));
 sky130_fd_sc_hd__clkinv_2 clkload83 (.A(clknet_leaf_86_clk));
 sky130_fd_sc_hd__clkinv_2 clkload84 (.A(clknet_leaf_87_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload85 (.A(clknet_leaf_88_clk));
 sky130_fd_sc_hd__clkinv_1 clkload86 (.A(clknet_leaf_89_clk));
 sky130_fd_sc_hd__clkinv_2 clkload87 (.A(clknet_leaf_90_clk));
 sky130_fd_sc_hd__inv_8 clkload88 (.A(clknet_leaf_47_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload89 (.A(clknet_leaf_54_clk));
 sky130_fd_sc_hd__clkinv_1 clkload9 (.A(clknet_leaf_3_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload90 (.A(clknet_leaf_56_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload91 (.A(clknet_leaf_57_clk));
 sky130_fd_sc_hd__clkinvlp_4 clkload92 (.A(clknet_leaf_58_clk));
 sky130_fd_sc_hd__bufinv_16 clkload93 (.A(clknet_leaf_59_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload94 (.A(clknet_leaf_60_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload95 (.A(clknet_leaf_67_clk));
 sky130_fd_sc_hd__clkinv_2 clkload96 (.A(clknet_leaf_48_clk));
 sky130_fd_sc_hd__clkinv_2 clkload97 (.A(clknet_leaf_49_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload98 (.A(clknet_leaf_50_clk));
 sky130_fd_sc_hd__clkbuf_1 clkload99 (.A(clknet_leaf_51_clk));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input1 (.A(cfg_CL_nCK[0]),
    .X(net1));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input10 (.A(cfg_CWL_nCK[1]),
    .X(net10));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input11 (.A(cfg_CWL_nCK[2]),
    .X(net11));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input12 (.A(cfg_CWL_nCK[3]),
    .X(net12));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input13 (.A(cfg_CWL_nCK[4]),
    .X(net13));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input14 (.A(cfg_CWL_nCK[5]),
    .X(net14));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input15 (.A(cfg_CWL_nCK[6]),
    .X(net15));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input16 (.A(cfg_CWL_nCK[7]),
    .X(net16));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input17 (.A(cmd_aux[0]),
    .X(net17));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input18 (.A(cmd_aux[1]),
    .X(net18));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input19 (.A(cmd_aux[2]),
    .X(net19));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input2 (.A(cfg_CL_nCK[1]),
    .X(net2));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input20 (.A(cmd_aux[3]),
    .X(net20));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input21 (.A(cmd_rd_valid),
    .X(net21));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input22 (.A(cmd_wr_valid),
    .X(net22));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input23 (.A(ddr_dq_i[0]),
    .X(net23));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input24 (.A(ddr_dq_i[10]),
    .X(net24));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input25 (.A(ddr_dq_i[11]),
    .X(net25));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input26 (.A(ddr_dq_i[12]),
    .X(net26));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input27 (.A(ddr_dq_i[13]),
    .X(net27));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input28 (.A(ddr_dq_i[14]),
    .X(net28));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input29 (.A(ddr_dq_i[15]),
    .X(net29));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input3 (.A(cfg_CL_nCK[2]),
    .X(net3));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input30 (.A(ddr_dq_i[1]),
    .X(net30));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input31 (.A(ddr_dq_i[2]),
    .X(net31));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input32 (.A(ddr_dq_i[3]),
    .X(net32));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input33 (.A(ddr_dq_i[4]),
    .X(net33));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input34 (.A(ddr_dq_i[5]),
    .X(net34));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input35 (.A(ddr_dq_i[6]),
    .X(net35));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input36 (.A(ddr_dq_i[7]),
    .X(net36));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input37 (.A(ddr_dq_i[8]),
    .X(net37));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input38 (.A(ddr_dq_i[9]),
    .X(net38));
 sky130_fd_sc_hd__buf_6 input39 (.A(rst_n),
    .X(net39));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input4 (.A(cfg_CL_nCK[3]),
    .X(net4));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input40 (.A(wr_data[0]),
    .X(net40));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input41 (.A(wr_data[10]),
    .X(net41));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input42 (.A(wr_data[11]),
    .X(net42));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input43 (.A(wr_data[12]),
    .X(net43));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input44 (.A(wr_data[13]),
    .X(net44));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input45 (.A(wr_data[14]),
    .X(net45));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input46 (.A(wr_data[15]),
    .X(net46));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input47 (.A(wr_data[16]),
    .X(net47));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input48 (.A(wr_data[17]),
    .X(net48));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input49 (.A(wr_data[18]),
    .X(net49));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input5 (.A(cfg_CL_nCK[4]),
    .X(net5));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input50 (.A(wr_data[19]),
    .X(net50));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input51 (.A(wr_data[1]),
    .X(net51));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input52 (.A(wr_data[20]),
    .X(net52));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input53 (.A(wr_data[21]),
    .X(net53));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input54 (.A(wr_data[22]),
    .X(net54));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input55 (.A(wr_data[23]),
    .X(net55));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input56 (.A(wr_data[24]),
    .X(net56));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input57 (.A(wr_data[25]),
    .X(net57));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input58 (.A(wr_data[26]),
    .X(net58));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input59 (.A(wr_data[27]),
    .X(net59));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input6 (.A(cfg_CL_nCK[5]),
    .X(net6));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input60 (.A(wr_data[28]),
    .X(net60));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input61 (.A(wr_data[29]),
    .X(net61));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input62 (.A(wr_data[2]),
    .X(net62));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input63 (.A(wr_data[30]),
    .X(net63));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input64 (.A(wr_data[31]),
    .X(net64));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input65 (.A(wr_data[3]),
    .X(net65));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input66 (.A(wr_data[4]),
    .X(net66));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input67 (.A(wr_data[5]),
    .X(net67));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input68 (.A(wr_data[6]),
    .X(net68));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input69 (.A(wr_data[7]),
    .X(net69));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input7 (.A(cfg_CL_nCK[6]),
    .X(net7));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input70 (.A(wr_data[8]),
    .X(net70));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input71 (.A(wr_data[9]),
    .X(net71));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input72 (.A(wr_data_valid),
    .X(net72));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input73 (.A(wr_mask[0]),
    .X(net73));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input74 (.A(wr_mask[1]),
    .X(net74));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input75 (.A(wr_mask[2]),
    .X(net75));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input76 (.A(wr_mask[3]),
    .X(net76));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input8 (.A(cfg_CL_nCK[7]),
    .X(net8));
 sky130_fd_sc_hd__clkdlybuf4s50_1 input9 (.A(cfg_CWL_nCK[0]),
    .X(net9));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output100 (.A(net100),
    .X(rd_rsp_aux[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output101 (.A(net101),
    .X(rd_rsp_aux[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output102 (.A(net102),
    .X(rd_rsp_data[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output103 (.A(net103),
    .X(rd_rsp_data[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output104 (.A(net104),
    .X(rd_rsp_data[11]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output105 (.A(net105),
    .X(rd_rsp_data[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output106 (.A(net106),
    .X(rd_rsp_data[13]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output107 (.A(net107),
    .X(rd_rsp_data[14]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output108 (.A(net108),
    .X(rd_rsp_data[15]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output109 (.A(net109),
    .X(rd_rsp_data[16]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output110 (.A(net110),
    .X(rd_rsp_data[17]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output111 (.A(net111),
    .X(rd_rsp_data[18]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output112 (.A(net112),
    .X(rd_rsp_data[19]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output113 (.A(net113),
    .X(rd_rsp_data[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output114 (.A(net114),
    .X(rd_rsp_data[20]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output115 (.A(net115),
    .X(rd_rsp_data[21]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output116 (.A(net116),
    .X(rd_rsp_data[22]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output117 (.A(net117),
    .X(rd_rsp_data[23]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output118 (.A(net118),
    .X(rd_rsp_data[24]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output119 (.A(net119),
    .X(rd_rsp_data[25]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output120 (.A(net120),
    .X(rd_rsp_data[26]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output121 (.A(net121),
    .X(rd_rsp_data[27]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output122 (.A(net122),
    .X(rd_rsp_data[28]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output123 (.A(net123),
    .X(rd_rsp_data[29]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output124 (.A(net124),
    .X(rd_rsp_data[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output125 (.A(net125),
    .X(rd_rsp_data[30]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output126 (.A(net126),
    .X(rd_rsp_data[31]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output127 (.A(net127),
    .X(rd_rsp_data[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output128 (.A(net128),
    .X(rd_rsp_data[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output129 (.A(net129),
    .X(rd_rsp_data[5]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output130 (.A(net130),
    .X(rd_rsp_data[6]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output131 (.A(net131),
    .X(rd_rsp_data[7]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output132 (.A(net132),
    .X(rd_rsp_data[8]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output133 (.A(net133),
    .X(rd_rsp_data[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output134 (.A(net134),
    .X(rd_rsp_valid));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output135 (.A(net135),
    .X(wr_data_ready));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output77 (.A(net77),
    .X(ddr_dm_o[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output78 (.A(net78),
    .X(ddr_dm_o[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output79 (.A(net79),
    .X(ddr_dq_o[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output80 (.A(net80),
    .X(ddr_dq_o[10]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output81 (.A(net81),
    .X(ddr_dq_o[11]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output82 (.A(net82),
    .X(ddr_dq_o[12]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output83 (.A(net83),
    .X(ddr_dq_o[13]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output84 (.A(net84),
    .X(ddr_dq_o[14]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output85 (.A(net85),
    .X(ddr_dq_o[15]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output86 (.A(net86),
    .X(ddr_dq_o[1]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output87 (.A(net87),
    .X(ddr_dq_o[2]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output88 (.A(net88),
    .X(ddr_dq_o[3]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output89 (.A(net89),
    .X(ddr_dq_o[4]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output90 (.A(net90),
    .X(ddr_dq_o[5]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output91 (.A(net91),
    .X(ddr_dq_o[6]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output92 (.A(net92),
    .X(ddr_dq_o[7]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output93 (.A(net93),
    .X(ddr_dq_o[8]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output94 (.A(net94),
    .X(ddr_dq_o[9]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output95 (.A(net95),
    .X(ddr_dq_oe));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output96 (.A(net95),
    .X(net96));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output97 (.A(net95),
    .X(net97));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output98 (.A(net98),
    .X(rd_rsp_aux[0]));
 sky130_fd_sc_hd__clkdlybuf4s50_1 output99 (.A(net99),
    .X(rd_rsp_aux[1]));
 sky130_fd_sc_hd__buf_12 place269 (.A(_0036_),
    .X(net269));
 sky130_fd_sc_hd__buf_12 place270 (.A(_0037_),
    .X(net270));
 sky130_fd_sc_hd__buf_12 place271 (.A(_0023_),
    .X(net271));
 sky130_fd_sc_hd__buf_12 place272 (.A(_0024_),
    .X(net272));
 sky130_fd_sc_hd__buf_12 place273 (.A(_0028_),
    .X(net273));
 sky130_fd_sc_hd__buf_12 place274 (.A(_0027_),
    .X(net274));
 sky130_fd_sc_hd__buf_12 place275 (.A(_0026_),
    .X(net275));
 sky130_fd_sc_hd__buf_12 place276 (.A(_0025_),
    .X(net276));
 sky130_fd_sc_hd__buf_4 place277 (.A(_0035_),
    .X(net277));
 sky130_fd_sc_hd__buf_4 place278 (.A(_0032_),
    .X(net278));
 sky130_fd_sc_hd__buf_4 place279 (.A(_0033_),
    .X(net279));
 sky130_fd_sc_hd__buf_4 place280 (.A(_0034_),
    .X(net280));
 sky130_fd_sc_hd__buf_4 place281 (.A(_0034_),
    .X(net281));
 sky130_fd_sc_hd__buf_4 place282 (.A(_0392_),
    .X(net282));
 sky130_fd_sc_hd__buf_12 place283 (.A(_0022_),
    .X(net283));
 sky130_fd_sc_hd__buf_12 place284 (.A(_0029_),
    .X(net284));
 sky130_fd_sc_hd__buf_12 place285 (.A(_0030_),
    .X(net285));
 sky130_fd_sc_hd__buf_12 place286 (.A(_0031_),
    .X(net286));
 sky130_fd_sc_hd__buf_4 place287 (.A(_0231_),
    .X(net287));
 sky130_fd_sc_hd__buf_4 place288 (.A(_0358_),
    .X(net288));
 sky130_fd_sc_hd__buf_4 place289 (.A(_0013_),
    .X(net289));
 sky130_fd_sc_hd__buf_4 place290 (.A(_0014_),
    .X(net290));
 sky130_fd_sc_hd__buf_4 place291 (.A(_0015_),
    .X(net291));
 sky130_fd_sc_hd__buf_12 place292 (.A(_0016_),
    .X(net292));
 sky130_fd_sc_hd__buf_12 place293 (.A(_0017_),
    .X(net293));
 sky130_fd_sc_hd__buf_4 place294 (.A(_0008_),
    .X(net294));
 sky130_fd_sc_hd__buf_12 place295 (.A(_0018_),
    .X(net295));
 sky130_fd_sc_hd__buf_4 place296 (.A(_0009_),
    .X(net296));
 sky130_fd_sc_hd__buf_4 place297 (.A(_0010_),
    .X(net297));
 sky130_fd_sc_hd__buf_4 place298 (.A(_0011_),
    .X(net298));
 sky130_fd_sc_hd__buf_4 place299 (.A(_0012_),
    .X(net299));
 sky130_fd_sc_hd__buf_12 place300 (.A(_0019_),
    .X(net300));
 sky130_fd_sc_hd__buf_4 place301 (.A(_0020_),
    .X(net301));
 sky130_fd_sc_hd__buf_4 place302 (.A(_0020_),
    .X(net302));
 sky130_fd_sc_hd__buf_4 place303 (.A(_0021_),
    .X(net303));
 sky130_fd_sc_hd__buf_4 place304 (.A(_0021_),
    .X(net304));
 sky130_fd_sc_hd__buf_4 place305 (.A(_0007_),
    .X(net305));
 sky130_fd_sc_hd__buf_4 place306 (.A(_0006_),
    .X(net306));
 sky130_fd_sc_hd__buf_4 place307 (.A(_0355_),
    .X(net307));
 sky130_fd_sc_hd__buf_4 place308 (.A(_0095_),
    .X(net308));
 sky130_fd_sc_hd__buf_12 place309 (.A(_0286_),
    .X(net309));
 sky130_fd_sc_hd__buf_4 place310 (.A(net311),
    .X(net310));
 sky130_fd_sc_hd__buf_4 place311 (.A(_0281_),
    .X(net311));
 sky130_fd_sc_hd__buf_4 place312 (.A(\wr_rptr[2] ),
    .X(net312));
 sky130_fd_sc_hd__buf_4 place313 (.A(net314),
    .X(net313));
 sky130_fd_sc_hd__buf_12 place314 (.A(\wr_rptr[1] ),
    .X(net314));
 sky130_fd_sc_hd__buf_12 place315 (.A(\wr_rptr[0] ),
    .X(net315));
 sky130_fd_sc_hd__buf_12 place316 (.A(\wr_rptr[0] ),
    .X(net316));
 sky130_fd_sc_hd__buf_4 place317 (.A(\rd_rptr[2] ),
    .X(net317));
 sky130_fd_sc_hd__buf_4 place318 (.A(\rd_rptr[1] ),
    .X(net318));
 sky130_fd_sc_hd__buf_12 place319 (.A(\rd_rptr[1] ),
    .X(net319));
 sky130_fd_sc_hd__buf_4 place320 (.A(\rd_rptr[1] ),
    .X(net320));
 sky130_fd_sc_hd__buf_12 place321 (.A(\rd_rptr[0] ),
    .X(net321));
 sky130_fd_sc_hd__buf_12 place322 (.A(\rd_rptr[0] ),
    .X(net322));
 sky130_fd_sc_hd__buf_12 place323 (.A(\rd_rptr[0] ),
    .X(net323));
 sky130_fd_sc_hd__buf_12 place324 (.A(\rd_rptr[0] ),
    .X(net324));
 sky130_fd_sc_hd__buf_4 place325 (.A(net39),
    .X(net325));
 sky130_fd_sc_hd__buf_4 place326 (.A(net39),
    .X(net326));
 sky130_fd_sc_hd__dfrtp_1 \rd_aux_r[0]$_DFFE_PN0P_  (.D(_0106_),
    .Q(\rd_aux_r[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_aux_r[1]$_DFFE_PN0P_  (.D(_0107_),
    .Q(\rd_aux_r[1] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_aux_r[2]$_DFFE_PN0P_  (.D(_0108_),
    .Q(\rd_aux_r[2] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_47_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_aux_r[3]$_DFFE_PN0P_  (.D(_0109_),
    .Q(\rd_aux_r[3] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_47_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_burst_ctr[0]$_DFFE_PN0P_  (.D(_0110_),
    .Q(\rd_burst_ctr[0] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_burst_ctr[1]$_DFFE_PN0P_  (.D(_0111_),
    .Q(\rd_burst_ctr[1] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net306),
    .Q(\rd_fifo[0][0] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net306),
    .Q(\rd_fifo[0][10] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net306),
    .Q(\rd_fifo[0][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net306),
    .Q(\rd_fifo[0][12] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(net306),
    .Q(\rd_fifo[0][13] ),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net306),
    .Q(\rd_fifo[0][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net306),
    .Q(\rd_fifo[0][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net306),
    .Q(\rd_fifo[0][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net306),
    .Q(\rd_fifo[0][17] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net306),
    .Q(\rd_fifo[0][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net306),
    .Q(\rd_fifo[0][19] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net306),
    .Q(\rd_fifo[0][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][20]$_DFFE_PP_  (.D(net23),
    .DE(net306),
    .Q(\rd_fifo[0][20] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][21]$_DFFE_PP_  (.D(net30),
    .DE(net306),
    .Q(\rd_fifo[0][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][22]$_DFFE_PP_  (.D(net31),
    .DE(net306),
    .Q(\rd_fifo[0][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][23]$_DFFE_PP_  (.D(net32),
    .DE(net306),
    .Q(\rd_fifo[0][23] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][24]$_DFFE_PP_  (.D(net33),
    .DE(net306),
    .Q(\rd_fifo[0][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][25]$_DFFE_PP_  (.D(net34),
    .DE(net306),
    .Q(\rd_fifo[0][25] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][26]$_DFFE_PP_  (.D(net35),
    .DE(net306),
    .Q(\rd_fifo[0][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][27]$_DFFE_PP_  (.D(net36),
    .DE(net306),
    .Q(\rd_fifo[0][27] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][28]$_DFFE_PP_  (.D(net37),
    .DE(net306),
    .Q(\rd_fifo[0][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][29]$_DFFE_PP_  (.D(net38),
    .DE(net306),
    .Q(\rd_fifo[0][29] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net306),
    .Q(\rd_fifo[0][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][30]$_DFFE_PP_  (.D(net24),
    .DE(net306),
    .Q(\rd_fifo[0][30] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][31]$_DFFE_PP_  (.D(net25),
    .DE(net306),
    .Q(\rd_fifo[0][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][32]$_DFFE_PP_  (.D(net26),
    .DE(net306),
    .Q(\rd_fifo[0][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][33]$_DFFE_PP_  (.D(net27),
    .DE(net306),
    .Q(\rd_fifo[0][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][34]$_DFFE_PP_  (.D(net28),
    .DE(net306),
    .Q(\rd_fifo[0][34] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][35]$_DFFE_PP_  (.D(net29),
    .DE(net306),
    .Q(\rd_fifo[0][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net306),
    .Q(\rd_fifo[0][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net306),
    .Q(\rd_fifo[0][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net306),
    .Q(\rd_fifo[0][5] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net306),
    .Q(\rd_fifo[0][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net306),
    .Q(\rd_fifo[0][7] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net306),
    .Q(\rd_fifo[0][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[0][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net306),
    .Q(\rd_fifo[0][9] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net305),
    .Q(\rd_fifo[10][0] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net305),
    .Q(\rd_fifo[10][10] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net305),
    .Q(\rd_fifo[10][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net305),
    .Q(\rd_fifo[10][12] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(net305),
    .Q(\rd_fifo[10][13] ),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net305),
    .Q(\rd_fifo[10][14] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net305),
    .Q(\rd_fifo[10][15] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net305),
    .Q(\rd_fifo[10][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net305),
    .Q(\rd_fifo[10][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net305),
    .Q(\rd_fifo[10][18] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net305),
    .Q(\rd_fifo[10][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net305),
    .Q(\rd_fifo[10][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][20]$_DFFE_PP_  (.D(net23),
    .DE(net305),
    .Q(\rd_fifo[10][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][21]$_DFFE_PP_  (.D(net30),
    .DE(net305),
    .Q(\rd_fifo[10][21] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][22]$_DFFE_PP_  (.D(net31),
    .DE(net305),
    .Q(\rd_fifo[10][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][23]$_DFFE_PP_  (.D(net32),
    .DE(net305),
    .Q(\rd_fifo[10][23] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][24]$_DFFE_PP_  (.D(net33),
    .DE(net305),
    .Q(\rd_fifo[10][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][25]$_DFFE_PP_  (.D(net34),
    .DE(net305),
    .Q(\rd_fifo[10][25] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][26]$_DFFE_PP_  (.D(net35),
    .DE(net305),
    .Q(\rd_fifo[10][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][27]$_DFFE_PP_  (.D(net36),
    .DE(net305),
    .Q(\rd_fifo[10][27] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][28]$_DFFE_PP_  (.D(net37),
    .DE(net305),
    .Q(\rd_fifo[10][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][29]$_DFFE_PP_  (.D(net38),
    .DE(net305),
    .Q(\rd_fifo[10][29] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net305),
    .Q(\rd_fifo[10][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][30]$_DFFE_PP_  (.D(net24),
    .DE(net305),
    .Q(\rd_fifo[10][30] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][31]$_DFFE_PP_  (.D(net25),
    .DE(net305),
    .Q(\rd_fifo[10][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][32]$_DFFE_PP_  (.D(net26),
    .DE(net305),
    .Q(\rd_fifo[10][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][33]$_DFFE_PP_  (.D(net27),
    .DE(net305),
    .Q(\rd_fifo[10][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][34]$_DFFE_PP_  (.D(net28),
    .DE(net305),
    .Q(\rd_fifo[10][34] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][35]$_DFFE_PP_  (.D(net29),
    .DE(net305),
    .Q(\rd_fifo[10][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net305),
    .Q(\rd_fifo[10][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net305),
    .Q(\rd_fifo[10][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net305),
    .Q(\rd_fifo[10][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net305),
    .Q(\rd_fifo[10][6] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net305),
    .Q(\rd_fifo[10][7] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net305),
    .Q(\rd_fifo[10][8] ),
    .CLK(clknet_leaf_95_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[10][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net305),
    .Q(\rd_fifo[10][9] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net294),
    .Q(\rd_fifo[11][0] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net294),
    .Q(\rd_fifo[11][10] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net294),
    .Q(\rd_fifo[11][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net294),
    .Q(\rd_fifo[11][12] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(net294),
    .Q(\rd_fifo[11][13] ),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net294),
    .Q(\rd_fifo[11][14] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net294),
    .Q(\rd_fifo[11][15] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net294),
    .Q(\rd_fifo[11][16] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net294),
    .Q(\rd_fifo[11][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net294),
    .Q(\rd_fifo[11][18] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net294),
    .Q(\rd_fifo[11][19] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net294),
    .Q(\rd_fifo[11][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][20]$_DFFE_PP_  (.D(net23),
    .DE(net294),
    .Q(\rd_fifo[11][20] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][21]$_DFFE_PP_  (.D(net30),
    .DE(net294),
    .Q(\rd_fifo[11][21] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][22]$_DFFE_PP_  (.D(net31),
    .DE(net294),
    .Q(\rd_fifo[11][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][23]$_DFFE_PP_  (.D(net32),
    .DE(net294),
    .Q(\rd_fifo[11][23] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][24]$_DFFE_PP_  (.D(net33),
    .DE(net294),
    .Q(\rd_fifo[11][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][25]$_DFFE_PP_  (.D(net34),
    .DE(net294),
    .Q(\rd_fifo[11][25] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][26]$_DFFE_PP_  (.D(net35),
    .DE(net294),
    .Q(\rd_fifo[11][26] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][27]$_DFFE_PP_  (.D(net36),
    .DE(net294),
    .Q(\rd_fifo[11][27] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][28]$_DFFE_PP_  (.D(net37),
    .DE(net294),
    .Q(\rd_fifo[11][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][29]$_DFFE_PP_  (.D(net38),
    .DE(net294),
    .Q(\rd_fifo[11][29] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net294),
    .Q(\rd_fifo[11][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][30]$_DFFE_PP_  (.D(net24),
    .DE(net294),
    .Q(\rd_fifo[11][30] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][31]$_DFFE_PP_  (.D(net25),
    .DE(net294),
    .Q(\rd_fifo[11][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][32]$_DFFE_PP_  (.D(net26),
    .DE(net294),
    .Q(\rd_fifo[11][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][33]$_DFFE_PP_  (.D(net27),
    .DE(net294),
    .Q(\rd_fifo[11][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][34]$_DFFE_PP_  (.D(net28),
    .DE(net294),
    .Q(\rd_fifo[11][34] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][35]$_DFFE_PP_  (.D(net29),
    .DE(net294),
    .Q(\rd_fifo[11][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net294),
    .Q(\rd_fifo[11][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net294),
    .Q(\rd_fifo[11][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net294),
    .Q(\rd_fifo[11][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net294),
    .Q(\rd_fifo[11][6] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net294),
    .Q(\rd_fifo[11][7] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net294),
    .Q(\rd_fifo[11][8] ),
    .CLK(clknet_leaf_95_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[11][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net294),
    .Q(\rd_fifo[11][9] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0009_),
    .Q(\rd_fifo[12][0] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net296),
    .Q(\rd_fifo[12][10] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0009_),
    .Q(\rd_fifo[12][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net296),
    .Q(\rd_fifo[12][12] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0009_),
    .Q(\rd_fifo[12][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net296),
    .Q(\rd_fifo[12][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net296),
    .Q(\rd_fifo[12][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net296),
    .Q(\rd_fifo[12][16] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net296),
    .Q(\rd_fifo[12][17] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net296),
    .Q(\rd_fifo[12][18] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net296),
    .Q(\rd_fifo[12][19] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0009_),
    .Q(\rd_fifo[12][1] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][20]$_DFFE_PP_  (.D(net23),
    .DE(net296),
    .Q(\rd_fifo[12][20] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][21]$_DFFE_PP_  (.D(net30),
    .DE(net296),
    .Q(\rd_fifo[12][21] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][22]$_DFFE_PP_  (.D(net31),
    .DE(net296),
    .Q(\rd_fifo[12][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][23]$_DFFE_PP_  (.D(net32),
    .DE(net296),
    .Q(\rd_fifo[12][23] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][24]$_DFFE_PP_  (.D(net33),
    .DE(net296),
    .Q(\rd_fifo[12][24] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][25]$_DFFE_PP_  (.D(net34),
    .DE(net296),
    .Q(\rd_fifo[12][25] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][26]$_DFFE_PP_  (.D(net35),
    .DE(net296),
    .Q(\rd_fifo[12][26] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][27]$_DFFE_PP_  (.D(net36),
    .DE(net296),
    .Q(\rd_fifo[12][27] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][28]$_DFFE_PP_  (.D(net37),
    .DE(net296),
    .Q(\rd_fifo[12][28] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][29]$_DFFE_PP_  (.D(net38),
    .DE(net296),
    .Q(\rd_fifo[12][29] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net296),
    .Q(\rd_fifo[12][2] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][30]$_DFFE_PP_  (.D(net24),
    .DE(net296),
    .Q(\rd_fifo[12][30] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][31]$_DFFE_PP_  (.D(net25),
    .DE(net296),
    .Q(\rd_fifo[12][31] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][32]$_DFFE_PP_  (.D(net26),
    .DE(net296),
    .Q(\rd_fifo[12][32] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][33]$_DFFE_PP_  (.D(net27),
    .DE(net296),
    .Q(\rd_fifo[12][33] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][34]$_DFFE_PP_  (.D(net28),
    .DE(net296),
    .Q(\rd_fifo[12][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][35]$_DFFE_PP_  (.D(net29),
    .DE(net296),
    .Q(\rd_fifo[12][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0009_),
    .Q(\rd_fifo[12][3] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net296),
    .Q(\rd_fifo[12][4] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net296),
    .Q(\rd_fifo[12][5] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net296),
    .Q(\rd_fifo[12][6] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net296),
    .Q(\rd_fifo[12][7] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net296),
    .Q(\rd_fifo[12][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[12][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0009_),
    .Q(\rd_fifo[12][9] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0010_),
    .Q(\rd_fifo[13][0] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net297),
    .Q(\rd_fifo[13][10] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0010_),
    .Q(\rd_fifo[13][11] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net297),
    .Q(\rd_fifo[13][12] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0010_),
    .Q(\rd_fifo[13][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net297),
    .Q(\rd_fifo[13][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net297),
    .Q(\rd_fifo[13][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net297),
    .Q(\rd_fifo[13][16] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net297),
    .Q(\rd_fifo[13][17] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net297),
    .Q(\rd_fifo[13][18] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net297),
    .Q(\rd_fifo[13][19] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0010_),
    .Q(\rd_fifo[13][1] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][20]$_DFFE_PP_  (.D(net23),
    .DE(net297),
    .Q(\rd_fifo[13][20] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][21]$_DFFE_PP_  (.D(net30),
    .DE(net297),
    .Q(\rd_fifo[13][21] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][22]$_DFFE_PP_  (.D(net31),
    .DE(net297),
    .Q(\rd_fifo[13][22] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][23]$_DFFE_PP_  (.D(net32),
    .DE(net297),
    .Q(\rd_fifo[13][23] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][24]$_DFFE_PP_  (.D(net33),
    .DE(net297),
    .Q(\rd_fifo[13][24] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][25]$_DFFE_PP_  (.D(net34),
    .DE(net297),
    .Q(\rd_fifo[13][25] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][26]$_DFFE_PP_  (.D(net35),
    .DE(net297),
    .Q(\rd_fifo[13][26] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][27]$_DFFE_PP_  (.D(net36),
    .DE(net297),
    .Q(\rd_fifo[13][27] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][28]$_DFFE_PP_  (.D(net37),
    .DE(net297),
    .Q(\rd_fifo[13][28] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][29]$_DFFE_PP_  (.D(net38),
    .DE(net297),
    .Q(\rd_fifo[13][29] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net297),
    .Q(\rd_fifo[13][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][30]$_DFFE_PP_  (.D(net24),
    .DE(net297),
    .Q(\rd_fifo[13][30] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][31]$_DFFE_PP_  (.D(net25),
    .DE(net297),
    .Q(\rd_fifo[13][31] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][32]$_DFFE_PP_  (.D(net26),
    .DE(net297),
    .Q(\rd_fifo[13][32] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][33]$_DFFE_PP_  (.D(net27),
    .DE(net297),
    .Q(\rd_fifo[13][33] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][34]$_DFFE_PP_  (.D(net28),
    .DE(net297),
    .Q(\rd_fifo[13][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][35]$_DFFE_PP_  (.D(net29),
    .DE(net297),
    .Q(\rd_fifo[13][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0010_),
    .Q(\rd_fifo[13][3] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net297),
    .Q(\rd_fifo[13][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net297),
    .Q(\rd_fifo[13][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net297),
    .Q(\rd_fifo[13][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net297),
    .Q(\rd_fifo[13][7] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net297),
    .Q(\rd_fifo[13][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[13][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0010_),
    .Q(\rd_fifo[13][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0011_),
    .Q(\rd_fifo[14][0] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net298),
    .Q(\rd_fifo[14][10] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0011_),
    .Q(\rd_fifo[14][11] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net298),
    .Q(\rd_fifo[14][12] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0011_),
    .Q(\rd_fifo[14][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net298),
    .Q(\rd_fifo[14][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net298),
    .Q(\rd_fifo[14][15] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net298),
    .Q(\rd_fifo[14][16] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net298),
    .Q(\rd_fifo[14][17] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net298),
    .Q(\rd_fifo[14][18] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net298),
    .Q(\rd_fifo[14][19] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0011_),
    .Q(\rd_fifo[14][1] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][20]$_DFFE_PP_  (.D(net23),
    .DE(net298),
    .Q(\rd_fifo[14][20] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][21]$_DFFE_PP_  (.D(net30),
    .DE(net298),
    .Q(\rd_fifo[14][21] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][22]$_DFFE_PP_  (.D(net31),
    .DE(net298),
    .Q(\rd_fifo[14][22] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][23]$_DFFE_PP_  (.D(net32),
    .DE(net298),
    .Q(\rd_fifo[14][23] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][24]$_DFFE_PP_  (.D(net33),
    .DE(net298),
    .Q(\rd_fifo[14][24] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][25]$_DFFE_PP_  (.D(net34),
    .DE(net298),
    .Q(\rd_fifo[14][25] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][26]$_DFFE_PP_  (.D(net35),
    .DE(net298),
    .Q(\rd_fifo[14][26] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][27]$_DFFE_PP_  (.D(net36),
    .DE(net298),
    .Q(\rd_fifo[14][27] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][28]$_DFFE_PP_  (.D(net37),
    .DE(net298),
    .Q(\rd_fifo[14][28] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][29]$_DFFE_PP_  (.D(net38),
    .DE(net298),
    .Q(\rd_fifo[14][29] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net298),
    .Q(\rd_fifo[14][2] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][30]$_DFFE_PP_  (.D(net24),
    .DE(net298),
    .Q(\rd_fifo[14][30] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][31]$_DFFE_PP_  (.D(net25),
    .DE(net298),
    .Q(\rd_fifo[14][31] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][32]$_DFFE_PP_  (.D(net26),
    .DE(net298),
    .Q(\rd_fifo[14][32] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][33]$_DFFE_PP_  (.D(net27),
    .DE(net298),
    .Q(\rd_fifo[14][33] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][34]$_DFFE_PP_  (.D(net28),
    .DE(net298),
    .Q(\rd_fifo[14][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][35]$_DFFE_PP_  (.D(net29),
    .DE(net298),
    .Q(\rd_fifo[14][35] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0011_),
    .Q(\rd_fifo[14][3] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net298),
    .Q(\rd_fifo[14][4] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net298),
    .Q(\rd_fifo[14][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net298),
    .Q(\rd_fifo[14][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net298),
    .Q(\rd_fifo[14][7] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net298),
    .Q(\rd_fifo[14][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[14][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0011_),
    .Q(\rd_fifo[14][9] ),
    .CLK(clknet_leaf_100_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0012_),
    .Q(\rd_fifo[15][0] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net299),
    .Q(\rd_fifo[15][10] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0012_),
    .Q(\rd_fifo[15][11] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net299),
    .Q(\rd_fifo[15][12] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0012_),
    .Q(\rd_fifo[15][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net299),
    .Q(\rd_fifo[15][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net299),
    .Q(\rd_fifo[15][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net299),
    .Q(\rd_fifo[15][16] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net299),
    .Q(\rd_fifo[15][17] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net299),
    .Q(\rd_fifo[15][18] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net299),
    .Q(\rd_fifo[15][19] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0012_),
    .Q(\rd_fifo[15][1] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][20]$_DFFE_PP_  (.D(net23),
    .DE(net299),
    .Q(\rd_fifo[15][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][21]$_DFFE_PP_  (.D(net30),
    .DE(net299),
    .Q(\rd_fifo[15][21] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][22]$_DFFE_PP_  (.D(net31),
    .DE(net299),
    .Q(\rd_fifo[15][22] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][23]$_DFFE_PP_  (.D(net32),
    .DE(net299),
    .Q(\rd_fifo[15][23] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][24]$_DFFE_PP_  (.D(net33),
    .DE(net299),
    .Q(\rd_fifo[15][24] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][25]$_DFFE_PP_  (.D(net34),
    .DE(net299),
    .Q(\rd_fifo[15][25] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][26]$_DFFE_PP_  (.D(net35),
    .DE(net299),
    .Q(\rd_fifo[15][26] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][27]$_DFFE_PP_  (.D(net36),
    .DE(net299),
    .Q(\rd_fifo[15][27] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][28]$_DFFE_PP_  (.D(net37),
    .DE(net299),
    .Q(\rd_fifo[15][28] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][29]$_DFFE_PP_  (.D(net38),
    .DE(net299),
    .Q(\rd_fifo[15][29] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net299),
    .Q(\rd_fifo[15][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][30]$_DFFE_PP_  (.D(net24),
    .DE(net299),
    .Q(\rd_fifo[15][30] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][31]$_DFFE_PP_  (.D(net25),
    .DE(net299),
    .Q(\rd_fifo[15][31] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][32]$_DFFE_PP_  (.D(net26),
    .DE(net299),
    .Q(\rd_fifo[15][32] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][33]$_DFFE_PP_  (.D(net27),
    .DE(net299),
    .Q(\rd_fifo[15][33] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][34]$_DFFE_PP_  (.D(net28),
    .DE(net299),
    .Q(\rd_fifo[15][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][35]$_DFFE_PP_  (.D(net29),
    .DE(net299),
    .Q(\rd_fifo[15][35] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0012_),
    .Q(\rd_fifo[15][3] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net299),
    .Q(\rd_fifo[15][4] ),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net299),
    .Q(\rd_fifo[15][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net299),
    .Q(\rd_fifo[15][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net299),
    .Q(\rd_fifo[15][7] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net299),
    .Q(\rd_fifo[15][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[15][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0012_),
    .Q(\rd_fifo[15][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net289),
    .Q(\rd_fifo[1][0] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net289),
    .Q(\rd_fifo[1][10] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net289),
    .Q(\rd_fifo[1][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net289),
    .Q(\rd_fifo[1][12] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(net289),
    .Q(\rd_fifo[1][13] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net289),
    .Q(\rd_fifo[1][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net289),
    .Q(\rd_fifo[1][15] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net289),
    .Q(\rd_fifo[1][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net289),
    .Q(\rd_fifo[1][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net289),
    .Q(\rd_fifo[1][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net289),
    .Q(\rd_fifo[1][19] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net289),
    .Q(\rd_fifo[1][1] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][20]$_DFFE_PP_  (.D(net23),
    .DE(net289),
    .Q(\rd_fifo[1][20] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][21]$_DFFE_PP_  (.D(net30),
    .DE(net289),
    .Q(\rd_fifo[1][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][22]$_DFFE_PP_  (.D(net31),
    .DE(net289),
    .Q(\rd_fifo[1][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][23]$_DFFE_PP_  (.D(net32),
    .DE(net289),
    .Q(\rd_fifo[1][23] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][24]$_DFFE_PP_  (.D(net33),
    .DE(net289),
    .Q(\rd_fifo[1][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][25]$_DFFE_PP_  (.D(net34),
    .DE(net289),
    .Q(\rd_fifo[1][25] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][26]$_DFFE_PP_  (.D(net35),
    .DE(net289),
    .Q(\rd_fifo[1][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][27]$_DFFE_PP_  (.D(net36),
    .DE(net289),
    .Q(\rd_fifo[1][27] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][28]$_DFFE_PP_  (.D(net37),
    .DE(net289),
    .Q(\rd_fifo[1][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][29]$_DFFE_PP_  (.D(net38),
    .DE(net289),
    .Q(\rd_fifo[1][29] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net289),
    .Q(\rd_fifo[1][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][30]$_DFFE_PP_  (.D(net24),
    .DE(net289),
    .Q(\rd_fifo[1][30] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][31]$_DFFE_PP_  (.D(net25),
    .DE(net289),
    .Q(\rd_fifo[1][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][32]$_DFFE_PP_  (.D(net26),
    .DE(net289),
    .Q(\rd_fifo[1][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][33]$_DFFE_PP_  (.D(net27),
    .DE(net289),
    .Q(\rd_fifo[1][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][34]$_DFFE_PP_  (.D(net28),
    .DE(net289),
    .Q(\rd_fifo[1][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][35]$_DFFE_PP_  (.D(net29),
    .DE(net289),
    .Q(\rd_fifo[1][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net289),
    .Q(\rd_fifo[1][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net289),
    .Q(\rd_fifo[1][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net289),
    .Q(\rd_fifo[1][5] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net289),
    .Q(\rd_fifo[1][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net289),
    .Q(\rd_fifo[1][7] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net289),
    .Q(\rd_fifo[1][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[1][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net289),
    .Q(\rd_fifo[1][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net290),
    .Q(\rd_fifo[2][0] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net290),
    .Q(\rd_fifo[2][10] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net290),
    .Q(\rd_fifo[2][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net290),
    .Q(\rd_fifo[2][12] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(net290),
    .Q(\rd_fifo[2][13] ),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net290),
    .Q(\rd_fifo[2][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net290),
    .Q(\rd_fifo[2][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net290),
    .Q(\rd_fifo[2][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net290),
    .Q(\rd_fifo[2][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net290),
    .Q(\rd_fifo[2][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net290),
    .Q(\rd_fifo[2][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net290),
    .Q(\rd_fifo[2][1] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][20]$_DFFE_PP_  (.D(net23),
    .DE(net290),
    .Q(\rd_fifo[2][20] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][21]$_DFFE_PP_  (.D(net30),
    .DE(net290),
    .Q(\rd_fifo[2][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][22]$_DFFE_PP_  (.D(net31),
    .DE(net290),
    .Q(\rd_fifo[2][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][23]$_DFFE_PP_  (.D(net32),
    .DE(net290),
    .Q(\rd_fifo[2][23] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][24]$_DFFE_PP_  (.D(net33),
    .DE(net290),
    .Q(\rd_fifo[2][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][25]$_DFFE_PP_  (.D(net34),
    .DE(net290),
    .Q(\rd_fifo[2][25] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][26]$_DFFE_PP_  (.D(net35),
    .DE(net290),
    .Q(\rd_fifo[2][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][27]$_DFFE_PP_  (.D(net36),
    .DE(net290),
    .Q(\rd_fifo[2][27] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][28]$_DFFE_PP_  (.D(net37),
    .DE(net290),
    .Q(\rd_fifo[2][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][29]$_DFFE_PP_  (.D(net38),
    .DE(net290),
    .Q(\rd_fifo[2][29] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net290),
    .Q(\rd_fifo[2][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][30]$_DFFE_PP_  (.D(net24),
    .DE(net290),
    .Q(\rd_fifo[2][30] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][31]$_DFFE_PP_  (.D(net25),
    .DE(net290),
    .Q(\rd_fifo[2][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][32]$_DFFE_PP_  (.D(net26),
    .DE(net290),
    .Q(\rd_fifo[2][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][33]$_DFFE_PP_  (.D(net27),
    .DE(net290),
    .Q(\rd_fifo[2][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][34]$_DFFE_PP_  (.D(net28),
    .DE(net290),
    .Q(\rd_fifo[2][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][35]$_DFFE_PP_  (.D(net29),
    .DE(net290),
    .Q(\rd_fifo[2][35] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net290),
    .Q(\rd_fifo[2][3] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net290),
    .Q(\rd_fifo[2][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net290),
    .Q(\rd_fifo[2][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net290),
    .Q(\rd_fifo[2][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net290),
    .Q(\rd_fifo[2][7] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net290),
    .Q(\rd_fifo[2][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[2][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net290),
    .Q(\rd_fifo[2][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net291),
    .Q(\rd_fifo[3][0] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net291),
    .Q(\rd_fifo[3][10] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net291),
    .Q(\rd_fifo[3][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net291),
    .Q(\rd_fifo[3][12] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(net291),
    .Q(\rd_fifo[3][13] ),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net291),
    .Q(\rd_fifo[3][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net291),
    .Q(\rd_fifo[3][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net291),
    .Q(\rd_fifo[3][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net291),
    .Q(\rd_fifo[3][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net291),
    .Q(\rd_fifo[3][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net291),
    .Q(\rd_fifo[3][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net291),
    .Q(\rd_fifo[3][1] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][20]$_DFFE_PP_  (.D(net23),
    .DE(net291),
    .Q(\rd_fifo[3][20] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][21]$_DFFE_PP_  (.D(net30),
    .DE(net291),
    .Q(\rd_fifo[3][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][22]$_DFFE_PP_  (.D(net31),
    .DE(net291),
    .Q(\rd_fifo[3][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][23]$_DFFE_PP_  (.D(net32),
    .DE(net291),
    .Q(\rd_fifo[3][23] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][24]$_DFFE_PP_  (.D(net33),
    .DE(net291),
    .Q(\rd_fifo[3][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][25]$_DFFE_PP_  (.D(net34),
    .DE(net291),
    .Q(\rd_fifo[3][25] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][26]$_DFFE_PP_  (.D(net35),
    .DE(net291),
    .Q(\rd_fifo[3][26] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][27]$_DFFE_PP_  (.D(net36),
    .DE(net291),
    .Q(\rd_fifo[3][27] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][28]$_DFFE_PP_  (.D(net37),
    .DE(net291),
    .Q(\rd_fifo[3][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][29]$_DFFE_PP_  (.D(net38),
    .DE(net291),
    .Q(\rd_fifo[3][29] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net291),
    .Q(\rd_fifo[3][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][30]$_DFFE_PP_  (.D(net24),
    .DE(net291),
    .Q(\rd_fifo[3][30] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][31]$_DFFE_PP_  (.D(net25),
    .DE(net291),
    .Q(\rd_fifo[3][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][32]$_DFFE_PP_  (.D(net26),
    .DE(net291),
    .Q(\rd_fifo[3][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][33]$_DFFE_PP_  (.D(net27),
    .DE(net291),
    .Q(\rd_fifo[3][33] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][34]$_DFFE_PP_  (.D(net28),
    .DE(net291),
    .Q(\rd_fifo[3][34] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][35]$_DFFE_PP_  (.D(net29),
    .DE(net291),
    .Q(\rd_fifo[3][35] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net291),
    .Q(\rd_fifo[3][3] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net291),
    .Q(\rd_fifo[3][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net291),
    .Q(\rd_fifo[3][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net291),
    .Q(\rd_fifo[3][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net291),
    .Q(\rd_fifo[3][7] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net291),
    .Q(\rd_fifo[3][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[3][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net291),
    .Q(\rd_fifo[3][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][0] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net292),
    .Q(\rd_fifo[4][10] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net292),
    .Q(\rd_fifo[4][12] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][14] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net292),
    .Q(\rd_fifo[4][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net292),
    .Q(\rd_fifo[4][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][20]$_DFFE_PP_  (.D(net23),
    .DE(net292),
    .Q(\rd_fifo[4][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][21]$_DFFE_PP_  (.D(net30),
    .DE(net292),
    .Q(\rd_fifo[4][21] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][22]$_DFFE_PP_  (.D(net31),
    .DE(net292),
    .Q(\rd_fifo[4][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][23]$_DFFE_PP_  (.D(net32),
    .DE(net292),
    .Q(\rd_fifo[4][23] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][24]$_DFFE_PP_  (.D(net33),
    .DE(net292),
    .Q(\rd_fifo[4][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][25]$_DFFE_PP_  (.D(net34),
    .DE(net292),
    .Q(\rd_fifo[4][25] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][26]$_DFFE_PP_  (.D(net35),
    .DE(net292),
    .Q(\rd_fifo[4][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][27]$_DFFE_PP_  (.D(net36),
    .DE(net292),
    .Q(\rd_fifo[4][27] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][28]$_DFFE_PP_  (.D(net37),
    .DE(net292),
    .Q(\rd_fifo[4][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][29]$_DFFE_PP_  (.D(net38),
    .DE(net292),
    .Q(\rd_fifo[4][29] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][2] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][30]$_DFFE_PP_  (.D(net24),
    .DE(net292),
    .Q(\rd_fifo[4][30] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][31]$_DFFE_PP_  (.D(net25),
    .DE(net292),
    .Q(\rd_fifo[4][31] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][32]$_DFFE_PP_  (.D(net26),
    .DE(net292),
    .Q(\rd_fifo[4][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][33]$_DFFE_PP_  (.D(net27),
    .DE(net292),
    .Q(\rd_fifo[4][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][34]$_DFFE_PP_  (.D(net28),
    .DE(net292),
    .Q(\rd_fifo[4][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][35]$_DFFE_PP_  (.D(net29),
    .DE(net292),
    .Q(\rd_fifo[4][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][4] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net292),
    .Q(\rd_fifo[4][5] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net292),
    .Q(\rd_fifo[4][6] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net292),
    .Q(\rd_fifo[4][7] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net292),
    .Q(\rd_fifo[4][8] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[4][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0016_),
    .Q(\rd_fifo[4][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][0] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net293),
    .Q(\rd_fifo[5][10] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net293),
    .Q(\rd_fifo[5][12] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][13] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][14] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net293),
    .Q(\rd_fifo[5][16] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net293),
    .Q(\rd_fifo[5][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][18] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][20]$_DFFE_PP_  (.D(net23),
    .DE(net293),
    .Q(\rd_fifo[5][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][21]$_DFFE_PP_  (.D(net30),
    .DE(net293),
    .Q(\rd_fifo[5][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][22]$_DFFE_PP_  (.D(net31),
    .DE(net293),
    .Q(\rd_fifo[5][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][23]$_DFFE_PP_  (.D(net32),
    .DE(net293),
    .Q(\rd_fifo[5][23] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][24]$_DFFE_PP_  (.D(net33),
    .DE(net293),
    .Q(\rd_fifo[5][24] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][25]$_DFFE_PP_  (.D(net34),
    .DE(net293),
    .Q(\rd_fifo[5][25] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][26]$_DFFE_PP_  (.D(net35),
    .DE(net293),
    .Q(\rd_fifo[5][26] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][27]$_DFFE_PP_  (.D(net36),
    .DE(net293),
    .Q(\rd_fifo[5][27] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][28]$_DFFE_PP_  (.D(net37),
    .DE(net293),
    .Q(\rd_fifo[5][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][29]$_DFFE_PP_  (.D(net38),
    .DE(net293),
    .Q(\rd_fifo[5][29] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][30]$_DFFE_PP_  (.D(net24),
    .DE(net293),
    .Q(\rd_fifo[5][30] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][31]$_DFFE_PP_  (.D(net25),
    .DE(net293),
    .Q(\rd_fifo[5][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][32]$_DFFE_PP_  (.D(net26),
    .DE(net293),
    .Q(\rd_fifo[5][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][33]$_DFFE_PP_  (.D(net27),
    .DE(net293),
    .Q(\rd_fifo[5][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][34]$_DFFE_PP_  (.D(net28),
    .DE(net293),
    .Q(\rd_fifo[5][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][35]$_DFFE_PP_  (.D(net29),
    .DE(net293),
    .Q(\rd_fifo[5][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][4] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net293),
    .Q(\rd_fifo[5][5] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net293),
    .Q(\rd_fifo[5][6] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net293),
    .Q(\rd_fifo[5][7] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net293),
    .Q(\rd_fifo[5][8] ),
    .CLK(clknet_leaf_95_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[5][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0017_),
    .Q(\rd_fifo[5][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][0] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net295),
    .Q(\rd_fifo[6][10] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][11] ),
    .CLK(clknet_leaf_100_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net295),
    .Q(\rd_fifo[6][12] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][13] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][14] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][15] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net295),
    .Q(\rd_fifo[6][16] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net295),
    .Q(\rd_fifo[6][17] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][20]$_DFFE_PP_  (.D(net23),
    .DE(net295),
    .Q(\rd_fifo[6][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][21]$_DFFE_PP_  (.D(net30),
    .DE(net295),
    .Q(\rd_fifo[6][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][22]$_DFFE_PP_  (.D(net31),
    .DE(net295),
    .Q(\rd_fifo[6][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][23]$_DFFE_PP_  (.D(net32),
    .DE(net295),
    .Q(\rd_fifo[6][23] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][24]$_DFFE_PP_  (.D(net33),
    .DE(net295),
    .Q(\rd_fifo[6][24] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][25]$_DFFE_PP_  (.D(net34),
    .DE(net295),
    .Q(\rd_fifo[6][25] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][26]$_DFFE_PP_  (.D(net35),
    .DE(net295),
    .Q(\rd_fifo[6][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][27]$_DFFE_PP_  (.D(net36),
    .DE(net295),
    .Q(\rd_fifo[6][27] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][28]$_DFFE_PP_  (.D(net37),
    .DE(net295),
    .Q(\rd_fifo[6][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][29]$_DFFE_PP_  (.D(net38),
    .DE(net295),
    .Q(\rd_fifo[6][29] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][2] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][30]$_DFFE_PP_  (.D(net24),
    .DE(net295),
    .Q(\rd_fifo[6][30] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][31]$_DFFE_PP_  (.D(net25),
    .DE(net295),
    .Q(\rd_fifo[6][31] ),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][32]$_DFFE_PP_  (.D(net26),
    .DE(net295),
    .Q(\rd_fifo[6][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][33]$_DFFE_PP_  (.D(net27),
    .DE(net295),
    .Q(\rd_fifo[6][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][34]$_DFFE_PP_  (.D(net28),
    .DE(net295),
    .Q(\rd_fifo[6][34] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][35]$_DFFE_PP_  (.D(net29),
    .DE(net295),
    .Q(\rd_fifo[6][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][3] ),
    .CLK(clknet_leaf_59_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][4] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net295),
    .Q(\rd_fifo[6][5] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net295),
    .Q(\rd_fifo[6][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net295),
    .Q(\rd_fifo[6][7] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net295),
    .Q(\rd_fifo[6][8] ),
    .CLK(clknet_leaf_95_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[6][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0018_),
    .Q(\rd_fifo[6][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][0] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net300),
    .Q(\rd_fifo[7][10] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][11] ),
    .CLK(clknet_leaf_60_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net300),
    .Q(\rd_fifo[7][12] ),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][14] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][15] ),
    .CLK(clknet_leaf_57_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net300),
    .Q(\rd_fifo[7][16] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net300),
    .Q(\rd_fifo[7][17] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][18] ),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][19] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][20]$_DFFE_PP_  (.D(net23),
    .DE(net300),
    .Q(\rd_fifo[7][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][21]$_DFFE_PP_  (.D(net30),
    .DE(net300),
    .Q(\rd_fifo[7][21] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][22]$_DFFE_PP_  (.D(net31),
    .DE(net300),
    .Q(\rd_fifo[7][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][23]$_DFFE_PP_  (.D(net32),
    .DE(net300),
    .Q(\rd_fifo[7][23] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][24]$_DFFE_PP_  (.D(net33),
    .DE(net300),
    .Q(\rd_fifo[7][24] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][25]$_DFFE_PP_  (.D(net34),
    .DE(net300),
    .Q(\rd_fifo[7][25] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][26]$_DFFE_PP_  (.D(net35),
    .DE(net300),
    .Q(\rd_fifo[7][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][27]$_DFFE_PP_  (.D(net36),
    .DE(net300),
    .Q(\rd_fifo[7][27] ),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][28]$_DFFE_PP_  (.D(net37),
    .DE(net300),
    .Q(\rd_fifo[7][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][29]$_DFFE_PP_  (.D(net38),
    .DE(net300),
    .Q(\rd_fifo[7][29] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][2] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][30]$_DFFE_PP_  (.D(net24),
    .DE(net300),
    .Q(\rd_fifo[7][30] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][31]$_DFFE_PP_  (.D(net25),
    .DE(net300),
    .Q(\rd_fifo[7][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][32]$_DFFE_PP_  (.D(net26),
    .DE(net300),
    .Q(\rd_fifo[7][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][33]$_DFFE_PP_  (.D(net27),
    .DE(net300),
    .Q(\rd_fifo[7][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][34]$_DFFE_PP_  (.D(net28),
    .DE(net300),
    .Q(\rd_fifo[7][34] ),
    .CLK(clknet_leaf_89_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][35]$_DFFE_PP_  (.D(net29),
    .DE(net300),
    .Q(\rd_fifo[7][35] ),
    .CLK(clknet_leaf_86_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][3] ),
    .CLK(clknet_leaf_58_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][4] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net300),
    .Q(\rd_fifo[7][5] ),
    .CLK(clknet_leaf_51_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net300),
    .Q(\rd_fifo[7][6] ),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net300),
    .Q(\rd_fifo[7][7] ),
    .CLK(clknet_leaf_91_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net300),
    .Q(\rd_fifo[7][8] ),
    .CLK(clknet_leaf_95_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[7][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(_0019_),
    .Q(\rd_fifo[7][9] ),
    .CLK(clknet_leaf_99_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net301),
    .Q(\rd_fifo[8][0] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net302),
    .Q(\rd_fifo[8][10] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net301),
    .Q(\rd_fifo[8][11] ),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net302),
    .Q(\rd_fifo[8][12] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0020_),
    .Q(\rd_fifo[8][13] ),
    .CLK(clknet_leaf_98_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net301),
    .Q(\rd_fifo[8][14] ),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net301),
    .Q(\rd_fifo[8][15] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net301),
    .Q(\rd_fifo[8][16] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net301),
    .Q(\rd_fifo[8][17] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net301),
    .Q(\rd_fifo[8][18] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net301),
    .Q(\rd_fifo[8][19] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net301),
    .Q(\rd_fifo[8][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][20]$_DFFE_PP_  (.D(net23),
    .DE(net301),
    .Q(\rd_fifo[8][20] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][21]$_DFFE_PP_  (.D(net30),
    .DE(net301),
    .Q(\rd_fifo[8][21] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][22]$_DFFE_PP_  (.D(net31),
    .DE(net301),
    .Q(\rd_fifo[8][22] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][23]$_DFFE_PP_  (.D(net32),
    .DE(net301),
    .Q(\rd_fifo[8][23] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][24]$_DFFE_PP_  (.D(net33),
    .DE(net301),
    .Q(\rd_fifo[8][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][25]$_DFFE_PP_  (.D(net34),
    .DE(net301),
    .Q(\rd_fifo[8][25] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][26]$_DFFE_PP_  (.D(net35),
    .DE(net301),
    .Q(\rd_fifo[8][26] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][27]$_DFFE_PP_  (.D(net36),
    .DE(net302),
    .Q(\rd_fifo[8][27] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][28]$_DFFE_PP_  (.D(net37),
    .DE(net301),
    .Q(\rd_fifo[8][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][29]$_DFFE_PP_  (.D(net38),
    .DE(net302),
    .Q(\rd_fifo[8][29] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net301),
    .Q(\rd_fifo[8][2] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][30]$_DFFE_PP_  (.D(net24),
    .DE(net302),
    .Q(\rd_fifo[8][30] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][31]$_DFFE_PP_  (.D(net25),
    .DE(net301),
    .Q(\rd_fifo[8][31] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][32]$_DFFE_PP_  (.D(net26),
    .DE(net302),
    .Q(\rd_fifo[8][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][33]$_DFFE_PP_  (.D(net27),
    .DE(net302),
    .Q(\rd_fifo[8][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][34]$_DFFE_PP_  (.D(net28),
    .DE(net302),
    .Q(\rd_fifo[8][34] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][35]$_DFFE_PP_  (.D(net29),
    .DE(net302),
    .Q(\rd_fifo[8][35] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net301),
    .Q(\rd_fifo[8][3] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net301),
    .Q(\rd_fifo[8][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net301),
    .Q(\rd_fifo[8][5] ),
    .CLK(clknet_leaf_49_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net302),
    .Q(\rd_fifo[8][6] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net302),
    .Q(\rd_fifo[8][7] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net302),
    .Q(\rd_fifo[8][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[8][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net301),
    .Q(\rd_fifo[8][9] ),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][0]$_DFFE_PP_  (.D(\rd_aux_r[0] ),
    .DE(net303),
    .Q(\rd_fifo[9][0] ),
    .CLK(clknet_leaf_61_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][10]$_DFFE_PP_  (.D(\rd_shift_r[6] ),
    .DE(net304),
    .Q(\rd_fifo[9][10] ),
    .CLK(clknet_leaf_77_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][11]$_DFFE_PP_  (.D(\rd_shift_r[7] ),
    .DE(net303),
    .Q(\rd_fifo[9][11] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][12]$_DFFE_PP_  (.D(\rd_shift_r[8] ),
    .DE(net304),
    .Q(\rd_fifo[9][12] ),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][13]$_DFFE_PP_  (.D(\rd_shift_r[9] ),
    .DE(_0021_),
    .Q(\rd_fifo[9][13] ),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][14]$_DFFE_PP_  (.D(\rd_shift_r[10] ),
    .DE(net303),
    .Q(\rd_fifo[9][14] ),
    .CLK(clknet_leaf_67_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][15]$_DFFE_PP_  (.D(\rd_shift_r[11] ),
    .DE(net303),
    .Q(\rd_fifo[9][15] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][16]$_DFFE_PP_  (.D(\rd_shift_r[12] ),
    .DE(net303),
    .Q(\rd_fifo[9][16] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][17]$_DFFE_PP_  (.D(\rd_shift_r[13] ),
    .DE(net303),
    .Q(\rd_fifo[9][17] ),
    .CLK(clknet_leaf_50_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][18]$_DFFE_PP_  (.D(\rd_shift_r[14] ),
    .DE(net303),
    .Q(\rd_fifo[9][18] ),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][19]$_DFFE_PP_  (.D(\rd_shift_r[15] ),
    .DE(net303),
    .Q(\rd_fifo[9][19] ),
    .CLK(clknet_leaf_68_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][1]$_DFFE_PP_  (.D(\rd_aux_r[1] ),
    .DE(net303),
    .Q(\rd_fifo[9][1] ),
    .CLK(clknet_leaf_62_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][20]$_DFFE_PP_  (.D(net23),
    .DE(net303),
    .Q(\rd_fifo[9][20] ),
    .CLK(clknet_leaf_71_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][21]$_DFFE_PP_  (.D(net30),
    .DE(net303),
    .Q(\rd_fifo[9][21] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][22]$_DFFE_PP_  (.D(net31),
    .DE(net303),
    .Q(\rd_fifo[9][22] ),
    .CLK(clknet_leaf_72_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][23]$_DFFE_PP_  (.D(net32),
    .DE(net303),
    .Q(\rd_fifo[9][23] ),
    .CLK(clknet_leaf_70_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][24]$_DFFE_PP_  (.D(net33),
    .DE(net303),
    .Q(\rd_fifo[9][24] ),
    .CLK(clknet_leaf_74_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][25]$_DFFE_PP_  (.D(net34),
    .DE(net303),
    .Q(\rd_fifo[9][25] ),
    .CLK(clknet_leaf_73_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][26]$_DFFE_PP_  (.D(net35),
    .DE(net303),
    .Q(\rd_fifo[9][26] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][27]$_DFFE_PP_  (.D(net36),
    .DE(net304),
    .Q(\rd_fifo[9][27] ),
    .CLK(clknet_leaf_75_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][28]$_DFFE_PP_  (.D(net37),
    .DE(net303),
    .Q(\rd_fifo[9][28] ),
    .CLK(clknet_leaf_82_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][29]$_DFFE_PP_  (.D(net38),
    .DE(net304),
    .Q(\rd_fifo[9][29] ),
    .CLK(clknet_leaf_83_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][2]$_DFFE_PP_  (.D(\rd_aux_r[2] ),
    .DE(net303),
    .Q(\rd_fifo[9][2] ),
    .CLK(clknet_leaf_54_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][30]$_DFFE_PP_  (.D(net24),
    .DE(net304),
    .Q(\rd_fifo[9][30] ),
    .CLK(clknet_leaf_87_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][31]$_DFFE_PP_  (.D(net25),
    .DE(net303),
    .Q(\rd_fifo[9][31] ),
    .CLK(clknet_leaf_81_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][32]$_DFFE_PP_  (.D(net26),
    .DE(net304),
    .Q(\rd_fifo[9][32] ),
    .CLK(clknet_leaf_84_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][33]$_DFFE_PP_  (.D(net27),
    .DE(net304),
    .Q(\rd_fifo[9][33] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][34]$_DFFE_PP_  (.D(net28),
    .DE(net304),
    .Q(\rd_fifo[9][34] ),
    .CLK(clknet_leaf_88_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][35]$_DFFE_PP_  (.D(net29),
    .DE(net304),
    .Q(\rd_fifo[9][35] ),
    .CLK(clknet_leaf_85_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][3]$_DFFE_PP_  (.D(\rd_aux_r[3] ),
    .DE(net303),
    .Q(\rd_fifo[9][3] ),
    .CLK(clknet_leaf_56_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][4]$_DFFE_PP_  (.D(\rd_shift_r[0] ),
    .DE(net303),
    .Q(\rd_fifo[9][4] ),
    .CLK(clknet_leaf_55_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][5]$_DFFE_PP_  (.D(\rd_shift_r[1] ),
    .DE(net303),
    .Q(\rd_fifo[9][5] ),
    .CLK(clknet_leaf_48_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][6]$_DFFE_PP_  (.D(\rd_shift_r[2] ),
    .DE(net304),
    .Q(\rd_fifo[9][6] ),
    .CLK(clknet_leaf_90_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][7]$_DFFE_PP_  (.D(\rd_shift_r[3] ),
    .DE(net304),
    .Q(\rd_fifo[9][7] ),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][8]$_DFFE_PP_  (.D(\rd_shift_r[4] ),
    .DE(net304),
    .Q(\rd_fifo[9][8] ),
    .CLK(clknet_leaf_94_clk));
 sky130_fd_sc_hd__edfxtp_1 \rd_fifo[9][9]$_DFFE_PP_  (.D(\rd_shift_r[5] ),
    .DE(net303),
    .Q(\rd_fifo[9][9] ),
    .CLK(clknet_leaf_63_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[0]$_DFFE_PN0P_  (.D(_0112_),
    .Q(\rd_lat_ctr[0] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[1]$_DFFE_PN0P_  (.D(_0113_),
    .Q(\rd_lat_ctr[1] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[2]$_DFFE_PN0P_  (.D(_0114_),
    .Q(\rd_lat_ctr[2] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[3]$_DFFE_PN0P_  (.D(_0115_),
    .Q(\rd_lat_ctr[3] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[4]$_DFFE_PN0P_  (.D(_0116_),
    .Q(\rd_lat_ctr[4] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[5]$_DFFE_PN0P_  (.D(_0117_),
    .Q(\rd_lat_ctr[5] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[6]$_DFFE_PN0P_  (.D(_0118_),
    .Q(\rd_lat_ctr[6] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_lat_ctr[7]$_DFFE_PN0P_  (.D(_0119_),
    .Q(\rd_lat_ctr[7] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_4 \rd_rptr[0]$_DFFE_PN0P_  (.D(_0120_),
    .Q(\rd_rptr[0] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__dfrtp_4 \rd_rptr[1]$_DFFE_PN0P_  (.D(_0121_),
    .Q(\rd_rptr[1] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__dfrtp_2 \rd_rptr[2]$_DFFE_PN0P_  (.D(_0122_),
    .Q(\rd_rptr[2] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_rptr[3]$_DFFE_PN0P_  (.D(_0123_),
    .Q(\rd_rptr[3] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_rptr[4]$_DFFE_PN0P_  (.D(_0124_),
    .Q(\rd_rptr[4] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_93_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[0]$_DFFE_PN0P_  (.D(_0125_),
    .Q(\rd_shift_r[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[10]$_DFFE_PN0P_  (.D(_0126_),
    .Q(\rd_shift_r[10] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[11]$_DFFE_PN0P_  (.D(_0127_),
    .Q(\rd_shift_r[11] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[12]$_DFFE_PN0P_  (.D(_0128_),
    .Q(\rd_shift_r[12] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[13]$_DFFE_PN0P_  (.D(_0129_),
    .Q(\rd_shift_r[13] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_53_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[14]$_DFFE_PN0P_  (.D(_0130_),
    .Q(\rd_shift_r[14] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_69_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[15]$_DFFE_PN0P_  (.D(_0131_),
    .Q(\rd_shift_r[15] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_66_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[1]$_DFFE_PN0P_  (.D(_0132_),
    .Q(\rd_shift_r[1] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_52_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[2]$_DFFE_PN0P_  (.D(_0133_),
    .Q(\rd_shift_r[2] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[3]$_DFFE_PN0P_  (.D(_0134_),
    .Q(\rd_shift_r[3] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_79_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[4]$_DFFE_PN0P_  (.D(_0135_),
    .Q(\rd_shift_r[4] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_78_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[5]$_DFFE_PN0P_  (.D(_0136_),
    .Q(\rd_shift_r[5] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_64_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[6]$_DFFE_PN0P_  (.D(_0137_),
    .Q(\rd_shift_r[6] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_76_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[7]$_DFFE_PN0P_  (.D(_0138_),
    .Q(\rd_shift_r[7] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_65_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[8]$_DFFE_PN0P_  (.D(_0139_),
    .Q(\rd_shift_r[8] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_80_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_shift_r[9]$_DFFE_PN0P_  (.D(_0140_),
    .Q(\rd_shift_r[9] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_92_clk));
 sky130_fd_sc_hd__dfstp_2 \rd_state[0]$_DFF_PN1_  (.D(_0000_),
    .Q(\rd_state[0] ),
    .SET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_state[1]$_DFF_PN0_  (.D(_0001_),
    .Q(rd_capture_valid),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_state[2]$_DFF_PN0_  (.D(_0002_),
    .Q(\rd_state[2] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_wptr[0]$_DFFE_PN0P_  (.D(_0141_),
    .Q(\rd_wptr[0] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_wptr[1]$_DFFE_PN0P_  (.D(_0142_),
    .Q(\rd_wptr[1] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_96_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_wptr[2]$_DFFE_PN0P_  (.D(_0143_),
    .Q(\rd_wptr[2] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_wptr[3]$_DFFE_PN0P_  (.D(_0144_),
    .Q(\rd_wptr[3] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_100_clk));
 sky130_fd_sc_hd__dfrtp_1 \rd_wptr[4]$_DFFE_PN0P_  (.D(_0145_),
    .Q(\rd_wptr[4] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_97_clk));
 sky130_fd_sc_hd__buf_12 split (.A(\rd_rptr[0] ),
    .X(net));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][0]$_DFFE_PP_  (.D(net73),
    .DE(net283),
    .Q(\wr_buf[0][0] ),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][10]$_DFFE_PP_  (.D(net68),
    .DE(net283),
    .Q(\wr_buf[0][10] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][11]$_DFFE_PP_  (.D(net69),
    .DE(net283),
    .Q(\wr_buf[0][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][12]$_DFFE_PP_  (.D(net70),
    .DE(net283),
    .Q(\wr_buf[0][12] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][13]$_DFFE_PP_  (.D(net71),
    .DE(net283),
    .Q(\wr_buf[0][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][14]$_DFFE_PP_  (.D(net41),
    .DE(net283),
    .Q(\wr_buf[0][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][15]$_DFFE_PP_  (.D(net42),
    .DE(net283),
    .Q(\wr_buf[0][15] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][16]$_DFFE_PP_  (.D(net43),
    .DE(net283),
    .Q(\wr_buf[0][16] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][17]$_DFFE_PP_  (.D(net44),
    .DE(net283),
    .Q(\wr_buf[0][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][18]$_DFFE_PP_  (.D(net45),
    .DE(net283),
    .Q(\wr_buf[0][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][19]$_DFFE_PP_  (.D(net46),
    .DE(net283),
    .Q(\wr_buf[0][19] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][1]$_DFFE_PP_  (.D(net74),
    .DE(net283),
    .Q(\wr_buf[0][1] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][20]$_DFFE_PP_  (.D(net47),
    .DE(net283),
    .Q(\wr_buf[0][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][21]$_DFFE_PP_  (.D(net48),
    .DE(net283),
    .Q(\wr_buf[0][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][22]$_DFFE_PP_  (.D(net49),
    .DE(net283),
    .Q(\wr_buf[0][22] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][23]$_DFFE_PP_  (.D(net50),
    .DE(net283),
    .Q(\wr_buf[0][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][24]$_DFFE_PP_  (.D(net52),
    .DE(net283),
    .Q(\wr_buf[0][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][25]$_DFFE_PP_  (.D(net53),
    .DE(net283),
    .Q(\wr_buf[0][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][26]$_DFFE_PP_  (.D(net54),
    .DE(net283),
    .Q(\wr_buf[0][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][27]$_DFFE_PP_  (.D(net55),
    .DE(net283),
    .Q(\wr_buf[0][27] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][28]$_DFFE_PP_  (.D(net56),
    .DE(net283),
    .Q(\wr_buf[0][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][29]$_DFFE_PP_  (.D(net57),
    .DE(net283),
    .Q(\wr_buf[0][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][2]$_DFFE_PP_  (.D(net75),
    .DE(net283),
    .Q(\wr_buf[0][2] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][30]$_DFFE_PP_  (.D(net58),
    .DE(net283),
    .Q(\wr_buf[0][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][31]$_DFFE_PP_  (.D(net59),
    .DE(net283),
    .Q(\wr_buf[0][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][32]$_DFFE_PP_  (.D(net60),
    .DE(net283),
    .Q(\wr_buf[0][32] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][33]$_DFFE_PP_  (.D(net61),
    .DE(net283),
    .Q(\wr_buf[0][33] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][34]$_DFFE_PP_  (.D(net63),
    .DE(net283),
    .Q(\wr_buf[0][34] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][35]$_DFFE_PP_  (.D(net64),
    .DE(net283),
    .Q(\wr_buf[0][35] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][3]$_DFFE_PP_  (.D(net76),
    .DE(net283),
    .Q(\wr_buf[0][3] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][4]$_DFFE_PP_  (.D(net40),
    .DE(net283),
    .Q(\wr_buf[0][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][5]$_DFFE_PP_  (.D(net51),
    .DE(net283),
    .Q(\wr_buf[0][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][6]$_DFFE_PP_  (.D(net62),
    .DE(net283),
    .Q(\wr_buf[0][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][7]$_DFFE_PP_  (.D(net65),
    .DE(net283),
    .Q(\wr_buf[0][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][8]$_DFFE_PP_  (.D(net66),
    .DE(net283),
    .Q(\wr_buf[0][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[0][9]$_DFFE_PP_  (.D(net67),
    .DE(net283),
    .Q(\wr_buf[0][9] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][0]$_DFFE_PP_  (.D(net73),
    .DE(_0023_),
    .Q(\wr_buf[10][0] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][10]$_DFFE_PP_  (.D(net68),
    .DE(net271),
    .Q(\wr_buf[10][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][11]$_DFFE_PP_  (.D(net69),
    .DE(net271),
    .Q(\wr_buf[10][11] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][12]$_DFFE_PP_  (.D(net70),
    .DE(net271),
    .Q(\wr_buf[10][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][13]$_DFFE_PP_  (.D(net71),
    .DE(net271),
    .Q(\wr_buf[10][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][14]$_DFFE_PP_  (.D(net41),
    .DE(net271),
    .Q(\wr_buf[10][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][15]$_DFFE_PP_  (.D(net42),
    .DE(net271),
    .Q(\wr_buf[10][15] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][16]$_DFFE_PP_  (.D(net43),
    .DE(net271),
    .Q(\wr_buf[10][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][17]$_DFFE_PP_  (.D(net44),
    .DE(net271),
    .Q(\wr_buf[10][17] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][18]$_DFFE_PP_  (.D(net45),
    .DE(net271),
    .Q(\wr_buf[10][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][19]$_DFFE_PP_  (.D(net46),
    .DE(net271),
    .Q(\wr_buf[10][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][1]$_DFFE_PP_  (.D(net74),
    .DE(_0023_),
    .Q(\wr_buf[10][1] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][20]$_DFFE_PP_  (.D(net47),
    .DE(net271),
    .Q(\wr_buf[10][20] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][21]$_DFFE_PP_  (.D(net48),
    .DE(net271),
    .Q(\wr_buf[10][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][22]$_DFFE_PP_  (.D(net49),
    .DE(net271),
    .Q(\wr_buf[10][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][23]$_DFFE_PP_  (.D(net50),
    .DE(net271),
    .Q(\wr_buf[10][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][24]$_DFFE_PP_  (.D(net52),
    .DE(net271),
    .Q(\wr_buf[10][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][25]$_DFFE_PP_  (.D(net53),
    .DE(net271),
    .Q(\wr_buf[10][25] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][26]$_DFFE_PP_  (.D(net54),
    .DE(net271),
    .Q(\wr_buf[10][26] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][27]$_DFFE_PP_  (.D(net55),
    .DE(net271),
    .Q(\wr_buf[10][27] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][28]$_DFFE_PP_  (.D(net56),
    .DE(net271),
    .Q(\wr_buf[10][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][29]$_DFFE_PP_  (.D(net57),
    .DE(net271),
    .Q(\wr_buf[10][29] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][2]$_DFFE_PP_  (.D(net75),
    .DE(_0023_),
    .Q(\wr_buf[10][2] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][30]$_DFFE_PP_  (.D(net58),
    .DE(net271),
    .Q(\wr_buf[10][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][31]$_DFFE_PP_  (.D(net59),
    .DE(net271),
    .Q(\wr_buf[10][31] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][32]$_DFFE_PP_  (.D(net60),
    .DE(net271),
    .Q(\wr_buf[10][32] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][33]$_DFFE_PP_  (.D(net61),
    .DE(net271),
    .Q(\wr_buf[10][33] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][34]$_DFFE_PP_  (.D(net63),
    .DE(net271),
    .Q(\wr_buf[10][34] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][35]$_DFFE_PP_  (.D(net64),
    .DE(net271),
    .Q(\wr_buf[10][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][3]$_DFFE_PP_  (.D(net76),
    .DE(_0023_),
    .Q(\wr_buf[10][3] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][4]$_DFFE_PP_  (.D(net40),
    .DE(net271),
    .Q(\wr_buf[10][4] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][5]$_DFFE_PP_  (.D(net51),
    .DE(net271),
    .Q(\wr_buf[10][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][6]$_DFFE_PP_  (.D(net62),
    .DE(net271),
    .Q(\wr_buf[10][6] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][7]$_DFFE_PP_  (.D(net65),
    .DE(net271),
    .Q(\wr_buf[10][7] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][8]$_DFFE_PP_  (.D(net66),
    .DE(net271),
    .Q(\wr_buf[10][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[10][9]$_DFFE_PP_  (.D(net67),
    .DE(net271),
    .Q(\wr_buf[10][9] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][0]$_DFFE_PP_  (.D(net73),
    .DE(_0024_),
    .Q(\wr_buf[11][0] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][10]$_DFFE_PP_  (.D(net68),
    .DE(net272),
    .Q(\wr_buf[11][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][11]$_DFFE_PP_  (.D(net69),
    .DE(net272),
    .Q(\wr_buf[11][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][12]$_DFFE_PP_  (.D(net70),
    .DE(net272),
    .Q(\wr_buf[11][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][13]$_DFFE_PP_  (.D(net71),
    .DE(net272),
    .Q(\wr_buf[11][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][14]$_DFFE_PP_  (.D(net41),
    .DE(net272),
    .Q(\wr_buf[11][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][15]$_DFFE_PP_  (.D(net42),
    .DE(net272),
    .Q(\wr_buf[11][15] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][16]$_DFFE_PP_  (.D(net43),
    .DE(net272),
    .Q(\wr_buf[11][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][17]$_DFFE_PP_  (.D(net44),
    .DE(net272),
    .Q(\wr_buf[11][17] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][18]$_DFFE_PP_  (.D(net45),
    .DE(net272),
    .Q(\wr_buf[11][18] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][19]$_DFFE_PP_  (.D(net46),
    .DE(net272),
    .Q(\wr_buf[11][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][1]$_DFFE_PP_  (.D(net74),
    .DE(_0024_),
    .Q(\wr_buf[11][1] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][20]$_DFFE_PP_  (.D(net47),
    .DE(net272),
    .Q(\wr_buf[11][20] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][21]$_DFFE_PP_  (.D(net48),
    .DE(net272),
    .Q(\wr_buf[11][21] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][22]$_DFFE_PP_  (.D(net49),
    .DE(net272),
    .Q(\wr_buf[11][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][23]$_DFFE_PP_  (.D(net50),
    .DE(net272),
    .Q(\wr_buf[11][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][24]$_DFFE_PP_  (.D(net52),
    .DE(net272),
    .Q(\wr_buf[11][24] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][25]$_DFFE_PP_  (.D(net53),
    .DE(net272),
    .Q(\wr_buf[11][25] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][26]$_DFFE_PP_  (.D(net54),
    .DE(net272),
    .Q(\wr_buf[11][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][27]$_DFFE_PP_  (.D(net55),
    .DE(net272),
    .Q(\wr_buf[11][27] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][28]$_DFFE_PP_  (.D(net56),
    .DE(net272),
    .Q(\wr_buf[11][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][29]$_DFFE_PP_  (.D(net57),
    .DE(net272),
    .Q(\wr_buf[11][29] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][2]$_DFFE_PP_  (.D(net75),
    .DE(_0024_),
    .Q(\wr_buf[11][2] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][30]$_DFFE_PP_  (.D(net58),
    .DE(net272),
    .Q(\wr_buf[11][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][31]$_DFFE_PP_  (.D(net59),
    .DE(net272),
    .Q(\wr_buf[11][31] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][32]$_DFFE_PP_  (.D(net60),
    .DE(net272),
    .Q(\wr_buf[11][32] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][33]$_DFFE_PP_  (.D(net61),
    .DE(net272),
    .Q(\wr_buf[11][33] ),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][34]$_DFFE_PP_  (.D(net63),
    .DE(net272),
    .Q(\wr_buf[11][34] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][35]$_DFFE_PP_  (.D(net64),
    .DE(net272),
    .Q(\wr_buf[11][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][3]$_DFFE_PP_  (.D(net76),
    .DE(_0024_),
    .Q(\wr_buf[11][3] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][4]$_DFFE_PP_  (.D(net40),
    .DE(net272),
    .Q(\wr_buf[11][4] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][5]$_DFFE_PP_  (.D(net51),
    .DE(net272),
    .Q(\wr_buf[11][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][6]$_DFFE_PP_  (.D(net62),
    .DE(net272),
    .Q(\wr_buf[11][6] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][7]$_DFFE_PP_  (.D(net65),
    .DE(net272),
    .Q(\wr_buf[11][7] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][8]$_DFFE_PP_  (.D(net66),
    .DE(net272),
    .Q(\wr_buf[11][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[11][9]$_DFFE_PP_  (.D(net67),
    .DE(net272),
    .Q(\wr_buf[11][9] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][0]$_DFFE_PP_  (.D(net73),
    .DE(net276),
    .Q(\wr_buf[12][0] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][10]$_DFFE_PP_  (.D(net68),
    .DE(net276),
    .Q(\wr_buf[12][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][11]$_DFFE_PP_  (.D(net69),
    .DE(net276),
    .Q(\wr_buf[12][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][12]$_DFFE_PP_  (.D(net70),
    .DE(net276),
    .Q(\wr_buf[12][12] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][13]$_DFFE_PP_  (.D(net71),
    .DE(net276),
    .Q(\wr_buf[12][13] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][14]$_DFFE_PP_  (.D(net41),
    .DE(net276),
    .Q(\wr_buf[12][14] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][15]$_DFFE_PP_  (.D(net42),
    .DE(net276),
    .Q(\wr_buf[12][15] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][16]$_DFFE_PP_  (.D(net43),
    .DE(net276),
    .Q(\wr_buf[12][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][17]$_DFFE_PP_  (.D(net44),
    .DE(net276),
    .Q(\wr_buf[12][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][18]$_DFFE_PP_  (.D(net45),
    .DE(net276),
    .Q(\wr_buf[12][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][19]$_DFFE_PP_  (.D(net46),
    .DE(net276),
    .Q(\wr_buf[12][19] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][1]$_DFFE_PP_  (.D(net74),
    .DE(net276),
    .Q(\wr_buf[12][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][20]$_DFFE_PP_  (.D(net47),
    .DE(net276),
    .Q(\wr_buf[12][20] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][21]$_DFFE_PP_  (.D(net48),
    .DE(net276),
    .Q(\wr_buf[12][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][22]$_DFFE_PP_  (.D(net49),
    .DE(net276),
    .Q(\wr_buf[12][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][23]$_DFFE_PP_  (.D(net50),
    .DE(net276),
    .Q(\wr_buf[12][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][24]$_DFFE_PP_  (.D(net52),
    .DE(net276),
    .Q(\wr_buf[12][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][25]$_DFFE_PP_  (.D(net53),
    .DE(net276),
    .Q(\wr_buf[12][25] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][26]$_DFFE_PP_  (.D(net54),
    .DE(net276),
    .Q(\wr_buf[12][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][27]$_DFFE_PP_  (.D(net55),
    .DE(net276),
    .Q(\wr_buf[12][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][28]$_DFFE_PP_  (.D(net56),
    .DE(net276),
    .Q(\wr_buf[12][28] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][29]$_DFFE_PP_  (.D(net57),
    .DE(net276),
    .Q(\wr_buf[12][29] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][2]$_DFFE_PP_  (.D(net75),
    .DE(net276),
    .Q(\wr_buf[12][2] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][30]$_DFFE_PP_  (.D(net58),
    .DE(net276),
    .Q(\wr_buf[12][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][31]$_DFFE_PP_  (.D(net59),
    .DE(net276),
    .Q(\wr_buf[12][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][32]$_DFFE_PP_  (.D(net60),
    .DE(net276),
    .Q(\wr_buf[12][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][33]$_DFFE_PP_  (.D(net61),
    .DE(net276),
    .Q(\wr_buf[12][33] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][34]$_DFFE_PP_  (.D(net63),
    .DE(net276),
    .Q(\wr_buf[12][34] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][35]$_DFFE_PP_  (.D(net64),
    .DE(net276),
    .Q(\wr_buf[12][35] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][3]$_DFFE_PP_  (.D(net76),
    .DE(net276),
    .Q(\wr_buf[12][3] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][4]$_DFFE_PP_  (.D(net40),
    .DE(net276),
    .Q(\wr_buf[12][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][5]$_DFFE_PP_  (.D(net51),
    .DE(net276),
    .Q(\wr_buf[12][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][6]$_DFFE_PP_  (.D(net62),
    .DE(net276),
    .Q(\wr_buf[12][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][7]$_DFFE_PP_  (.D(net65),
    .DE(net276),
    .Q(\wr_buf[12][7] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][8]$_DFFE_PP_  (.D(net66),
    .DE(net276),
    .Q(\wr_buf[12][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[12][9]$_DFFE_PP_  (.D(net67),
    .DE(net276),
    .Q(\wr_buf[12][9] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][0]$_DFFE_PP_  (.D(net73),
    .DE(net275),
    .Q(\wr_buf[13][0] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][10]$_DFFE_PP_  (.D(net68),
    .DE(net275),
    .Q(\wr_buf[13][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][11]$_DFFE_PP_  (.D(net69),
    .DE(net275),
    .Q(\wr_buf[13][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][12]$_DFFE_PP_  (.D(net70),
    .DE(net275),
    .Q(\wr_buf[13][12] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][13]$_DFFE_PP_  (.D(net71),
    .DE(net275),
    .Q(\wr_buf[13][13] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][14]$_DFFE_PP_  (.D(net41),
    .DE(net275),
    .Q(\wr_buf[13][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][15]$_DFFE_PP_  (.D(net42),
    .DE(net275),
    .Q(\wr_buf[13][15] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][16]$_DFFE_PP_  (.D(net43),
    .DE(net275),
    .Q(\wr_buf[13][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][17]$_DFFE_PP_  (.D(net44),
    .DE(net275),
    .Q(\wr_buf[13][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][18]$_DFFE_PP_  (.D(net45),
    .DE(net275),
    .Q(\wr_buf[13][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][19]$_DFFE_PP_  (.D(net46),
    .DE(net275),
    .Q(\wr_buf[13][19] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][1]$_DFFE_PP_  (.D(net74),
    .DE(net275),
    .Q(\wr_buf[13][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][20]$_DFFE_PP_  (.D(net47),
    .DE(net275),
    .Q(\wr_buf[13][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][21]$_DFFE_PP_  (.D(net48),
    .DE(net275),
    .Q(\wr_buf[13][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][22]$_DFFE_PP_  (.D(net49),
    .DE(net275),
    .Q(\wr_buf[13][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][23]$_DFFE_PP_  (.D(net50),
    .DE(net275),
    .Q(\wr_buf[13][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][24]$_DFFE_PP_  (.D(net52),
    .DE(net275),
    .Q(\wr_buf[13][24] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][25]$_DFFE_PP_  (.D(net53),
    .DE(net275),
    .Q(\wr_buf[13][25] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][26]$_DFFE_PP_  (.D(net54),
    .DE(net275),
    .Q(\wr_buf[13][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][27]$_DFFE_PP_  (.D(net55),
    .DE(net275),
    .Q(\wr_buf[13][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][28]$_DFFE_PP_  (.D(net56),
    .DE(net275),
    .Q(\wr_buf[13][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][29]$_DFFE_PP_  (.D(net57),
    .DE(net275),
    .Q(\wr_buf[13][29] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][2]$_DFFE_PP_  (.D(net75),
    .DE(net275),
    .Q(\wr_buf[13][2] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][30]$_DFFE_PP_  (.D(net58),
    .DE(net275),
    .Q(\wr_buf[13][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][31]$_DFFE_PP_  (.D(net59),
    .DE(net275),
    .Q(\wr_buf[13][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][32]$_DFFE_PP_  (.D(net60),
    .DE(net275),
    .Q(\wr_buf[13][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][33]$_DFFE_PP_  (.D(net61),
    .DE(net275),
    .Q(\wr_buf[13][33] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][34]$_DFFE_PP_  (.D(net63),
    .DE(net275),
    .Q(\wr_buf[13][34] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][35]$_DFFE_PP_  (.D(net64),
    .DE(net275),
    .Q(\wr_buf[13][35] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][3]$_DFFE_PP_  (.D(net76),
    .DE(net275),
    .Q(\wr_buf[13][3] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][4]$_DFFE_PP_  (.D(net40),
    .DE(net275),
    .Q(\wr_buf[13][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][5]$_DFFE_PP_  (.D(net51),
    .DE(net275),
    .Q(\wr_buf[13][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][6]$_DFFE_PP_  (.D(net62),
    .DE(net275),
    .Q(\wr_buf[13][6] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][7]$_DFFE_PP_  (.D(net65),
    .DE(net275),
    .Q(\wr_buf[13][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][8]$_DFFE_PP_  (.D(net66),
    .DE(net275),
    .Q(\wr_buf[13][8] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[13][9]$_DFFE_PP_  (.D(net67),
    .DE(net275),
    .Q(\wr_buf[13][9] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][0]$_DFFE_PP_  (.D(net73),
    .DE(net274),
    .Q(\wr_buf[14][0] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][10]$_DFFE_PP_  (.D(net68),
    .DE(net274),
    .Q(\wr_buf[14][10] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][11]$_DFFE_PP_  (.D(net69),
    .DE(net274),
    .Q(\wr_buf[14][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][12]$_DFFE_PP_  (.D(net70),
    .DE(net274),
    .Q(\wr_buf[14][12] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][13]$_DFFE_PP_  (.D(net71),
    .DE(net274),
    .Q(\wr_buf[14][13] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][14]$_DFFE_PP_  (.D(net41),
    .DE(net274),
    .Q(\wr_buf[14][14] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][15]$_DFFE_PP_  (.D(net42),
    .DE(net274),
    .Q(\wr_buf[14][15] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][16]$_DFFE_PP_  (.D(net43),
    .DE(net274),
    .Q(\wr_buf[14][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][17]$_DFFE_PP_  (.D(net44),
    .DE(net274),
    .Q(\wr_buf[14][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][18]$_DFFE_PP_  (.D(net45),
    .DE(net274),
    .Q(\wr_buf[14][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][19]$_DFFE_PP_  (.D(net46),
    .DE(net274),
    .Q(\wr_buf[14][19] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][1]$_DFFE_PP_  (.D(net74),
    .DE(net274),
    .Q(\wr_buf[14][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][20]$_DFFE_PP_  (.D(net47),
    .DE(net274),
    .Q(\wr_buf[14][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][21]$_DFFE_PP_  (.D(net48),
    .DE(net274),
    .Q(\wr_buf[14][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][22]$_DFFE_PP_  (.D(net49),
    .DE(net274),
    .Q(\wr_buf[14][22] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][23]$_DFFE_PP_  (.D(net50),
    .DE(net274),
    .Q(\wr_buf[14][23] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][24]$_DFFE_PP_  (.D(net52),
    .DE(net274),
    .Q(\wr_buf[14][24] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][25]$_DFFE_PP_  (.D(net53),
    .DE(net274),
    .Q(\wr_buf[14][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][26]$_DFFE_PP_  (.D(net54),
    .DE(net274),
    .Q(\wr_buf[14][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][27]$_DFFE_PP_  (.D(net55),
    .DE(net274),
    .Q(\wr_buf[14][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][28]$_DFFE_PP_  (.D(net56),
    .DE(net274),
    .Q(\wr_buf[14][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][29]$_DFFE_PP_  (.D(net57),
    .DE(net274),
    .Q(\wr_buf[14][29] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][2]$_DFFE_PP_  (.D(net75),
    .DE(net274),
    .Q(\wr_buf[14][2] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][30]$_DFFE_PP_  (.D(net58),
    .DE(net274),
    .Q(\wr_buf[14][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][31]$_DFFE_PP_  (.D(net59),
    .DE(net274),
    .Q(\wr_buf[14][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][32]$_DFFE_PP_  (.D(net60),
    .DE(net274),
    .Q(\wr_buf[14][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][33]$_DFFE_PP_  (.D(net61),
    .DE(net274),
    .Q(\wr_buf[14][33] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][34]$_DFFE_PP_  (.D(net63),
    .DE(net274),
    .Q(\wr_buf[14][34] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][35]$_DFFE_PP_  (.D(net64),
    .DE(net274),
    .Q(\wr_buf[14][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][3]$_DFFE_PP_  (.D(net76),
    .DE(net274),
    .Q(\wr_buf[14][3] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][4]$_DFFE_PP_  (.D(net40),
    .DE(net274),
    .Q(\wr_buf[14][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][5]$_DFFE_PP_  (.D(net51),
    .DE(net274),
    .Q(\wr_buf[14][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][6]$_DFFE_PP_  (.D(net62),
    .DE(net274),
    .Q(\wr_buf[14][6] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][7]$_DFFE_PP_  (.D(net65),
    .DE(net274),
    .Q(\wr_buf[14][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][8]$_DFFE_PP_  (.D(net66),
    .DE(net274),
    .Q(\wr_buf[14][8] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[14][9]$_DFFE_PP_  (.D(net67),
    .DE(net274),
    .Q(\wr_buf[14][9] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][0]$_DFFE_PP_  (.D(net73),
    .DE(net273),
    .Q(\wr_buf[15][0] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][10]$_DFFE_PP_  (.D(net68),
    .DE(net273),
    .Q(\wr_buf[15][10] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][11]$_DFFE_PP_  (.D(net69),
    .DE(net273),
    .Q(\wr_buf[15][11] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][12]$_DFFE_PP_  (.D(net70),
    .DE(net273),
    .Q(\wr_buf[15][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][13]$_DFFE_PP_  (.D(net71),
    .DE(net273),
    .Q(\wr_buf[15][13] ),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][14]$_DFFE_PP_  (.D(net41),
    .DE(net273),
    .Q(\wr_buf[15][14] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][15]$_DFFE_PP_  (.D(net42),
    .DE(net273),
    .Q(\wr_buf[15][15] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][16]$_DFFE_PP_  (.D(net43),
    .DE(net273),
    .Q(\wr_buf[15][16] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][17]$_DFFE_PP_  (.D(net44),
    .DE(net273),
    .Q(\wr_buf[15][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][18]$_DFFE_PP_  (.D(net45),
    .DE(net273),
    .Q(\wr_buf[15][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][19]$_DFFE_PP_  (.D(net46),
    .DE(net273),
    .Q(\wr_buf[15][19] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][1]$_DFFE_PP_  (.D(net74),
    .DE(net273),
    .Q(\wr_buf[15][1] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][20]$_DFFE_PP_  (.D(net47),
    .DE(net273),
    .Q(\wr_buf[15][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][21]$_DFFE_PP_  (.D(net48),
    .DE(net273),
    .Q(\wr_buf[15][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][22]$_DFFE_PP_  (.D(net49),
    .DE(net273),
    .Q(\wr_buf[15][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][23]$_DFFE_PP_  (.D(net50),
    .DE(net273),
    .Q(\wr_buf[15][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][24]$_DFFE_PP_  (.D(net52),
    .DE(net273),
    .Q(\wr_buf[15][24] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][25]$_DFFE_PP_  (.D(net53),
    .DE(net273),
    .Q(\wr_buf[15][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][26]$_DFFE_PP_  (.D(net54),
    .DE(net273),
    .Q(\wr_buf[15][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][27]$_DFFE_PP_  (.D(net55),
    .DE(net273),
    .Q(\wr_buf[15][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][28]$_DFFE_PP_  (.D(net56),
    .DE(net273),
    .Q(\wr_buf[15][28] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][29]$_DFFE_PP_  (.D(net57),
    .DE(net273),
    .Q(\wr_buf[15][29] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][2]$_DFFE_PP_  (.D(net75),
    .DE(net273),
    .Q(\wr_buf[15][2] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][30]$_DFFE_PP_  (.D(net58),
    .DE(net273),
    .Q(\wr_buf[15][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][31]$_DFFE_PP_  (.D(net59),
    .DE(net273),
    .Q(\wr_buf[15][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][32]$_DFFE_PP_  (.D(net60),
    .DE(net273),
    .Q(\wr_buf[15][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][33]$_DFFE_PP_  (.D(net61),
    .DE(net273),
    .Q(\wr_buf[15][33] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][34]$_DFFE_PP_  (.D(net63),
    .DE(net273),
    .Q(\wr_buf[15][34] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][35]$_DFFE_PP_  (.D(net64),
    .DE(net273),
    .Q(\wr_buf[15][35] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][3]$_DFFE_PP_  (.D(net76),
    .DE(net273),
    .Q(\wr_buf[15][3] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][4]$_DFFE_PP_  (.D(net40),
    .DE(net273),
    .Q(\wr_buf[15][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][5]$_DFFE_PP_  (.D(net51),
    .DE(net273),
    .Q(\wr_buf[15][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][6]$_DFFE_PP_  (.D(net62),
    .DE(net273),
    .Q(\wr_buf[15][6] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][7]$_DFFE_PP_  (.D(net65),
    .DE(net273),
    .Q(\wr_buf[15][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][8]$_DFFE_PP_  (.D(net66),
    .DE(net273),
    .Q(\wr_buf[15][8] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[15][9]$_DFFE_PP_  (.D(net67),
    .DE(net273),
    .Q(\wr_buf[15][9] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][0]$_DFFE_PP_  (.D(net73),
    .DE(net284),
    .Q(\wr_buf[1][0] ),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][10]$_DFFE_PP_  (.D(net68),
    .DE(net284),
    .Q(\wr_buf[1][10] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][11]$_DFFE_PP_  (.D(net69),
    .DE(net284),
    .Q(\wr_buf[1][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][12]$_DFFE_PP_  (.D(net70),
    .DE(net284),
    .Q(\wr_buf[1][12] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][13]$_DFFE_PP_  (.D(net71),
    .DE(net284),
    .Q(\wr_buf[1][13] ),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][14]$_DFFE_PP_  (.D(net41),
    .DE(net284),
    .Q(\wr_buf[1][14] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][15]$_DFFE_PP_  (.D(net42),
    .DE(net284),
    .Q(\wr_buf[1][15] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][16]$_DFFE_PP_  (.D(net43),
    .DE(net284),
    .Q(\wr_buf[1][16] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][17]$_DFFE_PP_  (.D(net44),
    .DE(net284),
    .Q(\wr_buf[1][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][18]$_DFFE_PP_  (.D(net45),
    .DE(net284),
    .Q(\wr_buf[1][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][19]$_DFFE_PP_  (.D(net46),
    .DE(net284),
    .Q(\wr_buf[1][19] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][1]$_DFFE_PP_  (.D(net74),
    .DE(net284),
    .Q(\wr_buf[1][1] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][20]$_DFFE_PP_  (.D(net47),
    .DE(net284),
    .Q(\wr_buf[1][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][21]$_DFFE_PP_  (.D(net48),
    .DE(net284),
    .Q(\wr_buf[1][21] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][22]$_DFFE_PP_  (.D(net49),
    .DE(net284),
    .Q(\wr_buf[1][22] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][23]$_DFFE_PP_  (.D(net50),
    .DE(net284),
    .Q(\wr_buf[1][23] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][24]$_DFFE_PP_  (.D(net52),
    .DE(net284),
    .Q(\wr_buf[1][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][25]$_DFFE_PP_  (.D(net53),
    .DE(net284),
    .Q(\wr_buf[1][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][26]$_DFFE_PP_  (.D(net54),
    .DE(net284),
    .Q(\wr_buf[1][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][27]$_DFFE_PP_  (.D(net55),
    .DE(net284),
    .Q(\wr_buf[1][27] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][28]$_DFFE_PP_  (.D(net56),
    .DE(net284),
    .Q(\wr_buf[1][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][29]$_DFFE_PP_  (.D(net57),
    .DE(net284),
    .Q(\wr_buf[1][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][2]$_DFFE_PP_  (.D(net75),
    .DE(net284),
    .Q(\wr_buf[1][2] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][30]$_DFFE_PP_  (.D(net58),
    .DE(net284),
    .Q(\wr_buf[1][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][31]$_DFFE_PP_  (.D(net59),
    .DE(net284),
    .Q(\wr_buf[1][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][32]$_DFFE_PP_  (.D(net60),
    .DE(net284),
    .Q(\wr_buf[1][32] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][33]$_DFFE_PP_  (.D(net61),
    .DE(net284),
    .Q(\wr_buf[1][33] ),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][34]$_DFFE_PP_  (.D(net63),
    .DE(net284),
    .Q(\wr_buf[1][34] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][35]$_DFFE_PP_  (.D(net64),
    .DE(net284),
    .Q(\wr_buf[1][35] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][3]$_DFFE_PP_  (.D(net76),
    .DE(net284),
    .Q(\wr_buf[1][3] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][4]$_DFFE_PP_  (.D(net40),
    .DE(net284),
    .Q(\wr_buf[1][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][5]$_DFFE_PP_  (.D(net51),
    .DE(net284),
    .Q(\wr_buf[1][5] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][6]$_DFFE_PP_  (.D(net62),
    .DE(net284),
    .Q(\wr_buf[1][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][7]$_DFFE_PP_  (.D(net65),
    .DE(net284),
    .Q(\wr_buf[1][7] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][8]$_DFFE_PP_  (.D(net66),
    .DE(net284),
    .Q(\wr_buf[1][8] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[1][9]$_DFFE_PP_  (.D(net67),
    .DE(net284),
    .Q(\wr_buf[1][9] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][0]$_DFFE_PP_  (.D(net73),
    .DE(net285),
    .Q(\wr_buf[2][0] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][10]$_DFFE_PP_  (.D(net68),
    .DE(net285),
    .Q(\wr_buf[2][10] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][11]$_DFFE_PP_  (.D(net69),
    .DE(net285),
    .Q(\wr_buf[2][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][12]$_DFFE_PP_  (.D(net70),
    .DE(net285),
    .Q(\wr_buf[2][12] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][13]$_DFFE_PP_  (.D(net71),
    .DE(net285),
    .Q(\wr_buf[2][13] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][14]$_DFFE_PP_  (.D(net41),
    .DE(net285),
    .Q(\wr_buf[2][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][15]$_DFFE_PP_  (.D(net42),
    .DE(net285),
    .Q(\wr_buf[2][15] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][16]$_DFFE_PP_  (.D(net43),
    .DE(net285),
    .Q(\wr_buf[2][16] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][17]$_DFFE_PP_  (.D(net44),
    .DE(net285),
    .Q(\wr_buf[2][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][18]$_DFFE_PP_  (.D(net45),
    .DE(net285),
    .Q(\wr_buf[2][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][19]$_DFFE_PP_  (.D(net46),
    .DE(net285),
    .Q(\wr_buf[2][19] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][1]$_DFFE_PP_  (.D(net74),
    .DE(net285),
    .Q(\wr_buf[2][1] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][20]$_DFFE_PP_  (.D(net47),
    .DE(net285),
    .Q(\wr_buf[2][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][21]$_DFFE_PP_  (.D(net48),
    .DE(net285),
    .Q(\wr_buf[2][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][22]$_DFFE_PP_  (.D(net49),
    .DE(net285),
    .Q(\wr_buf[2][22] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][23]$_DFFE_PP_  (.D(net50),
    .DE(net285),
    .Q(\wr_buf[2][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][24]$_DFFE_PP_  (.D(net52),
    .DE(net285),
    .Q(\wr_buf[2][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][25]$_DFFE_PP_  (.D(net53),
    .DE(net285),
    .Q(\wr_buf[2][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][26]$_DFFE_PP_  (.D(net54),
    .DE(net285),
    .Q(\wr_buf[2][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][27]$_DFFE_PP_  (.D(net55),
    .DE(net285),
    .Q(\wr_buf[2][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][28]$_DFFE_PP_  (.D(net56),
    .DE(net285),
    .Q(\wr_buf[2][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][29]$_DFFE_PP_  (.D(net57),
    .DE(net285),
    .Q(\wr_buf[2][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][2]$_DFFE_PP_  (.D(net75),
    .DE(net285),
    .Q(\wr_buf[2][2] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][30]$_DFFE_PP_  (.D(net58),
    .DE(net285),
    .Q(\wr_buf[2][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][31]$_DFFE_PP_  (.D(net59),
    .DE(net285),
    .Q(\wr_buf[2][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][32]$_DFFE_PP_  (.D(net60),
    .DE(net285),
    .Q(\wr_buf[2][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][33]$_DFFE_PP_  (.D(net61),
    .DE(net285),
    .Q(\wr_buf[2][33] ),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][34]$_DFFE_PP_  (.D(net63),
    .DE(net285),
    .Q(\wr_buf[2][34] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][35]$_DFFE_PP_  (.D(net64),
    .DE(net285),
    .Q(\wr_buf[2][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][3]$_DFFE_PP_  (.D(net76),
    .DE(net285),
    .Q(\wr_buf[2][3] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][4]$_DFFE_PP_  (.D(net40),
    .DE(net285),
    .Q(\wr_buf[2][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][5]$_DFFE_PP_  (.D(net51),
    .DE(net285),
    .Q(\wr_buf[2][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][6]$_DFFE_PP_  (.D(net62),
    .DE(net285),
    .Q(\wr_buf[2][6] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][7]$_DFFE_PP_  (.D(net65),
    .DE(net285),
    .Q(\wr_buf[2][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][8]$_DFFE_PP_  (.D(net66),
    .DE(net285),
    .Q(\wr_buf[2][8] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[2][9]$_DFFE_PP_  (.D(net67),
    .DE(net285),
    .Q(\wr_buf[2][9] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][0]$_DFFE_PP_  (.D(net73),
    .DE(net286),
    .Q(\wr_buf[3][0] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][10]$_DFFE_PP_  (.D(net68),
    .DE(net286),
    .Q(\wr_buf[3][10] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][11]$_DFFE_PP_  (.D(net69),
    .DE(net286),
    .Q(\wr_buf[3][11] ),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][12]$_DFFE_PP_  (.D(net70),
    .DE(net286),
    .Q(\wr_buf[3][12] ),
    .CLK(clknet_leaf_30_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][13]$_DFFE_PP_  (.D(net71),
    .DE(net286),
    .Q(\wr_buf[3][13] ),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][14]$_DFFE_PP_  (.D(net41),
    .DE(net286),
    .Q(\wr_buf[3][14] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][15]$_DFFE_PP_  (.D(net42),
    .DE(net286),
    .Q(\wr_buf[3][15] ),
    .CLK(clknet_leaf_104_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][16]$_DFFE_PP_  (.D(net43),
    .DE(net286),
    .Q(\wr_buf[3][16] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][17]$_DFFE_PP_  (.D(net44),
    .DE(net286),
    .Q(\wr_buf[3][17] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][18]$_DFFE_PP_  (.D(net45),
    .DE(net286),
    .Q(\wr_buf[3][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][19]$_DFFE_PP_  (.D(net46),
    .DE(net286),
    .Q(\wr_buf[3][19] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][1]$_DFFE_PP_  (.D(net74),
    .DE(net286),
    .Q(\wr_buf[3][1] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][20]$_DFFE_PP_  (.D(net47),
    .DE(net286),
    .Q(\wr_buf[3][20] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][21]$_DFFE_PP_  (.D(net48),
    .DE(net286),
    .Q(\wr_buf[3][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][22]$_DFFE_PP_  (.D(net49),
    .DE(net286),
    .Q(\wr_buf[3][22] ),
    .CLK(clknet_leaf_108_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][23]$_DFFE_PP_  (.D(net50),
    .DE(net286),
    .Q(\wr_buf[3][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][24]$_DFFE_PP_  (.D(net52),
    .DE(net286),
    .Q(\wr_buf[3][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][25]$_DFFE_PP_  (.D(net53),
    .DE(net286),
    .Q(\wr_buf[3][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][26]$_DFFE_PP_  (.D(net54),
    .DE(net286),
    .Q(\wr_buf[3][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][27]$_DFFE_PP_  (.D(net55),
    .DE(net286),
    .Q(\wr_buf[3][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][28]$_DFFE_PP_  (.D(net56),
    .DE(net286),
    .Q(\wr_buf[3][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][29]$_DFFE_PP_  (.D(net57),
    .DE(net286),
    .Q(\wr_buf[3][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][2]$_DFFE_PP_  (.D(net75),
    .DE(net286),
    .Q(\wr_buf[3][2] ),
    .CLK(clknet_leaf_40_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][30]$_DFFE_PP_  (.D(net58),
    .DE(net286),
    .Q(\wr_buf[3][30] ),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][31]$_DFFE_PP_  (.D(net59),
    .DE(net286),
    .Q(\wr_buf[3][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][32]$_DFFE_PP_  (.D(net60),
    .DE(net286),
    .Q(\wr_buf[3][32] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][33]$_DFFE_PP_  (.D(net61),
    .DE(net286),
    .Q(\wr_buf[3][33] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][34]$_DFFE_PP_  (.D(net63),
    .DE(net286),
    .Q(\wr_buf[3][34] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][35]$_DFFE_PP_  (.D(net64),
    .DE(net286),
    .Q(\wr_buf[3][35] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][3]$_DFFE_PP_  (.D(net76),
    .DE(net286),
    .Q(\wr_buf[3][3] ),
    .CLK(clknet_leaf_44_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][4]$_DFFE_PP_  (.D(net40),
    .DE(net286),
    .Q(\wr_buf[3][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][5]$_DFFE_PP_  (.D(net51),
    .DE(net286),
    .Q(\wr_buf[3][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][6]$_DFFE_PP_  (.D(net62),
    .DE(net286),
    .Q(\wr_buf[3][6] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][7]$_DFFE_PP_  (.D(net65),
    .DE(net286),
    .Q(\wr_buf[3][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][8]$_DFFE_PP_  (.D(net66),
    .DE(net286),
    .Q(\wr_buf[3][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[3][9]$_DFFE_PP_  (.D(net67),
    .DE(net286),
    .Q(\wr_buf[3][9] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][0]$_DFFE_PP_  (.D(net73),
    .DE(net278),
    .Q(\wr_buf[4][0] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][10]$_DFFE_PP_  (.D(net68),
    .DE(net278),
    .Q(\wr_buf[4][10] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][11]$_DFFE_PP_  (.D(net69),
    .DE(net278),
    .Q(\wr_buf[4][11] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][12]$_DFFE_PP_  (.D(net70),
    .DE(net278),
    .Q(\wr_buf[4][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][13]$_DFFE_PP_  (.D(net71),
    .DE(net278),
    .Q(\wr_buf[4][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][14]$_DFFE_PP_  (.D(net41),
    .DE(net278),
    .Q(\wr_buf[4][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][15]$_DFFE_PP_  (.D(net42),
    .DE(net278),
    .Q(\wr_buf[4][15] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][16]$_DFFE_PP_  (.D(net43),
    .DE(net278),
    .Q(\wr_buf[4][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][17]$_DFFE_PP_  (.D(net44),
    .DE(net278),
    .Q(\wr_buf[4][17] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][18]$_DFFE_PP_  (.D(net45),
    .DE(net278),
    .Q(\wr_buf[4][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][19]$_DFFE_PP_  (.D(net46),
    .DE(net278),
    .Q(\wr_buf[4][19] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][1]$_DFFE_PP_  (.D(net74),
    .DE(net278),
    .Q(\wr_buf[4][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][20]$_DFFE_PP_  (.D(net47),
    .DE(net278),
    .Q(\wr_buf[4][20] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][21]$_DFFE_PP_  (.D(net48),
    .DE(net278),
    .Q(\wr_buf[4][21] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][22]$_DFFE_PP_  (.D(net49),
    .DE(net278),
    .Q(\wr_buf[4][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][23]$_DFFE_PP_  (.D(net50),
    .DE(net278),
    .Q(\wr_buf[4][23] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][24]$_DFFE_PP_  (.D(net52),
    .DE(net278),
    .Q(\wr_buf[4][24] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][25]$_DFFE_PP_  (.D(net53),
    .DE(net278),
    .Q(\wr_buf[4][25] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][26]$_DFFE_PP_  (.D(net54),
    .DE(net278),
    .Q(\wr_buf[4][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][27]$_DFFE_PP_  (.D(net55),
    .DE(net278),
    .Q(\wr_buf[4][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][28]$_DFFE_PP_  (.D(net56),
    .DE(net278),
    .Q(\wr_buf[4][28] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][29]$_DFFE_PP_  (.D(net57),
    .DE(net278),
    .Q(\wr_buf[4][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][2]$_DFFE_PP_  (.D(net75),
    .DE(net278),
    .Q(\wr_buf[4][2] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][30]$_DFFE_PP_  (.D(net58),
    .DE(net278),
    .Q(\wr_buf[4][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][31]$_DFFE_PP_  (.D(net59),
    .DE(net278),
    .Q(\wr_buf[4][31] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][32]$_DFFE_PP_  (.D(net60),
    .DE(net278),
    .Q(\wr_buf[4][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][33]$_DFFE_PP_  (.D(net61),
    .DE(net278),
    .Q(\wr_buf[4][33] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][34]$_DFFE_PP_  (.D(net63),
    .DE(net278),
    .Q(\wr_buf[4][34] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][35]$_DFFE_PP_  (.D(net64),
    .DE(net278),
    .Q(\wr_buf[4][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][3]$_DFFE_PP_  (.D(net76),
    .DE(net278),
    .Q(\wr_buf[4][3] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][4]$_DFFE_PP_  (.D(net40),
    .DE(net278),
    .Q(\wr_buf[4][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][5]$_DFFE_PP_  (.D(net51),
    .DE(net278),
    .Q(\wr_buf[4][5] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][6]$_DFFE_PP_  (.D(net62),
    .DE(net278),
    .Q(\wr_buf[4][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][7]$_DFFE_PP_  (.D(net65),
    .DE(net278),
    .Q(\wr_buf[4][7] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][8]$_DFFE_PP_  (.D(net66),
    .DE(net278),
    .Q(\wr_buf[4][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[4][9]$_DFFE_PP_  (.D(net67),
    .DE(net278),
    .Q(\wr_buf[4][9] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][0]$_DFFE_PP_  (.D(net73),
    .DE(net279),
    .Q(\wr_buf[5][0] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][10]$_DFFE_PP_  (.D(net68),
    .DE(net279),
    .Q(\wr_buf[5][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][11]$_DFFE_PP_  (.D(net69),
    .DE(net279),
    .Q(\wr_buf[5][11] ),
    .CLK(clknet_leaf_37_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][12]$_DFFE_PP_  (.D(net70),
    .DE(net279),
    .Q(\wr_buf[5][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][13]$_DFFE_PP_  (.D(net71),
    .DE(net279),
    .Q(\wr_buf[5][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][14]$_DFFE_PP_  (.D(net41),
    .DE(net279),
    .Q(\wr_buf[5][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][15]$_DFFE_PP_  (.D(net42),
    .DE(net279),
    .Q(\wr_buf[5][15] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][16]$_DFFE_PP_  (.D(net43),
    .DE(net279),
    .Q(\wr_buf[5][16] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][17]$_DFFE_PP_  (.D(net44),
    .DE(net279),
    .Q(\wr_buf[5][17] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][18]$_DFFE_PP_  (.D(net45),
    .DE(net279),
    .Q(\wr_buf[5][18] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][19]$_DFFE_PP_  (.D(net46),
    .DE(net279),
    .Q(\wr_buf[5][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][1]$_DFFE_PP_  (.D(net74),
    .DE(net279),
    .Q(\wr_buf[5][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][20]$_DFFE_PP_  (.D(net47),
    .DE(net279),
    .Q(\wr_buf[5][20] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][21]$_DFFE_PP_  (.D(net48),
    .DE(net279),
    .Q(\wr_buf[5][21] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][22]$_DFFE_PP_  (.D(net49),
    .DE(net279),
    .Q(\wr_buf[5][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][23]$_DFFE_PP_  (.D(net50),
    .DE(net279),
    .Q(\wr_buf[5][23] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][24]$_DFFE_PP_  (.D(net52),
    .DE(net279),
    .Q(\wr_buf[5][24] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][25]$_DFFE_PP_  (.D(net53),
    .DE(net279),
    .Q(\wr_buf[5][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][26]$_DFFE_PP_  (.D(net54),
    .DE(net279),
    .Q(\wr_buf[5][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][27]$_DFFE_PP_  (.D(net55),
    .DE(net279),
    .Q(\wr_buf[5][27] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][28]$_DFFE_PP_  (.D(net56),
    .DE(net279),
    .Q(\wr_buf[5][28] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][29]$_DFFE_PP_  (.D(net57),
    .DE(net279),
    .Q(\wr_buf[5][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][2]$_DFFE_PP_  (.D(net75),
    .DE(net279),
    .Q(\wr_buf[5][2] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][30]$_DFFE_PP_  (.D(net58),
    .DE(net279),
    .Q(\wr_buf[5][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][31]$_DFFE_PP_  (.D(net59),
    .DE(net279),
    .Q(\wr_buf[5][31] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][32]$_DFFE_PP_  (.D(net60),
    .DE(net279),
    .Q(\wr_buf[5][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][33]$_DFFE_PP_  (.D(net61),
    .DE(net279),
    .Q(\wr_buf[5][33] ),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][34]$_DFFE_PP_  (.D(net63),
    .DE(net279),
    .Q(\wr_buf[5][34] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][35]$_DFFE_PP_  (.D(net64),
    .DE(net279),
    .Q(\wr_buf[5][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][3]$_DFFE_PP_  (.D(net76),
    .DE(net279),
    .Q(\wr_buf[5][3] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][4]$_DFFE_PP_  (.D(net40),
    .DE(net279),
    .Q(\wr_buf[5][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][5]$_DFFE_PP_  (.D(net51),
    .DE(net279),
    .Q(\wr_buf[5][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][6]$_DFFE_PP_  (.D(net62),
    .DE(net279),
    .Q(\wr_buf[5][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][7]$_DFFE_PP_  (.D(net65),
    .DE(net279),
    .Q(\wr_buf[5][7] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][8]$_DFFE_PP_  (.D(net66),
    .DE(net279),
    .Q(\wr_buf[5][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[5][9]$_DFFE_PP_  (.D(net67),
    .DE(net279),
    .Q(\wr_buf[5][9] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][0]$_DFFE_PP_  (.D(net73),
    .DE(net281),
    .Q(\wr_buf[6][0] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][10]$_DFFE_PP_  (.D(net68),
    .DE(_0034_),
    .Q(\wr_buf[6][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][11]$_DFFE_PP_  (.D(net69),
    .DE(net281),
    .Q(\wr_buf[6][11] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][12]$_DFFE_PP_  (.D(net70),
    .DE(_0034_),
    .Q(\wr_buf[6][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][13]$_DFFE_PP_  (.D(net71),
    .DE(net281),
    .Q(\wr_buf[6][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][14]$_DFFE_PP_  (.D(net41),
    .DE(net281),
    .Q(\wr_buf[6][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][15]$_DFFE_PP_  (.D(net42),
    .DE(net280),
    .Q(\wr_buf[6][15] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][16]$_DFFE_PP_  (.D(net43),
    .DE(net281),
    .Q(\wr_buf[6][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][17]$_DFFE_PP_  (.D(net44),
    .DE(net280),
    .Q(\wr_buf[6][17] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][18]$_DFFE_PP_  (.D(net45),
    .DE(net280),
    .Q(\wr_buf[6][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][19]$_DFFE_PP_  (.D(net46),
    .DE(net280),
    .Q(\wr_buf[6][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][1]$_DFFE_PP_  (.D(net74),
    .DE(net281),
    .Q(\wr_buf[6][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][20]$_DFFE_PP_  (.D(net47),
    .DE(net280),
    .Q(\wr_buf[6][20] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][21]$_DFFE_PP_  (.D(net48),
    .DE(net280),
    .Q(\wr_buf[6][21] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][22]$_DFFE_PP_  (.D(net49),
    .DE(net280),
    .Q(\wr_buf[6][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][23]$_DFFE_PP_  (.D(net50),
    .DE(net280),
    .Q(\wr_buf[6][23] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][24]$_DFFE_PP_  (.D(net52),
    .DE(net280),
    .Q(\wr_buf[6][24] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][25]$_DFFE_PP_  (.D(net53),
    .DE(_0034_),
    .Q(\wr_buf[6][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][26]$_DFFE_PP_  (.D(net54),
    .DE(net281),
    .Q(\wr_buf[6][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][27]$_DFFE_PP_  (.D(net55),
    .DE(net281),
    .Q(\wr_buf[6][27] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][28]$_DFFE_PP_  (.D(net56),
    .DE(net280),
    .Q(\wr_buf[6][28] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][29]$_DFFE_PP_  (.D(net57),
    .DE(net281),
    .Q(\wr_buf[6][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][2]$_DFFE_PP_  (.D(net75),
    .DE(net281),
    .Q(\wr_buf[6][2] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][30]$_DFFE_PP_  (.D(net58),
    .DE(net281),
    .Q(\wr_buf[6][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][31]$_DFFE_PP_  (.D(net59),
    .DE(net280),
    .Q(\wr_buf[6][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][32]$_DFFE_PP_  (.D(net60),
    .DE(_0034_),
    .Q(\wr_buf[6][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][33]$_DFFE_PP_  (.D(net61),
    .DE(net280),
    .Q(\wr_buf[6][33] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][34]$_DFFE_PP_  (.D(net63),
    .DE(_0034_),
    .Q(\wr_buf[6][34] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][35]$_DFFE_PP_  (.D(net64),
    .DE(net280),
    .Q(\wr_buf[6][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][3]$_DFFE_PP_  (.D(net76),
    .DE(net281),
    .Q(\wr_buf[6][3] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][4]$_DFFE_PP_  (.D(net40),
    .DE(net281),
    .Q(\wr_buf[6][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][5]$_DFFE_PP_  (.D(net51),
    .DE(net281),
    .Q(\wr_buf[6][5] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][6]$_DFFE_PP_  (.D(net62),
    .DE(net280),
    .Q(\wr_buf[6][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][7]$_DFFE_PP_  (.D(net65),
    .DE(_0034_),
    .Q(\wr_buf[6][7] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][8]$_DFFE_PP_  (.D(net66),
    .DE(_0034_),
    .Q(\wr_buf[6][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[6][9]$_DFFE_PP_  (.D(net67),
    .DE(net281),
    .Q(\wr_buf[6][9] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][0]$_DFFE_PP_  (.D(net73),
    .DE(net277),
    .Q(\wr_buf[7][0] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][10]$_DFFE_PP_  (.D(net68),
    .DE(net277),
    .Q(\wr_buf[7][10] ),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][11]$_DFFE_PP_  (.D(net69),
    .DE(net277),
    .Q(\wr_buf[7][11] ),
    .CLK(clknet_leaf_36_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][12]$_DFFE_PP_  (.D(net70),
    .DE(net277),
    .Q(\wr_buf[7][12] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][13]$_DFFE_PP_  (.D(net71),
    .DE(net277),
    .Q(\wr_buf[7][13] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][14]$_DFFE_PP_  (.D(net41),
    .DE(net277),
    .Q(\wr_buf[7][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][15]$_DFFE_PP_  (.D(net42),
    .DE(net277),
    .Q(\wr_buf[7][15] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][16]$_DFFE_PP_  (.D(net43),
    .DE(net277),
    .Q(\wr_buf[7][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][17]$_DFFE_PP_  (.D(net44),
    .DE(net277),
    .Q(\wr_buf[7][17] ),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][18]$_DFFE_PP_  (.D(net45),
    .DE(net277),
    .Q(\wr_buf[7][18] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][19]$_DFFE_PP_  (.D(net46),
    .DE(net277),
    .Q(\wr_buf[7][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][1]$_DFFE_PP_  (.D(net74),
    .DE(net277),
    .Q(\wr_buf[7][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][20]$_DFFE_PP_  (.D(net47),
    .DE(net277),
    .Q(\wr_buf[7][20] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][21]$_DFFE_PP_  (.D(net48),
    .DE(net277),
    .Q(\wr_buf[7][21] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][22]$_DFFE_PP_  (.D(net49),
    .DE(net277),
    .Q(\wr_buf[7][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][23]$_DFFE_PP_  (.D(net50),
    .DE(net277),
    .Q(\wr_buf[7][23] ),
    .CLK(clknet_leaf_106_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][24]$_DFFE_PP_  (.D(net52),
    .DE(net277),
    .Q(\wr_buf[7][24] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][25]$_DFFE_PP_  (.D(net53),
    .DE(net277),
    .Q(\wr_buf[7][25] ),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][26]$_DFFE_PP_  (.D(net54),
    .DE(net277),
    .Q(\wr_buf[7][26] ),
    .CLK(clknet_leaf_9_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][27]$_DFFE_PP_  (.D(net55),
    .DE(net277),
    .Q(\wr_buf[7][27] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][28]$_DFFE_PP_  (.D(net56),
    .DE(net277),
    .Q(\wr_buf[7][28] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][29]$_DFFE_PP_  (.D(net57),
    .DE(net277),
    .Q(\wr_buf[7][29] ),
    .CLK(clknet_leaf_33_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][2]$_DFFE_PP_  (.D(net75),
    .DE(net277),
    .Q(\wr_buf[7][2] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][30]$_DFFE_PP_  (.D(net58),
    .DE(net277),
    .Q(\wr_buf[7][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][31]$_DFFE_PP_  (.D(net59),
    .DE(net277),
    .Q(\wr_buf[7][31] ),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][32]$_DFFE_PP_  (.D(net60),
    .DE(net277),
    .Q(\wr_buf[7][32] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][33]$_DFFE_PP_  (.D(net61),
    .DE(net277),
    .Q(\wr_buf[7][33] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][34]$_DFFE_PP_  (.D(net63),
    .DE(net277),
    .Q(\wr_buf[7][34] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][35]$_DFFE_PP_  (.D(net64),
    .DE(net277),
    .Q(\wr_buf[7][35] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][3]$_DFFE_PP_  (.D(net76),
    .DE(net277),
    .Q(\wr_buf[7][3] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][4]$_DFFE_PP_  (.D(net40),
    .DE(net277),
    .Q(\wr_buf[7][4] ),
    .CLK(clknet_leaf_8_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][5]$_DFFE_PP_  (.D(net51),
    .DE(net277),
    .Q(\wr_buf[7][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][6]$_DFFE_PP_  (.D(net62),
    .DE(net277),
    .Q(\wr_buf[7][6] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][7]$_DFFE_PP_  (.D(net65),
    .DE(net277),
    .Q(\wr_buf[7][7] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][8]$_DFFE_PP_  (.D(net66),
    .DE(net277),
    .Q(\wr_buf[7][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[7][9]$_DFFE_PP_  (.D(net67),
    .DE(net277),
    .Q(\wr_buf[7][9] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][0]$_DFFE_PP_  (.D(net73),
    .DE(_0036_),
    .Q(\wr_buf[8][0] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][10]$_DFFE_PP_  (.D(net68),
    .DE(net269),
    .Q(\wr_buf[8][10] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][11]$_DFFE_PP_  (.D(net69),
    .DE(net269),
    .Q(\wr_buf[8][11] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][12]$_DFFE_PP_  (.D(net70),
    .DE(net269),
    .Q(\wr_buf[8][12] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][13]$_DFFE_PP_  (.D(net71),
    .DE(net269),
    .Q(\wr_buf[8][13] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][14]$_DFFE_PP_  (.D(net41),
    .DE(net269),
    .Q(\wr_buf[8][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][15]$_DFFE_PP_  (.D(net42),
    .DE(net269),
    .Q(\wr_buf[8][15] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][16]$_DFFE_PP_  (.D(net43),
    .DE(net269),
    .Q(\wr_buf[8][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][17]$_DFFE_PP_  (.D(net44),
    .DE(net269),
    .Q(\wr_buf[8][17] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][18]$_DFFE_PP_  (.D(net45),
    .DE(net269),
    .Q(\wr_buf[8][18] ),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][19]$_DFFE_PP_  (.D(net46),
    .DE(net269),
    .Q(\wr_buf[8][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][1]$_DFFE_PP_  (.D(net74),
    .DE(_0036_),
    .Q(\wr_buf[8][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][20]$_DFFE_PP_  (.D(net47),
    .DE(net269),
    .Q(\wr_buf[8][20] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][21]$_DFFE_PP_  (.D(net48),
    .DE(net269),
    .Q(\wr_buf[8][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][22]$_DFFE_PP_  (.D(net49),
    .DE(net269),
    .Q(\wr_buf[8][22] ),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][23]$_DFFE_PP_  (.D(net50),
    .DE(net269),
    .Q(\wr_buf[8][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][24]$_DFFE_PP_  (.D(net52),
    .DE(net269),
    .Q(\wr_buf[8][24] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][25]$_DFFE_PP_  (.D(net53),
    .DE(net269),
    .Q(\wr_buf[8][25] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][26]$_DFFE_PP_  (.D(net54),
    .DE(net269),
    .Q(\wr_buf[8][26] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][27]$_DFFE_PP_  (.D(net55),
    .DE(net269),
    .Q(\wr_buf[8][27] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][28]$_DFFE_PP_  (.D(net56),
    .DE(net269),
    .Q(\wr_buf[8][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][29]$_DFFE_PP_  (.D(net57),
    .DE(net269),
    .Q(\wr_buf[8][29] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][2]$_DFFE_PP_  (.D(net75),
    .DE(_0036_),
    .Q(\wr_buf[8][2] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][30]$_DFFE_PP_  (.D(net58),
    .DE(net269),
    .Q(\wr_buf[8][30] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][31]$_DFFE_PP_  (.D(net59),
    .DE(net269),
    .Q(\wr_buf[8][31] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][32]$_DFFE_PP_  (.D(net60),
    .DE(net269),
    .Q(\wr_buf[8][32] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][33]$_DFFE_PP_  (.D(net61),
    .DE(net269),
    .Q(\wr_buf[8][33] ),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][34]$_DFFE_PP_  (.D(net63),
    .DE(net269),
    .Q(\wr_buf[8][34] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][35]$_DFFE_PP_  (.D(net64),
    .DE(net269),
    .Q(\wr_buf[8][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][3]$_DFFE_PP_  (.D(net76),
    .DE(_0036_),
    .Q(\wr_buf[8][3] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][4]$_DFFE_PP_  (.D(net40),
    .DE(net269),
    .Q(\wr_buf[8][4] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][5]$_DFFE_PP_  (.D(net51),
    .DE(net269),
    .Q(\wr_buf[8][5] ),
    .CLK(clknet_leaf_0_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][6]$_DFFE_PP_  (.D(net62),
    .DE(net269),
    .Q(\wr_buf[8][6] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][7]$_DFFE_PP_  (.D(net65),
    .DE(net269),
    .Q(\wr_buf[8][7] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][8]$_DFFE_PP_  (.D(net66),
    .DE(net269),
    .Q(\wr_buf[8][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[8][9]$_DFFE_PP_  (.D(net67),
    .DE(net269),
    .Q(\wr_buf[8][9] ),
    .CLK(clknet_leaf_27_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][0]$_DFFE_PP_  (.D(net73),
    .DE(_0037_),
    .Q(\wr_buf[9][0] ),
    .CLK(clknet_leaf_25_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][10]$_DFFE_PP_  (.D(net68),
    .DE(net270),
    .Q(\wr_buf[9][10] ),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][11]$_DFFE_PP_  (.D(net69),
    .DE(net270),
    .Q(\wr_buf[9][11] ),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][12]$_DFFE_PP_  (.D(net70),
    .DE(net270),
    .Q(\wr_buf[9][12] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][13]$_DFFE_PP_  (.D(net71),
    .DE(net270),
    .Q(\wr_buf[9][13] ),
    .CLK(clknet_leaf_39_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][14]$_DFFE_PP_  (.D(net41),
    .DE(net270),
    .Q(\wr_buf[9][14] ),
    .CLK(clknet_leaf_34_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][15]$_DFFE_PP_  (.D(net42),
    .DE(net270),
    .Q(\wr_buf[9][15] ),
    .CLK(clknet_leaf_103_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][16]$_DFFE_PP_  (.D(net43),
    .DE(net270),
    .Q(\wr_buf[9][16] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][17]$_DFFE_PP_  (.D(net44),
    .DE(net270),
    .Q(\wr_buf[9][17] ),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][18]$_DFFE_PP_  (.D(net45),
    .DE(net270),
    .Q(\wr_buf[9][18] ),
    .CLK(clknet_leaf_5_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][19]$_DFFE_PP_  (.D(net46),
    .DE(net270),
    .Q(\wr_buf[9][19] ),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][1]$_DFFE_PP_  (.D(net74),
    .DE(_0037_),
    .Q(\wr_buf[9][1] ),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][20]$_DFFE_PP_  (.D(net47),
    .DE(net270),
    .Q(\wr_buf[9][20] ),
    .CLK(clknet_leaf_2_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][21]$_DFFE_PP_  (.D(net48),
    .DE(net270),
    .Q(\wr_buf[9][21] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][22]$_DFFE_PP_  (.D(net49),
    .DE(net270),
    .Q(\wr_buf[9][22] ),
    .CLK(clknet_leaf_107_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][23]$_DFFE_PP_  (.D(net50),
    .DE(net270),
    .Q(\wr_buf[9][23] ),
    .CLK(clknet_leaf_105_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][24]$_DFFE_PP_  (.D(net52),
    .DE(net270),
    .Q(\wr_buf[9][24] ),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][25]$_DFFE_PP_  (.D(net53),
    .DE(net270),
    .Q(\wr_buf[9][25] ),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][26]$_DFFE_PP_  (.D(net54),
    .DE(net270),
    .Q(\wr_buf[9][26] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][27]$_DFFE_PP_  (.D(net55),
    .DE(net270),
    .Q(\wr_buf[9][27] ),
    .CLK(clknet_leaf_35_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][28]$_DFFE_PP_  (.D(net56),
    .DE(net270),
    .Q(\wr_buf[9][28] ),
    .CLK(clknet_leaf_6_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][29]$_DFFE_PP_  (.D(net57),
    .DE(net270),
    .Q(\wr_buf[9][29] ),
    .CLK(clknet_leaf_12_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][2]$_DFFE_PP_  (.D(net75),
    .DE(_0037_),
    .Q(\wr_buf[9][2] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][30]$_DFFE_PP_  (.D(net58),
    .DE(net270),
    .Q(\wr_buf[9][30] ),
    .CLK(clknet_leaf_11_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][31]$_DFFE_PP_  (.D(net59),
    .DE(net270),
    .Q(\wr_buf[9][31] ),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][32]$_DFFE_PP_  (.D(net60),
    .DE(net270),
    .Q(\wr_buf[9][32] ),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][33]$_DFFE_PP_  (.D(net61),
    .DE(net270),
    .Q(\wr_buf[9][33] ),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][34]$_DFFE_PP_  (.D(net63),
    .DE(net270),
    .Q(\wr_buf[9][34] ),
    .CLK(clknet_leaf_24_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][35]$_DFFE_PP_  (.D(net64),
    .DE(net270),
    .Q(\wr_buf[9][35] ),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][3]$_DFFE_PP_  (.D(net76),
    .DE(_0037_),
    .Q(\wr_buf[9][3] ),
    .CLK(clknet_leaf_26_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][4]$_DFFE_PP_  (.D(net40),
    .DE(net270),
    .Q(\wr_buf[9][4] ),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][5]$_DFFE_PP_  (.D(net51),
    .DE(net270),
    .Q(\wr_buf[9][5] ),
    .CLK(clknet_leaf_1_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][6]$_DFFE_PP_  (.D(net62),
    .DE(net270),
    .Q(\wr_buf[9][6] ),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][7]$_DFFE_PP_  (.D(net65),
    .DE(net270),
    .Q(\wr_buf[9][7] ),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][8]$_DFFE_PP_  (.D(net66),
    .DE(net270),
    .Q(\wr_buf[9][8] ),
    .CLK(clknet_leaf_29_clk));
 sky130_fd_sc_hd__edfxtp_1 \wr_buf[9][9]$_DFFE_PP_  (.D(net67),
    .DE(net270),
    .Q(\wr_buf[9][9] ),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_burst_ctr[0]$_DFFE_PN0P_  (.D(_0146_),
    .Q(\wr_burst_ctr[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_burst_ctr[1]$_DFFE_PN0P_  (.D(_0147_),
    .Q(\wr_burst_ctr[1] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[0]$_DFFE_PN0P_  (.D(_0148_),
    .Q(\wr_dat_r[0] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[10]$_DFFE_PN0P_  (.D(_0149_),
    .Q(\wr_dat_r[10] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[11]$_DFFE_PN0P_  (.D(_0150_),
    .Q(\wr_dat_r[11] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_100_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[12]$_DFFE_PN0P_  (.D(_0151_),
    .Q(\wr_dat_r[12] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_10_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[13]$_DFFE_PN0P_  (.D(_0152_),
    .Q(\wr_dat_r[13] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_100_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[14]$_DFFE_PN0P_  (.D(_0153_),
    .Q(\wr_dat_r[14] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[15]$_DFFE_PN0P_  (.D(_0154_),
    .Q(\wr_dat_r[15] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[16]$_DFFE_PN0P_  (.D(_0155_),
    .Q(\wr_dat_r[16] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_3_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[17]$_DFFE_PN0P_  (.D(_0156_),
    .Q(\wr_dat_r[17] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[18]$_DFFE_PN0P_  (.D(_0157_),
    .Q(\wr_dat_r[18] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_4_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[19]$_DFFE_PN0P_  (.D(_0158_),
    .Q(\wr_dat_r[19] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_18_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[1]$_DFFE_PN0P_  (.D(_0159_),
    .Q(\wr_dat_r[1] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_7_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[20]$_DFFE_PN0P_  (.D(_0160_),
    .Q(\wr_dat_r[20] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_22_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[21]$_DFFE_PN0P_  (.D(_0161_),
    .Q(\wr_dat_r[21] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_15_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[22]$_DFFE_PN0P_  (.D(_0162_),
    .Q(\wr_dat_r[22] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[23]$_DFFE_PN0P_  (.D(_0163_),
    .Q(\wr_dat_r[23] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[24]$_DFFE_PN0P_  (.D(_0164_),
    .Q(\wr_dat_r[24] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_16_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[25]$_DFFE_PN0P_  (.D(_0165_),
    .Q(\wr_dat_r[25] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[26]$_DFFE_PN0P_  (.D(_0166_),
    .Q(\wr_dat_r[26] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[27]$_DFFE_PN0P_  (.D(_0167_),
    .Q(\wr_dat_r[27] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_102_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[28]$_DFFE_PN0P_  (.D(_0168_),
    .Q(\wr_dat_r[28] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_13_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[29]$_DFFE_PN0P_  (.D(_0169_),
    .Q(\wr_dat_r[29] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_101_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[2]$_DFFE_PN0P_  (.D(_0170_),
    .Q(\wr_dat_r[2] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_17_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[30]$_DFFE_PN0P_  (.D(_0171_),
    .Q(\wr_dat_r[30] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[31]$_DFFE_PN0P_  (.D(_0172_),
    .Q(\wr_dat_r[31] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_21_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[3]$_DFFE_PN0P_  (.D(_0173_),
    .Q(\wr_dat_r[3] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_19_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[4]$_DFFE_PN0P_  (.D(_0174_),
    .Q(\wr_dat_r[4] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_20_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[5]$_DFFE_PN0P_  (.D(_0175_),
    .Q(\wr_dat_r[5] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_28_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[6]$_DFFE_PN0P_  (.D(_0176_),
    .Q(\wr_dat_r[6] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_32_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[7]$_DFFE_PN0P_  (.D(_0177_),
    .Q(\wr_dat_r[7] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_38_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[8]$_DFFE_PN0P_  (.D(_0178_),
    .Q(\wr_dat_r[8] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_14_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_dat_r[9]$_DFFE_PN0P_  (.D(_0179_),
    .Q(\wr_dat_r[9] ),
    .RESET_B(net326),
    .CLK(clknet_leaf_31_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[0]$_DFFE_PN0P_  (.D(_0180_),
    .Q(\wr_lat_ctr[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_47_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[1]$_DFFE_PN0P_  (.D(_0181_),
    .Q(\wr_lat_ctr[1] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_47_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[2]$_DFFE_PN0P_  (.D(_0182_),
    .Q(\wr_lat_ctr[2] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[3]$_DFFE_PN0P_  (.D(_0183_),
    .Q(\wr_lat_ctr[3] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[4]$_DFFE_PN0P_  (.D(_0184_),
    .Q(\wr_lat_ctr[4] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[5]$_DFFE_PN0P_  (.D(_0185_),
    .Q(\wr_lat_ctr[5] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[6]$_DFFE_PN0P_  (.D(_0186_),
    .Q(\wr_lat_ctr[6] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_lat_ctr[7]$_DFFE_PN0P_  (.D(_0187_),
    .Q(\wr_lat_ctr[7] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_43_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_msk_r[0]$_DFFE_PN0P_  (.D(_0188_),
    .Q(\wr_msk_r[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_42_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_msk_r[1]$_DFFE_PN0P_  (.D(_0189_),
    .Q(\wr_msk_r[1] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_43_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_msk_r[2]$_DFFE_PN0P_  (.D(_0190_),
    .Q(\wr_msk_r[2] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_41_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_msk_r[3]$_DFFE_PN0P_  (.D(_0191_),
    .Q(\wr_msk_r[3] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_4 \wr_rptr[0]$_DFFE_PN0P_  (.D(_0192_),
    .Q(\wr_rptr[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_4 \wr_rptr[1]$_DFFE_PN0P_  (.D(_0193_),
    .Q(\wr_rptr[1] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_45_clk));
 sky130_fd_sc_hd__dfrtp_2 \wr_rptr[2]$_DFFE_PN0P_  (.D(_0194_),
    .Q(\wr_rptr[2] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_rptr[3]$_DFFE_PN0P_  (.D(_0195_),
    .Q(\wr_rptr[3] ),
    .RESET_B(net39),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_rptr[4]$_DFFE_PN0P_  (.D(_0196_),
    .Q(\wr_rptr[4] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfstp_2 \wr_state[0]$_DFF_PN1_  (.D(_0003_),
    .Q(\wr_state[0] ),
    .SET_B(net325),
    .CLK(clknet_leaf_43_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_state[1]$_DFF_PN0_  (.D(_0004_),
    .Q(net95),
    .RESET_B(net325),
    .CLK(clknet_leaf_43_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_state[2]$_DFF_PN0_  (.D(_0005_),
    .Q(\wr_state[2] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_43_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_wptr[0]$_DFFE_PN0P_  (.D(_0197_),
    .Q(\wr_wptr[0] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_wptr[1]$_DFFE_PN0P_  (.D(_0198_),
    .Q(\wr_wptr[1] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_23_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_wptr[2]$_DFFE_PN0P_  (.D(_0199_),
    .Q(\wr_wptr[2] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_wptr[3]$_DFFE_PN0P_  (.D(_0200_),
    .Q(\wr_wptr[3] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 sky130_fd_sc_hd__dfrtp_1 \wr_wptr[4]$_DFFE_PN0P_  (.D(_0201_),
    .Q(\wr_wptr[4] ),
    .RESET_B(net325),
    .CLK(clknet_leaf_46_clk));
 assign ddr_dqs_o = net96;
 assign ddr_dqs_oe = net97;
endmodule
