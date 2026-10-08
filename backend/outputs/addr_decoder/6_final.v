module addr_decoder (dec_rank,
    dec_bank,
    dec_col,
    dec_row,
    req_addr);
 output dec_rank;
 output [2:0] dec_bank;
 output [9:0] dec_col;
 output [14:0] dec_row;
 input [28:0] req_addr;


 sky130_fd_sc_hd__conb_1 _05__1 (.LO(dec_col[0]));
 sky130_fd_sc_hd__conb_1 _06__2 (.LO(dec_col[1]));
 sky130_fd_sc_hd__conb_1 _07__3 (.LO(dec_col[2]));
 sky130_fd_sc_hd__conb_1 _15__4 (.LO(dec_rank));
 assign dec_bank[0] = req_addr[11];
 assign dec_bank[1] = req_addr[12];
 assign dec_bank[2] = req_addr[13];
 assign dec_col[3] = req_addr[4];
 assign dec_col[4] = req_addr[5];
 assign dec_col[5] = req_addr[6];
 assign dec_col[6] = req_addr[7];
 assign dec_col[7] = req_addr[8];
 assign dec_col[8] = req_addr[9];
 assign dec_col[9] = req_addr[10];
 assign dec_row[0] = req_addr[14];
 assign dec_row[10] = req_addr[24];
 assign dec_row[11] = req_addr[25];
 assign dec_row[12] = req_addr[26];
 assign dec_row[13] = req_addr[27];
 assign dec_row[14] = req_addr[28];
 assign dec_row[1] = req_addr[15];
 assign dec_row[2] = req_addr[16];
 assign dec_row[3] = req_addr[17];
 assign dec_row[4] = req_addr[18];
 assign dec_row[5] = req_addr[19];
 assign dec_row[6] = req_addr[20];
 assign dec_row[7] = req_addr[21];
 assign dec_row[8] = req_addr[22];
 assign dec_row[9] = req_addr[23];
endmodule
