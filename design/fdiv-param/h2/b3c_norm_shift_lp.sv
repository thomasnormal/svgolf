// H2 probe B3c: the normalizer exactly as in the reference (constant shifts `<< 8`..`<< 1` under ?:),
// with vectors declared by localparam bounds so that part selects are not "legacy".
module b3c_norm_shift_lp (
  input  logic [10:0] mi,
  output logic [10:0] no,
  output logic [3:0]  lzo
);
  localparam integer W11 = 11;
  logic [W11-1:0] ma, na1, na2, na3, na4;
  logic           za8, za4, za2, za1;
  assign ma  = mi;
  assign za8 = (ma[10:3] == 8'd0);
  assign na1 = za8 ? (ma << 8) : ma;
  assign za4 = (na1[10:7] == 4'd0);
  assign na2 = za4 ? (na1 << 4) : na1;
  assign za2 = (na2[10:9] == 2'd0);
  assign na3 = za2 ? (na2 << 2) : na2;
  assign za1 = ~na3[10];
  assign na4 = za1 ? (na3 << 1) : na3;
  assign no  = na4;
  assign lzo = {za8, za4, za2, za1};
endmodule
