// H2 probe B3: the normalizer (lines 64-74), as written (constant shifts `<< 8`, `<< 4`, `<< 2`, `<< 1` under ?:).
module b3_norm (
  input  logic [10:0] ma,
  output logic [10:0] na4,
  output logic [3:0]  lza
);
  logic [10:0] na1, na2, na3;
  logic        za8, za4, za2, za1;
  assign za8 = (ma[10:3] == 8'd0);
  assign na1 = za8 ? (ma << 8) : ma;
  assign za4 = (na1[10:7] == 4'd0);
  assign na2 = za4 ? (na1 << 4) : na1;
  assign za2 = (na2[10:9] == 2'd0);
  assign na3 = za2 ? (na2 << 2) : na2;
  assign za1 = ~na3[10];
  assign na4 = za1 ? (na3 << 1) : na3;
  assign lza = {za8, za4, za2, za1};
endmodule
