// H2 probe B5: quotient normalization (lines 101-107), as written.
module b5_qnorm (
  input  logic [12:0] qq,
  input  logic [11:0] rem13,
  output logic        adj,
  output logic [11:0] qm,
  output logic        st0
);
  assign adj = ~qq[12];
  assign qm  = qq[12] ? qq[12:1] : qq[11:0];
  assign st0 = (qq[12] & qq[0]) | (rem13 != 12'd0);
endmodule
