// H2 probe B2: significands with the hidden bit and effective exponents (lines 55-62), as written.
module b2_sig (
  input  logic [4:0] ea,
  input  logic [9:0] fa,
  output logic [10:0] ma,
  output logic [4:0]  xa
);
  assign ma = {ea != 5'd0, fa};
  assign xa = (ea == 5'd0) ? 5'd1 : ea;
endmodule
