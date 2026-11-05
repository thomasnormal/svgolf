// H2 probe B2b: the same, rewritten for today's fragment: the comparison named first.
module b2b_sig_rw (
  input  logic [4:0] ea,
  input  logic [9:0] fa,
  output logic [10:0] ma,
  output logic [4:0]  xa
);
  logic nz;
  assign nz = ea != 5'd0;
  assign ma = {nz, fa};
  assign xa = nz ? ea : 5'd1;
endmodule
