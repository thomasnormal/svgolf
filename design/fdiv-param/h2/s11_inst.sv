// H2 style S11: structural style with sub-module instances (Bh4r4t style: comparator/subtractor per stage).
module s11_cmp (input logic [3:0] x, y, output logic ge);
  assign ge = (x >= y);
endmodule
module s11_inst (input logic [3:0] a, b, output logic g);
  s11_cmp u0 (.x(a), .y(b), .ge(g));
endmodule
