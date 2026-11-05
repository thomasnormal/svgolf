// H2 style S10: replication and an indexed part select (fpu_div_sqrt_mvp / dgrid style).
module s10_repl (
  input  logic [10:0] m,
  output logic [13:0] y,
  output logic [2:0]  z
);
  assign y = {m, {3{1'b0}}};
  assign z = m[8 -: 3];
endmodule
