// An undriven net in a decision: ls-sv (and IEEE) read `u` as x, so t is x and
// the if takes its else branch (a & b); Yosys's `-undriven` makes u a
// don't-care and resolves the mux to t = 1 (a | b), measured with Yosys 0.53.
module undriven_mux #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic u, t;
  assign t = u ? 1'b0 : 1'b1;
  always_comb if (t) y = a | b; else y = a & b;
endmodule
