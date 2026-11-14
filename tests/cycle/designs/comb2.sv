// tests/cycle: two continuous assignments beside a register (sv_mirror refuses the second comb process by name:
// the settle of several comb processes in every schedule order is not proved yet).
module comb2 #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t, u;
  assign t = a | b;
  assign u = t & a;
  always_ff @(posedge clk) q <= u;
endmodule
