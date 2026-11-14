// tests/cycle: a plain edge-triggered always (sv_mirror refuses it by name: only always_ff is covered).
module plain #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  always @(posedge clk) q <= a;
endmodule
