// tests/cycle: a nonblocking write to a dynamic index (sv_mirror refuses it by name: not a static window).
module dynidx #(parameter int N = 4) (
  input  logic         clk,
  input  logic [1:0]   sel,
  input  logic         d,
  output logic [N-1:0] q
);
  always_ff @(posedge clk) q[sel] <= d;
endmodule
