// tests/cycle: an always_comb inside a generate loop (sv_mirror refuses it by name: a family of comb processes).
module combgen #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t;
  for (genvar k = 0; k < N; k++) begin : g_and
    always_comb t[k] = a[k] & b[k];
  end
  always_ff @(posedge clk) q <= t;
endmodule
