// svGolf task `add`, a design proved for every N (add_n_kogge_stone.lean
// beside it): a Kogge-Stone parallel-prefix adder, built from gates in generate
// loops. Positions 0..N: position 0 carries cin (generate = cin,
// propagate = 0), position k+1 is bit k. Level l combines every position
// k >= 2^l with position k - 2^l, so after L = $clog2(N+1) levels g[L][k] is
// the carry INTO bit k. All index arithmetic is over genvars and parameters
// (elaboration time).
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int L = $clog2(N + 1);
  logic [L:0][N:0] g, p;
  logic [N-1:0] x;
  assign g[0][0] = cin;
  assign p[0][0] = 1'b0;
  genvar i, l;
  generate
    for (i = 0; i < N; i++) begin : g_in
      assign x[i]       = a[i] ^ b[i];
      assign g[0][i+1]  = a[i] & b[i];
      assign p[0][i+1]  = a[i] ^ b[i];
    end
    for (l = 0; l < L; l++) begin : g_lvl
      for (i = 0; i < N + 1; i++) begin : g_node
        if (i >= (1 << l)) begin : g_op
          assign g[l+1][i] = g[l][i] | (p[l][i] & g[l][i - (1 << l)]);
          assign p[l+1][i] = p[l][i] & p[l][i - (1 << l)];
        end else begin : g_pass
          assign g[l+1][i] = g[l][i];
          assign p[l+1][i] = p[l][i];
        end
      end
    end
    for (i = 0; i < N; i++) begin : g_sum
      assign s[i] = x[i] ^ g[L][i];
    end
  endgenerate
  assign cout = g[L][N];
endmodule
