// STYLE: a column temporary declared inside a generate block, with a conditional generate for the diagonal and a
// reduction XOR per column (a hand-written "column" form of the carry-less product).
// Correct for every N. ls-sv refuses the generate-local declaration `t` (and the conditional generate inside a
// generate-for is outside the tactics' fragment as well).
// procedural-for-free but compound-op: generate-for with += style XOR on a 2-D accumulator
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N-1:0][N-1:0] pp;
  genvar i, j;
  generate
    for (i = 0; i < N; i++) begin : g_i
      for (j = 0; j < N; j++) begin : g_j
        assign pp[i][j] = a[i] & b[j];
      end
    end
    for (i = 0; i < 2*N-1; i++) begin : g_col
      logic [N-1:0] t;
      for (j = 0; j < N; j++) begin : g_t
        if (i - j >= 0 && i - j < N) begin : g_in
          assign t[j] = pp[j][i-j];
        end else begin : g_out
          assign t[j] = 1'b0;
        end
      end
      assign p[i] = ^t;
    end
  endgenerate
endmodule
