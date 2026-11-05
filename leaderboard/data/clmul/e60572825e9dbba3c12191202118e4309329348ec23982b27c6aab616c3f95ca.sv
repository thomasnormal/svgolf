// svGolf task `clmul` -- reference solution: an N x N -> 2N-1 carry-less (GF(2)[x]) array multiplier.
//
// The product polynomial p = a (x) b has coefficients p_k = XOR over i + j = k of (a_i AND b_j).
// The array is `mul_n`'s with XOR where `mul_n` has a full adder, and no carries: row i (0 <= i < N)
// holds r[i][j] = XOR over t <= i of a[t] & b[i + j - t] (a term whose b index is >= N is 0), the
// accumulator of the first i + 1 rows shifted down by i, so
//   r[0][j]   = a[0] & b[j]
//   r[i][j]   = r[i-1][j+1] ^ (a[i] & b[j])   for 1 <= i < N and 0 <= j < N-1
//   r[i][N-1] = a[i] & b[N-1]                 for 1 <= i < N  (nothing above it in row i-1)
// Output bit i < N is bit 0 of row i (p_i = r[i][0]); the top N-1 bits are the upper N-1 bits of the
// last row (p_{N+m} = r[N-1][m+1], 0 <= m < N-1; no iteration at N = 1).
// Bitwise operators only; genvar loops step with `++` (ls-sv's tier).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N-1:0][N-1:0] r;

  genvar i, j, m;
  generate
    for (j = 0; j < N; j++) begin : g_row0
      assign r[0][j] = a[0] & b[j];
    end
    for (i = 1; i < N; i++) begin : g_row
      for (j = 0; j < N-1; j++) begin : g_bit
        assign r[i][j] = r[i-1][j+1] ^ (a[i] & b[j]);
      end
      assign r[i][N-1] = a[i] & b[N-1];
    end
    for (i = 0; i < N; i++) begin : g_lo
      assign p[i] = r[i][0];
    end
    for (m = 0; m < N-1; m++) begin : g_hi
      assign p[N+m] = r[N-1][m+1];
    end
  endgenerate
endmodule
