// Carry-less multiplier, schoolbook form with a balanced XOR tree per output column, parametric in N.
//
// One 2-D packed array T of 2N-1 columns by 2N-1 positions, a TAPE per output column k.
// Positions 0 .. N-1 of column k are its partial products, zero-padded to N leaves, in the order of
// the index of a (ascending); XOR node g (g = 0 .. N-2) of a column reads positions 2g and 2g+1 and
// writes position N+g, so the root is position 2N-2 (heap order; a perfect tree when N is a power of 2).
//   lower columns k < N:     T[k][i]    = a[i] & be[k - i + N]    (be = {b, N zero bits})
//   upper columns N + k:     T[N+k][t]  = ae[t + k + 1] & b[N-1-t] (ae = {N zero bits, a})
//   every column, node g:    T[k][N+g]  = T[k][2g] ^ T[k][2g+1]
//   output:                  p[k]       = T[k][2N-2]
// The padded leaves are constant zeros, folded by synthesis. Bitwise operators only.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [2*N-1:0]          ae, be;
  logic [2*N-2:0][2*N-2:0] T;

  assign ae[N-1:0]   = a;
  assign ae[2*N-1:N] = '0;
  assign be[N-1:0]   = '0;
  assign be[2*N-1:N] = b;

  genvar k, t, g;
  generate
    for (k = 0; k < N; k++) begin : g_lo
      for (t = 0; t < N; t++) begin : g_ll
        assign T[k][t] = a[t] & be[k - t + N];
      end
    end
    for (k = 0; k < N-1; k++) begin : g_hi
      for (t = 0; t < N; t++) begin : g_hl
        assign T[N+k][t] = ae[t + k + 1] & b[N-1-t];
      end
    end
    for (k = 0; k < 2*N-1; k++) begin : g_col
      for (g = 0; g < N-1; g++) begin : g_node
        assign T[k][N+g] = T[k][2*g] ^ T[k][2*g+1];
      end
      assign p[k] = T[k][2*N-2];
    end
  endgenerate
endmodule
