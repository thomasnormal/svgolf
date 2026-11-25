// svGolf task `clmul`: transposed row-wise balanced XOR tape over N shifted partial-product rows.
// Builds on record 3aa7a23ffc4a's balanced XOR tape by orienting T as rows x columns and driving
// each internal tape node as a whole-vector XOR T[N+g] = T[2*g] ^ T[2*g+1]. Parametric in N >= 1.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [3*N-1:0]          be;
  logic [2*N-2:0][2*N-2:0] T;
  assign be[N-1:0]     = '0;
  assign be[2*N-1:N]   = b;
  assign be[3*N-1:2*N] = '0;
  genvar k, t, g;
  generate
    for (t = 0; t < N; t++) begin : g_row
      for (k = 0; k < 2*N-1; k++) begin : g_col
        assign T[t][k] = a[t] & be[k - t + N];
      end
    end
    for (g = 0; g < N-1; g++) begin : g_node
      assign T[N+g] = T[2*g] ^ T[2*g+1];
    end
    assign p = T[2*N-2];
  endgenerate
endmodule
