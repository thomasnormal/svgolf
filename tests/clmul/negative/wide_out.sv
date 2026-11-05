// NEGATIVE: interface. p is 2N bits wide with a constant-zero top bit (the product is right, the port is not
// the task's 2N-1 bits; refuted by the interface conjunct at every N).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N-1:0][N-1:0] r;

  assign p[2*N-1] = 1'b0;
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
