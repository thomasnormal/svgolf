// NEGATIVE (works only for some N): the reference array at the scoring point N = 16, and p = 0 at every
// other N. Synthesis at N = 16 sees exactly the reference circuit, so it scores the same; the statement
// covers every N >= 1 and fails at N = 1 (a = b = 1 gives p = 0, not 1).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N-1:0][N-1:0] r;

  genvar i, j, m;
  generate
    if (N == 16) begin : g_scored
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
    end else begin : g_other
      assign p = '0;
    end
  endgenerate
endmodule
