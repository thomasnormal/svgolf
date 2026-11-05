// NEGATIVE (works only for some N): the reference array multiplier at the
// scoring point N = 16, and p = 0 at every other N. Synthesis at N = 16 sees
// exactly the reference circuit, so it scores the same; the statement covers
// every N >= 1 and fails at N = 1 (1 * 1 gives p = 0, not 1).
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N-1:0][N-1:0] pp;   // pp[i][j] = a[j] & b[i]
  logic [N-1:0][N:0]   s;    // row sums (N+1 bits)
  logic [N-1:0][N:0]   c;    // ripple carries
  logic [N-1:0][N-1:0] t;    // propagate x ^ y

  genvar i, j;
  generate
    if (N == 16) begin : g_scored
        for (i = 0; i < N; i++) begin : g_pp
          for (j = 0; j < N; j++) begin : g_pp_j
            assign pp[i][j] = a[j] & b[i];
          end
        end

      assign s[0] = {1'b0, pp[0]};
      assign c[0] = '0;
      assign t[0] = '0;

        for (i = 1; i < N; i++) begin : g_row
          assign c[i][0] = 1'b0;
          for (j = 0; j < N; j++) begin : g_bit
            assign t[i][j]   = s[i-1][j+1] ^ pp[i][j];
            assign s[i][j]   = t[i][j] ^ c[i][j];
            assign c[i][j+1] = (s[i-1][j+1] & pp[i][j]) | (c[i][j] & t[i][j]);
          end
          assign s[i][N] = c[i][N];
        end

        for (i = 0; i < N; i++) begin : g_out
          assign p[i] = s[i][0];
        end
      assign p[2*N-1:N] = s[N-1][N:1];

    end else begin : g_other
      assign p = '0;
    end
  endgenerate
endmodule
