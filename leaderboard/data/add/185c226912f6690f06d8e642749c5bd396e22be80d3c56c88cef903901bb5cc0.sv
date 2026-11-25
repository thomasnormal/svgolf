// svGolf task `add`: padded sparse-6 Kogge-Stone parallel-prefix adder with late-carry local ripple.
// Pads a and b to M = 6 * ceil(N/6) bits, computes 6-bit block (G, P), combines block carries
// with an L = $clog2(Q+1) Kogge-Stone tree, and ripples locally within each block using p ? c : a.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam integer Q = (N + 6 - 1) / 6;
  localparam integer M = 6 * Q;
  localparam integer L = $clog2(Q + 1);
  logic [M:0] ap, bp;
  logic [M-1:0] x, p, g;
  logic [Q-1:0][6:0] gg, pp, cc;
  logic [L:0][Q:0] bg, bp_g;
  logic [M:0] c_all;
  genvar i, j, t, l;
  assign ap[N-1:0]  = a;
  assign bp[N-1:0]  = b;
  assign bg[0][0]   = cin;
  assign bp_g[0][0] = 1'b0;
  assign c_all[M]   = bg[L][Q];
  assign cout       = c_all[N];
  generate
    for (i = N; i < M + 1; i++) begin : g_pad
      assign ap[i] = 1'b0;
      assign bp[i] = 1'b0;
    end
    for (i = 0; i < M; i++) begin : g_pg
      assign x[i] = ap[i] ^ bp[i];
      assign p[i] = ap[i] ^ bp[i];
      assign g[i] = ap[i] & bp[i];
    end
    for (j = 0; j < Q; j++) begin : g_blk
      assign gg[j][0] = 1'b0;
      assign pp[j][0] = 1'b1;
      for (t = 0; t < 6; t++) begin : g_rip
        assign gg[j][t+1] = g[6*j+t] | (p[6*j+t] & gg[j][t]);
        assign pp[j][t+1] = p[6*j+t] & pp[j][t];
      end
      assign bg[0][j+1]   = gg[j][6];
      assign bp_g[0][j+1] = pp[j][6];
    end
    for (l = 0; l < L; l++) begin : g_lvl
      for (j = 0; j < Q + 1; j++) begin : g_node
        if (j >= (1 << l)) begin : g_op
          assign bg[l+1][j] = bg[l][j] | (bp_g[l][j] & bg[l][j - (1 << l)]);
          assign bp_g[l+1][j] = bp_g[l][j] & bp_g[l][j - (1 << l)];
        end else begin : g_pass
          assign bg[l+1][j] = bg[l][j];
          assign bp_g[l+1][j] = bp_g[l][j];
        end
      end
    end
    for (j = 0; j < Q; j++) begin : g_loc
      assign cc[j][0] = bg[L][j];
      for (t = 0; t < 6; t++) begin : g_lc
        assign cc[j][t+1] = x[6*j+t] ? cc[j][t] : ap[6*j+t];
        assign c_all[6*j+t] = cc[j][t];
      end
    end
    for (i = 0; i < N; i++) begin : g_sum
      assign s[i] = x[i] ^ c_all[i];
    end
  endgenerate
endmodule
