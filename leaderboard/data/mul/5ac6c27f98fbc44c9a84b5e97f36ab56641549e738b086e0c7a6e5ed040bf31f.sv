// svGolf task `mul`: two-row-leaf 4:2 compressor heap multiplier with a hybrid ripple + sparse-5
// Kogge-Stone upper final adder, parametric in N >= 1.
// The partial-product gather arrays and 4:2 compressor binary heap (S, C, X, Y) are from record 7d6d9bd9da7a
// (late-carry, derived from tasks/mul/reference/mul_tree_h.sv). The 2N-bit ripple final adder is replaced by:
//   - low M = (3*N)/4 bits: late-carry ripple adder R[0..M];
//   - upper U = 2*N - M bits: FQ = (U - 1)/5 blocks of 5 bits with block (G, P), an L = $clog2(FQ + 1)
//     Kogge-Stone block-carry prefix tree, late-carry local ripple inside each block, and a non-empty
//     late-carry ripple tail of FR = U - 5*FQ bits.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  localparam integer H = (N + 1) / 2;   // leaves: ceil(N/2) pairs of partial-product rows

  logic [4*N-2:0]          ae;   // ae[x] = a[x-(2N-1)] for 2N-1 <= x < 3N-1, else 0
  logic [2*H:0]            bb;   // b zero-extended
  logic [2*H-2:0][2*N-1:0] S, C; // sum / carry row of each heap node
  logic [H-1:0][2*N-1:0]   X, Y; // first-row sum / carry of node k (row H-1 unused)
  localparam integer M = (3*N)/4;
  localparam integer U = 2*N - M;
  localparam integer FQ = (U - 1) / 5;
  localparam integer FR = U - 5 * FQ;
  localparam integer FL = $clog2(FQ + 1);
  logic [M:0] R;
  logic [U-1:0] fp, fg;
  logic [FQ:0][5:0] fgg, fpp, fcc;
  logic [FL:0][FQ:0] bg, bp;
  logic [FR:0] Rt;

  assign ae[2*N-2:0]     = '0;
  assign ae[3*N-2:2*N-1] = a;
  assign ae[4*N-2:3*N-1] = '0;
  assign bb[N-1:0]       = b;
  assign bb[2*H:N]       = '0;
  assign X[H-1]          = '0;
  assign Y[H-1]          = '0;
  assign R[0] = 1'b0;
  assign bg[0][0] = R[M];
  assign bp[0][0] = 1'b0;
  assign fgg[FQ] = '0;
  assign fpp[FQ] = '0;
  assign fcc[FQ] = '0;
  assign Rt[0] = bg[FL][FQ];

  genvar j, k, c, t, fl;
  generate
    // leaves: node H-1+j is the pair of partial-product rows 2j and 2j+1 (gather reads of ae)
    for (j = 0; j < H; j++) begin : g_leaf
      for (c = 0; c < 2*N; c++) begin : g_lc
        assign S[H-1+j][c] = bb[2*j] & ae[c + 2*N - 1 - 2*j];
        assign C[H-1+j][c] = ae[c + 2*N - 2 - 2*j] & bb[2*j+1];
      end
    end
    // internal nodes: a 4:2 compressor on the children 2k+1, 2k+2
    for (k = 0; k < H-1; k++) begin : g_node
      assign Y[k][0] = 1'b0;
      assign C[k][0] = 1'b0;
      for (c = 0; c < 2*N; c++) begin : g_col
        assign X[k][c] = (S[2*k+2][c] ^ C[2*k+1][c]) ^ S[2*k+1][c];
        assign S[k][c] = (X[k][c] ^ C[2*k+2][c]) ^ Y[k][c];
      end
      for (c = 0; c < 2*N-1; c++) begin : g_car
        assign Y[k][c+1] = (S[2*k+2][c] ^ C[2*k+1][c]) ? S[2*k+1][c] : C[2*k+1][c];
        assign C[k][c+1] = (Y[k][c] ^ C[2*k+2][c]) ? X[k][c] : C[2*k+2][c];
      end
    end
    for (c = 0; c < M; c++) begin : g_fin_lo
      assign p[c]   = S[0][c] ^ (C[0][c] ^ R[c]);
      assign R[c+1] = (C[0][c] ^ S[0][c]) ? R[c] : S[0][c];
    end
    for (c = 0; c < U; c++) begin : g_fpg
      assign fp[c] = S[0][M+c] ^ C[0][M+c];
      assign fg[c] = S[0][M+c] & C[0][M+c];
    end
    for (j = 0; j < FQ; j++) begin : g_fblk
      assign fgg[j][0] = 1'b0;
      assign fpp[j][0] = 1'b1;
      for (t = 0; t < 5; t++) begin : g_frip
        assign fgg[j][t+1] = fg[5*j+t] | (fp[5*j+t] & fgg[j][t]);
        assign fpp[j][t+1] = fp[5*j+t] & fpp[j][t];
      end
      assign bg[0][j+1] = fgg[j][5];
      assign bp[0][j+1] = fpp[j][5];
    end
    for (fl = 0; fl < FL; fl++) begin : g_flvl
      for (j = 0; j < FQ + 1; j++) begin : g_fnd
        if (j >= (1 << fl)) begin : g_fop
          assign bg[fl+1][j] = bg[fl][j] | (bp[fl][j] & bg[fl][j - (1 << fl)]);
          assign bp[fl+1][j] = bp[fl][j] & bp[fl][j - (1 << fl)];
        end else begin : g_fpass
          assign bg[fl+1][j] = bg[fl][j];
          assign bp[fl+1][j] = bp[fl][j];
        end
      end
    end
    for (j = 0; j < FQ; j++) begin : g_floc
      assign fcc[j][0] = bg[FL][j];
      for (t = 0; t < 5; t++) begin : g_flc
        assign fcc[j][t+1] = fp[5*j+t] ? fcc[j][t] : S[0][M+5*j+t];
        assign p[M+5*j+t] = S[0][M+5*j+t] ^ (C[0][M+5*j+t] ^ fcc[j][t]);
      end
    end
    for (t = 0; t < FR; t++) begin : g_ftail
      assign Rt[t+1]       = fp[5*FQ+t] ? Rt[t] : S[0][M+5*FQ+t];
      assign p[M+5*FQ+t] = S[0][M+5*FQ+t] ^ (C[0][M+5*FQ+t] ^ Rt[t]);
    end
  endgenerate
endmodule
