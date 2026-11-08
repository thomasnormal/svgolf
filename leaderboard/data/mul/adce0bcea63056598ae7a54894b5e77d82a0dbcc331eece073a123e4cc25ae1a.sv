// A radix-4 (modified) Booth multiplier, unsigned, N x N -> 2N, parametric in N.
//
// Recoding: bb = {0..., b, 1'b0} (bb[0] = b[-1] = 0). Digit k (k = 0 .. K-1, K = (N+3)/2) is
// d_k = -2 bb[2k+2] + bb[2k+1] + bb[2k] in {-2..2}, and b = sum_k d_k 4^k (the top digit is >= 0).
// Encoder: one = bb[2k+1] ^ bb[2k], two = the 011/100 patterns, sign s_k = ng[k+1] = bb[2k+2].
// Row k of the tape: the magnitude |d_k| * a (one ? a : two ? 2a : 0, N+1 bits) XORed with s_k at
// columns 2k .. 2k+N, then the sign-extension constants (row 0: s, s, ~s at N+1 .. N+3; row k >= 1:
// ~s at 2k+N+1 and a constant 1 at 2k+N+2; their sum is 2^(2K+N+1), which is 0 mod 2^(2N)), and the
// "+1" of row k-1's two's complement, s_{k-1}, at column 2k-2 (row k's zero region). Everything is
// mod 2^(2N). Rows 0 .. K-1 are reduced by a carry-save tape (adder g reads rows 3g, 3g+1, 3g+2 and
// appends its sum and carry rows at K+2g and K+1+2g); a 2N-bit ripple adder adds the last two rows.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  localparam integer K = (N + 3) / 2;          // number of Booth digits (rows)
  localparam integer P = 2 * N + 4;            // pad offset of the gather arrays

  logic [2*K:0]            bb;                 // {0, b, 0}
  logic [K-1:0]            one, two;           // digit k: |d| = 1, |d| = 2
  logic [K:0]              ng;                 // ng[k+1] = sign of digit k, ng[0] = 0
  logic [4*N+5:0]          ae;                 // ae[x] = a[x-P] for P <= x < P+N, else 0
  logic [4*N+5:0]          wm;                 // wm[x] = (P <= x <= P+N)
  logic [4*N+5:0]          pt;                 // pt[x] = (x == P)
  logic [3*K-5:0][2*N-1:0] T;                  // the tape
  logic [2*N:0]            C;                  // final-adder carries

  assign bb[0]         = 1'b0;
  assign bb[N:1]       = b;
  assign bb[2*K:N+1]   = '0;
  assign ae[P-1:0]     = '0;
  assign ae[P+N-1:P]   = a;
  assign ae[4*N+5:P+N] = '0;
  assign wm[P-1:0]     = '0;
  assign wm[P+N:P]     = '1;
  assign wm[4*N+5:P+N+1] = '0;
  assign pt[P-1:0]     = '0;
  assign pt[P]         = 1'b1;
  assign pt[4*N+5:P+1] = '0;
  assign ng[0]         = 1'b0;
  assign C[0]          = 1'b0;

  genvar k, c, g;
  generate
    for (k = 0; k < K; k++) begin : g_enc
      assign one[k]  = bb[2*k+1] ^ bb[2*k];
      assign two[k]  = (bb[2*k+2] & ~bb[2*k+1] & ~bb[2*k]) | (~bb[2*k+2] & bb[2*k+1] & bb[2*k]);
      assign ng[k+1] = bb[2*k+2];
    end
    for (c = 0; c < 2*N; c++) begin : g_r0
      assign T[0][c] = (((one[0] & ae[c+P]) | (two[0] & ae[c+P-1])) ^ (ng[1] & wm[c+P]))
                       | (ng[1] & pt[c+P-N-1]) | (ng[1] & pt[c+P-N-2]) | (~ng[1] & pt[c+P-N-3]);
    end
    for (k = 1; k < K; k++) begin : g_row
      for (c = 0; c < 2*N; c++) begin : g_rc
        assign T[k][c] = (((one[k] & ae[c+P-2*k]) | (two[k] & ae[c+P-1-2*k])) ^ (ng[k+1] & wm[c+P-2*k]))
                         | (~ng[k+1] & pt[c+P-N-1-2*k]) | pt[c+P-N-2-2*k] | (ng[k] & pt[c+P+2-2*k]);
      end
    end
    for (g = 0; g < K-2; g++) begin : g_csa
      assign T[K+1+2*g][0] = 1'b0;
      for (c = 0; c < 2*N; c++) begin : g_sum
        assign T[K+2*g][c] = T[3*g][c] ^ T[3*g+1][c] ^ T[3*g+2][c];
      end
      for (c = 0; c < 2*N-1; c++) begin : g_car
        assign T[K+1+2*g][c+1] = (T[3*g][c] & T[3*g+1][c]) | (T[3*g+2][c] & (T[3*g][c] ^ T[3*g+1][c]));
      end
    end
    for (c = 0; c < 2*N; c++) begin : g_fin
      assign p[c]   = T[3*K-6][c] ^ T[3*K-5][c] ^ C[c];
      assign C[c+1] = (T[3*K-6][c] & T[3*K-5][c]) | (C[c] & (T[3*K-6][c] ^ T[3*K-5][c]));
    end
  endgenerate
endmodule
