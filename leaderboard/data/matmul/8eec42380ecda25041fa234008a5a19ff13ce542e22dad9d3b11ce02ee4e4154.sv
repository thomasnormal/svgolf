// One level of Strassen's scheme: seven block products in place of eight.
//
// The matrices are split into 2 x 2 blocks of size H = ceil(N/2). Block (p, q) of A is A_pq, entry (u, w) of
// it is A[p*H + u][q*H + w]; likewise B. With the zero padding of odd N (below), Strassen's identities give
//   M1 = (A11 + A22)(B11 + B22)   M2 = (A21 + A22) B11       M3 = A11 (B12 - B22)     M4 = A22 (B21 - B11)
//   M5 = (A11 + A12) B22          M6 = (A21 - A11)(B11 + B12) M7 = (A12 - A22)(B21 + B22)
//   C11 = M1 + M4 - M5 + M7   C12 = M3 + M5   C21 = M2 + M4   C22 = M1 - M2 + M3 + M6.
// They hold in every ring (no commutativity is used), here the integers mod 2^AccW.
//
// Datapath:
// * a_sh, b_sh: A and B captured on start (zero-extended) and shifted one column of A (one entry) and one row
//   of B (N entries) per step, so that at step w every select is static: entry u*N + c of a_sh is A[u][c + w],
//   entry k*N + j of b_sh is B[k + w][j], and an index past the matrix reads 0.
// * The pre-sums (10 block additions, one column of the S blocks and one row of the T blocks per step):
//   S[(u*7 + r)*WS +: WS] holds column w of S_{r+1} at row u, T[(v*7 + r)*WS +: WS] row w of T_{r+1} at column v,
//   where S1..S7 = A11 + A22, A21 + A22, A11, A22, A11 + A12, A21 - A11, A12 - A22 and
//   T1..T7 = B11 + B22, B11, B12 - B22, B21 - B11, B22, B11 + B12, B21 + B22. Every operand is the sum of at most
//   two block entries, exact in WS = W + 1 bits: here each W-bit entry is sign-extended by one bit.
// * Seven identical block-product engines, each H x H multiply-accumulate cells (generate loop r = 0 .. 6):
//   cell (u, v) of engine r, M[((u*H + v)*7 + r)*AccW +: AccW], adds S_{r+1}[u][w] * T_{r+1}[w][v], both
//   operands sign-extended from WS to AccW + WS bits; the sum wraps at AccW bits. No eighth product exists.
// * The post-sums (8 block additions) write C once, block by block, at the last step.
// Odd N: the blocks are those of the matrices padded to 2H. The shared index k = N of the padding meets row N
// of B, which reads 0 (past B), so it adds nothing; the padded row and column of the result are computed and
// dropped (C has no entry for them).
//
// Schedule: start loads a_sh, b_sh (t = 0); edge t = 0 .. H-1 loads the pre-sums of column t; edge t clears
// (t = 0) or accumulates column t-1 (t = 1 .. H) into the engines; edge t = H + 1 writes C and raises done.
// done shows H + 2 snapshots after the start's (4 at N = 4).
//
// Flip-flops only: every register is written by nonblocking assignments in an always_ff, at a static window.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  localparam int H  = (N + 1) / 2;    // the block size
  localparam int L  = (2*H + 1) * N;  // entries of the operand shift registers
  localparam int WS = W + 1;          // the width of a pre-sum

  logic [31:0]           t;
  logic                  busy;
  logic [L*W-1:0]        a_sh, b_sh;
  logic [7*H*WS-1:0]     S, T;
  logic [7*H*H*AccW-1:0] M;

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      t    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      t    <= 32'd0;
      a_sh <= A;
      b_sh <= B;
    end else if (busy) begin
      t    <= t + 32'd1;
      a_sh <= a_sh >> W;
      b_sh <= b_sh >> (N*W);
      if (t == H + 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  // The A-side pre-sums of row u: A11 at entry u*N, A12 at u*N + H, A21 at (H+u)*N, A22 at (H+u)*N + H.
  for (genvar u = 0; u < H; u++) begin : g_sa
    always_ff @(posedge clk)
      if (busy) begin
        S[(u*7 + 0)*WS +: WS] <= {a_sh[(u*N)*W + W-1], a_sh[(u*N)*W +: W]}
                               + {a_sh[((H+u)*N + H)*W + W-1], a_sh[((H+u)*N + H)*W +: W]};   // S1 = A11 + A22
        S[(u*7 + 1)*WS +: WS] <= {a_sh[((H+u)*N)*W + W-1], a_sh[((H+u)*N)*W +: W]}
                               + {a_sh[((H+u)*N + H)*W + W-1], a_sh[((H+u)*N + H)*W +: W]};   // S2 = A21 + A22
        S[(u*7 + 2)*WS +: WS] <= {a_sh[(u*N)*W + W-1], a_sh[(u*N)*W +: W]};                   // S3 = A11
        S[(u*7 + 3)*WS +: WS] <= {a_sh[((H+u)*N + H)*W + W-1], a_sh[((H+u)*N + H)*W +: W]};   // S4 = A22
        S[(u*7 + 4)*WS +: WS] <= {a_sh[(u*N)*W + W-1], a_sh[(u*N)*W +: W]}
                               + {a_sh[(u*N + H)*W + W-1], a_sh[(u*N + H)*W +: W]};           // S5 = A11 + A12
        S[(u*7 + 5)*WS +: WS] <= {a_sh[((H+u)*N)*W + W-1], a_sh[((H+u)*N)*W +: W]}
                               - {a_sh[(u*N)*W + W-1], a_sh[(u*N)*W +: W]};                   // S6 = A21 - A11
        S[(u*7 + 6)*WS +: WS] <= {a_sh[(u*N + H)*W + W-1], a_sh[(u*N + H)*W +: W]}
                               - {a_sh[((H+u)*N + H)*W + W-1], a_sh[((H+u)*N + H)*W +: W]};   // S7 = A12 - A22
      end
  end

  // The B-side pre-sums of column v: B11 at entry v, B12 at H + v, B21 at H*N + v, B22 at H*N + H + v.
  for (genvar v = 0; v < H; v++) begin : g_tb
    always_ff @(posedge clk)
      if (busy) begin
        T[(v*7 + 0)*WS +: WS] <= {b_sh[v*W + W-1], b_sh[v*W +: W]}
                               + {b_sh[(H*N + H + v)*W + W-1], b_sh[(H*N + H + v)*W +: W]};   // T1 = B11 + B22
        T[(v*7 + 1)*WS +: WS] <= {b_sh[v*W + W-1], b_sh[v*W +: W]};                           // T2 = B11
        T[(v*7 + 2)*WS +: WS] <= {b_sh[(H + v)*W + W-1], b_sh[(H + v)*W +: W]}
                               - {b_sh[(H*N + H + v)*W + W-1], b_sh[(H*N + H + v)*W +: W]};   // T3 = B12 - B22
        T[(v*7 + 3)*WS +: WS] <= {b_sh[(H*N + v)*W + W-1], b_sh[(H*N + v)*W +: W]}
                               - {b_sh[v*W + W-1], b_sh[v*W +: W]};                           // T4 = B21 - B11
        T[(v*7 + 4)*WS +: WS] <= {b_sh[(H*N + H + v)*W + W-1], b_sh[(H*N + H + v)*W +: W]};   // T5 = B22
        T[(v*7 + 5)*WS +: WS] <= {b_sh[v*W + W-1], b_sh[v*W +: W]}
                               + {b_sh[(H + v)*W + W-1], b_sh[(H + v)*W +: W]};               // T6 = B11 + B12
        T[(v*7 + 6)*WS +: WS] <= {b_sh[(H*N + v)*W + W-1], b_sh[(H*N + v)*W +: W]}
                               + {b_sh[(H*N + H + v)*W + W-1], b_sh[(H*N + H + v)*W +: W]};   // T7 = B21 + B22
      end
  end

  // The seven engines: cell (u, v) of engine r multiplies S_{r+1}[u][w] by T_{r+1}[w][v] and accumulates.
  for (genvar u = 0; u < H; u++) begin : g_mu
    for (genvar v = 0; v < H; v++) begin : g_mv
      for (genvar r = 0; r < 7; r++) begin : g_mr
        always_ff @(posedge clk)
          if (busy)
            if (t == 0)
              M[((u*H + v)*7 + r)*AccW +: AccW] <= '0;
            else
              M[((u*H + v)*7 + r)*AccW +: AccW] <= M[((u*H + v)*7 + r)*AccW +: AccW]
                  + {{AccW{S[(u*7 + r)*WS + W]}}, S[(u*7 + r)*WS +: WS]}
                  * {{AccW{T[(v*7 + r)*WS + W]}}, T[(v*7 + r)*WS +: WS]};
      end
    end
  end

  // The post-sums, one family per block of C, grouped by block row so that C is written row by row (rows and
  // columns of a block past N - 1 do not exist).
  for (genvar u = 0; u < H; u++) begin : g_ct
    for (genvar v = 0; v < H; v++) begin : g_c11
      always_ff @(posedge clk)
        if (busy)
          if (t == H + 1)   // C11 = M1 + M4 - M5 + M7
            C[(u*N + v)*AccW +: AccW] <= M[((u*H + v)*7 + 0)*AccW +: AccW] + M[((u*H + v)*7 + 3)*AccW +: AccW]
                                       - M[((u*H + v)*7 + 4)*AccW +: AccW] + M[((u*H + v)*7 + 6)*AccW +: AccW];
    end
    for (genvar v = 0; v < N - H; v++) begin : g_c12
      always_ff @(posedge clk)
        if (busy)
          if (t == H + 1)   // C12 = M3 + M5
            C[(u*N + H + v)*AccW +: AccW] <= M[((u*H + v)*7 + 2)*AccW +: AccW] + M[((u*H + v)*7 + 4)*AccW +: AccW];
    end
  end
  for (genvar u = 0; u < N - H; u++) begin : g_cb
    for (genvar v = 0; v < H; v++) begin : g_c21
      always_ff @(posedge clk)
        if (busy)
          if (t == H + 1)   // C21 = M2 + M4
            C[((H + u)*N + v)*AccW +: AccW] <= M[((u*H + v)*7 + 1)*AccW +: AccW] + M[((u*H + v)*7 + 3)*AccW +: AccW];
    end
    for (genvar v = 0; v < N - H; v++) begin : g_c22
      always_ff @(posedge clk)
        if (busy)
          if (t == H + 1)   // C22 = M1 - M2 + M3 + M6
            C[((H + u)*N + H + v)*AccW +: AccW] <= M[((u*H + v)*7 + 0)*AccW +: AccW] - M[((u*H + v)*7 + 1)*AccW +: AccW]
                                                 + M[((u*H + v)*7 + 2)*AccW +: AccW] + M[((u*H + v)*7 + 5)*AccW +: AccW];
    end
  end
endmodule
