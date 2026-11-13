// svGolf task `mul` -- a log-depth carry-save TREE multiplier, parametric in N.
//
// The N partial-product rows pp[j] are the N leaves (a single row each: sum row S = pp[j], carry
// row C = 0) of one balanced binary tree in a binary-HEAP numbering: the root is node 0, node k has
// the children 2k+1 and 2k+2, the N-1 internal nodes are 0 .. N-2 and the N leaves N-1 .. 2N-2.
// An internal node whose children are both leaves (2k+1 >= N-1) just pairs them, S = S[2k+1],
// C = S[2k+2]: two rows are already a carry-save pair. Every other internal node is a 4:2
// compressor on its two children's pairs: two stacked rows of 3:2 counters (full adders), the
// first row X/Y, the second S/C. So the carry-save part has ceil(log2 N) - 1 levels of two full
// adders, and the two rows of the root go through a ripple-carry final adder.
//
// Which nodes pair and which compress is decided by the constant vectors `th` (th[x] = 1 iff
// x >= N-1) and `nth` (its complement), read at the affine index 2k+1: a node-level multiplexer
// whose select is a constant, which synthesis removes. The heap numbering needs no stage counter,
// no localparam, no conditional generate and no division: every index and bound is affine in N and
// the genvars. A shifted partial product is a GATHER read of `ae`, the zero-padded copy of `a`, so no
// write ever leaves its vector. All sums are taken modulo 2^(2N), exactly the width of the product.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [4*N-2:0]          ae;      // ae[x] = a[x-(2N-1)] for 2N-1 <= x < 3N-1, else 0
  logic [2*N-2:0]          th, nth; // th[x] = (x >= N-1), nth = its complement
  logic [2*N-2:0][2*N-1:0] S, C;    // sum / carry row of each heap node
  logic [N-1:0][2*N-1:0]   X, Y;    // first-row sum / carry of node k (row N-1 unused)
  logic [2*N:0]            R;       // final-adder carries

  assign ae[2*N-2:0]       = '0;
  assign ae[3*N-2:2*N-1]   = a;
  assign ae[4*N-2:3*N-1]   = '0;
  assign X[N-1]            = '0;
  assign Y[N-1]            = '0;
  assign R[0]              = 1'b0;

  genvar j, k, c, x;
  generate
    for (x = 0; x < N-1; x++) begin : g_thlo
      assign th[x]  = 1'b0;
      assign nth[x] = 1'b1;
    end
    for (x = 0; x < N; x++) begin : g_thhi
      assign th[N-1+x]  = 1'b1;
      assign nth[N-1+x] = 1'b0;
    end
    // leaves: node N-1+j is the partial-product row j, shifted left by j (a gather read of ae)
    for (j = 0; j < N; j++) begin : g_leaf
      for (c = 0; c < 2*N; c++) begin : g_lc
        assign S[N-1+j][c] = ae[c + 2*N - 1 - j] & b[j];
        assign C[N-1+j][c] = 1'b0;
      end
    end
    // internal nodes: pair two leaves (th), or a 4:2 compressor (nth) on the children 2k+1, 2k+2
    for (k = 0; k < N-1; k++) begin : g_node
      assign Y[k][0] = 1'b0;
      assign C[k][0] = th[2*k+1] & S[2*k+2][0];
      for (c = 0; c < 2*N; c++) begin : g_col
        assign X[k][c] = S[2*k+1][c] ^ C[2*k+1][c] ^ S[2*k+2][c];
        assign S[k][c] = (th[2*k+1] & S[2*k+1][c]) | (nth[2*k+1] & (X[k][c] ^ Y[k][c] ^ C[2*k+2][c]));
      end
      for (c = 0; c < 2*N-1; c++) begin : g_car
        assign Y[k][c+1] = (S[2*k+1][c] & C[2*k+1][c]) | (S[2*k+2][c] & (S[2*k+1][c] ^ C[2*k+1][c]));
        assign C[k][c+1] = (th[2*k+1] & S[2*k+2][c+1])
                         | (nth[2*k+1] & ((X[k][c] & Y[k][c]) | (C[2*k+2][c] & (X[k][c] ^ Y[k][c]))));
      end
    end
    // final carry-propagate (ripple) adder of the root's two rows
    for (c = 0; c < 2*N; c++) begin : g_fin
      assign p[c]   = S[0][c] ^ C[0][c] ^ R[c];
      assign R[c+1] = (S[0][c] & C[0][c]) | (R[c] & (S[0][c] ^ C[0][c]));
    end
  endgenerate
endmodule
