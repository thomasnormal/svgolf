// svGolf task `mul` -- a log-depth carry-save TREE multiplier whose leaves each hold TWO
// partial-product rows, parametric in N, written with a LOCALPARAM.
//
// The N partial-product rows pp[j] (the shifted copies of a, gated by the bits of b) are taken two at a time:
// leaf j of H = ceil(N/2) holds the carry-save pair (S, C) = (pp[2j], pp[2j+1]), two rows being already a
// pair. The H leaves are those of one balanced binary tree in a binary-HEAP numbering: the root is node 0,
// node k has the children 2k+1 and 2k+2, the H-1 internal nodes are 0 .. H-2 and the H leaves H-1 .. 2H-2.
// EVERY internal node is a 4:2 compressor on its two children's pairs: two stacked rows of 3:2 counters
// (full adders), the first row X/Y, the second S/C; the two rows of the root go through a ripple-carry
// final adder. There is no pairing node and no constant select: a node never has to be told apart from
// its siblings, which is what the single-row tree (mul_tree.sv) needs th/nth for.
//
// The one non-affine quantity, H = ceil(N/2), is a `localparam integer` defined by a division by a literal:
// the sv_comb tactics read it as one more named constant of N (PROVING.md, section 4), so every index and
// bound stays an integer constant expression and `omega` decides the obligations (H = (N + 1) / 2 is
// known to it). `bb` is `b` zero-extended to 2H+1 bits, so the last leaf of an odd N has a zero row.
// A shifted partial product is a GATHER read of `ae`, the zero-padded copy of `a`, so no write ever
// leaves its vector. All sums are taken modulo 2^(2N), exactly the width of the product.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  localparam integer H = (N + 1) / 2;   // leaves: ceil(N/2) pairs of partial-product rows

  logic [4*N-2:0]          ae;   // ae[x] = a[x-(2N-1)] for 2N-1 <= x < 3N-1, else 0
  logic [2*H:0]            bb;   // b zero-extended
  logic [2*H-2:0][2*N-1:0] S, C; // sum / carry row of each heap node
  logic [H-1:0][2*N-1:0]   X, Y; // first-row sum / carry of node k (row H-1 unused)
  logic [2*N:0]            R;    // final-adder carries

  assign ae[2*N-2:0]     = '0;
  assign ae[3*N-2:2*N-1] = a;
  assign ae[4*N-2:3*N-1] = '0;
  assign bb[N-1:0]       = b;
  assign bb[2*H:N]       = '0;
  assign X[H-1]          = '0;
  assign Y[H-1]          = '0;
  assign R[0]            = 1'b0;

  genvar j, k, c;
  generate
    // leaves: node H-1+j is the pair of partial-product rows 2j and 2j+1 (gather reads of ae)
    for (j = 0; j < H; j++) begin : g_leaf
      for (c = 0; c < 2*N; c++) begin : g_lc
        assign S[H-1+j][c] = ae[c + 2*N - 1 - 2*j] & bb[2*j];
        assign C[H-1+j][c] = ae[c + 2*N - 2 - 2*j] & bb[2*j+1];
      end
    end
    // internal nodes: a 4:2 compressor on the children 2k+1, 2k+2
    for (k = 0; k < H-1; k++) begin : g_node
      assign Y[k][0] = 1'b0;
      assign C[k][0] = 1'b0;
      for (c = 0; c < 2*N; c++) begin : g_col
        assign X[k][c] = S[2*k+1][c] ^ C[2*k+1][c] ^ S[2*k+2][c];
        assign S[k][c] = X[k][c] ^ Y[k][c] ^ C[2*k+2][c];
      end
      for (c = 0; c < 2*N-1; c++) begin : g_car
        assign Y[k][c+1] = (S[2*k+1][c] & C[2*k+1][c]) | (S[2*k+2][c] & (S[2*k+1][c] ^ C[2*k+1][c]));
        assign C[k][c+1] = (X[k][c] & Y[k][c]) | (C[2*k+2][c] & (X[k][c] ^ Y[k][c]));
      end
    end
    // final carry-propagate (ripple) adder of the root's two rows
    for (c = 0; c < 2*N; c++) begin : g_fin
      assign p[c]   = S[0][c] ^ C[0][c] ^ R[c];
      assign R[c+1] = (S[0][c] & C[0][c]) | (R[c] & (S[0][c] ^ C[0][c]));
    end
  endgenerate
endmodule
