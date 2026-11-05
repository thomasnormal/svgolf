// svGolf task `mul` -- reference solution 4: a WALLACE-TREE multiplier (tape of rows, 3:2 carry-save
// adder rows), parametric in N.
//
// The tape T is one 2-D packed array of 3N-1 rows of 2N bits. Rows 0 .. N-1 are the N partial
// products (row j = (a & {N{b[j]}}) << j) and row N is an all-zero dummy row, so N+1 rows are live
// at the start. Carry-save adder number g (g = 0 .. N-2) reads the three OLDEST live rows 3g, 3g+1,
// 3g+2 and APPENDS two rows: the sum row x ^ y ^ z at position N+1+2g and the carry row
// maj(x, y, z) << 1 at position N+2+2g. Each adder consumes three live rows and appends two, so after
// the N-1 adders exactly two rows remain, at positions 3N-3 and 3N-2: that is Wallace's reduction
// in its queue form (group the rows by threes, replace each group by its sum and carry row; the
// number of live rows shrinks by a factor 2/3 per level, so there are about log_{3/2}(N) levels).
// A 2N-bit ripple-carry adder adds the last two rows. Every sum is taken modulo 2^(2N), exactly
// the width of the product, so every carry out of bit 2N-1 is dropped without an argument.
//
// There is no localparam, no division, no conditional generate and no stage counter: every index is
// affine in N and the genvars (reads at 3*g+k, writes at N+1+2*g and N+2+2*g). A shifted partial
// product is a GATHER read of `ae`, the zero-padded copy of `a`, so no write leaves its vector.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [4*N-2:0]          ae;   // ae[x] = a[x-(2N-1)] for 2N-1 <= x < 3N-1, else 0
  logic [3*N-2:0][2*N-1:0] T;    // the tape of rows
  logic [2*N:0]            K;    // final-adder carries

  assign ae[2*N-2:0]       = '0;
  assign ae[3*N-2:2*N-1]   = a;
  assign ae[4*N-2:3*N-1]   = '0;
  assign T[N]              = '0;
  assign K[0]              = 1'b0;

  genvar j, g, c;
  generate
    // the N partial products: row j is a, shifted left by j and gated by b[j] (a gather read of ae)
    for (j = 0; j < N; j++) begin : g_leaf
      for (c = 0; c < 2*N; c++) begin : g_lc
        assign T[j][c] = ae[c + 2*N - 1 - j] & b[j];
      end
    end
    // carry-save adder g: rows 3g, 3g+1, 3g+2 in, rows N+1+2g (sum) and N+2+2g (carry) appended
    for (g = 0; g < N-1; g++) begin : g_csa
      assign T[N+2+2*g][0] = 1'b0;
      for (c = 0; c < 2*N; c++) begin : g_sum
        assign T[N+1+2*g][c] = T[3*g][c] ^ T[3*g+1][c] ^ T[3*g+2][c];
      end
      for (c = 0; c < 2*N-1; c++) begin : g_car
        assign T[N+2+2*g][c+1] = (T[3*g][c] & T[3*g+1][c]) | (T[3*g+2][c] & (T[3*g][c] ^ T[3*g+1][c]));
      end
    end
    // final carry-propagate (ripple) adder of the last two rows, positions 3N-3 and 3N-2
    for (c = 0; c < 2*N; c++) begin : g_fin
      assign p[c]   = T[3*N-3][c] ^ T[3*N-2][c] ^ K[c];
      assign K[c+1] = (T[3*N-3][c] & T[3*N-2][c]) | (K[c] & (T[3*N-3][c] ^ T[3*N-2][c]));
    end
  endgenerate
endmodule
