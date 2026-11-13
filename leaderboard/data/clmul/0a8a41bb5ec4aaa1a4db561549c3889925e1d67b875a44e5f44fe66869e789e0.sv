// Carry-less multiplier: Karatsuba recursion written level by level, schoolbook base of 4 bits, every N >= 1.
//
// The operands are zero-padded to P = 4 * 2^L bits, L = ceil(log2(N / 4)) (L = 0 for N <= 4). Level l
// (0 <= l <= L) holds 3^l nodes of width W = P >> l. Node t of level l has its operands in
//   av[l][t*W +: W], bv[l][t*W +: W]
// and its product (2W - 1 bits) in rv[l][t*2W +: 2W - 1] (a slot of 2W bits; the slot's top bit is unused).
// Top down: node t of level l < L, with halves of m = W / 2 bits, has three children at level l + 1:
//   3t (the low halves aL, bL), 3t + 1 (the high halves aH, bH), 3t + 2 (aL ^ aH, bL ^ bH).
// Bottom up: a node of the base level L multiplies 4 x 4 bits by schoolbook, each column a balanced XOR
// tree of its partial products by ascending index of a; node t of level l < L combines the products
// L, H, M of its children as  p = L + x^m (M + L + H) + x^2m H,  each column the balanced XOR tree of its
// terms in the order L[k-m], L[k], H[k-2m], H[k-m], M[k-m].
// The output is the low 2N - 1 bits of the product of level 0 (the padding contributes nothing).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  localparam integer L = $clog2((N + 3) / 4);
  localparam integer P = 4 * 2**L;
  localparam integer T = 3**L;
  logic [L:0][4*T-1:0] av, bv;
  logic [L:0][8*T-1:0] rv;

  // level 0: the operands, zero-extended to the width of a row (at least P bits)
  assign av[0] = a;
  assign bv[0] = b;

  genvar l, t;
  generate
    // top down: the operands of the three children of every node
    for (l = 0; l < L; l++) begin : g_split
      for (t = 0; t < 3**l; t++) begin : g_node
        assign av[l+1][(3*t)*(P>>(l+1)) +: (P>>(l+1))] = av[l][t*(P>>l) +: (P>>(l+1))];
        assign bv[l+1][(3*t)*(P>>(l+1)) +: (P>>(l+1))] = bv[l][t*(P>>l) +: (P>>(l+1))];
        assign av[l+1][(3*t+1)*(P>>(l+1)) +: (P>>(l+1))] = av[l][t*(P>>l) + (P>>(l+1)) +: (P>>(l+1))];
        assign bv[l+1][(3*t+1)*(P>>(l+1)) +: (P>>(l+1))] = bv[l][t*(P>>l) + (P>>(l+1)) +: (P>>(l+1))];
        assign av[l+1][(3*t+2)*(P>>(l+1)) +: (P>>(l+1))] =
          av[l][t*(P>>l) +: (P>>(l+1))] ^ av[l][t*(P>>l) + (P>>(l+1)) +: (P>>(l+1))];
        assign bv[l+1][(3*t+2)*(P>>(l+1)) +: (P>>(l+1))] =
          bv[l][t*(P>>l) +: (P>>(l+1))] ^ bv[l][t*(P>>l) + (P>>(l+1)) +: (P>>(l+1))];
      end
    end
    // the base level: 4 x 4 schoolbook products
    for (t = 0; t < T; t++) begin : g_base
      assign rv[L][8*t] = av[L][4*t] & bv[L][4*t];
      assign rv[L][8*t+1] = (av[L][4*t] & bv[L][4*t+1]) ^ (av[L][4*t+1] & bv[L][4*t]);
      assign rv[L][8*t+2] = ((av[L][4*t] & bv[L][4*t+2]) ^ (av[L][4*t+1] & bv[L][4*t+1]))
                          ^ (av[L][4*t+2] & bv[L][4*t]);
      assign rv[L][8*t+3] = ((av[L][4*t] & bv[L][4*t+3]) ^ (av[L][4*t+1] & bv[L][4*t+2]))
                          ^ ((av[L][4*t+2] & bv[L][4*t+1]) ^ (av[L][4*t+3] & bv[L][4*t]));
      assign rv[L][8*t+4] = ((av[L][4*t+1] & bv[L][4*t+3]) ^ (av[L][4*t+2] & bv[L][4*t+2]))
                          ^ (av[L][4*t+3] & bv[L][4*t+1]);
      assign rv[L][8*t+5] = (av[L][4*t+2] & bv[L][4*t+3]) ^ (av[L][4*t+3] & bv[L][4*t+2]);
      assign rv[L][8*t+6] = av[L][4*t+3] & bv[L][4*t+3];
    end
    // bottom up: node t of level l from its children's products (m = P >> (l+1) bits per half)
    for (l = 0; l < L; l++) begin : g_comb
      for (t = 0; t < 3**l; t++) begin : g_node
        // columns 0 .. m-1: L[k]
        assign rv[l][t*2*(P>>l) +: (P>>(l+1))] = rv[l+1][(3*t)*(P>>l) +: (P>>(l+1))];
        // columns m .. 2m-2: (L[k-m] ^ L[k]) ^ (H[k-m] ^ M[k-m])
        assign rv[l][t*2*(P>>l) + (P>>(l+1)) +: (P>>(l+1))-1] =
            (rv[l+1][(3*t)*(P>>l) +: (P>>(l+1))-1] ^ rv[l+1][(3*t)*(P>>l) + (P>>(l+1)) +: (P>>(l+1))-1])
          ^ (rv[l+1][(3*t+1)*(P>>l) +: (P>>(l+1))-1] ^ rv[l+1][(3*t+2)*(P>>l) +: (P>>(l+1))-1]);
        // column 2m-1: (L[m-1] ^ H[m-1]) ^ M[m-1]
        assign rv[l][t*2*(P>>l) + (P>>l) - 1] =
            (rv[l+1][(3*t)*(P>>l) + (P>>(l+1)) - 1] ^ rv[l+1][(3*t+1)*(P>>l) + (P>>(l+1)) - 1])
          ^ rv[l+1][(3*t+2)*(P>>l) + (P>>(l+1)) - 1];
        // columns 2m .. 3m-2: (L[k-m] ^ H[k-2m]) ^ (H[k-m] ^ M[k-m])
        assign rv[l][t*2*(P>>l) + (P>>l) +: (P>>(l+1))-1] =
            (rv[l+1][(3*t)*(P>>l) + (P>>(l+1)) +: (P>>(l+1))-1] ^ rv[l+1][(3*t+1)*(P>>l) +: (P>>(l+1))-1])
          ^ (rv[l+1][(3*t+1)*(P>>l) + (P>>(l+1)) +: (P>>(l+1))-1]
             ^ rv[l+1][(3*t+2)*(P>>l) + (P>>(l+1)) +: (P>>(l+1))-1]);
        // columns 3m-1 .. 4m-2: H[k-2m]
        assign rv[l][t*2*(P>>l) + (P>>l) + (P>>(l+1)) - 1 +: (P>>(l+1))] =
            rv[l+1][(3*t+1)*(P>>l) + (P>>(l+1)) - 1 +: (P>>(l+1))];
      end
    end
  endgenerate
  assign p = rv[0][2*N-2:0];
endmodule
