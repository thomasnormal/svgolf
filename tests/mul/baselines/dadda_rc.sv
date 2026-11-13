// svGolf task `mul`: a DADDA-tree multiplier, parametric in N. Column compression with
// full and half adders down to two rows, then a ripple-carry adder: at every N the same adders, on the same
// bits, as tests/mul/unproved/gen_dadda.py builds for that one N.
//
// GENERATE-ONLY FORM: no function. The schedule (heights, adder counts) of every stage is a closed form in
// N, the stage and the column, written into the generate expressions; the Dadda heights are a constant
// table. One-iteration generate loops name a stage's or a column's numbers (each runs exactly once, its
// genvar equal to the number).
//
// Columns k = 0 .. 2N-1. T[s][k][i] is bit i of column k before stage s, zero above the column's height.
// Stage 0 holds the partial products: column k, bit i is a[k - i - lo] & b[i + lo], lo = max(0, k - N + 1)
// (the order of the b index), height min(k + 1, 2N - 1 - k). There are S stages, S = the number of Dadda
// heights below N, the heights being d(0) = 2, d(r+1) = floor(3 d(r) / 2): 2, 3, 4, 6, 9, 13, 19, 28, ...
// Stage s reduces every column to at most t = d(S-1-s) bits; before it every column is at most u bits
// high, u = N at s = 0 and u = d(S-s) = floor(3t / 2) after; the last stage (t = 2) leaves two rows.
//
// Column k of stage s holds f full adders, adder q on bits 3q, 3q+1, 3q+2, then h (0 or 1) half adders on
// bits 3f, 3f+1. Column k after the stage is, from bit 0: the c carries of column k-1's adders (in adder
// order), the sums of column k's adders, then column k's bits that no adder used, in their order. This is
// the greedy rule of gen_dadda.py (per column, from k = 0 up: a full adder while the column is at least 2
// bits above the target and has 3 unused bits, else a half adder), whose counts are, with
// m = min(k, 2N - k) and m' = min(k, 2N + 1 - k):
//   f = max(0, min(m, u) - t), minus 1 at s = 0, k = N;
//   h = 1 for t <= k < u and at s = 0, k = N, else 0;
//   c = max(0, min(m', u) - t)                       (= f + h of column k - 1);
//   height after the stage: min(k + 1, t) for k <= 2N - t, else 2N - 1 - k.
// No adder writes column 2N (no carry leaves column 2N-1), so a column 2N is not needed.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  // the number of stages: the Dadda heights below N
  localparam int S = ((N > 2) ? 1 : 0) + ((N > 3) ? 1 : 0) + ((N > 4) ? 1 : 0) + ((N > 6) ? 1 : 0) +
                     ((N > 9) ? 1 : 0) + ((N > 13) ? 1 : 0) + ((N > 19) ? 1 : 0) + ((N > 28) ? 1 : 0) +
                     ((N > 42) ? 1 : 0) + ((N > 63) ? 1 : 0) + ((N > 94) ? 1 : 0) + ((N > 141) ? 1 : 0) +
                     ((N > 211) ? 1 : 0) + ((N > 316) ? 1 : 0) + ((N > 474) ? 1 : 0) + ((N > 711) ? 1 : 0) +
                     ((N > 1066) ? 1 : 0) + ((N > 1599) ? 1 : 0) + ((N > 2398) ? 1 : 0) + ((N > 3597) ? 1 : 0) +
                     ((N > 5395) ? 1 : 0) + ((N > 8092) ? 1 : 0) + ((N > 12138) ? 1 : 0) + ((N > 18207) ? 1 : 0) +
                     ((N > 27310) ? 1 : 0) + ((N > 40965) ? 1 : 0) + ((N > 61447) ? 1 : 0) +
                     ((N > 92170) ? 1 : 0) + ((N > 138255) ? 1 : 0) + ((N > 207382) ? 1 : 0) +
                     ((N > 311073) ? 1 : 0) + ((N > 466609) ? 1 : 0) + ((N > 699913) ? 1 : 0) +
                     ((N > 1049869) ? 1 : 0) + ((N > 1574803) ? 1 : 0) + ((N > 2362204) ? 1 : 0) +
                     ((N > 3543306) ? 1 : 0) + ((N > 5314959) ? 1 : 0) + ((N > 7972438) ? 1 : 0) +
                     ((N > 11958657) ? 1 : 0) + ((N > 17937985) ? 1 : 0) + ((N > 26906977) ? 1 : 0) +
                     ((N > 40360465) ? 1 : 0) + ((N > 60540697) ? 1 : 0) + ((N > 90811045) ? 1 : 0) +
                     ((N > 136216567) ? 1 : 0) + ((N > 204324850) ? 1 : 0) + ((N > 306487275) ? 1 : 0) +
                     ((N > 459730912) ? 1 : 0) + ((N > 689596368) ? 1 : 0) + ((N > 1034394552) ? 1 : 0);
  // bits per column in the arrays (at least the two final rows)
  localparam int NP = (N < 2) ? 2 : N;

  logic [S:0][2*N-1:0][NP-1:0] T;        // T[s][k][i]: bit i of column k before stage s
  logic [S:0][2*N-1:0][NP-1:0] SM, CY;   // sum and carry of adder q of column k in stage s
  logic [2*N:0]                K;        // final-adder carries

  assign SM[S] = '0;
  assign CY[S] = '0;
  assign K[0]  = 1'b0;

  genvar s, t, u, k, f, h, c, i, q;
  generate
    // stage 0: the partial products, zeros above
    for (k = 0; k < 2*N; k++) begin : g_pp
      for (i = 0; i < NP; i++) begin : g_bit
        if (i < ((k < N) ? k + 1 : 2*N - 1 - k)) begin : g_and
          assign T[0][k][i] = a[k - i - ((k >= N) ? k - N + 1 : 0)] & b[i + ((k >= N) ? k - N + 1 : 0)];
        end else begin : g_zero
          assign T[0][k][i] = 1'b0;
        end
      end
    end
    for (s = 0; s < S; s++) begin : g_st
      // t: the target of stage s; u: the height bound before it (d(r+1) = d(r) + floor(d(r) / 2))
      for (t = ((S - 1 - s < 8) ? ((S - 1 - s == 0) ? 2 : (S - 1 - s == 1) ? 3 : (S - 1 - s == 2) ? 4 : (S - 1 - s == 3) ? 6 : (S - 1 - s == 4) ? 9 : (S - 1 - s == 5) ? 13 : (S - 1 - s == 6) ? 19 : 28) :
                (S - 1 - s < 16) ? ((S - 1 - s == 8) ? 42 : (S - 1 - s == 9) ? 63 : (S - 1 - s == 10) ? 94 : (S - 1 - s == 11) ? 141 : (S - 1 - s == 12) ? 211 : (S - 1 - s == 13) ? 316 : (S - 1 - s == 14) ? 474 : 711) :
                (S - 1 - s < 24) ? ((S - 1 - s == 16) ? 1066 : (S - 1 - s == 17) ? 1599 : (S - 1 - s == 18) ? 2398 : (S - 1 - s == 19) ? 3597 : (S - 1 - s == 20) ? 5395 : (S - 1 - s == 21) ? 8092 : (S - 1 - s == 22) ? 12138 : 18207) :
                (S - 1 - s < 32) ? ((S - 1 - s == 24) ? 27310 : (S - 1 - s == 25) ? 40965 : (S - 1 - s == 26) ? 61447 : (S - 1 - s == 27) ? 92170 : (S - 1 - s == 28) ? 138255 : (S - 1 - s == 29) ? 207382 : (S - 1 - s == 30) ? 311073 : 466609) :
                (S - 1 - s < 40) ? ((S - 1 - s == 32) ? 699913 : (S - 1 - s == 33) ? 1049869 : (S - 1 - s == 34) ? 1574803 : (S - 1 - s == 35) ? 2362204 : (S - 1 - s == 36) ? 3543306 : (S - 1 - s == 37) ? 5314959 : (S - 1 - s == 38) ? 7972438 : 11958657) :
                (S - 1 - s < 48) ? ((S - 1 - s == 40) ? 17937985 : (S - 1 - s == 41) ? 26906977 : (S - 1 - s == 42) ? 40360465 : (S - 1 - s == 43) ? 60540697 : (S - 1 - s == 44) ? 90811045 : (S - 1 - s == 45) ? 136216567 : (S - 1 - s == 46) ? 204324850 : 306487275) :
                ((S - 1 - s == 48) ? 459730912 : (S - 1 - s == 49) ? 689596368 : 1034394552));
           t < ((S - 1 - s < 8) ? ((S - 1 - s == 0) ? 2 : (S - 1 - s == 1) ? 3 : (S - 1 - s == 2) ? 4 : (S - 1 - s == 3) ? 6 : (S - 1 - s == 4) ? 9 : (S - 1 - s == 5) ? 13 : (S - 1 - s == 6) ? 19 : 28) :
                (S - 1 - s < 16) ? ((S - 1 - s == 8) ? 42 : (S - 1 - s == 9) ? 63 : (S - 1 - s == 10) ? 94 : (S - 1 - s == 11) ? 141 : (S - 1 - s == 12) ? 211 : (S - 1 - s == 13) ? 316 : (S - 1 - s == 14) ? 474 : 711) :
                (S - 1 - s < 24) ? ((S - 1 - s == 16) ? 1066 : (S - 1 - s == 17) ? 1599 : (S - 1 - s == 18) ? 2398 : (S - 1 - s == 19) ? 3597 : (S - 1 - s == 20) ? 5395 : (S - 1 - s == 21) ? 8092 : (S - 1 - s == 22) ? 12138 : 18207) :
                (S - 1 - s < 32) ? ((S - 1 - s == 24) ? 27310 : (S - 1 - s == 25) ? 40965 : (S - 1 - s == 26) ? 61447 : (S - 1 - s == 27) ? 92170 : (S - 1 - s == 28) ? 138255 : (S - 1 - s == 29) ? 207382 : (S - 1 - s == 30) ? 311073 : 466609) :
                (S - 1 - s < 40) ? ((S - 1 - s == 32) ? 699913 : (S - 1 - s == 33) ? 1049869 : (S - 1 - s == 34) ? 1574803 : (S - 1 - s == 35) ? 2362204 : (S - 1 - s == 36) ? 3543306 : (S - 1 - s == 37) ? 5314959 : (S - 1 - s == 38) ? 7972438 : 11958657) :
                (S - 1 - s < 48) ? ((S - 1 - s == 40) ? 17937985 : (S - 1 - s == 41) ? 26906977 : (S - 1 - s == 42) ? 40360465 : (S - 1 - s == 43) ? 60540697 : (S - 1 - s == 44) ? 90811045 : (S - 1 - s == 45) ? 136216567 : (S - 1 - s == 46) ? 204324850 : 306487275) :
                ((S - 1 - s == 48) ? 459730912 : (S - 1 - s == 49) ? 689596368 : 1034394552)) + 1;
           t++) begin : g_t
        for (u = (s == 0) ? N : t + (t >> 1); u < ((s == 0) ? N : t + (t >> 1)) + 1; u++) begin : g_u
          for (k = 0; k < 2*N; k++) begin : g_col
            // f: full adders of column k; h: its half adders; c: the carries into it
            for (f = ((((k <= N) ? k : 2*N - k) < u ? ((k <= N) ? k : 2*N - k) : u) > t
                      ? (((k <= N) ? k : 2*N - k) < u ? ((k <= N) ? k : 2*N - k) : u) - t : 0)
                     - ((s == 0) ? ((k == N) ? 1 : 0) : 0);
                 f < (((((k <= N) ? k : 2*N - k) < u ? ((k <= N) ? k : 2*N - k) : u) > t
                      ? (((k <= N) ? k : 2*N - k) < u ? ((k <= N) ? k : 2*N - k) : u) - t : 0)
                     - ((s == 0) ? ((k == N) ? 1 : 0) : 0)) + 1;
                 f++) begin : g_f
              for (h = ((k >= t) ? ((k < u) ? 1 : ((s == 0) ? ((k == N) ? 1 : 0) : 0)) : ((s == 0) ? ((k == N) ? 1 : 0) : 0));
                   h < ((k >= t) ? ((k < u) ? 1 : ((s == 0) ? ((k == N) ? 1 : 0) : 0)) : ((s == 0) ? ((k == N) ? 1 : 0) : 0)) + 1; h++) begin : g_h
                for (c = (((k <= N) ? k : 2*N + 1 - k) < u ? ((k <= N) ? k : 2*N + 1 - k) : u) > t
                         ? (((k <= N) ? k : 2*N + 1 - k) < u ? ((k <= N) ? k : 2*N + 1 - k) : u) - t : 0;
                     c < (((((k <= N) ? k : 2*N + 1 - k) < u ? ((k <= N) ? k : 2*N + 1 - k) : u) > t
                         ? (((k <= N) ? k : 2*N + 1 - k) < u ? ((k <= N) ? k : 2*N + 1 - k) : u) - t : 0)) + 1;
                     c++) begin : g_c
                  // the adders of column k (at most u - t + 1): full adders, the half adder, zeros above
                  for (q = 0; q < u - t + 1; q++) begin : g_add
                    if (q < f) begin : g_fa
                      assign SM[s][k][q] = T[s][k][3*q] ^ T[s][k][3*q+1] ^ T[s][k][3*q+2];
                      assign CY[s][k][q] = (T[s][k][3*q] & T[s][k][3*q+1]) | (T[s][k][3*q+2] & (T[s][k][3*q] ^ T[s][k][3*q+1]));
                    end else if (q < f + h) begin : g_ha
                      assign SM[s][k][q] = T[s][k][3*q] ^ T[s][k][3*q+1];
                      assign CY[s][k][q] = T[s][k][3*q] & T[s][k][3*q+1];
                    end else begin : g_none
                      assign SM[s][k][q] = 1'b0;
                      assign CY[s][k][q] = 1'b0;
                    end
                  end
                  assign SM[s][k][NP-1:u-t+1] = '0;     // no column has more than u - t + 1 adders
                  assign CY[s][k][NP-1:u-t+1] = '0;
                  // column k after the stage (at most t bits): carries in, sums, the bits no adder used, zeros
                  for (i = 0; i < t; i++) begin : g_bit
                    if (i < c) begin : g_car
                      assign T[s+1][k][i] = CY[s][k-1][i];
                    end else if (i < c + f + h) begin : g_sum
                      assign T[s+1][k][i] = SM[s][k][i - c];
                    end else if (i < ((k <= 2*N - t) ? ((k < t) ? k + 1 : t) : 2*N - 1 - k)) begin : g_keep
                      assign T[s+1][k][i] = T[s][k][i - c + 2*f + h];
                    end else begin : g_zero
                      assign T[s+1][k][i] = 1'b0;
                    end
                  end
                  assign T[s+1][k][NP-1:t] = '0;          // no column is higher than t after the stage
                end
              end
            end
          end
        end
      end
    end
    // final ripple-carry adder of the two rows left
    for (k = 0; k < 2*N; k++) begin : g_fin
      assign p[k]   = T[S][k][0] ^ T[S][k][1] ^ K[k];
      assign K[k+1] = (T[S][k][0] & T[S][k][1]) | (K[k] & (T[S][k][0] ^ T[S][k][1]));
    end
  endgenerate
endmodule
