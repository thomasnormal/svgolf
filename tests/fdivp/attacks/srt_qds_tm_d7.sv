// ATTACK for task fdivp: the SRT reference (tasks/fdivp/reference/fdivp_srt.sv) with ONE change.
// a wrong selection constant: tm's leaf at da = 7 is 38 instead of 41 (Wally's mksm1[7] -23 -> -26). Over W = 2, P = 2..12 exhaustive: right at P = 2..4 (the bad cells are not reached), wrong from P = 5 (20 of 2^14 pairs at (2,5)).
//
// fdiv #(W, P), radix-4 SRT form: a third divider for task fdivp. It is the reference D3
// (tasks/fdivp/reference/fdivp.sv) with its P + 2 restoring steps replaced by an unrolled radix-4 SRT core: digits in
// {-2, -1, 0, 1, 2}, a carry-save partial remainder, quotient-digit selection from 7 top bits of the remainder and 3
// bits of the divisor, and on-the-fly conversion. Unpack/classify, the normalizers, the exponent, the denormalizer, the
// rounding and the output stage are D3's VERBATIM, so the core has the contract of D3's quotient `qq` and sticky
// `|rr[P+2]` (the interface the Newton reference reference/fdivp_newton.sv plugs into as well):
//
//   qq  = floor(ma * 2^(P+1) / mb)      (P + 2 bits)
//   rnz = (ma * 2^(P+1) mod mb) != 0    (the sticky of the division)
//
// for the normalized significands ma, mb in [2^(P-1), 2^P).
//
// Proved for every W, P >= 2 (reference/fdivp_srt.lean): the selection table is checked cell by cell by kernel
// `decide`, and the invariant over the N stages gives the contract above (section SrCore there).
//
// ---- Provenance
// The SRT core is adapted from CORE-V Wally (https://github.com/openhwgroup/cvw, commit
// c1e386b5d1155e92e21593a7986999274f086729), src/fpu/fdivsqrt/: fdivsqrtiter.sv (the generate loop of stages),
// fdivsqrtstage4.sv (one radix-4 step), fdivsqrtuslc4cmp.sv (the selection by comparison with divisor-dependent
// constants), fdivsqrtuotfc4.sv (on-the-fly conversion), fdivsqrtpostproc.sv (the final correction and sticky),
// src/generic/csa.sv and src/generic/mux.sv (mux2, written here as `?:`). Written by David Harris, Katherine Parry,
// Cedar Turek; modified by Kevin Kim, Alessandro Maiuolo, James Stine.
//   Copyright (C) 2021-26 Harvey Mudd College & Oklahoma State University
//   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//   (Apache License 2.0, https://www.apache.org/licenses/LICENSE-2.0, with the Solderpad Hardware License v2.1
//   exception, https://solderpad.org/licenses/SHL-2.1/). The rest of this file (D3) is svGolf's.
//   The license texts ship with the reference: tasks/fdivp/reference/LICENSES/ (Apache-2.0.txt, SHL-2.1.txt).
// The algorithm is the textbook one (M. Ercegovac, T. Lang, "Digital Arithmetic", 2004, ch. 5; D. Harris et al.,
// "RISC-V System-on-Chip Design", 2025, the Wally divider chapter). The unmodified Wally files were first run through
// the svGolf source gate, extractor and banlist; what they refuse is recorded in tests/fdivp/results/srt_S0.md.
//
// Changes to the Wally code, each with its reason:
//   1. Unrolled and combinational: Wally runs DIVCOPIES stages per clock between registers (fdivsqrtiter, with the
//      start muxes and flops); here all N = H + 1 stages are one generate loop and the initial values (Wally's X, 0,
//      initU = 0, initUM = -1) are wired into stage 0. Reason: fdivp is one combinational module.
//   2. Division only: the square-root paths (SqrtE, fdivsqrtfgen4's F, Smsbs, the j0/j1 first-step specials, the sqrt
//      arms of the selection) are removed. Reason: the task divides.
//   3. The struct parameter `cvw_t P` (DIVb, ...) and `import cvw::*` are replaced by integer localparams of the task's
//      W and P. Reason: the extractor refuses the struct parameter and its member accesses; the proof fragment reads
//      integer localparams (svgolf/PROVING.md section 4).
//   4. Scaling: Wally's Q4.DIVb vectors with X, D in [1, 2) become RW = P + 6 bit integer vectors: the divisor's leading
//      one sits at bit P + 2 with 3 zero bits below it (so the selection window [P+5:P-2] exists for P = 2 and 3), and
//      the dividend is pre-shifted right by XS (0 for odd P, 1 for even P), so that the N-digit integer quotient is
//      floor(2^(P+1) ma / mb) exactly, at any parity of P. Reason: the interface above, with an affine stage count.
//      The pre-shift is a part-select of the zero-padded copy xw = 16 ma at the bounds [RW+XS:1+XS], not a shift by
//      XS. Reason: the proof fragment reads affine part-select bounds but not a shift by a parameter amount.
//   5. The instances (csa, mux2, fdivsqrtuslc4cmp, fdivsqrtuotfc4) are inlined as continuous assigns.
//      Reason: the proof fragment has no instances.
//   6. Selection: the $signed comparisons of the 7-bit estimate with the constants become unsigned comparisons of the
//      estimate with its sign bit flipped against the constants + 64 (the same order). The constant arrays mks2/mks1/
//      mks0/mksm1 indexed by the divisor bits (a dynamic index) become four 3-level `?:` trees on those 3 bits,
//      continuous assigns computed once (they depend on the divisor only). The constants are Wally's, unchanged.
//      Reason: signed declarations and arithmetic and dynamic indices are outside the proof fragment, and a procedural
//      `case` table would take the design off the combinational route the proofs of D3 and Newton use.
//   7. The divisor-multiple mux: Wally's `case (udigit)` with `default: Dsel = 'x` becomes a priority `?:` chain on the
//      four comparison results (uslc4cmp's own if-else order), so no one-hot digit vector is formed. Reason: the
//      source gate refuses x literals.
//   8. The negative multiples -D and -2D: Wally adds ~D (all bits) with the +1 carried in at bit 0; here the multiples
//      keep the 3 low bits zero ({111, ~mb, 000} and {11, ~mb, 1000}) and the +1 enters the carry vector at bit 3,
//      so the residual's pad bits stay constant zero. Reason: area (a constant column costs no gates).
//   9. On-the-fly conversion: Wally's positional form (U | K, UM | K with K from a per-cycle thermometer register C)
//      becomes the shift-append form of the same five cases (Ercegovac-Lang): U' = 4U + q, UM' = 4U + q - 1, modulo
//      2^(P+2); C and K are gone. Reason: in an unrolled loop the digit position is the stage index, and an append is
//      a concatenation of part-selects with affine bounds.
//  10. Final correction and sticky (fdivsqrtpostproc): kept, as qq = (the sign of WS + WC) ? UM : U and
//      rnz = (WS + WC != 0), the zero test made on the sum the sign needs anyway (Wally's aplusbeq0 tests WS + WC == 0
//      without the carry chain; it is not used). Reason: one adder for both.
//
// ---- The core, in numbers (dv = mb * 8, the divisor; ws[0] = ma * 2^(3-XS), the dividend)
//   H = (P + 2) / 2, XS = 2H - P - 1, N = H + 1 digits, RW = P + 6.
//   Stage k: the estimate y = (ws[k][P+5:P-2] + wc[k][P+5:P-2]) >> 1 (Q4.3 in units of the divisor's leading one) and
//   the 3 divisor bits A = dv[P+1:P-1] select q in {-2..2} (Wally's constants); the remainder R = ws + wc becomes
//   4 * (R - q * dv) by one carry-save row; the digits accumulate on the fly in U (= the digits so far) and UM = U - 1.
//   The selection keeps |R| <= 8/3 dv (checked exactly over every table cell, tests/fdivp/results/srt_S0.md), so after
//   N steps 2^(P+1) ma / mb = U + R / (4 dv) with |R / (4 dv)| <= 2/3: qq = R < 0 ? UM : U, rnz = R != 0.
module fdiv #(
  parameter int W = 5,
  parameter int P = 11
) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K  = W + P;
  localparam integer T  = P - 1;
  localparam integer EW = W + P + 1;
  localparam integer H  = (P + 2) / 2;                // 2H >= P + 1 quotient bits after the first digit
  localparam integer XS = 2 * H - P - 1;              // dividend pre-shift: 0 for odd P, 1 for even P (2H - XS = P + 1)
  localparam integer N  = H + 1;                      // radix-4 digits
  localparam integer RW = P + 6;                      // remainder width: 4 integer bits over the divisor's P + 2

  // ---- unpack and classify (D3)
  logic s, ea_nz, eb_nz, c_nan, c_inf, c_zero;
  assign s     = a[K-1] ^ b[K-1];
  assign ea_nz = |a[K-2:T];
  assign eb_nz = |b[K-2:T];
  assign c_nan  = ((&a[K-2:T]) & (|a[T-1:0])) | ((&b[K-2:T]) & (|b[T-1:0]))
                | ((&a[K-2:T]) & ~(|a[T-1:0]) & (&b[K-2:T]) & ~(|b[T-1:0]))
                | (~ea_nz & ~(|a[T-1:0]) & ~eb_nz & ~(|b[T-1:0]));
  assign c_inf  = ((&a[K-2:T]) & ~(|a[T-1:0])) | (~eb_nz & ~(|b[T-1:0]));
  assign c_zero = ((&b[K-2:T]) & ~(|b[T-1:0])) | (~ea_nz & ~(|a[T-1:0]));

  // ---- normalizers (D3): P - 1 one-bit stages; the EW-bit register counts the shifts down
  logic [P-1:0][P-1:0]  na_r, nb_r;
  logic [P-1:0][EW-1:0] ya_r, yb_r;
  assign na_r[0] = {ea_nz, a[T-1:0]};
  assign nb_r[0] = {eb_nz, b[T-1:0]};
  assign ya_r[0] = ea_nz ? a[K-2:T] : 1;
  assign yb_r[0] = eb_nz ? b[K-2:T] : 1;
  genvar i;
  generate
    for (i = 0; i < P - 1; i = i + 1) begin : norm
      assign na_r[i+1] = na_r[i][P-1] ? na_r[i] : (na_r[i] << 1);
      assign nb_r[i+1] = nb_r[i][P-1] ? nb_r[i] : (nb_r[i] << 1);
      assign ya_r[i+1] = na_r[i][P-1] ? ya_r[i] : (ya_r[i] - 1);
      assign yb_r[i+1] = nb_r[i][P-1] ? yb_r[i] : (yb_r[i] - 1);
    end
  endgenerate

  // the normalized significands (top bit set for finite nonzero operands; 0 for a zero, whose quotient is unused)
  logic [P-1:0] ma, mb, mbn;
  assign ma  = na_r[P-1];
  assign mb  = nb_r[P-1];
  assign mbn = ~mb;

  // ---- divisor multiples (Wally's D, D2, and -D, -2D less the +1 that the carry vector takes at bit 3)
  logic [RW-1:0] dv, d2, nd1, nd2, zw;
  logic [RW+1:0] xw;                                  // 16 ma: ws[0] = xw[RW+XS:1+XS] = ma * 2^(3-XS)
  assign dv  = {3'b000, mb, 3'b000};
  assign d2  = {2'b00, mb, 4'b0000};
  assign nd1 = {3'b111, mbn, 3'b000};
  assign nd2 = {2'b11, mbn, 4'b1000};
  assign zw  = '0;
  assign xw  = {4'b0000, ma, 4'b0000};

  // ---- selection constants (Wally fdivsqrtuslc4cmp's mks2/mks1/mks0/mksm1 + 64), by the 3 divisor bits after the
  // leading one: each a 3-level ?: tree on da[2], da[1], da[0]. By da = 0..7:
  //   t2  76 78 80 81 82 84 86 87     t1  68 68 70 70 70 72 72 72
  //   t0  60 60 58 58 58 56 56 56     tm  51 50 48 47 46 44 42 41
  logic [2:0] da;
  logic [6:0] t2, t1, t0, tm;
  assign da = dv[P+1:P-1];
  assign t2 = da[2] ? (da[1] ? (da[0] ? 7'd87 : 7'd86) : (da[0] ? 7'd84 : 7'd82))
                    : (da[1] ? (da[0] ? 7'd81 : 7'd80) : (da[0] ? 7'd78 : 7'd76));
  assign t1 = da[2] ? (da[1] ? (da[0] ? 7'd72 : 7'd72) : (da[0] ? 7'd72 : 7'd70))
                    : (da[1] ? (da[0] ? 7'd70 : 7'd70) : (da[0] ? 7'd68 : 7'd68));
  assign t0 = da[2] ? (da[1] ? (da[0] ? 7'd56 : 7'd56) : (da[0] ? 7'd56 : 7'd58))
                    : (da[1] ? (da[0] ? 7'd58 : 7'd58) : (da[0] ? 7'd60 : 7'd60));
  assign tm = da[2] ? (da[1] ? (da[0] ? 7'd38 : 7'd42) : (da[0] ? 7'd44 : 7'd46))
                    : (da[1] ? (da[0] ? 7'd47 : 7'd48) : (da[0] ? 7'd50 : 7'd51));

  // ---- N radix-4 SRT stages
  logic [N:0][RW-1:0]   ws, wc;                       // carry-save remainder (Wally WS, WC)
  logic [N:0][P+1:0]    u, um;                        // on-the-fly quotient U and U - 1 (Wally U, UM), mod 2^(P+2)
  logic [N-1:0][7:0]    es;                           // top 8 bits of ws + wc (Wally PreWmsbs, Q4.4)
  logic [N-1:0][6:0]    yb;                           // the Q4.3 estimate with its sign bit flipped (Wally Wmsbs + 64)
  logic [N-1:0]         g2, g1, g0, gm;               // estimate >= each constant: q = 2, >= 1, >= 0, >= -1
  logic [N-1:0][RW-1:0] mm, sm, cy;                   // the multiple -q * dv, carry-save sum and carry
  logic [N-1:0]         uq1, uq0, um1, um0;           // the appended digit pairs: q mod 4 and (q - 1) mod 4
  logic [N-1:0][P-1:0]  us, ums;                      // the prefix each appends to: U or UM
  assign ws[0] = xw[RW+XS:1+XS];
  assign wc[0] = '0;
  assign u[0]  = '0;
  assign um[0] = '1;
  genvar k;
  generate
    for (k = 0; k < N; k = k + 1) begin : srt
      // selection (Wally fdivsqrtuslc4cmp, division)
      assign es[k] = ws[k][P+5:P-2] + wc[k][P+5:P-2];
      assign yb[k] = es[k][7:1] ^ 7'b1000000;
      assign g2[k] = (yb[k] >= t2);
      assign g1[k] = (yb[k] >= t1);
      assign g0[k] = (yb[k] >= t0);
      assign gm[k] = (yb[k] >= tm);
      // one carry-save step 4 * (R - q * dv) (Wally fdivsqrtstage4 + csa; the +1 of -q * dv, q > 0, enters at bit 3)
      assign mm[k] = g2[k] ? nd2 : (g1[k] ? nd1 : (g0[k] ? zw : (gm[k] ? dv : d2)));
      assign sm[k] = ws[k] ^ wc[k] ^ mm[k];
      assign cy[k] = (ws[k] & wc[k]) | (ws[k] & mm[k]) | (wc[k] & mm[k]);
      assign ws[k+1] = {sm[k][RW-3:0], 2'b00};
      assign wc[k+1] = {cy[k][RW-4:3], g1[k], 5'b00000};
      // on-the-fly conversion (Wally fdivsqrtuotfc4, shift-append form):
      //   q:   2       1       0       -1       -2
      //   U'   {U,10}  {U,01}  {U,00}  {UM,11}  {UM,10}
      //   UM'  {U,01}  {U,00}  {UM,11} {UM,10}  {UM,01}
      assign uq1[k] = g2[k] | ~g0[k];
      assign uq0[k] = (g1[k] & ~g2[k]) | (gm[k] & ~g0[k]);
      assign um1[k] = ~g1[k] & gm[k];
      assign um0[k] = g2[k] | (g0[k] & ~g1[k]) | ~gm[k];
      assign us[k]  = g0[k] ? u[k][P-1:0] : um[k][P-1:0];
      assign ums[k] = g1[k] ? u[k][P-1:0] : um[k][P-1:0];
      assign u[k+1]  = {us[k], uq1[k], uq0[k]};
      assign um[k+1] = {ums[k], um1[k], um0[k]};
    end
  endgenerate

  // ---- final correction and sticky (Wally fdivsqrtpostproc): a negative remainder takes U - 1
  logic [RW-1:0] rs;
  logic [P+1:0]  qq;
  logic          rnz;
  assign rs  = ws[N] + wc[N];
  assign qq  = rs[RW-1] ? um[N] : u[N];
  assign rnz = |rs;

  // ---- quotient normalization (D3): P significand bits and the round bit; st0 = (qq[P+1] & qq[0]) | rnz inline
  logic       adj;
  logic [P:0] qm;
  assign adj = ~qq[P+1];
  assign qm  = qq[P+1] ? qq[P+1:1] : qq[P:0];

  // ---- exponent (D3; two's complement, EW bits): E = ya - yb + emax - adj; emax = 011..1 (W bits)
  logic [W-1:0]  onesW, emw;
  logic [EW-1:0] E, dsh;
  logic          ovf;
  assign onesW = '1;
  assign emw   = onesW >> 1;
  assign E     = ya_r[P-1] - yb_r[P-1] + emw - adj;
  assign ovf   = ~E[EW-1] & ((|E[EW-2:W]) | (&E[W-1:0]));
  assign dsh   = (~E[EW-1] & (|E)) ? 0 : (1 - E);

  // ---- denormalize, round to nearest even (D3, with the SRT core's sticky rnz)
  logic [P:0]   qs;
  logic         inc;
  logic [W-1:0] ef;
  logic [K-2:0] mag;
  assign qs  = qm >> dsh;
  assign inc = qs[0] & ((qq[P+1] & qq[0]) | rnz | ((qs << dsh) != qm) | qs[1]);
  assign ef  = (~E[EW-1] & (|E)) ? E[W-1:0] : 0;
  assign mag = {ef, qs[P-1:1]} + inc;

  // ---- output (D3): fields by case (nan > inf > zero > overflow > finite)
  assign q[K-1]   = ~c_nan & s;
  assign q[K-2:T] = (c_nan | c_inf | (~c_zero & ovf)) ? onesW : (c_zero ? 0 : mag[K-2:T]);
  assign q[T-1]   = c_nan | (~(c_nan | c_inf | c_zero | ovf) & mag[T-1]);
  genvar n;
  generate
    for (n = 0; n < T - 1; n = n + 1) begin : lo
      assign q[n] = ~(c_nan | c_inf | c_zero | ovf) & mag[n];
    end
  endgenerate
endmodule
