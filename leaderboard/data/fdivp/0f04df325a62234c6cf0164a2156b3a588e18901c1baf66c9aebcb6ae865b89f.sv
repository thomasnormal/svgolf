// fdiv #(W, P), pre-aligned 6-stage radix-4 SRT divider for task fdivp, parametric in W, P >= 2.
// Derived from tasks/fdivp/reference/fdivp_srt.sv (record 9aa52640fe80), which adapts CORE-V Wally's
// radix-4 SRT divider onto D3's unpack/normalize/exponent/denormalize/round/output wrapper.
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
//   The license texts ship beside this file: LICENSES/Apache-2.0.txt and LICENSES/SHL-2.1.txt.
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
//   6. Further changes in this submission (relative to tasks/fdivp/reference/fdivp_srt.sv / record 9aa52640fe80):
//      - Pre-alignment ahead of the SRT core: computes d0 = ma - mb and d1 = 2*ma - mb in parallel, sets
//        adj = d0[P] (= ma < mb) and r0 = adj ? d1[P-1:0] : d0[P-1:0] in [0, mb), fixing the leading quotient
//        bit qm[P] = 1 upfront.
//      - Six radix-4 stages at P = 11: NS = P/2 + 1 stages (down from (P+2)/2 + 1 = 7) compute the P remaining
//        fractional quotient bits with parity pre-shift XS2 = 2*NS - P in {1, 2}.
//      - Exponent and denormalization shift ahead of the core: since adj = (ma < mb) is known before the SRT
//        loop, E, ovf, and dsh are computed in parallel with the SRT stages.
//      - Clamped-width denormalizer shift: clamps dsh to DL = $clog2(P + 2) bits (dsh_c) with a saturating
//        dsh_big guard instead of shifting by the full EW-bit dsh.
module fdiv #(
  parameter int W = 5,
  parameter int P = 11
) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K   = W + P;
  localparam integer T   = P - 1;
  localparam integer EW  = W + P + 1;
  localparam integer NS  = P / 2 + 1;                 // 6 radix-4 stages at P = 11 (vs 7 in fdivp_srt)
  localparam integer XS2 = 2 * NS - P;                // 1 for odd P, 2 for even P
  localparam integer RW  = P + 6;
  localparam integer DL  = $clog2(P + 2);

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

  // ---- normalizers (D3): P - 1 affine stages (100% sv_comb-compatible)
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

  logic [P-1:0] ma, mb, mbn;
  assign ma  = na_r[P-1];
  assign mb  = nb_r[P-1];
  assign mbn = ~mb;

  // ---- pre-align: parallel d0 = ma - mb, d1 = 2*ma - mb; adj = (ma < mb); r0 in [0, mb)
  logic         adj;
  logic [P:0]   d0, d1;
  logic [P-1:0] r0;
  assign d0  = {1'b0, ma} - {1'b0, mb};
  assign d1  = {ma, 1'b0} - {1'b0, mb};
  assign adj = d0[P];
  assign r0  = adj ? d1[P-1:0] : d0[P-1:0];

  // ---- exponent (computed in parallel with SRT core!)
  logic [W-1:0]  onesW, emw;
  logic [EW-1:0] E, dsh;
  logic          ovf;
  assign onesW = '1;
  assign emw   = onesW >> 1;
  assign E     = ya_r[P-1] - yb_r[P-1] + emw - adj;
  assign ovf   = ~E[EW-1] & ((|E[EW-2:W]) | (&E[W-1:0]));
  assign dsh   = (~E[EW-1] & (|E)) ? 0 : (1 - E);

  // ---- divisor multiples (dv = 8*mb)
  logic [RW-1:0] dv, d2, nd1, nd2, zw;
  logic [RW+1:0] xw;
  assign dv  = {3'b000, mb, 3'b000};
  assign d2  = {2'b00, mb, 4'b0000};
  assign nd1 = {3'b111, mbn, 3'b000};
  assign nd2 = {2'b11, mbn, 4'b1000};
  assign zw  = '0;
  assign xw  = {3'b000, r0, 5'b00000};

  // ---- selection constants (Wally)
  logic [2:0] da;
  logic [6:0] t2, t1, t0, tm;
  assign da = dv[P+1:P-1];
  assign t2 = da[2] ? (da[1] ? (da[0] ? 7'd87 : 7'd86) : (da[0] ? 7'd84 : 7'd82))
                    : (da[1] ? (da[0] ? 7'd81 : 7'd80) : (da[0] ? 7'd78 : 7'd76));
  assign t1 = da[2] ? (da[1] ? (da[0] ? 7'd72 : 7'd72) : (da[0] ? 7'd72 : 7'd70))
                    : (da[1] ? (da[0] ? 7'd70 : 7'd70) : (da[0] ? 7'd68 : 7'd68));
  assign t0 = da[2] ? (da[1] ? (da[0] ? 7'd56 : 7'd56) : (da[0] ? 7'd56 : 7'd58))
                    : (da[1] ? (da[0] ? 7'd58 : 7'd58) : (da[0] ? 7'd60 : 7'd60));
  assign tm = da[2] ? (da[1] ? (da[0] ? 7'd41 : 7'd42) : (da[0] ? 7'd44 : 7'd46))
                    : (da[1] ? (da[0] ? 7'd47 : 7'd48) : (da[0] ? 7'd50 : 7'd51));

  // ---- NS = P/2 + 1 radix-4 SRT stages (6 at P = 11)
  logic [NS:0][RW-1:0]   ws, wc;
  logic [NS:0][P+1:0]    u, um;
  logic [NS-1:0][7:0]    es;
  logic [NS-1:0][6:0]    yb;
  logic [NS-1:0]         g2, g1, g0, gm;
  logic [NS-1:0][RW-1:0] mm, sm, cy;
  logic [NS-1:0]         uq1, uq0, um1, um0;
  logic [NS-1:0][P-1:0]  us, ums;
  assign ws[0] = xw[RW+XS2-1:XS2];
  assign wc[0] = '0;
  assign u[0]  = '0;
  assign um[0] = '1;
  genvar k;
  generate
    for (k = 0; k < NS; k = k + 1) begin : srt
      assign es[k] = ws[k][P+5:P-2] + wc[k][P+5:P-2];
      assign yb[k] = es[k][7:1] ^ 7'b1000000;
      assign g2[k] = (yb[k] >= t2);
      assign g1[k] = (yb[k] >= t1);
      assign g0[k] = (yb[k] >= t0);
      assign gm[k] = (yb[k] >= tm);
      assign mm[k] = g2[k] ? nd2 : (g1[k] ? nd1 : (g0[k] ? zw : (gm[k] ? dv : d2)));
      assign sm[k] = ws[k] ^ wc[k] ^ mm[k];
      assign cy[k] = (ws[k] & wc[k]) | (ws[k] & mm[k]) | (wc[k] & mm[k]);
      assign ws[k+1] = {sm[k][RW-3:0], 2'b00};
      assign wc[k+1] = {cy[k][RW-4:3], g1[k], 5'b00000};
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

  logic [RW-1:0] rs;
  logic [P-1:0]  ql;
  logic [P:0]    qm;
  logic          rnz;
  assign rs  = ws[NS] + wc[NS];
  assign ql  = rs[RW-1] ? um[NS][P-1:0] : u[NS][P-1:0];
  assign qm  = {1'b1, ql};
  assign rnz = |rs;

  // ---- clamped-width denormalize and round to nearest even (sv_comb-compatible!)
  logic          dsh_big;
  logic [DL-1:0] dsh_c;
  logic [P:0]    qs;
  logic          inc;
  logic [W-1:0]  ef;
  logic [K-2:0]  mag;
  assign dsh_big = (dsh >= (P + 1));
  assign dsh_c   = dsh_big ? (P + 1) : dsh[DL-1:0];
  assign qs      = dsh_big ? zw[P:0] : (qm >> dsh_c);
  assign inc     = qs[0] & (rnz | ((qs << dsh_c) != qm) | qs[1]);
  assign ef      = (~E[EW-1] & (|E)) ? E[W-1:0] : 0;
  assign mag     = {ef, qs[P-1:1]} + inc;

  // ---- output (D3)
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
