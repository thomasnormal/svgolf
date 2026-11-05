// ATTACK for task fdivp: the Newton reference (tasks/fdivp/reference/fdivp_newton.sv) with ONE change.
// one Newton step fewer (NI = $clog2((P + 9) / 8)): no step at all for P <= 6, one too few above. Right at P = 2 (the linear estimate is close enough there), wrong from P = 3 on.
//
// fdiv #(W, P), Newton-Raphson form: a second, independent divider for task fdivp. It is the reference D3
// (tasks/fdivp/reference/fdivp.sv) with its P + 2 restoring steps replaced by a reciprocal, a quotient estimate
// and an exact correction; unpack/classify, the normalizers, the exponent, the denormalizer, the rounding and the
// output stage are D3's, so the core has the contract of D3's quotient `qq` and sticky `|rr[P+2]`:
//
//   qq  = floor(ma * 2^(P+1) / mb)      (P + 2 bits; 2^P < qq < 2^(P+2): a P-bit significand and a round bit,
//                                         plus one more bit when ma >= mb)
//   rnz = (ma * 2^(P+1) mod mb) != 0    (the sticky of the division)
//
// for the normalized significands ma, mb in [2^(P-1), 2^P). The exact quotient sits in [qq, qq + 1) and equals qq
// iff rnz = 0, so the round bit, the sticky and the tie test of round-to-nearest-even are exact: the same facts
// the rounding certificate certF (section CertF of reference/fdivp.lean) checks with a multiplication and a comparison.
//
// Proved for every W, P >= 2 (reference/fdivp_newton.lean): the sv_comb tactics read the run-time `*` and the
// `$clog2` localparam NI (a Newton count is logarithmic in P, so it cannot be affine; svgolf/PROVING.md section 4),
// and its section NwCore bounds the error of the core for every P. ls-sv loads it; the extractor reads it
// with no unsupported node at the task's probe points except D3's: the empty `lo` loop at P = 2.
//
// The core, in fixed point (d = mb / 2^(P-1) in [1, 2), x = ma / 2^(P-1) in [1, 2), Q = qq = floor(x/d * 2^(P+1))):
//
//   1. r0 = 45/32 - 15/32 * d: the linear minimax approximation of 1/d on [1, 2] (24/17 - 8/17 d, relative error
//      1/17) with its coefficients rounded to 5 fraction bits. Its relative error e0 = 1 - d * r0 satisfies
//      |e0| <= 1/16 on all of [1, 2] (e0 = +1/16 at d = 1 and d = 2, -7/128 at d = 3/2). It is exact at the working
//      precision F = P + 4 for every P (it has P - 1 + 5 = F fraction bits), and it needs no table and no multiplier:
//      15 * mb = 16 * mb - mb.
//   2. NI Newton steps r <- r * (2 - d * r), every product truncated to F fraction bits (all truncations round DOWN):
//        u  = the top F + 1 bits of ~(d*r), the one's complement of the exact product (1 integer bit): 2 - x is
//             ~x + ulp, so u is 2 - d*r rounded down to F fraction bits (below it by at most 2^-F), with no adder;
//        r' = r * u, truncated to F fraction bits.
//      Error: e' = 1 - d*r' = e^2 + d*r*du + d*dr' with du, dr' in [0, 2^-F], so 0 <= e' < e^2 + 3.07 * 2^-F (d < 2,
//      d*r <= 1 + 1/16). Every step leaves r <= 1/d (r * (2 - d*r) = 1/d - d * (1/d - r)^2), so e' >= 0: from r1 on
//      the estimate is one-sided, and d*r <= 1 makes the truncation term < 3 * 2^-F = 3/4 * 2^-(P+2). By induction,
//      for every k >= 1:  0 <= e_k <= 2^-(2^(k+2)) + 2^-(P+2)  (= 16^-(2^k) + 4 * 2^-F). Base: e1 < 2^-8 +
//      3.07 * 2^-(P+4). Step, with a = 16^-(2^k) <= 2^-8, b = 2^-(P+2) <= 2^-4: (a + b)^2 + 3/4 b <= a^2 + b
//      because 2a + b + 3/4 <= 1.
//   3. NI = the least K >= 1 with 2^(K+2) >= P + 2, i.e. max(1, clog2(P + 2) - 2) = clog2((P + 9) / 8) + 1:
//        P = 2..6: 1,  7..14: 2,  15..30: 3,  31..62: 4,  63..126: 5   (binary16 2, bfloat16 2, binary32 3,
//        binary64 4, binary128 5).
//      Then e_NI <= 2^-(P+2) + 2^-(P+2) = 2^-(P+1).
//   4. qf = floor(x * r * 2^(P+1)) = (ma * r) >> (F - 2). The exact quotient is above it by
//        x/d * 2^(P+1) * e_NI + (truncation) < 2^(P+2) * 2^-(P+1) + 1 = 3,
//      so Q is one of the three candidates qf, qf + 1, qf + 2 (q0 - 1, q0, q0 + 1 around q0 = qf + 1).
//   5. Exact correction: rm = ma * 2^(P+1) - qf * mb lies in [0, 3 mb) and 3 mb < 2^(P+2), so it is computed modulo
//      2^(P+2) (only the low P + 2 bits of qf * mb, and of ma * 2^(P+1), which is ma[0] at bit P + 1, take part).
//      The candidate is qf + [rm >= mb] + [rm >= 2 mb] (its remainder test is 0 <= rm - j * mb < mb), and its
//      remainder is zero iff rm is 0, mb or 2 mb.
//
// Widths: r (F + 1 = P + 5 bits, value in (0.45, 1]), d*r (P + F = 2P + 4 bits, value < 2), u (F + 1 bits),
// r*u (2F + 1 bits, value <= 1/d <= 1), ma*r (P + F bits), qf, rm (P + 2 bits). Per Newton step: a P x (F + 1)
// product and an (F + 1) x (F + 1) product; then one P x (F + 1) product and one (P + 2)-bit truncated product.
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
  localparam integer F  = P + 4;                      // working precision: fraction bits of r
  localparam integer NI = $clog2((P + 9) / 8) + 0;    // Newton steps: the least NI >= 1 with 2^(NI+2) >= P + 2

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
  logic [P-1:0] ma, mb;
  assign ma = na_r[P-1];
  assign mb = nb_r[P-1];

  // ---- 1. initial reciprocal r0 = 45/32 - 15/32 * d, in F fraction bits: 45 * 2^(P-1) - 16 * mb + mb
  logic [P:0] zr;                                     // P + 1 zero bits (for the constant products below)
  assign zr = '0;
  logic [NI:0][F:0] r;
  assign r[0] = {6'd45, zr[P-2:0]} - {mb, 4'd0} + mb;

  // ---- 2. NI Newton steps r <- r * (2 - d * r), truncated to F fraction bits
  logic [NI-1:0][P+F-1:0] dr;                         // d * r exactly: P - 1 + F fraction bits, value < 2
  logic [NI-1:0][F:0]     u;                          // 2 - d * r, truncated to F fraction bits
  logic [NI-1:0][2*F:0]   ru;                         // r * u: 2F fraction bits, value <= 1/d <= 1
  genvar k;
  generate
    for (k = 0; k < NI; k = k + 1) begin : newton
      assign dr[k]  = mb * r[k];
      assign u[k]   = ~dr[k][P+F-1:P-1];
      assign ru[k]  = r[k] * u[k];
      assign r[k+1] = ru[k][2*F:F];
    end
  endgenerate

  // ---- 3. quotient estimate qf = floor(ma * r * 2^(P+1) / 2^(P-1)) = (ma * r) >> (F - 2), at most 2 below Q
  logic [P+F-1:0] qp;
  logic [P+1:0]   qf;
  assign qp = ma * r[NI];
  assign qf = qp[P+F-1:F-2];

  // ---- 4. exact correction: rm = ma * 2^(P+1) - qf * mb in [0, 3 mb), modulo 2^(P+2); Q = qf + j, j = 0, 1, 2
  logic [P+1:0] qb, rm, qq;
  logic         ge1, ge2, rnz;
  // qe is qf, except when an exponent field is all ones (an infinite or NaN operand), where the output stage never
  // reads the core. Perturbing the estimate there keeps every value above for finite operands, and makes the facts that
  // only the Newton error bound proves (ge2 = 0 and rm < 2 mb for a nonzero divisor, |rm = 1) false over all inputs.
  // Without it, ABC's `&fraig -x` in the pinned scoring flow spends a SAT problem on each such near-constant node and
  // does not finish at (5, 11) in 1800 s; with it, the flow finishes in 66 s.
  logic [P+1:0] qe;
  assign qe  = ((&a[K-2:T]) | (&b[K-2:T])) ? (qf - a[0] - b[0]) : qf;
  assign qb  = qe * mb;
  assign rm  = {ma[0], zr} - qb;
  assign ge1 = (rm >= mb);
  assign ge2 = (rm >= {mb, 1'b0});
  assign qq  = qe + ge1 + ge2;
  assign rnz = (rm != mb) & (rm != {mb, 1'b0}) & (|rm);

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

  // ---- denormalize, round to nearest even (D3, with the Newton core's sticky rnz)
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
