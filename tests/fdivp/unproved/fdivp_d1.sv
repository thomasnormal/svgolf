// fdiv #(W, P): IEEE 754 division for every binary format, round to nearest even, canonical NaN, full subnormals.
// W = exponent field width (>= 2), P = precision including the implicit bit (>= 2), storage K = W + P.
// binary16 = (5, 11), bfloat16 = (8, 8), binary32 = (8, 24), the smallest format is (2, 2).
// One generate-based family; the datapath is the flat netlist of the former 16-bit task (H2) with its counts as parameters:
//   unpack and classify -> NS = $clog2(P) normalizer stages (shift by 2^(NS-1-i) when the top bits are zero)
//   -> P + 2 restoring-division steps -> quotient normalization (adj, qm, st0) -> exponent sum eoff (EW bits, offset
//   OFF, a multiple of 2^W so that eoff[W-1:0] is the result exponent field) -> shift amount sh (0 .. P + 1)
//   -> SW = $clog2(P + 2) shifter stages with a sticky bit -> round-to-nearest-even increment -> special cases.
module fdiv #(
  parameter int W = 5,
  parameter int P = 11
) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam int K    = W + P;
  localparam int T    = P - 1;
  localparam int NS   = $clog2(P);
  localparam int SW   = $clog2(P + 2);
  localparam int OFFM = (2**(W-1) + P + 2**W - 3) / 2**W;
  localparam int OFF  = OFFM * 2**W;
  localparam int EW   = $clog2(2**W + 2**(W-1) + P - 4 + OFF);
  localparam [EW-1:0] KOV   = 2**(W-1) - 1 + OFF;     // emax + OFF
  localparam [EW-1:0] NRMTH = OFF + 1;                // eoff >= OFF + 1: a normal result
  localparam [EW-1:0] OVFTH = OFF + 2**W - 1;         // eoff >= OFF + 2^W - 1: overflow
  localparam [EW-1:0] BIGTH = P + 1;                  // dsh >= P + 1: shift out everything
  localparam [SW-1:0] SHMAX = P + 1;

  // ---- unpack and classify
  logic [W-1:0] ea, eb;
  logic [T-1:0] fa, fb;
  logic         sa, sb, s;
  assign sa = a[K-1];
  assign sb = b[K-1];
  assign s  = sa ^ sb;
  assign ea = a[K-2:T];
  assign eb = b[K-2:T];
  assign fa = a[T-1:0];
  assign fb = b[T-1:0];

  logic eall_a, eall_b, ez_a, ez_b, fz_a, fz_b;
  assign eall_a = &ea;
  assign eall_b = &eb;
  assign ez_a   = ~|ea;
  assign ez_b   = ~|eb;
  assign fz_a   = ~|fa;
  assign fz_b   = ~|fb;

  logic a_nan, b_nan, a_inf, b_inf, a_zero, b_zero;
  assign a_nan  = eall_a & ~fz_a;
  assign b_nan  = eall_b & ~fz_b;
  assign a_inf  = eall_a & fz_a;
  assign b_inf  = eall_b & fz_b;
  assign a_zero = ez_a & fz_a;
  assign b_zero = ez_b & fz_b;

  logic nza, nzb;
  logic [P-1:0] ma, mb;
  logic [W-1:0] xa, xb;
  assign nza = ~ez_a;
  assign nzb = ~ez_b;
  assign ma  = {nza, fa};
  assign mb  = {nzb, fb};
  assign xa  = nza ? ea : 1;
  assign xb  = nzb ? eb : 1;

  // ---- normalizers: stage i shifts left by 2^(NS-1-i) when the top 2^(NS-1-i) bits are zero
  logic [NS:0][P-1:0] na_r, nb_r;
  logic [NS-1:0]      lza, lzb;
  assign na_r[0] = ma;
  assign nb_r[0] = mb;
  genvar i;
  generate
    for (i = 0; i < NS; i = i + 1) begin : norm
      localparam int SH = 2**(NS-1-i);
      logic top_a, top_b;
      assign top_a = ~|na_r[i][P-1:P-SH];
      assign top_b = ~|nb_r[i][P-1:P-SH];
      assign lza[NS-1-i] = top_a;
      assign lzb[NS-1-i] = top_b;
      assign na_r[i+1] = top_a ? (na_r[i] << SH) : na_r[i];
      assign nb_r[i+1] = top_b ? (nb_r[i] << SH) : nb_r[i];
    end
  endgenerate
  logic [P-1:0] na4, nb4;
  assign na4 = na_r[NS];
  assign nb4 = nb_r[NS];

  // ---- P + 2 restoring-division steps
  logic [P:0]         nbx;
  logic [P+2:0][P:0]  rr;
  logic [P+1:0][P:0]  dd;
  logic [P+1:0]       ge;
  logic [P+1:0]       qq;
  assign nbx   = {1'b0, nb4};
  assign rr[0] = {1'b0, na4};
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : div
      assign ge[k]      = (rr[k] >= nbx);
      assign dd[k]      = rr[k] - nbx;
      assign qq[P+1-k]  = ge[k];
      assign rr[k+1]    = ge[k] ? (dd[k] << 1) : (rr[k] << 1);
    end
  endgenerate

  // ---- quotient normalization
  logic         adj, rnz, st0;
  logic [P:0]   qm;
  assign adj = ~qq[P+1];
  assign qm  = qq[P+1] ? qq[P+1:1] : qq[P:0];
  assign rnz = |rr[P+2];
  assign st0 = (qq[P+1] & qq[0]) | rnz;

  // ---- exponent sum and shift amount
  logic [EW-1:0] eoff, dsh;
  logic          ovf, nrm, big;
  logic [SW-1:0] sh;
  assign eoff = xa + lzb + KOV - xb - lza - adj;
  assign ovf  = (eoff >= OVFTH);
  assign nrm  = (eoff >= NRMTH);
  assign dsh  = NRMTH - eoff;
  assign big  = (dsh >= BIGTH);
  assign sh   = nrm ? '0 : (big ? SHMAX : dsh[SW-1:0]);

  // ---- shifter with a sticky bit: stage j shifts right by 2^j when sh[j]
  logic [SW:0][P:0] qsh;
  logic [SW:0]      tt;
  assign qsh[0] = qm;
  assign tt[0]  = 1'b0;
  genvar j;
  generate
    for (j = 0; j < SW; j = j + 1) begin : shf
      localparam int SJ = 2**j;
      assign qsh[j+1] = sh[j] ? (qsh[j] >> SJ) : qsh[j];
      assign tt[j+1]  = tt[j] | (sh[j] & (|qsh[j][SJ-1:0]));
    end
  endgenerate
  logic [P:0] qs;
  logic       st1, rb, inc;
  assign qs  = qsh[SW];
  assign st1 = st0 | tt[SW];
  assign rb  = qs[0];
  assign inc = rb & (st1 | qs[1]);

  // ---- round to nearest even by adding the increment to {exponent, fraction}
  logic [W-1:0]   ef;
  logic [K-2:0]   efq, mag;
  assign ef  = nrm ? eoff[W-1:0] : '0;
  assign efq = {ef, qs[P-1:1]};
  assign mag = efq + inc;

  // ---- special cases and the output
  logic c_nan, c_inf, c_zero;
  logic [K-1:0] w_nan, w_inf, w_zero, w_fin;
  assign c_nan  = a_nan | b_nan | (a_inf & b_inf) | (a_zero & b_zero);
  assign c_inf  = a_inf | b_zero;
  assign c_zero = b_inf | a_zero;
  assign w_nan  = {1'b0, {W{1'b1}}, 1'b1, {(T-1){1'b0}}};
  assign w_inf  = {s, {W{1'b1}}, {T{1'b0}}};
  assign w_zero = {s, {(K-1){1'b0}}};
  assign w_fin  = {s, mag};
  assign q = c_nan ? w_nan : (c_inf ? w_inf : (c_zero ? w_zero : (ovf ? w_inf : w_fin)));
endmodule
