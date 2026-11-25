// fdiv #(W, P), the fragment-friendly family (D2): the same divider as fdivp.sv with every construct the sv_comb
// tactics refuse today replaced by an affine one. No $clog2, no 2**e, no localparam beyond integer affine ones, no
// replication, no genvar value, no sized localparam: counts are P-affine (P - 1 normalizer stages, P + 2 division
// steps, P + 1 denormalizer stages) and the exponent datapath is EW = W + P + 1 bits wide, offset by OFF = 2^(W+P).
//   normalizer a (b alike): stage i shifts left by one when the top bit is zero; an EW-bit register counts the shifts
//   division: P + 2 restoring steps
//   eoff = (xa - lza) - (xb - lzb) + emax + OFF - adj
//   denormalizer: stage s shifts qm right by one (sticky collects) while e[s] < OFF + 1, e[s+1] = e[s] + 1: at most P + 1 shifts
//   round to nearest even, special cases as before.
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

  // ---- normalizers: P - 1 stages of a one-bit left shift; the exponent register counts them down
  logic [P-1:0][P-1:0]  na_r, nb_r;
  logic [P-1:0][EW-1:0] ya_r, yb_r;
  logic [P-2:0]         za, zb;
  assign na_r[0] = ma;
  assign nb_r[0] = mb;
  assign ya_r[0] = xa;
  assign yb_r[0] = xb;
  genvar i;
  generate
    for (i = 0; i < P - 1; i = i + 1) begin : norm
      assign za[i]     = ~na_r[i][P-1];
      assign zb[i]     = ~nb_r[i][P-1];
      assign na_r[i+1] = za[i] ? (na_r[i] << 1) : na_r[i];
      assign nb_r[i+1] = zb[i] ? (nb_r[i] << 1) : nb_r[i];
      assign ya_r[i+1] = za[i] ? (ya_r[i] - 1) : ya_r[i];
      assign yb_r[i+1] = zb[i] ? (yb_r[i] - 1) : yb_r[i];
    end
  endgenerate
  logic [P-1:0]  na4, nb4;
  logic [EW-1:0] ya, yb;
  assign na4 = na_r[P-1];
  assign nb4 = nb_r[P-1];
  assign ya  = ya_r[P-1];
  assign yb  = yb_r[P-1];

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
      assign ge[k]     = (rr[k] >= nbx);
      assign dd[k]     = rr[k] - nbx;
      assign qq[P+1-k] = ge[k];
      assign rr[k+1]   = ge[k] ? (dd[k] << 1) : (rr[k] << 1);
    end
  endgenerate

  // ---- quotient normalization
  logic         adj, rnz, st0;
  logic [P:0]   qm;
  assign adj = ~qq[P+1];
  assign qm  = qq[P+1] ? qq[P+1:1] : qq[P:0];
  assign rnz = |rr[P+2];
  assign st0 = (qq[P+1] & qq[0]) | rnz;

  // ---- constants as vectors (EW bits): emax + OFF, OFF + 1, OFF + 2^W - 1
  logic [EW-1:0] kv, nrmth, ovfth;
  assign kv[W-2:0]    = '1;
  assign kv[W-1]      = 1'b0;
  assign kv[EW-2:W]   = '0;
  assign kv[EW-1]     = 1'b1;
  assign nrmth[0]     = 1'b1;
  assign nrmth[EW-2:1] = '0;
  assign nrmth[EW-1]  = 1'b1;
  assign ovfth[W-1:0] = '1;
  assign ovfth[EW-2:W] = '0;
  assign ovfth[EW-1]  = 1'b1;

  // ---- exponent sum
  logic [EW-1:0] eoff;
  logic          ovf, nrm;
  assign eoff = ya - yb + kv - adj;
  assign ovf  = (eoff >= ovfth);
  assign nrm  = (eoff >= nrmth);

  // ---- denormalizer: shift right by one (sticky collects) while e < OFF + 1, at most P + 1 times
  logic [P+1:0][EW-1:0] e_r;
  logic [P+1:0][P:0]    q_r;
  logic [P+1:0]         t_r;
  logic [P:0]           act;
  assign e_r[0] = eoff;
  assign q_r[0] = qm;
  assign t_r[0] = 1'b0;
  genvar j;
  generate
    for (j = 0; j < P + 1; j = j + 1) begin : den
      assign act[j]     = (e_r[j] < nrmth);
      assign e_r[j+1]   = act[j] ? (e_r[j] + 1) : e_r[j];
      assign q_r[j+1]   = act[j] ? (q_r[j] >> 1) : q_r[j];
      assign t_r[j+1]   = t_r[j] | (act[j] & q_r[j][0]);
    end
  endgenerate
  logic [P:0] qs;
  logic       st1, rb, inc;
  assign qs  = q_r[P+1];
  assign st1 = st0 | t_r[P+1];
  assign rb  = qs[0];
  assign inc = rb & (st1 | qs[1]);

  // ---- round to nearest even by adding the increment to {exponent, fraction}
  logic [W-1:0]   ef;
  logic [K-2:0]   efq, mag;
  genvar m;
  generate
    for (m = 0; m < W; m = m + 1) begin : efg
      assign ef[m] = eoff[m] & nrm;
    end
  endgenerate
  assign efq = {ef, qs[P-1:1]};
  assign mag = efq + inc;

  // ---- special cases and the output
  logic c_nan, c_inf, c_zero;
  logic [K-1:0] w_nan, w_inf, w_zero, w_fin;
  assign c_nan  = a_nan | b_nan | (a_inf & b_inf) | (a_zero & b_zero);
  assign c_inf  = a_inf | b_zero;
  assign c_zero = b_inf | a_zero;
  assign w_nan[K-1]       = 1'b0;
  assign w_nan[K-2:T]     = '1;
  assign w_nan[T-1]       = 1'b1;
  genvar n;
  generate
    for (n = 0; n < T - 1; n = n + 1) begin : nanz
      assign w_nan[n] = 1'b0;
    end
  endgenerate
  assign w_inf[K-1]       = s;
  assign w_inf[K-2:T]     = '1;
  assign w_inf[T-1:0]     = '0;
  assign w_zero[K-1]      = s;
  assign w_zero[K-2:0]    = '0;
  assign w_fin            = {s, mag};
  assign q = c_nan ? w_nan : (c_inf ? w_inf : (c_zero ? w_zero : (ovf ? w_inf : w_fin)));
endmodule
