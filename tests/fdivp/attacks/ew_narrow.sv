// ATTACK for task fdivp: the reference (tasks/fdivp/reference/fdivp.sv) with ONE change.
// the exponent register is W + 2 bits instead of W + P + 1: right for every format whose exponent range fits (1.5 * 2^W + P < 2^(W+1), true at (5, 11), (8, 8), (8, 24), (11, 53)), wrong when P is large against W, e.g. (2, 30), (3, 60).
//
// fdiv #(W, P), word-level family form (D3): the same divider as D2 with every bit-level plain site folded into a
// vector site or a generate family. 34 sites: unpack/classify 6, normalizer 4 row-0 + 4 family, division 2 + 3 family,
// quotient 2, exponent 5, denormalizer/round 4, output 3 + 1 family. Only constructs the sv_comb tactics read.
//   normalizer:  P - 1 one-bit stages (an EW-bit register counts the shifts down)
//   division:    P + 2 restoring steps, quotient bit k written by a comparison
//   exponent:    E = ya - yb + emax - adj (EW = W + P + 1 bits, two's complement, no offset);
//                nrm = E >= 1 (sign clear and nonzero), ovf = E >= 2^W - 1
//   denormalize: qs = qm >> dsh with dsh = 1 - E when E <= 0 (any amount: a shift of >= P + 1 empties qm),
//                sticky by (qs << dsh) != qm
//   round to nearest even by adding the increment to {exponent, fraction}; the fields of the result by case.
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
  localparam integer EW = W + 2;

  // ---- unpack and classify
  logic s, ea_nz, eb_nz, c_nan, c_inf, c_zero;
  assign s     = a[K-1] ^ b[K-1];
  assign ea_nz = |a[K-2:T];
  assign eb_nz = |b[K-2:T];
  assign c_nan  = ((&a[K-2:T]) & (|a[T-1:0])) | ((&b[K-2:T]) & (|b[T-1:0]))
                | ((&a[K-2:T]) & ~(|a[T-1:0]) & (&b[K-2:T]) & ~(|b[T-1:0]))
                | (~ea_nz & ~(|a[T-1:0]) & ~eb_nz & ~(|b[T-1:0]));
  assign c_inf  = ((&a[K-2:T]) & ~(|a[T-1:0])) | (~eb_nz & ~(|b[T-1:0]));
  assign c_zero = ((&b[K-2:T]) & ~(|b[T-1:0])) | (~ea_nz & ~(|a[T-1:0]));

  // ---- normalizers: P - 1 one-bit stages; the EW-bit register counts the shifts down
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

  // ---- P + 2 restoring-division steps
  logic [P:0]         nbx;
  logic [P+2:0][P:0]  rr;
  logic [P+1:0][P:0]  dd;
  logic [P+1:0]       qq;
  assign nbx   = {1'b0, nb_r[P-1]};
  assign rr[0] = {1'b0, na_r[P-1]};
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : div
      assign qq[P+1-k] = (rr[k] >= nbx);
      assign dd[k]     = rr[k] - nbx;
      assign rr[k+1]   = qq[P+1-k] ? (dd[k] << 1) : (rr[k] << 1);
    end
  endgenerate

  // ---- quotient normalization (st0 = (qq[P+1] & qq[0]) | (rr[P+2] != 0) is used inline; adj must be a 1-bit signal:
  // `~qq[P+1]` inside the EW-bit sum would be complemented AFTER the extension to EW bits)
  logic       adj;
  logic [P:0] qm;
  assign adj = ~qq[P+1];
  assign qm  = qq[P+1] ? qq[P+1:1] : qq[P:0];

  // ---- exponent (two's complement, EW bits): E = ya - yb + emax - adj; emax = 011..1 (W bits)
  logic [W-1:0]  onesW, emw;
  logic [EW-1:0] E, dsh;
  logic          ovf;
  assign onesW = '1;
  assign emw   = onesW >> 1;
  assign E     = ya_r[P-1] - yb_r[P-1] + emw - adj;
  assign ovf   = ~E[EW-1] & ((|E[EW-2:W]) | (&E[W-1:0]));
  assign dsh   = (~E[EW-1] & (|E)) ? 0 : (1 - E);

  // ---- denormalize, round to nearest even
  logic [P:0]   qs;
  logic         inc;
  logic [W-1:0] ef;
  logic [K-2:0] mag;
  assign qs  = qm >> dsh;
  assign inc = qs[0] & ((qq[P+1] & qq[0]) | (|rr[P+2]) | ((qs << dsh) != qm) | qs[1]);
  assign ef  = (~E[EW-1] & (|E)) ? E[W-1:0] : 0;
  assign mag = {ef, qs[P-1:1]} + inc;

  // ---- output: fields by case (nan > inf > zero > overflow > finite)
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
