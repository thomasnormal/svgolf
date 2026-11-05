// H2 G0 variant t4: FLAT. The fdiv16 reference as ONE netlist of continuous assigns (no generate loop, no 2-D array, no
// always_comb), written for the tactic fast path "a flat netlist leaves nothing" (PROVING.md sections 2.1, 12): when every
// site is plain and there is no free parameter, sv_structure and sv_equations DECIDE their obligations, linear in the
// number of sites. With a generate loop or an always_comb the same design needs more than 2,000,000 x 1000 heartbeats
// in sv_structure (measured: t3). Same circuit as tasks/fdiv16/reference/fdiv16.sv; the differences:
//   (R1) every part-selected vector is declared with localparam bounds (a part select over a literally-bounded
//        declaration is a "legacy part select", refused);
//   (R2) the 13 restoring steps are written out (r0..r13, d0..d12, qq bits), and the run-time shift qm >> sh with the
//        sticky test (qs << sh) != qm is a 4-stage mux shifter that collects the sticky bit; constant shifts stay
//        shifts (a concatenation inside ?: is outside the fragment of sv_equations, a constant shift is inside);
//   (R3) every comparison is written into a one-bit signal first, concatenations used as operands are named, the
//        exponent sum uses implicit zero extension, and the special-case table is a ?: chain over named words.
module fdiv16 (
  input  logic [15:0] a,
  input  logic [15:0] b,
  output logic [15:0] q
);
  localparam integer W16 = 16;
  localparam integer W11 = 11;
  localparam integer W12 = 12;
  localparam integer W13 = 13;
  localparam integer W15 = 15;
  localparam integer W7  = 7;

  logic [W16-1:0] aw, bw;
  assign aw = a;
  assign bw = b;

  logic        sa, sb, s;
  logic [4:0]  ea, eb;
  logic [9:0]  fa, fb;
  assign sa = aw[15];
  assign sb = bw[15];
  assign s  = sa ^ sb;
  assign ea = aw[14:10];
  assign eb = bw[14:10];
  assign fa = aw[9:0];
  assign fb = bw[9:0];

  logic a_nan, b_nan, a_inf, b_inf, a_zero, b_zero;
  assign a_nan  = (ea == 5'd31) && (fa != 10'd0);
  assign b_nan  = (eb == 5'd31) && (fb != 10'd0);
  assign a_inf  = (ea == 5'd31) && (fa == 10'd0);
  assign b_inf  = (eb == 5'd31) && (fb == 10'd0);
  assign a_zero = (ea == 5'd0) && (fa == 10'd0);
  assign b_zero = (eb == 5'd0) && (fb == 10'd0);

  logic          nza, nzb;
  logic [W11-1:0] ma, mb;
  logic [4:0]    xa, xb;
  assign nza = ea != 5'd0;
  assign nzb = eb != 5'd0;
  assign ma  = {nza, fa};
  assign mb  = {nzb, fb};
  assign xa  = nza ? ea : 5'd1;
  assign xb  = nzb ? eb : 5'd1;

  logic [W11-1:0] na1, na2, na3, na4;
  logic           za8, za4, za2, za1;
  assign za8 = (ma[10:3] == 8'd0);
  assign na1 = za8 ? (ma << 8) : ma;
  assign za4 = (na1[10:7] == 4'd0);
  assign na2 = za4 ? (na1 << 4) : na1;
  assign za2 = (na2[10:9] == 2'd0);
  assign na3 = za2 ? (na2 << 2) : na2;
  assign za1 = ~na3[10];
  assign na4 = za1 ? (na3 << 1) : na3;

  logic [W11-1:0] nb1, nb2, nb3, nb4;
  logic           zb8, zb4, zb2, zb1;
  assign zb8 = (mb[10:3] == 8'd0);
  assign nb1 = zb8 ? (mb << 8) : mb;
  assign zb4 = (nb1[10:7] == 4'd0);
  assign nb2 = zb4 ? (nb1 << 4) : nb1;
  assign zb2 = (nb2[10:9] == 2'd0);
  assign nb3 = zb2 ? (nb2 << 2) : nb2;
  assign zb1 = ~nb3[10];
  assign nb4 = zb1 ? (nb3 << 1) : nb3;

  logic [3:0] lza, lzb;
  assign lza = {za8, za4, za2, za1};
  assign lzb = {zb8, zb4, zb2, zb1};

  logic [W12-1:0] nb12;
  logic [W12-1:0] r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13;
  logic [W12-1:0] d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12;
  logic [W13-1:0] qq;
  assign nb12 = {1'b0, nb4};
  assign r0   = {1'b0, na4};
  assign qq[12] = (r0 >= nb12);
  assign d0    = r0 - nb12;
  assign r1   = qq[12] ? (d0 << 1) : (r0 << 1);
  assign qq[11] = (r1 >= nb12);
  assign d1    = r1 - nb12;
  assign r2   = qq[11] ? (d1 << 1) : (r1 << 1);
  assign qq[10] = (r2 >= nb12);
  assign d2    = r2 - nb12;
  assign r3   = qq[10] ? (d2 << 1) : (r2 << 1);
  assign qq[9] = (r3 >= nb12);
  assign d3    = r3 - nb12;
  assign r4   = qq[9] ? (d3 << 1) : (r3 << 1);
  assign qq[8] = (r4 >= nb12);
  assign d4    = r4 - nb12;
  assign r5   = qq[8] ? (d4 << 1) : (r4 << 1);
  assign qq[7] = (r5 >= nb12);
  assign d5    = r5 - nb12;
  assign r6   = qq[7] ? (d5 << 1) : (r5 << 1);
  assign qq[6] = (r6 >= nb12);
  assign d6    = r6 - nb12;
  assign r7   = qq[6] ? (d6 << 1) : (r6 << 1);
  assign qq[5] = (r7 >= nb12);
  assign d7    = r7 - nb12;
  assign r8   = qq[5] ? (d7 << 1) : (r7 << 1);
  assign qq[4] = (r8 >= nb12);
  assign d8    = r8 - nb12;
  assign r9   = qq[4] ? (d8 << 1) : (r8 << 1);
  assign qq[3] = (r9 >= nb12);
  assign d9    = r9 - nb12;
  assign r10   = qq[3] ? (d9 << 1) : (r9 << 1);
  assign qq[2] = (r10 >= nb12);
  assign d10    = r10 - nb12;
  assign r11   = qq[2] ? (d10 << 1) : (r10 << 1);
  assign qq[1] = (r11 >= nb12);
  assign d11    = r11 - nb12;
  assign r12   = qq[1] ? (d11 << 1) : (r11 << 1);
  assign qq[0] = (r12 >= nb12);
  assign d12    = r12 - nb12;
  assign r13   = qq[0] ? (d12 << 1) : (r12 << 1);

  logic           adj;
  logic [W12-1:0] qm;
  logic           rnz, st0;
  assign adj = ~qq[12];
  assign qm  = qq[12] ? qq[12:1] : qq[11:0];
  assign rnz = r13 != 12'd0;
  assign st0 = (qq[12] & qq[0]) | rnz;

  logic [W7-1:0] eoff;
  assign eoff = xa + lzb + 7'd47 - xb - lza - adj;

  logic          ovf, nrm, big;
  logic [W7-1:0] dsh;
  logic [3:0]    sh;
  assign ovf = (eoff >= 7'd63);
  assign nrm = (eoff >= 7'd33);
  assign dsh = 7'd33 - eoff;
  assign big = (dsh >= 7'd12);
  assign sh  = nrm ? 4'd0 : (big ? 4'd12 : dsh[3:0]);

  logic [W12-1:0] q1, q2, q3, qs;
  logic           t1, t2, t3, st1, rb, inc;
  assign q1  = sh[0] ? (qm >> 1) : qm;
  assign t1  = sh[0] & qm[0];
  assign q2  = sh[1] ? (q1 >> 2) : q1;
  assign t2  = t1 | (sh[1] & (|q1[1:0]));
  assign q3  = sh[2] ? (q2 >> 4) : q2;
  assign t3  = t2 | (sh[2] & (|q2[3:0]));
  assign qs  = sh[3] ? (q3 >> 8) : q3;
  assign st1 = st0 | t3 | (sh[3] & (|q3[7:0]));
  assign rb  = qs[0];
  assign inc = rb & (st1 | qs[1]);

  logic [4:0]     ef;
  logic [W15-1:0] efq, mag;
  assign ef  = nrm ? eoff[4:0] : 5'd0;
  assign efq = {ef, qs[10:1]};
  assign mag = efq + inc;

  logic        c_nan, c_inf, c_zero;
  logic [15:0] w_nan, w_inf, w_zero, w_fin;
  assign c_nan  = a_nan | b_nan | (a_inf & b_inf) | (a_zero & b_zero);
  assign c_inf  = a_inf | b_zero;
  assign c_zero = b_inf | a_zero;
  assign w_nan  = 16'h7E00;
  assign w_inf  = {s, 15'h7C00};
  assign w_zero = {s, 15'h0000};
  assign w_fin  = {s, mag};
  assign q = c_nan ? w_nan : (c_inf ? w_inf : (c_zero ? w_zero : (ovf ? w_inf : w_fin)));
endmodule
