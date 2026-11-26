#!/usr/bin/env python3.12
"""Generator of the `gemm` design `fip`: the inner-product form (the 1968 identity that halves the multiplications),
own code.

    python3.12 tasks/gemm/reference/gen_fip.py OUTDIR      # writes OUTDIR/fip.sv and OUTDIR/fip.json

ARCHITECTURE. par's machine (gen.py) with the array's rows rebuilt. For one tile row w and one activation slice x
(E entries, pairs (2t, 2t+1), H = E/2 pairs):

    sum_j w[j] x[j] = sum_t (w[2t] + x[2t+1]) (w[2t+1] + x[2t])  -  sum_t w[2t] w[2t+1]  -  sum_t x[2t] x[2t+1]

so a row has H cells, each one 18 x 18 signed multiplier behind two registered pre-adders (w signed 16 bits plus x
unsigned 16 bits fits 18 bits signed). Everything is exact integer arithmetic modulo 2^SW, SW = 33 + LGE: the true
inner product of a slice is below 2^(31+LGE) in magnitude, so its SW-bit residue sign-extends to the exact value,
which is what the 48-bit accumulator memory adds.

  weight correction      -sum_t w[2t] w[2t+1] of a tile row is computed ONCE per loaded beat by one shared unit
                         (gemm_wcorr: H multipliers 16 x 16 and a registered adder tree) from the beat register the
                         cells load from, and stored in the row's correction register, double-buffered exactly as
                         the weights: the shadow is loaded by the row's load strobe delayed by the unit's latency,
                         the active register follows the swap tag of the row's first cell. The active register IS
                         the start value of the row's sum chain.
  activation correction  sum_t x[2t] x[2t+1] of a slice is computed ONCE per slice (inside the input skew: H
                         multipliers 16 x 16 on the first register of every column, a registered adder tree and a
                         delay line) and travels down the rows one register per row, as the slice does; a row
                         subtracts it where its chain's sum meets the accumulator memory.
  unchanged from par     T = E tiles in the canonical layout, chunks of 2 E vectors, the job sequence, the activation
                         buffer, the loader and the swap tag, the two-block accumulator memory per row, the output
                         stage, the result FIFO and its credits (gen.py's module texts XBUF, SCALE, FIFO, and
                         PAR_TOP with the edits listed in `top_text`).

TIMING (c0 = the cycle a buffer read's data is valid, row i, pair t; "valid in cycle").
  skew: pair t and its tag are delayed t + 1 cycles (par: column j by j + 1), so row i sees pair t in c0 + t + 1 + i
  and the tag one cycle earlier. Cell: pre-adders registered (c0 + t + 2 + i), then product and chain add in one
  cycle, s_out valid c0 + t + 3 + i; the chain advances one cell per cycle; its end is valid in c0 + H + 2 + i, the
  cycle the row writes its accumulator (read one cycle earlier): the accumulate control reaches row 0
  DL = H + 3 cycles after the main sequence issues the read (par: E + 2), and DRAIN = DL + E + 2.
  Activation correction: column registers c0 + 1, products c0 + 2, tree TS = LGE/2 stages (4 values per stage),
  delay line H - TS stages: valid at row 0 in c0 + H + 2, at row i one cycle later per row: the write cycle.
  Weight correction: beat register valid in cycle L (the row's load strobe), products L + 1, tree L + 1 + TS; the
  top delays the load strobes by 1 + TS. The row's correction swaps on its first cell's registered tag (c0 + 1 + i),
  one cycle before the chain's first use of it (c0 + 2 + i); the previous pass used it in c0 + i at the latest.
  The loader's wait for the swap wave is H - 1 (par: E - 1): the tag crosses a row in H cycles, and the beats
  follow it row by row; the correction's shadow load is later still (1 + TS cycles), and long before the next swap.
  Long paths: the cell's 18 x 18 multiplier and SW-bit add (par: 16 x 17 and a 48-bit add); the pre-adders, both
  correction multipliers and every tree stage are registered apart from it. The output stage is par's.

CYCLES. par's formula (gen.par_cycles) with the two constants that changed: the tile slot's wait for the swap wave
is e//2 instead of e, and the array's depth from read to read-out is e + e//2 + 1 instead of 2 e. Derivation as in
par: a chunk of c vectors = the activations in (or the first tile's load), n/e passes per row block, one per slot
max(c + 1, load), load = e + max(lat + 2, 4, e//2); between row blocks the drain and the c sums read out.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import gen  # noqa: E402

SUM = r"""
// The sum of 2^(LGE-1) values modulo 2^W: a tree, four values per register stage, LGE/2 stages.
module gemm_sum #(parameter int LGE = 2, parameter int W = 35) (
  input  logic                        clk,
  input  logic [W*(1<<(LGE-1))-1:0]   d,
  output logic [W-1:0]                q
);
  localparam int H = 1 << (LGE - 1);
  localparam int TS = LGE / 2;
  if (TS == 0) begin : g_wire
    assign q = d[W-1:0];
  end else begin : g_tree
    logic [W*H*TS-1:0] vr;                                 // stage s's outputs in slot s (unused entries are 0)
    logic [W*H*TS-1:0] vi;                                 // stage s's inputs in slot s
    assign vi[W*H-1:0] = d;
    for (genvar s = 1; s < TS; s++) begin : g_in
      assign vi[W*H*s +: W*H] = vr[W*H*(s-1) +: W*H];
    end
    for (genvar s = 0; s < TS; s++) begin : g_st
      localparam int NI = H >> (2 * s);
      localparam int G = (NI >= 4) ? 4 : 2;
      for (genvar k = 0; k < H; k++) begin : g_k
        if (k < NI / G) begin : g_add
          if (G == 4) begin : g_four
            always_ff @(posedge clk)
              vr[W*H*s + W*k +: W] <= (vi[W*H*s + W*(4*k) +: W] + vi[W*H*s + W*(4*k+1) +: W])
                                    + (vi[W*H*s + W*(4*k+2) +: W] + vi[W*H*s + W*(4*k+3) +: W]);
          end else begin : g_two
            always_ff @(posedge clk)
              vr[W*H*s + W*k +: W] <= vi[W*H*s + W*(2*k) +: W] + vi[W*H*s + W*(2*k+1) +: W];
          end
        end else begin : g_zero
          always_ff @(posedge clk) vr[W*H*s + W*k +: W] <= '0;
        end
      end
    end
    assign q = vr[W*H*(TS-1) +: W];
  end
endmodule
"""

WCORR = r"""
// The weight correction of one tile row (one beat): -sum_t w[2t] * w[2t+1] modulo 2^SW, 1 + LGE/2 cycles.
module gemm_wcorr #(parameter int LGE = 2) (
  input  logic                   clk,
  input  logic [16*(1<<LGE)-1:0] w,
  output logic [32+LGE:0]        ncw
);
  localparam int H = 1 << (LGE - 1);
  localparam int SW = 33 + LGE;
  logic [SW*H-1:0] pe;
  for (genvar t = 0; t < H; t++) begin : g_p
    logic signed [31:0] p;
    always_ff @(posedge clk) p <= -($signed(w[32*t +: 16]) * $signed(w[32*t+16 +: 16]));
    assign pe[SW*t +: SW] = {{(SW-32){p[31]}}, p};
  end
  gemm_sum #(.LGE(LGE), .W(SW)) tree (.clk(clk), .d(pe), .q(ncw));
endmodule
"""

SKEWP = r"""
// The input skew of the inner-product array: pair t of the activation beat (and the swap tag) is delayed t + 1
// cycles, so that every cell of a row sees its pair one cycle after its left neighbour's. The activation
// correction sum_t x[2t] * x[2t+1] (modulo 2^SW) is formed from every column's first register and leaves
// H + 2 cycles after the beat: the cycle row 0 writes the beat's sum.
module gemm_skewp #(parameter int LGE = 2, parameter int LGB = 0) (
  input  logic                   clk,
  input  logic                   swap,
  input  logic [(16<<LGE)*(1<<LGB)-1:0] q,
  input  logic [LGB:0]           qsel,
  output logic [(1<<(LGE-1))-1:0] swap_o,
  output logic [16*(1<<LGE)-1:0] x_o,
  output logic [32+LGE:0]        cx
);
  localparam int E = 1 << LGE;
  localparam int H = E / 2;
  localparam int MEMW = 16 * E;
  localparam int SW = 33 + LGE;
  localparam int PAD = H - LGE / 2;                 // the delay line behind the tree, >= 1
  logic [MEMW-1:0] x;
  logic [MEMW*((1<<LGB)+1)-1:0] pick;               // the selected bank's beat, as an OR over the banks
  assign pick[MEMW-1:0] = '0;
  for (genvar b = 0; b < (1 << LGB); b++) begin : g_pick
    assign pick[MEMW*(b+1) +: MEMW] = pick[MEMW*b +: MEMW] | ((qsel == b) ? q[MEMW*b +: MEMW] : '0);
  end
  assign x = pick[MEMW*(1<<LGB) +: MEMW];
  logic [SW*H-1:0] pe;
  for (genvar t = 0; t < H; t++) begin : g_col
    logic [33*(t+1)-1:0] d;
    logic [31:0]         p;
    if (t == 0) begin : g_first
      always_ff @(posedge clk) d <= {swap, x[31:0]};
    end else begin : g_rest
      always_ff @(posedge clk) d <= {d[33*t-1:0], swap, x[32*t +: 32]};
    end
    always_ff @(posedge clk) p <= {16'd0, d[15:0]} * {16'd0, d[31:16]};
    assign swap_o[t]        = d[33*t + 32];
    assign x_o[32*t +: 32]  = d[33*t +: 32];
    assign pe[SW*t +: SW]   = {{(SW-32){1'b0}}, p};
  end
  logic [SW-1:0]     cxs;
  logic [SW*PAD-1:0] dl;
  gemm_sum #(.LGE(LGE), .W(SW)) tree (.clk(clk), .d(pe), .q(cxs));
  if (PAD == 1) begin : g_one
    always_ff @(posedge clk) dl <= cxs;
  end else begin : g_line
    always_ff @(posedge clk) dl <= {dl[SW*(PAD-1)-1:0], cxs};
  end
  assign cx = dl[SW*(PAD-1) +: SW];
endmodule
"""

CELLF = r"""
// One cell of the inner-product array: (w0 + x1) * (w1 + x0) added to the row's sum chain; (w0, w1) is a pair of
// weights, double-buffered as in par (`ld` loads the shadow, the tag `swap_in` moves it into the active register),
// (x0, x1) the pair of activations. The pre-adders are registered; the product and the chain add share a cycle.
module gemm_cellf #(parameter int SW = 35) (
  input  logic          clk,
  input  logic          ld,
  input  logic [31:0]   w_d,
  input  logic          swap_in,
  input  logic [31:0]   x_in,
  input  logic [SW-1:0] s_in,
  output logic          swap_out,
  output logic [31:0]   x_out,
  output logic [SW-1:0] s_out
);
  logic [31:0]        w_sh, w_act;
  logic signed [17:0] a, b;
  logic signed [47:0] p;
  assign p = a * b;                                         // exact: |a|, |b| < 2^17
  always_ff @(posedge clk) begin
    if (ld) w_sh <= w_d;
    if (swap_in) w_act <= w_sh;
    swap_out <= swap_in;
    x_out    <= x_in;
    a        <= $signed({{2{w_act[15]}}, w_act[15:0]})  + $signed({2'b00, x_in[31:16]});
    b        <= $signed({{2{w_act[31]}}, w_act[31:16]}) + $signed({2'b00, x_in[15:0]});
    s_out    <= s_in + p[SW-1:0];
  end
endmodule
"""

ROWF = r"""
// One row of the inner-product array: E/2 cells, the row's weight correction (shadow and active, the active one
// starts the sum chain), the row's accumulator memory (two blocks, even and odd vectors) and its output stage.
// The activation correction arrives in the cycle the chain's sum is written, and goes on to the next row.
module gemm_rowf #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic                ld,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic                cld,
  input  logic [32+LGE:0]     cw_d,
  input  logic [(1<<(LGE-1))-1:0] swap_in,
  input  logic [16*(1<<LGE)-1:0] x_in,
  input  logic [32+LGE:0]     cx_in,
  input  logic                a_rd, a_first,
  input  logic [LGE:0]        a_v,
  input  logic                r_rd,
  input  logic [LGE:0]        r_v,
  input  logic [15:0]         mul,
  input  logic [5:0]          shift,
  input  logic [15:0]         zp, lo, hi,
  output logic [(1<<(LGE-1))-1:0] swap_out,
  output logic [16*(1<<LGE)-1:0] x_out,
  output logic [32+LGE:0]     cx_out,
  output logic                a_rd_o, a_first_o,
  output logic [LGE:0]        a_v_o,
  output logic [15:0]         y
);
  localparam int E = 1 << LGE;
  localparam int H = E / 2;
  localparam int SW = 33 + LGE;
  logic [SW-1:0]       cw_sh, cw_act;
  logic [SW*(H+1)-1:0] s;
  assign s[SW-1:0] = cw_act;
  for (genvar t = 0; t < H; t++) begin : g_cell
    gemm_cellf #(.SW(SW)) u (.clk(clk), .ld(ld), .w_d(w_d[32*t +: 32]), .swap_in(swap_in[t]),
                             .x_in(x_in[32*t +: 32]), .s_in(s[SW*t +: SW]), .swap_out(swap_out[t]),
                             .x_out(x_out[32*t +: 32]), .s_out(s[SW*(t+1) +: SW]));
  end

  logic        r_sel;
  logic [SW-1:0] ip;                                  // the slice's inner product modulo 2^SW
  logic [47:0] d0, d1, wd;
  logic        rd0, rd1, wr0, wr1;
  logic [7:0]  ad0, ad1;
  assign ip  = s[SW*H +: SW] - cx_in;
  assign wr0 = a_rd_o & ~a_v_o[0];
  assign wr1 = a_rd_o &  a_v_o[0];
  assign rd0 = (a_rd & ~a_v[0]) | (r_rd & ~r_v[0]);
  assign rd1 = (a_rd &  a_v[0]) | (r_rd &  r_v[0]);
  assign ad0 = wr0 ? 8'(a_v_o[LGE:1]) : a_rd ? 8'(a_v[LGE:1]) : 8'(r_v[LGE:1]);
  assign ad1 = wr1 ? 8'(a_v_o[LGE:1]) : a_rd ? 8'(a_v[LGE:1]) : 8'(r_v[LGE:1]);
  assign wd  = (a_first_o ? 48'd0 : (a_v_o[0] ? d1 : d0)) + {{(48-SW){ip[SW-1]}}, ip};
  srambank_64x4x48_6t122 m0 (.clk(clk), .ADDRESS(ad0), .wd(wd), .banksel(rd0 | wr0), .read(rd0 & ~wr0),
                             .write(wr0), .dataout(d0));
  srambank_64x4x48_6t122 m1 (.clk(clk), .ADDRESS(ad1), .wd(wd), .banksel(rd1 | wr1), .read(rd1 & ~wr1),
                             .write(wr1), .dataout(d1));
  always_ff @(posedge clk) begin
    if (cld) cw_sh <= cw_d;
    if (swap_out[0]) cw_act <= cw_sh;
    cx_out    <= cx_in;
    a_rd_o    <= a_rd;
    a_first_o <= a_first;
    a_v_o     <= a_v;
    if (r_rd) r_sel <= r_v[0];
  end
  gemm_scale sc (.clk(clk), .d0(d0), .d1(d1), .sel(r_sel), .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi),
                 .y(y));
endmodule
"""

ARRAYF = r"""
// The inner-product array: E rows; activations, their correction, the swap tag and the accumulate control travel
// down the rows.
module gemm_arrayf #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic [(1<<LGE)-1:0] ld,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [(1<<LGE)-1:0] cld,
  input  logic [32+LGE:0]     cw_d,
  input  logic [(1<<(LGE-1))-1:0] swap,
  input  logic [16*(1<<LGE)-1:0] x,
  input  logic [32+LGE:0]     cx,
  input  logic                a_rd, a_first,
  input  logic [LGE:0]        a_v,
  input  logic                r_rd,
  input  logic [LGE:0]        r_v,
  input  logic [15:0]         mul,
  input  logic [5:0]          shift,
  input  logic [15:0]         zp, lo, hi,
  output logic [16*(1<<LGE)-1:0] y
);
  localparam int E = 1 << LGE;
  localparam int H = E / 2;
  localparam int MEMW = 16 * E;
  localparam int SW = 33 + LGE;
  logic [H*(E+1)-1:0]     sw;
  logic [MEMW*(E+1)-1:0]  xx;
  logic [SW*(E+1)-1:0]    cc;
  logic [E:0]             ard, afi;
  logic [(LGE+1)*(E+1)-1:0] av;
  assign sw[H-1:0]    = swap;
  assign xx[MEMW-1:0] = x;
  assign cc[SW-1:0]   = cx;
  assign ard[0]       = a_rd;
  assign afi[0]       = a_first;
  assign av[LGE:0]    = a_v;
  for (genvar i = 0; i < E; i++) begin : g_row
    gemm_rowf #(.LGE(LGE)) u (
      .clk(clk), .ld(ld[i]), .w_d(w_d), .cld(cld[i]), .cw_d(cw_d), .swap_in(sw[H*i +: H]),
      .x_in(xx[MEMW*i +: MEMW]), .cx_in(cc[SW*i +: SW]),
      .a_rd(ard[i]), .a_first(afi[i]), .a_v(av[(LGE+1)*i +: LGE+1]), .r_rd(r_rd), .r_v(r_v),
      .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi),
      .swap_out(sw[H*(i+1) +: H]), .x_out(xx[MEMW*(i+1) +: MEMW]), .cx_out(cc[SW*(i+1) +: SW]),
      .a_rd_o(ard[i+1]), .a_first_o(afi[i+1]), .a_v_o(av[(LGE+1)*(i+1) +: LGE+1]),
      .y(y[16*i +: 16]));
  end
endmodule
"""

# The top is par's with these edits (each `old` text must occur exactly once in gen.PAR_TOP).
TOP_EDITS = [
    ("""// gemm, par: the plain classical array (own code; generated by tasks/gemm/reference/gen.py).
//
// T = E: a weight tile is E x E, one tile row per memory beat. Per job, in chunks of at most 2 E vectors:
// the chunk's activations are written to the on-chip buffer; then, row block by row block, every tile of the block
// is loaded into the cells' shadow registers (one burst per tile) while the previous tile computes, the chunk's
// vectors stream through the array once per tile, the sums accumulate in the row memories, and after the block's
// last tile the sums are read out through the output stage into the result FIFO.
""",
     """// gemm, fip: the inner-product form (own code; generated by tasks/gemm/reference/gen_fip.py).
//
// sum_j w[j] x[j] = sum_t (w[2t] + x[2t+1]) (w[2t+1] + x[2t]) - sum_t w[2t] w[2t+1] - sum_t x[2t] x[2t+1]:
// a row of the array has E/2 multipliers; the weight term is computed once per loaded tile row by one shared unit
// and kept in the row (double-buffered like the weights), the activation term once per slice, and it travels down
// the rows with the slice. The rest is the classical array's machine.
//
// T = E: a weight tile is E x E, one tile row per memory beat. Per job, in chunks of at most 2 E vectors:
// the chunk's activations are written to the on-chip buffer; then, row block by row block, every tile of the block
// is loaded into the cells' shadow registers (one burst per tile) while the previous tile computes, the chunk's
// vectors stream through the array once per tile, the sums accumulate in the row memories, and after the block's
// last tile the sums are read out through the output stage into the result FIFO.
"""),
    ("localparam int DL = E + 2;   ", "localparam int DL = E / 2 + 3;"),
    ("localparam int DRAIN = 2 * E + 4;    ", "localparam int DRAIN = 3 * (E / 2) + 5;"),
    ("  localparam int CAP = 16;",
     "  localparam int SW = 33 + LGE;                      // the sums inside the array, modulo 2^SW\n"
     "  localparam int TS = LGE / 2;                       // the register stages of a correction's adder tree\n"
     "  localparam int CAP = 16;"),
    ("  logic [E-1:0]    sk_swap;\n",
     "  logic [E/2-1:0]  sk_swap;\n"
     "  logic [SW-1:0]   sk_cx, cw_d;\n"
     "  logic [E*(TS+1)-1:0] ldd;                          // the load strobes, delayed as the weight correction is\n"),
    ("""  gemm_skew #(.LGE(LGE), .LGB(LGB)) skew (
    .clk(clk), .swap(swap), .q(xq), .qsel(xqsel), .swap_o(sk_swap), .x_o(sk_x));
  gemm_array #(.LGE(LGE)) array (
    .clk(clk), .ld(ld), .w_d(wbeat), .swap(sk_swap), .x(sk_x),
""",
     """  gemm_skewp #(.LGE(LGE), .LGB(LGB)) skew (
    .clk(clk), .swap(swap), .q(xq), .qsel(xqsel), .swap_o(sk_swap), .x_o(sk_x), .cx(sk_cx));
  gemm_wcorr #(.LGE(LGE)) wcorr (.clk(clk), .w(wbeat), .ncw(cw_d));
  gemm_arrayf #(.LGE(LGE)) array (
    .clk(clk), .ld(ld), .w_d(wbeat), .cld(ldd[E*TS +: E]), .cw_d(cw_d), .swap(sk_swap), .x(sk_x), .cx(sk_cx),
"""),
    ("    if (rd_take) wbeat <= rd_data;\n",
     "    if (rd_take) wbeat <= rd_data;\n"
     "    ldd <= rst ? '0 : (E*(TS+1))'({ldd, ld});\n"),
    ("wave    <= 16'(E - 1);", "wave    <= 16'(E / 2 - 1);"),
]


def top_text():
    text = gen.PAR_TOP
    for old, new in TOP_EDITS:
        if text.count(old) != 1:
            raise SystemExit(f"gen_fip.py: the text to edit is not in par's top exactly once: {old[:60]!r}")
        text = text.replace(old, new)
    return text


def design_text():
    parts = (top_text(), gen.XBUF, SKEWP, WCORR, SUM, ARRAYF, ROWF, CELLF, gen.SCALE, gen.FIFO)
    return "\n".join(s.strip("\n") + "\n" for s in parts)


def fip_cycles():
    """The steady-state cycles per job (names n, batch, e, lat): gen.par_cycles with the swap wave e//2 and the
    array's read-to-read-out depth e + e//2 + 1 (par: e and 2 e)."""
    nb = "(n//e)"
    load = "(e+max(lat+2,4,e//2))"
    depth = "(e+e//2+1)"

    def chunk(c):
        return (f"(max({c}*{nb},max(lat+1,3)+e)+{nb}*({nb}-1)*max({c}+1,{load})"
                f"+({nb}-1)*max(2*{c}+{depth}+5,{load})+2*{c}+{depth}+13)")
    return f"(batch//(2*e))*{chunk('(2*e)')}+min(batch%(2*e),1)*{chunk('(batch%(2*e))')}+1"


def declare():
    return {"cycles": fip_cycles(), "layout": None}


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 1:
        print("usage: gen_fip.py OUTDIR", file=sys.stderr)
        return 2
    os.makedirs(argv[0], exist_ok=True)
    with open(os.path.join(argv[0], "fip.sv"), "w") as fh:
        fh.write(design_text())
    with open(os.path.join(argv[0], "fip.json"), "w") as fh:
        fh.write(json.dumps(declare(), indent=1) + "\n")
    print("gen_fip.py: fip.sv and fip.json written")
    return 0


if __name__ == "__main__":
    sys.exit(main())
