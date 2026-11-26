#!/usr/bin/env python3.12
"""Generator of the Strassen designs of task `gemm` (own code).

    python3.12 gen_strassen.py NAME OUTDIR        # writes OUTDIR/NAME.sv and OUTDIR/NAME.json

    s1    one level of Strassen (original form) on one shared E x E array
    s2    two levels on three E x E arrays, one per leaf class, running the same schedule side by side
    s2s   two levels on one shared array (the simpler design s2 grew from; kept because it is the better score)

DESIGN NOTE

Common structure (the baseline `par` of gen.py, extended). A job runs in chunks; a chunk's vectors are the columns of
X, split in D = 2^L column parts of p = ceil(c / D) vectors (L levels; the last part is padded: a padding column's
buffer words are never written, and whatever they hold cancels, because a Strassen result column depends on the
same column of X only; padding results are not read out). The rows of X and of Y are split in 2^m row parts,
m = min(log2(N / E), L): with fewer levels than L the D / 2^m groups of column parts are independent sub-batches
(m = 0: one classical product per column part). Chunk size: 2 E vectors per column part in s1 and s2s (4 E and 8 E
per chunk), 4 E in s2 (16 E per chunk): a tile load takes about 2 E cycles (E + upper beats, after the swap has
crossed the array), so a pass shorter than that leaves the array waiting for weights: with par's 2 E chunk the
cycle formula of s1 is above par's.

  weights      STORED combinations: the declared layout holds at scale q the 7^m products' weight combinations as
               level-m segments at 16 + L bits (m = 0: the matrix itself, also at 16 + L bits, so that a tile is the
               same burst at every scale: E beats of low 16 bits, then E L / 16 beats of upper bits, at least one).
               The loader reads one burst per tile into the cells' shadow registers (a beat of upper bits loads the
               rows it covers, each row taking its slice), one slot ahead of the array.
  activations  the buffer has one bank per block (row part, column part): the up to 2^L blocks of a product's
               operand are read in the same cycle at the same address (vector of the part, column block) and added
               with their signs in front of the input skew. The buffer and the skew get the product's NUMBER and
               hold the operand table themselves: registers of table columns would be constant or duplicate
               flip-flops, which the flow's never-loaded rule refuses (it did, on an earlier text).
  cells        signed weight x signed operand, exact, accumulated modulo 2^48. The operand of a 2-block sum reaches
               2 * 65535, so it is 17 + L bits signed on a shared array (18 x 17-bit cells in s1; a 17-bit
               operand holds a difference or a single block, not a sum).
  accumulators a row's sum of a product is added with the product's signs into the result blocks it feeds as it
               leaves the array (read in one cycle, written in the next; no product is stored). Blocks updated in one
               cycle must be in different memories, and consecutive vectors in different memories (one port):
               result blocks are coloured per level 22 -> 0, 11 -> 1, {12, 21} -> 2 (the pairs a product shares are
               11-22, 21-22, 12-22, 11-21, 11-12; 11, 21, 22 are pairwise shared, so 3 colours per level are the
               minimum) and a colour word is a group of two memories, even and odd vectors: 6 memories per row in
               s1, 18 in s2s. The first product that touches a block (per row block, at column block 0) writes
               instead of adding, so nothing is cleared.
  read-out     per row block, after its last product: every result block of the row parts, vector by vector, through
               the output stage into the result FIFO, tagged (vector, row part * blocks + row block).

Products and targets, one level (s1; X11 = top half of the entries, first half of the vectors):
    M1 = (W11+W22)(X11+X22) -> +Y11 +Y22      M2 = (W21+W22) X11      -> +Y21 -Y22
    M3 = W11 (X12-X22)      -> +Y12 +Y22      M4 = W22 (X21-X11)      -> +Y11 +Y21
    M5 = (W11+W12) X22      -> -Y11 +Y12      M6 = (W21-W11)(X11+X12) -> +Y22
    M7 = (W12-W22)(X21+X22) -> +Y11
    groups: Y22 | Y11 | {Y12, Y21}.  At N = E: two classical products, W X(first half) -> Y11, W X(second) -> Y12.
Two levels: leaf (i, j) = outer product i, inner product j; weight, operand and target terms are the products of
the two levels' terms (`leaves`), 49 leaves, up to 4 weight blocks (18 bits), 4 activation blocks, 4 targets.

s2, three arrays by leaf class (activation blocks, weight blocks); M1, M6, M7 sum on both sides, M3, M4 on the
activation side only, M2, M5 on the weight side only:
    array a, class (1,2): 24 leaves with i or j in {2, 5}: at most 2 activation blocks (18-bit signed operand: a sum
             reaches 2 * 65535), up to 4 weight blocks (18 bits).                         18 x 18 signed cells
    array b, class (2,1): 16 leaves with i, j in {1, 3, 4, 6, 7}, one of them in {3, 4}: 4 activation blocks, two
             added and two subtracted (18 bits signed), at most 2 weight blocks (17 bits). 18 x 17 signed cells
    array c, class (2,2):  9 leaves with i, j in {1, 6, 7}: 4 activation blocks, all added (18 bits UNSIGNED),
             4 weight blocks (18 bits).                                         18 (unsigned) x 18 signed cells
The arrays work in lockstep SLOTS: slot s of a column block runs the s-th leaf of every array that still has one
(slots 0..8 three arrays, 9..15 two, 16..23 one), all with the same vector and column block, so one read of the
buffer serves the three operands. Balance: the arrays are busy 24 : 16 : 9 slots of 24 (100 %, 67 %, 38 %); the
single memory channel is the limit, not the arrays: the tiles of a slot arrive one burst after the other, so a
three-array slot costs about 2 E + 2 (E + LAT) cycles of loading against a pass of p + 1, which is why the column
part is 4 E vectors here. Each array has its own accumulators (first-touch per array; array c needs 4 groups,
a and b all 9); the read-out selects one word per array and row, and the output stage adds the arrays that hold
a part of the block (a table by block). With one level or none in use (N <= 2 E) only array a works.

Pipeline timing (cycle t = the buffer read of a vector is issued, as in par): t+1 the banks' words; t+2 the operand
in the skew's first register, column j at t+2+j at cell (0, j) (the swap tag one cycle ahead); row i's sum at
t+E+2+i; the accumulate control travels a delay line of E+1 compact entries (valid, first column block, product,
vector), is decoded in one register stage and reaches row 0 at t+E+1 (memory read), row i one cycle later per row;
write at t+E+2+i. One idle cycle between passes keeps a pass's last write and the next pass's first read apart.
Read-out: read issue u, the word u+1, the five stages of the output stage (the baseline's), FIFO push u+6 (s2: u+8,
the select register and the adder of the three arrays in front), transfer u+8 (s2: u+10) at nominal timing; at most
16 beats are under way (the FIFO's size), so the read-out never waits at nominal timing.
Selections (buffer banks, accumulator memories) are explicit AND-OR terms; the buffer's sub-bank select covers
up to four 1024-word sub-banks per bank, which is the task's range LGE <= 7.

The cycle formula (per job = sum over its chunks + 1; a chunk of c vectors, p = ceil(c / D), nb = n / e,
g = min(nb, D) row parts, hb = nb / g blocks per part, P = products of the mode, tb = e + max(1, L e / 16) beats
per tile):
    start      max(c nb + 1, max(lat+2, 4) + tb)         the activations in, or the first tile's load
    passes     hb (P hb - 1) max(p + 1, load)            load = tb + max(lat+2, 4, e): request, latency, the beats
                                                         (which wait e cycles for the swap to cross the array)
    row blocks (hb - 1) max(p + 2e + 5 + g D p, load)    last pass, drain (2e + 4), read-out of g D p positions
    end        p + 2e + 5 + g D p + max(0, 7 - pad) + 1  the last block's read-out and the pipeline's tail
s2: a slot with k arrays loads k tiles, load(k) = load + (k - 1)(tb + max(lat+1, 3)); per row block and column
block 9 slots at k = 3, 7 at k = 2, 8 at k = 1 (with two levels in use), the tail is max(0, 9 - pad).
The formulas equal the simulation at every checked point (and at others tried by hand, up to LGE = 7).
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import gen  # noqa: E402  (the baseline's generator: its result FIFO is reused as text)

LEVELS = {"s1": 1, "s2": 2, "s2s": 2}
THREE = ("s2",)                                    # the designs with three arrays

# The original Strassen form on 2 x 2 blocks. A product is (weight terms, activation terms, result terms), a term
# (block row, block column, coefficient). Activation blocks: row = half of the entries, column = half of the vectors.
BASE = [
    ([(0, 0, 1), (1, 1, 1)], [(0, 0, 1), (1, 1, 1)], [(0, 0, 1), (1, 1, 1)]),      # M1 -> Y11, Y22
    ([(1, 0, 1), (1, 1, 1)], [(0, 0, 1)], [(1, 0, 1), (1, 1, -1)]),                # M2 -> Y21, -Y22
    ([(0, 0, 1)], [(0, 1, 1), (1, 1, -1)], [(0, 1, 1), (1, 1, 1)]),                # M3 -> Y12, Y22
    ([(1, 1, 1)], [(1, 0, 1), (0, 0, -1)], [(0, 0, 1), (1, 0, 1)]),                # M4 -> Y11, Y21
    ([(0, 0, 1), (0, 1, 1)], [(1, 1, 1)], [(0, 0, -1), (0, 1, 1)]),                # M5 -> -Y11, Y12
    ([(1, 0, 1), (0, 0, -1)], [(0, 0, 1), (0, 1, 1)], [(1, 1, 1)]),                # M6 -> Y22
    ([(0, 1, 1), (1, 1, -1)], [(1, 0, 1), (1, 1, 1)], [(0, 0, 1)]),                # M7 -> Y11
]


def leaves(m):
    """The 7^m leaf products of m recursive levels, on a 2^m x 2^m block grid (outer level = high index bit)."""
    if m == 0:
        return [([(0, 0, 1)], [(0, 0, 1)], [(0, 0, 1)])]
    h = 1 << (m - 1)
    out = []
    for ow, ox, oy in BASE:
        for iw, ix, iy in leaves(m - 1):
            out.append(tuple([(a * h + c, b * h + d, s * t) for a, b, s in o for c, d, t in i]
                             for o, i in ((ow, iw), (ox, ix), (oy, iy))))
    return out


def ygroups(L):
    """Result block (row part * D + column part) -> (accumulator group, slot in the group).

    Two result blocks that one product updates in the same cycle must lie in different memories. Per level the
    quadrants are coloured 22 -> 0, 11 -> 1, {12, 21} -> 2 (12 and 21 never share a product); the group is the
    colour word over the levels (3^L groups, the minimum: {11, 21, 22} are pairwise shared)."""
    D = 1 << L
    col = {(1, 1): 0, (0, 0): 1, (0, 1): 2, (1, 0): 2}
    grp, cnt = {}, {}
    for r in range(D):
        for c in range(D):
            g = sum(col[((r >> l) & 1, (c >> l) & 1)] * 3 ** l for l in range(L))
            grp[r * D + c] = (g, cnt.get(g, 0))
            cnt[g] = cnt.get(g, 0) + 1
    return grp


def products(L, m):
    """The products of mode m (m recursive levels in use, m <= L) of a design built for L levels, in schedule order.

    The chunk's vectors are always split in D = 2^L column parts. With m < L levels the D / 2^m groups of 2^m
    column parts are independent sub-batches, each a level-m problem (m = 0: one classical product per part)."""
    D = 1 << L
    out, seen = [], set()
    for g in range(D >> m):
        for seg, (w, x, y) in enumerate(leaves(m)):
            tg = []
            for r, c, s in y:
                yb = r * D + (g << m) + c
                tg.append((yb, s < 0, yb not in seen))
                seen.add(yb)
            out.append({"seg": seg, "x": [(a * D + (g << m) + c, s < 0) for a, c, s in x], "t": tg})
    return out


def layout(L):
    """The declared memory layout: at scale q the 7^m weight combinations of m = min(q, L) levels, each a segment
    of level m stored at 16 + L bits (the same tile format at every scale, so the loader has one burst shape)."""
    out = {}
    for q in range(6):
        m = min(q, L)
        out[str(q)] = [{"level": m, "terms": [list(t) for t in w], "bits": 16 + L, "tile": 0} for w, _, _ in leaves(m)]
    return out


# ------------------------------------------------------------------------------------------------ the module texts
CELL = r"""
// One multiply-accumulate cell: signed @WW@-bit weight (a stored block combination) times signed @XW@-bit activation
// operand (a block combination formed on chip), exact, accumulated modulo 2^48. The weight is double-buffered: `ld`
// loads the shadow's low 16 bits, `ld_hi` its upper bits, `swap_in` (a tag that travels with the activations, one
// cycle ahead of a pass's first vector) moves it into the active register.
module gemm_cell (
  input  logic        clk,
  input  logic        ld, ld_hi,
  input  logic [15:0] w_d,
  input  logic [@L@-1:0] w_h,
  input  logic        swap_in,
  input  logic [@XW@-1:0] x_in,
  input  logic [47:0] s_in,
  output logic        swap_out,
  output logic [@XW@-1:0] x_out,
  output logic [47:0] s_out
);
  logic [@WW@-1:0]        w_sh, w_act;
  logic signed [@PW@-1:0] p;
  assign p = $signed(w_act) * $signed(x_in);
  always_ff @(posedge clk) begin
    if (ld)    w_sh[15:0] <= w_d;
    if (ld_hi) w_sh[@WW@-1:16] <= w_h;
    if (swap_in) w_act <= w_sh;
    swap_out <= swap_in;
    x_out    <= x_in;
    s_out    <= s_in + {{@PX@{p[@PW@-1]}}, p};
  end
endmodule
"""

def scale_text(shared):
    """The output stage: the baseline's five register stages (gen.SCALE), behind this file's word select (shared
    array: one of the row's memories) or behind a register stage that adds the three arrays' words."""
    t = gen.SCALE

    def rep(a, b):
        nonlocal t
        assert t.count(a) == 1, a
        t = t.replace(a, b)
    if shared:
        rep("  input  logic [47:0] d0, d1,\n  input  logic        sel,\n",
            "  input  logic [48*@NS@-1:0] d,\n  input  logic [@SELW@-1:0] sel,\n")
        rep("  assign a = sel ? d1[43:0] : d0[43:0];\n",
            "  logic [47:0] aw;                                  // the selected memory's word, an OR over the memories\n"
            "  assign aw = @PICKS@;\n  assign a = aw[43:0];\n")
    else:
        rep("module gemm_scale (", "module gemm_scale3 (")
        rep("  input  logic [47:0] d0, d1,\n  input  logic        sel,\n",
            "  input  logic [47:0] d0, d1, d2,\n  input  logic [2:0]  use_d,\n")
        rep("  assign a = sel ? d1[43:0] : d0[43:0];\n",
            "  // a register stage in front: the words of the arrays that hold a part of the sum, added (carry-save, then\n"
            "  // one 44-bit add; the parts are modulo 2^48, their sum is the exact sum)\n"
            "  logic [43:0] m0, m1, m2, cs, cc;\n"
            "  assign m0 = use_d[0] ? d0[43:0] : 44'd0;\n  assign m1 = use_d[1] ? d1[43:0] : 44'd0;\n"
            "  assign m2 = use_d[2] ? d2[43:0] : 44'd0;\n  assign cs = m0 ^ m1 ^ m2;\n"
            "  assign cc = (m0 & m1) | (m0 & m2) | (m1 & m2);\n"
            "  always_ff @(posedge clk) a <= cs + {cc[42:0], 1'b0};\n")
    return t


ROW = r"""
// One row of the array: E cells, the row's accumulators and its output stage. The accumulators hold the result
// blocks of the row block under work in @NG@ groups of two memories (even and odd vectors): a product's sum is
// added with its sign into one block of every enabled group, read in one cycle and written in the next, and two
// blocks one product updates are never in one group. The accumulate control `acw` (vector, then per group: enable,
// negate, first, slot) enters from the row above one cycle later per row, as the activations do.
module gemm_row #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic                ld, ld_hi,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [@L@*(1<<LGE)-1:0] w_h,
  input  logic [(1<<LGE)-1:0] swap_in,
  input  logic [@XW@*(1<<LGE)-1:0] x_in,
  input  logic [LGE+@KP@+@TW@-1:0] acw,
  input  logic                r_rd,
  input  logic [@GW@-1:0]     r_g,
  input  logic [@SB@-1:0]     r_sub,
  input  logic [LGE+@KP@-1:0] r_v,
  input  logic [15:0]         mul,
  input  logic [5:0]          shift,
  input  logic [15:0]         zp, lo, hi,
  output logic [(1<<LGE)-1:0] swap_out,
  output logic [@XW@*(1<<LGE)-1:0] x_out,
  output logic [LGE+@KP@+@TW@-1:0] acw_o,
  output logic [15:0]         y
);
  localparam int E = 1 << LGE;
  localparam int KW = LGE + @KP@;
  logic [48*(E+1)-1:0] s;
  assign s[47:0] = 48'd0;
  for (genvar j = 0; j < E; j++) begin : g_cell
    gemm_cell u (.clk(clk), .ld(ld), .ld_hi(ld_hi), .w_d(w_d[16*j +: 16]), .w_h(w_h[@L@*j +: @L@]),
                 .swap_in(swap_in[j]), .x_in(x_in[@XW@*j +: @XW@]),
                 .s_in(s[48*j +: 48]), .swap_out(swap_out[j]), .x_out(x_out[@XW@*j +: @XW@]),
                 .s_out(s[48*(j+1) +: 48]));
  end

  logic [47:0] sp, sn;
  logic [48*@NS@-1:0] dd;
  logic [@SELW@-1:0] r_sel;
  assign sp = s[48*E +: 48];
  assign sn = 48'd0 - sp;
@ACC@
  always_ff @(posedge clk) begin
    acw_o <= acw;
    if (r_rd) r_sel <= {r_g, r_v[0]};
  end
  gemm_scale sc (.clk(clk), .d(dd), .sel(r_sel), .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi), .y(y));
endmodule
"""

ARRAY = r"""
// The array: E rows; activations, the swap tag and the accumulate control travel down the rows. A weight beat
// `w_d` is a tile row's low 16 bits (`ld`, one row) or a beat of the tile's upper bits, row-major (`ld_hi`, the
// rows of that beat: each row takes its own slice).
module gemm_array #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic [(1<<LGE)-1:0] ld,
  input  logic [(1<<((LGE+@L@>5)?LGE+@L@-5:1))-1:0] ld_hi,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [(1<<LGE)-1:0] swap,
  input  logic [@XW@*(1<<LGE)-1:0] x,
  input  logic [LGE+@KP@+@TW@-1:0] acw,
  input  logic                r_rd,
  input  logic [@GW@-1:0]     r_g,
  input  logic [@SB@-1:0]     r_sub,
  input  logic [LGE+@KP@-1:0] r_v,
  input  logic [15:0]         mul,
  input  logic [5:0]          shift,
  input  logic [15:0]         zp, lo, hi,
  output logic [16*(1<<LGE)-1:0] y
);
  localparam int E = 1 << LGE;
  localparam int XB = @XW@ * E;
  localparam int ACW = LGE + @KP@ + @TW@;
  localparam int LGR = (LGE < 5 - @L@) ? LGE : 5 - @L@;     // log2 of the tile rows in one beat of upper bits
  logic [E*(E+1)-1:0]    sw;
  logic [XB*(E+1)-1:0]   xx;
  logic [ACW*(E+1)-1:0]  ac;
  assign sw[E-1:0]   = swap;
  assign xx[XB-1:0]  = x;
  assign ac[ACW-1:0] = acw;
  for (genvar i = 0; i < E; i++) begin : g_row
    gemm_row #(.LGE(LGE)) u (
      .clk(clk), .ld(ld[i]), .ld_hi(ld_hi[i >> LGR]), .w_d(w_d),
      .w_h(w_d[@L@*E*(i & ((1 << LGR) - 1)) +: @L@*E]),
      .swap_in(sw[E*i +: E]), .x_in(xx[XB*i +: XB]), .acw(ac[ACW*i +: ACW]),
      .r_rd(r_rd), .r_g(r_g), .r_sub(r_sub), .r_v(r_v),
      .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi),
      .swap_out(sw[E*(i+1) +: E]), .x_out(xx[XB*(i+1) +: XB]), .acw_o(ac[ACW*(i+1) +: ACW]),
      .y(y[16*i +: 16]));
  end
endmodule
"""

XBUF = r"""
// The activation buffer: one bank per activation block (row part, column part), so that the up to @NT@ blocks of
// an operand are read in one cycle. A bank holds @CHP@ E vectors of up to 32 / @D@ beats, in 64-bit blocks.
// `q` is every bank's output; `qpid` (the product) and `qsb` (the sub-bank) say which words were read.
module gemm_xbuf #(parameter int LGE = 2) (
  input  logic                   clk,
  input  logic                   we_v, we_r,
  input  logic [@BW@-1:0]        wblk,
  input  logic [LGE+@AWO@-1:0]   waddr,
  input  logic [16*(1<<LGE)-1:0] wdata,
  input  logic                   rd,
  input  logic [1:0]             rmode,
  input  logic [@PIDW@-1:0]      rpid,
  input  logic [LGE+@AWO@-1:0]   raddr,
  output logic [(16<<LGE)*(@NB@<<((LGE+@AWO@>10)?LGE+@AWO@-10:0))-1:0] q,
  output logic [@PIDW@-1:0]      qpid,
  output logic [((LGE+@AWO@>10)?LGE+@AWO@-10:0):0] qsb
);
  localparam int MEMW = 16 << LGE;
  localparam int AW = LGE + @AWO@;
  localparam int LGS = (AW > 10) ? AW - 10 : 0;       // log2 of the 1024-word sub-banks of a bank
  logic            we;
  logic [LGS:0]    wsb, rsb;
  logic [@XTW@-1:0] ptx;                             // the operand of product rpid: per term {use, negate, block}
  assign we = we_v & we_r;
  always_comb begin
    case ({rmode, rpid})
@CASE_X@
      default: ptx = '0;
    endcase
  end
  if (LGS == 0) begin : g_one
    assign wsb = '0;
    assign rsb = '0;
  end else begin : g_many
    assign wsb = {1'b0, waddr[AW-1:10]};
    assign rsb = {1'b0, raddr[AW-1:10]};
  end
  for (genvar b = 0; b < @NB@; b++) begin : g_bank
    logic hit;
    assign hit = @HIT@;
    for (genvar sb = 0; sb < (1 << LGS); sb++) begin : g_sub
      logic bw, br;
      assign bw = we & (wblk == b) & (wsb == sb);
      assign br = rd & hit & (rsb == sb) & ~bw;
      for (genvar k = 0; k < MEMW / 64; k++) begin : g_blk
        if (AW <= 8) begin : g_256
          srambank_64x4x64_6t122 m (.clk(clk), .ADDRESS(bw ? 8'(waddr) : 8'(raddr)), .wd(wdata[64*k +: 64]),
                                    .banksel(bw | br), .read(br), .write(bw),
                                    .dataout(q[MEMW*((b << LGS) + sb) + 64*k +: 64]));
        end else if (AW == 9) begin : g_512
          srambank_128x4x64_6t122 m (.clk(clk), .ADDRESS(bw ? 9'(waddr) : 9'(raddr)), .wd(wdata[64*k +: 64]),
                                     .banksel(bw | br), .read(br), .write(bw),
                                     .dataout(q[MEMW*((b << LGS) + sb) + 64*k +: 64]));
        end else begin : g_1024
          srambank_256x4x64_6t122 m (.clk(clk), .ADDRESS(bw ? 10'(waddr) : 10'(raddr)), .wd(wdata[64*k +: 64]),
                                     .banksel(bw | br), .read(br), .write(bw),
                                     .dataout(q[MEMW*((b << LGS) + sb) + 64*k +: 64]));
        end
      end
    end
  end
  always_ff @(posedge clk)
    if (rd) begin
      qpid <= rpid;
      qsb  <= rsb;
    end
endmodule
"""

SKEW = r"""
// The operand and the input skew: the up to @NT@ blocks read from the buffer are added with their signs, entry by
// entry (a signed @XW@-bit operand), and column j of the result (and the swap tag) is delayed j + 1 cycles, so
// that every cell of a row sees its activation one cycle after its left neighbour's sum.
module gemm_skew #(parameter int LGE = 2) (
  input  logic                   clk,
  input  logic                   swap,
  input  logic [(16<<LGE)*(@NB@<<((LGE+@AWO@>10)?LGE+@AWO@-10:0))-1:0] q,
  input  logic [1:0]             mode,
  input  logic [@PIDW@-1:0]      qpid,
  input  logic [((LGE+@AWO@>10)?LGE+@AWO@-10:0):0] qsb,
  output logic [(1<<LGE)-1:0]    swap_o,
  output logic [@XW@*(1<<LGE)-1:0] x_o
);
  localparam int E = 1 << LGE;
  localparam int MEMW = 16 * E;
  localparam int AW = LGE + @AWO@;
  localparam int LGS = (AW > 10) ? AW - 10 : 0;
  logic [@NT@*(2+@BW@)-1:0] ptx;                    // the operand of product qpid: per term {use, negate, block}
  logic [@NT@*@BW@-1:0] qblk;
  logic [@NT@-1:0] quse, qneg;
  always_comb begin
    case ({mode, qpid})
@CASE_XS@
      default: ptx = '0;
    endcase
  end
  for (genvar t = 0; t < @NT@; t++) begin : g_op
    assign qblk[@BW@*t +: @BW@] = ptx[(2+@BW@)*t +: @BW@];
    assign qneg[t] = ptx[(2+@BW@)*t + @BW@];
    assign quse[t] = ptx[(2+@BW@)*t + @BW@ + 1];
  end
  logic [MEMW*@NB@-1:0] w;                          // per bank: the word of the sub-bank that was read
  for (genvar b = 0; b < @NB@; b++) begin : g_b
    if (LGS == 0) begin : g_1
      assign w[MEMW*b +: MEMW] = q[MEMW*b +: MEMW];
    end else if (LGS == 1) begin : g_2
      assign w[MEMW*b +: MEMW] = qsb[0] ? q[MEMW*(2*b+1) +: MEMW] : q[MEMW*(2*b) +: MEMW];
    end else begin : g_4                             // LGE <= 7: at most four sub-banks
      assign w[MEMW*b +: MEMW] = qsb[1] ? (qsb[0] ? q[MEMW*(4*b+3) +: MEMW] : q[MEMW*(4*b+2) +: MEMW])
                                        : (qsb[0] ? q[MEMW*(4*b+1) +: MEMW] : q[MEMW*(4*b) +: MEMW]);
    end
  end
  logic [MEMW*@NT@-1:0] xt;                         // per term: the selected bank's beat, an OR over the banks
  for (genvar t = 0; t < @NT@; t++) begin : g_term
    assign xt[MEMW*t +: MEMW] = @PICK@;
  end
  for (genvar j = 0; j < E; j++) begin : g_col
    logic [@XW@*@NT@-1:0] tv;
    for (genvar t = 0; t < @NT@; t++) begin : g_t
      logic [@XW@-1:0] ex;
      assign ex = {@XZ@'d0, xt[MEMW*t + 16*j +: 16]};
      assign tv[@XW@*t +: @XW@] = quse[t] ? (qneg[t] ? (@XW@'d0 - ex) : ex) : @XW@'d0;
    end
    logic [@XW@-1:0] sum;
    assign sum = @SUM@;
    logic [@XS@*(j+1)-1:0] d;
    if (j == 0) begin : g_first
      always_ff @(posedge clk) d <= {swap, sum};
    end else begin : g_rest
      always_ff @(posedge clk) d <= {d[@XS@*j-1:0], swap, sum};
    end
    assign swap_o[j]       = d[@XS@*j + @XW@];
    assign x_o[@XW@*j +: @XW@] = d[@XS@*j +: @XW@];
  end
endmodule
"""

TOP = r"""
// gemm, @NAME@: @TITLE@ (own code; generated by tasks/gemm/reference/gen_strassen.py).
//
// T = E: a weight tile is E x E. The memory holds, at scale q = log2(N / E), the 7^m weight combinations of
// m = min(q, @L@) Strassen levels at @WW@ bits (the declared layout); a tile is one burst: E beats of low 16 bits,
// then the upper bits. Per job, in chunks of at most @CHV@ E vectors split in @D@ column parts: the chunk's
// activations are written to the on-chip buffer, one bank per activation block; then, row block by row block, for
// every product and every column block the tile is loaded into the cells' shadow registers while the previous tile
// computes, the product's activation operand (a signed sum of up to @D@ blocks) streams through the array, the
// row sums are added with the product's signs into the accumulators of its result blocks, and after the row
// block's last product the result blocks are read out through the output stage into the result FIFO.
module gemm #(parameter int LGE = 2, parameter int LAT = 3) (
  input  logic                   clk, rst,
  input  logic                   job_valid,
  input  logic [3:0]             job_lgn,
  input  logic [15:0]            job_batch, job_mul,
  input  logic [5:0]             job_shift,
  input  logic [15:0]            job_zp, job_lo, job_hi,
  input  logic                   rq_ready,
  input  logic                   rd_valid,
  input  logic [16*(1<<LGE)-1:0] rd_data,
  input  logic                   x_valid,
  input  logic [16*(1<<LGE)-1:0] x_data,
  input  logic                   y_ready,
  output logic                   job_ready,
  output logic                   rq_valid,
  output logic [31:0]            rq_addr,
  output logic [23:0]            rq_len,
  output logic                   rd_ready,
  output logic                   x_ready,
  output logic                   y_valid,
  output logic [15:0]            y_vec,
  output logic [4:0]             y_row,
  output logic [16*(1<<LGE)-1:0] y_data
);
  localparam int E = 1 << LGE;
  localparam int MEMW = 16 * E;
  localparam int KW = LGE + @KP@;                    // a vector index inside a column part (@CHP@ E vectors)
  localparam int CBW = 5 - @L@;                      // a column block inside a row part
  localparam int AW = KW + CBW;                      // an address inside a buffer bank
  localparam int LGS = (AW > 10) ? AW - 10 : 0;
  localparam int VW = LGE + @KP@ + @L@;              // a vector index inside a chunk (@CHV@ E vectors)
  localparam int DL = E + 2;                         // from a buffer read to row 0's accumulator read
  localparam int DRAIN = 2 * E + 4;                  // from a block's last buffer read to its read-out
  localparam int CAP = 16;                           // result beats under way at most (the FIFO's size)
  localparam int LGUB = (LGE + @L@ > 5) ? LGE + @L@ - 5 : 0;   // log2 of a tile's beats of upper bits
  localparam int HW = (LGUB > 0) ? LGUB : 1;
  localparam int TBEATS = E + (1 << LGUB);           // beats of a tile
  localparam int ACW = KW + @TW@;                    // the accumulate control of a row
  localparam int CW = KW + @PIDW@ + 2;               // the same, compact: valid, first column block, product, vector

  // ---- the job
  logic [1:0]  mode;                                 // Strassen levels in use: min(log2(N / E), @L@)
  logic [2:0]  lgh;                                  // log2 of the column blocks of a row part
  logic [CBW-1:0] hbm;                               // column blocks of a row part - 1
  logic [4:0]  nbm;                                  // N / E - 1
  logic [@L@-1:0] nrm;                               // row parts - 1
  logic [@PIDW@-1:0] npm;                            // products - 1
  logic [15:0] rem, vbase;
  logic [15:0] mul, zp, lo, hi;
  logic [5:0]  shift;
  logic [VW:0] cnt;                                  // vectors in this chunk, 1 .. @CHV@ E
  logic [KW:0] part;                                 // vectors of a column part, ceil(cnt / @D@)

  // ---- the main sequence
  typedef enum logic [2:0] {M_IDLE, M_CHUNK, M_INGEST, M_TILE, M_RUN, M_DRAIN, M_RO, M_FLUSH} mstate_t;
  mstate_t     ms;
  logic [VW:0] iv;                                   // ingest: vector of the chunk
  logic [KW-1:0] ik;                                 // ingest: vector of the column part
  logic [@L@-1:0] ica, ia;                           // ingest: column part, row part
  logic [4:0]  ic;                                   // ingest: beat of the vector
  logic [CBW-1:0] icb;                               // ingest: beat of the row part
  logic [CBW-1:0] rr, cc;                            // the tile: row block, column block
  logic [@PIDW@-1:0] pp;                             // the product
  logic [KW:0] rv;                                   // the vector being read
  logic [15:0] dcnt;                                 // drain counter
  logic [@L@-1:0] ro_rho, ro_ch;                     // read-out: row part, column part
  logic [VW:0] ro_vb;                                // read-out: first vector of the column part

  // ---- registers that drive the children
  logic            swap;
  logic            xb_rd;
  logic [AW-1:0]   xb_ra;
  logic [@PIDW@-1:0] xb_pid;                         // the product whose operand is being read
  logic [E-1:0]    ld;
  logic [(1<<HW)-1:0] ld_hi;
  logic [MEMW-1:0] wbeat;
  logic [(DL-1)*CW-1:0] actl;                        // the accumulate control on its way to row 0, compact
  logic [ACW-1:0]  acw;                              // decoded, at row 0
  logic            r_rd;
  logic [@GW@-1:0] r_g;
  logic [@SB@-1:0] r_sub;
  logic [KW-1:0]   r_v;
  logic [20:0]     r_tag;                            // the position (vector, row block) of the beat being read out
  logic [@TV@-1:0] t_valid;                          // read-out pipeline: valid, and the beat's position
  logic [@TV@*21-1:0] t_tag;
  logic [4:0]      occ;                              // result beats issued and not yet transferred

  // ---- the weight loader
  typedef enum logic [1:0] {L_IDLE, L_REQ, L_RX} lstate_t;
  lstate_t     ls;
  logic [12:0] tiles;                                // tiles of this chunk not yet requested
  logic [@PIDW@-1:0] lp;
  logic [CBW-1:0] lr, lc;
  logic [LGE:0] li;
  logic        sh_full;
  logic [15:0] wave;                                 // cycles until the last swap has passed every cell

  logic [MEMW*(@NB@<<LGS)-1:0] xq;
  logic [@PIDW@-1:0] xqpid;
  logic [LGS:0]    xqsb;
  logic [E-1:0]    sk_swap;
  logic [@XW@*E-1:0] sk_x;
  logic [MEMW-1:0] ya;
  logic            f_valid;
  logic [MEMW+20:0] f_dout;

  gemm_xbuf #(.LGE(LGE)) xbuf (
    .clk(clk), .we_v(x_valid), .we_r(x_ready), .wblk({ia, ica}), .waddr({ik, icb}), .wdata(x_data),
    .rd(xb_rd), .rmode(mode), .rpid(xb_pid), .raddr(xb_ra),
    .q(xq), .qpid(xqpid), .qsb(xqsb));
  gemm_skew #(.LGE(LGE)) skew (
    .clk(clk), .swap(swap), .q(xq), .mode(mode), .qpid(xqpid), .qsb(xqsb),
    .swap_o(sk_swap), .x_o(sk_x));
  gemm_array #(.LGE(LGE)) array (
    .clk(clk), .ld(ld), .ld_hi(ld_hi), .w_d(wbeat), .swap(sk_swap), .x(sk_x), .acw(acw),
    .r_rd(r_rd), .r_g(r_g), .r_sub(r_sub), .r_v(r_v), .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi), .y(ya));
  gemm_fifo #(.W(MEMW + 21), .LGD(4)) fifo (
    .clk(clk), .rst(rst), .push(t_valid[@TV@-1]), .din({t_tag[(@TV@-1)*21 +: 21], ya}), .pop_ready(y_ready),
    .valid(f_valid), .dout(f_dout));
  assign y_valid = f_valid;
  assign y_data  = f_dout[MEMW-1:0];
  assign y_row   = f_dout[MEMW +: 5];
  assign y_vec   = f_dout[MEMW+5 +: 16];

  // ---- the product tables (constants of the algorithm): by {mode, product}; the operands' table is in the
  // buffer and in the skew, which get the product's number
  logic [@TW@-1:0]  ptt;                             // the targets: per group {slot, first, negate, enable}
  logic [@PIDW@-1:0] pseg;                           // the loader's product: its weight segment
  logic [@GW@+@SB@-1:0] ygs;                         // read-out: the block's {group, slot}
  logic [@PIDW@-1:0] a_pid;
  assign a_pid = actl[(DL-1)*CW-3 -: @PIDW@];
  always_comb begin
    case ({mode, a_pid})
@CASE_T@
      default: ptt = '0;
    endcase
  end
  always_comb begin
    case ({mode, lp})
@CASE_S@
      default: pseg = '0;
    endcase
  end
  always_comb begin
    case ({ro_rho, ro_ch})
@CASE_Y@
      default: ygs = '0;
    endcase
  end
  logic [2:0]  jq;
  logic [1:0]  jmode;
  assign jq    = 3'(job_lgn - 4'(LGE));
  assign jmode = (jq > 3'd@L@) ? 2'd@L@ : jq[1:0];
  always_comb begin
    case (mode)
@CASE_N@
      default: npm = '0;
    endcase
  end

  logic        x_take, y_take, start_pass, ro_go, rd_take, a_val, a_cb0, ro_pad;
  logic [VW:0] cnt_n, ro_v;
  logic [ACW-1:0] acw_n;
  logic [31:0] tix;
  logic [HW-1:0] hix;
  assign x_take     = x_valid & x_ready;
  assign y_take     = y_valid & y_ready;
  assign rd_take    = rd_valid & rd_ready;
  assign start_pass = (ms == M_TILE) & sh_full & ~xb_rd;   // one idle cycle between passes (the row memories)
  assign ro_go      = (ms == M_RO) & (occ < CAP[4:0]);
  assign cnt_n      = (rem > 16'(1 << VW)) ? (VW+1)'(1 << VW) : rem[VW:0];
  assign ro_v       = ro_vb + (VW+1)'(rv);
  assign ro_pad     = (ro_v >= cnt);                       // a padding vector: nothing to read out
  assign a_val      = actl[(DL-1)*CW-1];
  assign a_cb0      = actl[(DL-1)*CW-2];
  assign acw_n[KW-1:0] = actl[(DL-2)*CW +: KW];
  for (genvar g = 0; g < @NG@; g++) begin : g_dec
    assign acw_n[KW + @FW@*g]            = a_val & ptt[@FW@*g];
    assign acw_n[KW + @FW@*g + 1]        = ptt[@FW@*g + 1];
    assign acw_n[KW + @FW@*g + 2]        = a_cb0 & ptt[@FW@*g + 2];
    assign acw_n[KW + @FW@*g + 3 +: @SB@] = ptt[@FW@*g + 3 +: @SB@];
  end
  assign tix = (((32'(pseg) << lgh) + 32'(lr)) << lgh) + 32'(lc);
  if (LGUB == 0) begin : g_h1
    assign hix = '0;
  end else begin : g_hn
    assign hix = li[LGUB-1:0];
  end

  always_ff @(posedge clk) begin
    // the accumulate control's delay line and the read-out pipeline
    actl    <= {actl[(DL-2)*CW-1:0], ((ms == M_RUN) | start_pass), (cc == '0), pp, (start_pass ? KW'(0) : rv[KW-1:0])};
    acw     <= acw_n;
    t_valid <= {t_valid[@TV@-2:0], r_rd};
    t_tag   <= {t_tag[(@TV@-1)*21-1:0], r_tag};
    if (rd_take) wbeat <= rd_data;

    if (rst) begin
      ms        <= M_IDLE;
      job_ready <= 1'b0;
      x_ready   <= 1'b0;
      swap      <= 1'b0;
      xb_rd     <= 1'b0;
      r_rd      <= 1'b0;
      t_valid   <= '0;
      occ       <= 5'd0;
      ls        <= L_IDLE;
      rq_valid  <= 1'b0;
      rd_ready  <= 1'b0;
      ld        <= '0;
      ld_hi     <= '0;
      tiles     <= 13'd0;
      sh_full   <= 1'b0;
      wave      <= 16'd0;
      rq_addr   <= 32'd0;
      rq_len    <= 24'd0;
    end else begin
      swap  <= 1'b0;
      xb_rd <= 1'b0;
      r_rd  <= 1'b0;
      occ   <= occ + {4'd0, (ro_go & ~ro_pad)} - {4'd0, y_take};
      if (wave != 16'd0) wave <= wave - 16'd1;

      case (ms)
        M_IDLE: begin
          if (job_valid & job_ready) begin
            job_ready <= 1'b0;
            mode  <= jmode;
            lgh   <= jq - 3'(jmode);
            hbm   <= CBW'((6'd1 << (jq - 3'(jmode))) - 6'd1);
            nbm   <= 5'((6'd1 << jq) - 6'd1);
            nrm   <= @L@'((3'd1 << jmode) - 3'd1);
            rem   <= job_batch;
            vbase <= 16'd0;
            mul   <= job_mul;
            shift <= job_shift;
            zp    <= job_zp;
            lo    <= job_lo;
            hi    <= job_hi;
            ms    <= M_CHUNK;
          end else
            job_ready <= 1'b1;
        end
        M_CHUNK: begin                               // the next chunk of the job: at most @CHV@ E vectors
          cnt   <= cnt_n;
          part  <= (KW+1)'((cnt_n + (VW+1)'(@D@ - 1)) >> @L@);
          tiles <= 13'(((13'(npm) + 13'd1) << lgh) << lgh);
          lp    <= '0;
          lr    <= '0;
          lc    <= '0;
          iv    <= '0;
          ik    <= '0;
          ica   <= '0;
          ia    <= '0;
          ic    <= 5'd0;
          icb   <= '0;
          x_ready <= 1'b1;
          ms    <= M_INGEST;
        end
        M_INGEST: begin
          if (x_take) begin
            if (ic == nbm) begin
              ic  <= 5'd0;
              icb <= '0;
              ia  <= '0;
              iv  <= iv + 1'b1;
              if ((KW+1)'(ik) + 1'b1 == part) begin
                ik  <= '0;
                ica <= ica + 1'b1;
              end else
                ik <= ik + 1'b1;
              if (iv + 1'b1 == cnt) begin
                x_ready <= 1'b0;
                ms <= M_TILE;
                rr <= '0;
                cc <= '0;
                pp <= '0;
              end
            end else begin
              ic <= ic + 5'd1;
              if (icb == hbm) begin
                icb <= '0;
                ia  <= ia + 1'b1;
              end else
                icb <= icb + 1'b1;
            end
          end
        end
        M_TILE: begin
          if (start_pass) begin                      // the tile is in the shadow registers: start its pass
            swap    <= 1'b1;
            sh_full <= 1'b0;
            wave    <= 16'(E - 1);
            xb_rd   <= 1'b1;
            xb_ra   <= {KW'(0), cc};
            xb_pid  <= pp;
            rv      <= (KW+1)'(1);
            dcnt    <= 16'(DRAIN);
            if (part == (KW+1)'(1)) begin
@ADVANCE@
            end else
              ms <= M_RUN;
          end
        end
        M_RUN: begin
          xb_rd <= 1'b1;
          xb_ra <= {rv[KW-1:0], cc};
          rv    <= rv + 1'b1;
          dcnt  <= 16'(DRAIN);
          if (rv + 1'b1 == part) begin
@ADVANCE@
          end
        end
        M_DRAIN: begin                               // the block's last sums are on their way to the row memories
          dcnt   <= dcnt - 16'd1;
          rv     <= '0;
          ro_rho <= '0;
          ro_ch  <= '0;
          ro_vb  <= '0;
          if (dcnt == 16'd0) ms <= M_RO;
        end
        M_RO: begin
          if (ro_go) begin
            r_rd  <= ~ro_pad;
            r_g   <= ygs[@SB@ +: @GW@];
            r_sub <= ygs[@SB@-1:0];
            r_v   <= rv[KW-1:0];
            r_tag <= {vbase + 16'(ro_v), (5'(ro_rho) << lgh) | 5'(rr)};
            if (rv + 1'b1 == part) begin
              rv <= '0;
              if (ro_ch == @L@'d@DM1@) begin
                ro_ch <= '0;
                ro_vb <= '0;
                if (ro_rho == nrm) begin
                  if (rr == hbm) ms <= M_FLUSH;
                  else begin
                    rr <= rr + 1'b1;
                    ms <= M_TILE;
                  end
                end else
                  ro_rho <= ro_rho + 1'b1;
              end else begin
                ro_ch <= ro_ch + 1'b1;
                ro_vb <= ro_vb + (VW+1)'(part);
              end
            end else
              rv <= rv + 1'b1;
          end
        end
        M_FLUSH: begin                               // the chunk's last results leave the output stage
          if (~r_rd & (t_valid == '0)) begin
            vbase <= vbase + 16'(cnt);
            rem   <= rem - 16'(cnt);
            if (rem == 16'(cnt)) begin
              ms <= M_IDLE;
              job_ready <= 1'b1;
            end else
              ms <= M_CHUNK;
          end
        end
        default: ms <= M_IDLE;
      endcase

      // the weight loader: one burst per tile into the shadow registers, one tile ahead of the array
      ld    <= '0;
      ld_hi <= '0;
      case (ls)
        L_IDLE: begin
          if ((tiles != 13'd0) & ~sh_full & ~start_pass & (ms != M_IDLE) & (ms != M_CHUNK)) begin
            rq_valid <= 1'b1;
            rq_addr  <= (tix << LGE) + (tix << LGUB);
            rq_len   <= 24'(TBEATS);
            ls       <= L_REQ;
          end
        end
        L_REQ: begin
          if (rq_valid & rq_ready) begin
            rq_valid <= 1'b0;
            ls       <= L_RX;
            li       <= '0;
            tiles    <= tiles - 13'd1;
            if (lc == hbm) begin
              lc <= '0;
              if (lp == npm) begin
                lp <= '0;
                lr <= lr + 1'b1;
              end else
                lp <= lp + 1'b1;
            end else
              lc <= lc + 1'b1;
          end
        end
        L_RX: begin
          // a beat may land in the shadow registers only when the last swap has passed (wave = 0)
          rd_ready <= (wave <= 16'd1) & ~(rd_take & (li == (LGE+1)'(TBEATS - 1)));
          if (rd_take) begin
            if (~li[LGE]) ld[li[LGE-1:0]] <= 1'b1;
            else          ld_hi[hix] <= 1'b1;
            li <= li + 1'b1;
            if (li == (LGE+1)'(TBEATS - 1)) begin
              sh_full <= 1'b1;
              ls      <= L_IDLE;
            end
          end
        end
        default: ls <= L_IDLE;
      endcase
    end
  end
endmodule
"""

ACC = r"""
  begin : g_acc@G@                                    // group @G@: @NBLK@ result block(s)
    localparam int AG = LGE + @KP@ - 1 + @LGSUB@;    // address bits: slot, vector / 2
    logic        en, en_o, ng_o, fi_o, rdr;
    logic [@SB@-1:0] sub, sub_o;
    logic [47:0] d0, d1, wd;
    logic        rd0, rd1, wr0, wr1;
    logic [9:0]  a_w, a_a, a_r, ad0, ad1;
    assign en    = acw[KW + @FW@*@I@];
    assign sub   = acw[KW + @FW@*@I@ + 3 +: @SB@];
    assign en_o  = acw_o[KW + @FW@*@I@];
    assign ng_o  = acw_o[KW + @FW@*@I@ + 1];
    assign fi_o  = acw_o[KW + @FW@*@I@ + 2];
    assign sub_o = acw_o[KW + @FW@*@I@ + 3 +: @SB@];
    assign rdr   = r_rd & (r_g == @GW@'d@G@);
    assign a_w   = 10'({sub_o, acw_o[KW-1:0]} >> 1);
    assign a_a   = 10'({sub, acw[KW-1:0]} >> 1);
    assign a_r   = 10'({r_sub, r_v} >> 1);
    assign wr0   = en_o & ~acw_o[0];
    assign wr1   = en_o &  acw_o[0];
    assign rd0   = (en & ~acw[0]) | (rdr & ~r_v[0]);
    assign rd1   = (en &  acw[0]) | (rdr &  r_v[0]);
    assign ad0   = wr0 ? a_w : en ? a_a : a_r;
    assign ad1   = wr1 ? a_w : en ? a_a : a_r;
    assign wd    = (fi_o ? 48'd0 : (acw_o[0] ? d1 : d0)) + (ng_o ? sn : sp);
    if (AG <= 8) begin : g_256
      srambank_64x4x48_6t122 m0 (.clk(clk), .ADDRESS(ad0[7:0]), .wd(wd), .banksel(rd0 | wr0), .read(rd0 & ~wr0),
                                 .write(wr0), .dataout(d0));
      srambank_64x4x48_6t122 m1 (.clk(clk), .ADDRESS(ad1[7:0]), .wd(wd), .banksel(rd1 | wr1), .read(rd1 & ~wr1),
                                 .write(wr1), .dataout(d1));
    end else if (AG == 9) begin : g_512
      srambank_128x4x48_6t122 m0 (.clk(clk), .ADDRESS(ad0[8:0]), .wd(wd), .banksel(rd0 | wr0), .read(rd0 & ~wr0),
                                  .write(wr0), .dataout(d0));
      srambank_128x4x48_6t122 m1 (.clk(clk), .ADDRESS(ad1[8:0]), .wd(wd), .banksel(rd1 | wr1), .read(rd1 & ~wr1),
                                  .write(wr1), .dataout(d1));
    end else begin : g_1024
      srambank_256x4x48_6t122 m0 (.clk(clk), .ADDRESS(ad0), .wd(wd), .banksel(rd0 | wr0), .read(rd0 & ~wr0),
                                  .write(wr0), .dataout(d0));
      srambank_256x4x48_6t122 m1 (.clk(clk), .ADDRESS(ad1), .wd(wd), .banksel(rd1 | wr1), .read(rd1 & ~wr1),
                                  .write(wr1), .dataout(d1));
    end
    assign dd[48*(2*@I@) +: 48]   = d0;
    assign dd[48*(2*@I@+1) +: 48] = d1;
  end
"""

ADVANCE = """\
if (cc == hbm) begin
  cc <= '0;
  if (pp == npm) begin
    pp <= '0;
    ms <= M_DRAIN;
  end else begin
    pp <= pp + 1'b1;
    ms <= M_TILE;
  end
end else begin
  cc <= cc + 1'b1;
  ms <= M_TILE;
end"""


def _hit(bw, nt):
    """The buffer's read enable of bank b: some term of the product reads it."""
    return " | ".join(f"(ptx[{(2 + bw) * t + bw + 1}] & (ptx[{(2 + bw) * t} +: {bw}] == b))" for t in range(nt))


def _pick(bw, nb):
    """The skew's bank select of term t, as an explicit OR over the banks (no chained vector)."""
    return ("\n        | ".join(f"((qblk[{bw}*t +: {bw}] == {bw}'d{b}) ? w[MEMW*{b} +: MEMW] : '0)" for b in range(nb)))


def _indent(text, n):
    return "\n".join(" " * n + ln for ln in text.splitlines())


def consts(L):
    D = 1 << L
    grp = ygroups(L)
    NG = 3 ** L
    SB = L
    GW = (NG - 1).bit_length()
    NS = 2 * NG
    SELW = GW + 1
    FW = 3 + SB
    BW = 2 * L
    maxp = max(len(products(L, m)) for m in range(L + 1))
    c = dict(L=L, D=D, DM1=D - 1, NT=D, BW=BW, NB=D * D, WW=16 + L, XW=17 + L, PW=33 + 2 * L, PX=48 - 33 - 2 * L,
             NG=NG, SB=SB, GW=GW, NS=NS, SELW=SELW, NSP=1 << SELW, FW=FW, TW=NG * FW,
             PIDW=(maxp - 1).bit_length(), XTW=D * (2 + BW), XZ=1 + L, XS=18 + L)
    c["grp"] = grp
    return c


def tables(L, c):
    """The case arms of the product tables."""
    D, BW, FW, PIDW = c["D"], c["BW"], c["FW"], c["PIDW"]
    cx, ct, cs, cn = [], [], [], []
    for m in range(L + 1):
        ps = products(L, m)
        cn.append(f"      2'd{m}: npm = {PIDW}'d{len(ps) - 1};")
        for i, p in enumerate(ps):
            key = f"{2 + PIDW}'d{(m << PIDW) | i}"
            xw = 0
            for t, (blk, neg) in enumerate(p["x"]):
                xw |= ((1 << (BW + 1)) | (int(neg) << BW) | blk) << (t * (2 + BW))
            tw = 0
            groups = set()
            for yb, neg, first in p["t"]:
                g, sub = c["grp"][yb]
                assert g not in groups, "two targets of a product in one accumulator group"
                groups.add(g)
                tw |= (1 | (int(neg) << 1) | (int(first) << 2) | (sub << 3)) << (g * FW)
            cx.append(f"      {key}: ptx = {c['XTW']}'h{xw:x};")
            ct.append(f"      {key}: ptt = {c['TW']}'h{tw:x};")
            cs.append(f"      {key}: pseg = {PIDW}'d{p['seg']};")
    cy = []
    for yb in range(D * D):
        g, sub = c["grp"][yb]
        cy.append(f"      {2 * L}'d{yb}: ygs = {c['GW'] + c['SB']}'d{(g << c['SB']) | sub};")
    return {"CASE_X": "\n".join(cx), "CASE_T": "\n".join(ct), "CASE_S": "\n".join(cs), "CASE_Y": "\n".join(cy),
            "CASE_N": "\n".join(cn)}


TITLES = {
    "s1": "one level of Strassen on one shared array",
    "s2": "two levels of Strassen on three arrays, one per leaf class",
    "s2s": "two levels of Strassen on one shared array",
}


def design_text(name):
    if name in THREE:
        return design3(name)
    L = LEVELS[name]
    c = consts(L)
    D, BW, NT = c["D"], c["BW"], c["NT"]
    sub = {k: str(v) for k, v in c.items() if k != "grp"}
    sub.update(tables(L, c))
    nblk = [sum(1 for v in c["grp"].values() if v[0] == g) for g in range(c["NG"])]
    sub["ACC"] = "".join(ACC.replace("@G@", str(g)).replace("@I@", str(g)).replace("@NBLK@", str(nblk[g]))
                         .replace("@LGSUB@", str((nblk[g] - 1).bit_length())) for g in range(c["NG"])).strip("\n")
    sub["CHV"] = str(2 * D)
    sub["CHP"] = "2"
    sub["TV"] = "6"
    sub["KP"] = "1"
    sub["AWO"] = str(6 - L)
    sub["NAME"] = name
    sub["TITLE"] = TITLES[name]
    sub["HIT"] = _hit(BW, NT)
    sub["CASE_XS"] = sub["CASE_X"]
    sub["PICK"] = _pick(BW, c["NB"])
    sub["PICKS"] = ("\n               | ".join(f"((sel == {c['SELW']}'d{i}) ? d[48*{i} +: 48] : 48'd0)"
                                              for i in range(c["NS"])))
    sub["SUM"] = " + ".join(f"tv[{c['XW']}*{t} +: {c['XW']}]" for t in range(NT))
    top = TOP
    while "@ADVANCE@" in top:
        k = top.index("@ADVANCE@")
        col = k - top.rfind("\n", 0, k) - 1
        top = top[:k - col] + _indent(ADVANCE, col) + top[k + len("@ADVANCE@"):]
    parts = [top, XBUF, SKEW, ARRAY, ROW, CELL, scale_text(True), gen.FIFO]
    text = "\n".join(s.strip("\n") + "\n" for s in parts)
    text = text.replace("@ACC@", sub.pop("ACC"))
    for k in sorted(sub, key=len, reverse=True):
        text = text.replace(f"@{k}@", sub[k])
    left = re.search(r"@[A-Z_0-9]+@", text)
    assert left is None, left.group(0)
    return text


# ------------------------------------------------------------------- two levels, three arrays (one per leaf class)
LANES = [                   # (module suffix, activation terms, weight bits, the operand is unsigned)
    ("a", 2, 18, False),    # class (1,2): at most 2 activation blocks, up to 4 weight blocks
    ("b", 4, 17, False),    # class (2,1): 4 activation blocks (two added, two subtracted), at most 2 weight blocks
    ("c", 4, 18, True),     # class (2,2): 4 activation blocks, all added, 4 weight blocks
]


def lane_of(w, x):
    """The array of a leaf: the narrowest class that holds both operands."""
    return 0 if len(x) <= 2 else (1 if len(w) <= 2 else 2)


def lane_products(m):
    """Per array, its products of mode m in schedule order (`first` is per array: each array has its own
    accumulators, and the read-out adds the arrays' partial sums)."""
    lv = leaves(m)
    out, seen = [[], [], []], [set(), set(), set()]
    for p in products(2, m):
        w, x, _ = lv[p["seg"]]
        ln = lane_of(w, x)
        t = []
        for yb, neg, _ in p["t"]:
            t.append((yb, neg, yb not in seen[ln]))
            seen[ln].add(yb)
        out[ln].append({"seg": p["seg"], "x": p["x"], "t": t})
    return out


CELL3 = r"""
// One multiply-accumulate cell of array @S@: signed @WW@-bit weight times @XKIND@ 18-bit activation operand, exact,
// accumulated modulo 2^48; the weight double-buffered as in every design of this file.
module gemm_cell_@S@ (
  input  logic        clk,
  input  logic        ld, ld_hi,
  input  logic [15:0] w_d,
  input  logic [1:0]  w_h,
  input  logic        swap_in,
  input  logic [17:0] x_in,
  input  logic [47:0] s_in,
  output logic        swap_out,
  output logic [17:0] x_out,
  output logic [47:0] s_out
);
  logic [@WW@-1:0]        w_sh, w_act;
  logic signed [@PW@-1:0] p;
  assign p = $signed(w_act) * $signed(@XEXT@);
  always_ff @(posedge clk) begin
    if (ld)    w_sh[15:0] <= w_d;
    if (ld_hi) w_sh[@WW@-1:16] <= w_h[@WW@-17:0];
    if (swap_in) w_act <= w_sh;
    swap_out <= swap_in;
    x_out    <= x_in;
    s_out    <= s_in + {{@PX@{p[@PW@-1]}}, p};
  end
endmodule
"""

ROW3 = r"""
// One row of array @S@: E cells and the row's accumulators (the groups this array's products update), as in the
// shared-array designs; the read-out selects one word into the register `dout` (the output stage is outside:
// it adds the three arrays' partial sums).
module gemm_row_@S@ #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic                ld, ld_hi,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [2*(1<<LGE)-1:0] w_h,
  input  logic [(1<<LGE)-1:0] swap_in,
  input  logic [18*(1<<LGE)-1:0] x_in,
  input  logic [LGE+@KP@+@TWL@-1:0] acw,
  input  logic                r_rd,
  input  logic [@GW@-1:0]     r_g,
  input  logic [@SB@-1:0]     r_sub,
  input  logic [LGE+@KP@-1:0] r_v,
  output logic [(1<<LGE)-1:0] swap_out,
  output logic [18*(1<<LGE)-1:0] x_out,
  output logic [LGE+@KP@+@TWL@-1:0] acw_o,
  output logic [47:0]         dout
);
  localparam int E = 1 << LGE;
  localparam int KW = LGE + @KP@;
  logic [48*(E+1)-1:0] s;
  assign s[47:0] = 48'd0;
  for (genvar j = 0; j < E; j++) begin : g_cell
    gemm_cell_@S@ u (.clk(clk), .ld(ld), .ld_hi(ld_hi), .w_d(w_d[16*j +: 16]), .w_h(w_h[2*j +: 2]),
                   .swap_in(swap_in[j]), .x_in(x_in[18*j +: 18]),
                   .s_in(s[48*j +: 48]), .swap_out(swap_out[j]), .x_out(x_out[18*j +: 18]),
                   .s_out(s[48*(j+1) +: 48]));
  end

  logic [47:0] sp, sn;
  logic [48*@NGL@-1:0] pk;
  logic        r_par;
  assign sp = s[48*E +: 48];
  assign sn = 48'd0 - sp;
@ACC@
  always_ff @(posedge clk) begin
    acw_o <= acw;
    if (r_rd) r_par <= r_v[0];
    dout  <= @PKOR@;
  end
endmodule
"""

ARRAY3 = r"""
// Array @S@: E rows; activations, the swap tag and the accumulate control travel down the rows.
module gemm_array_@S@ #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic [(1<<LGE)-1:0] ld,
  input  logic [(1<<((LGE>3)?LGE-3:1))-1:0] ld_hi,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [(1<<LGE)-1:0] swap,
  input  logic [18*(1<<LGE)-1:0] x,
  input  logic [LGE+@KP@+@TWL@-1:0] acw,
  input  logic                r_rd,
  input  logic [@GW@-1:0]     r_g,
  input  logic [@SB@-1:0]     r_sub,
  input  logic [LGE+@KP@-1:0] r_v,
  output logic [48*(1<<LGE)-1:0] d
);
  localparam int E = 1 << LGE;
  localparam int XB = 18 * E;
  localparam int ACW = LGE + @KP@ + @TWL@;
  localparam int LGR = (LGE < 3) ? LGE : 3;          // log2 of the tile rows in one beat of upper bits
  logic [E*(E+1)-1:0]    sw;
  logic [XB*(E+1)-1:0]   xx;
  logic [ACW*(E+1)-1:0]  ac;
  assign sw[E-1:0]   = swap;
  assign xx[XB-1:0]  = x;
  assign ac[ACW-1:0] = acw;
  for (genvar i = 0; i < E; i++) begin : g_row
    gemm_row_@S@ #(.LGE(LGE)) u (
      .clk(clk), .ld(ld[i]), .ld_hi(ld_hi[i >> LGR]), .w_d(w_d),
      .w_h(w_d[2*E*(i & ((1 << LGR) - 1)) +: 2*E]),
      .swap_in(sw[E*i +: E]), .x_in(xx[XB*i +: XB]), .acw(ac[ACW*i +: ACW]),
      .r_rd(r_rd), .r_g(r_g), .r_sub(r_sub), .r_v(r_v),
      .swap_out(sw[E*(i+1) +: E]), .x_out(xx[XB*(i+1) +: XB]), .acw_o(ac[ACW*(i+1) +: ACW]),
      .dout(d[48*i +: 48]));
  end
endmodule
"""

OUTS = r"""
// The output stages: per row, the three arrays' partial sums of a result (those arrays that hold a part of it)
// are added in a register stage, then the five stages of the output stage.
module gemm_outs #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic [48*(1<<LGE)-1:0] d0, d1, d2,
  input  logic [2:0]          use_d,
  input  logic [15:0]         mul,
  input  logic [5:0]          shift,
  input  logic [15:0]         zp, lo, hi,
  output logic [16*(1<<LGE)-1:0] y
);
  for (genvar i = 0; i < (1 << LGE); i++) begin : g_row
    gemm_scale3 u (.clk(clk), .d0(d0[48*i +: 48]), .d1(d1[48*i +: 48]), .d2(d2[48*i +: 48]), .use_d(use_d),
                   .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi), .y(y[16*i +: 16]));
  end
endmodule
"""

LOADER3 = r"""      // the weight loader: one burst per tile; the tiles of the next slot (one per array that works in it) are
      // loaded one after the other into the arrays' shadow registers, one slot ahead of the arrays
@LDCLR@
      case (ls)
        L_IDLE: begin
          if ((tiles != 13'd0) & ~sh_full & ~start_pass & (ms != M_IDLE) & (ms != M_CHUNK)) begin
            rq_valid <= 1'b1;
            rq_addr  <= (tix << LGE) + (tix << LGUB);
            rq_len   <= 24'(TBEATS);
            ls       <= L_REQ;
          end
        end
        L_REQ: begin
          if (rq_valid & rq_ready) begin
            rq_valid <= 1'b0;
            ls       <= L_RX;
            li       <= '0;
            lmore    <= lnext;
            if (~lnext) begin                        // the slot's last tile: the loader's next slot
              tiles <= tiles - 13'd1;
              if (lc == hbm) begin
                lc <= '0;
                if (lp == npm) begin
                  lp <= '0;
                  lr <= lr + 1'b1;
                end else
                  lp <= lp + 1'b1;
              end else
                lc <= lc + 1'b1;
            end
          end
        end
        L_RX: begin
          // a beat may land in the shadow registers only when the last swap has passed (wave = 0)
          rd_ready <= (wave <= 16'd1) & ~(rd_take & (li == (LGE+1)'(TBEATS - 1)));
          if (rd_take) begin
@LDSET@
            li <= li + 1'b1;
            if (li == (LGE+1)'(TBEATS - 1)) begin
              ls <= L_IDLE;
              if (lmore) ll <= ll + 2'd1;
              else begin
                ll      <= 2'd0;
                sh_full <= 1'b1;
              end
            end
          end
        end
        default: ls <= L_IDLE;
      endcase
    end
  end
endmodule
"""


def top3():
    """The three-array top module: the shared-array top with the per-array parts replaced."""
    t = TOP

    def rep(a, b):
        nonlocal t
        assert t.count(a) == 1, (a, t.count(a))
        t = t.replace(a, b)
    lanes = range(3)
    rep("// T = E: a weight tile is E x E.", "// Three E x E arrays, one per leaf class (see the note in the generator); T = E: a weight tile is E x E.")
    rep("  localparam int ACW = KW + @TW@;                    // the accumulate control of a row\n",
        "".join(f"  localparam int ACW{l} = KW + @TWL{l}@;               // the accumulate control of a row of array {l}\n"
                for l in lanes))
    rep("  localparam int CW = KW + @PIDW@ + 2;               // the same, compact: valid, first column block, product, vector",
        "  localparam int CW = KW + @PIDW@ + 4;               // the same, compact: valid per array, first column block, slot, vector")
    rep("  logic [@PIDW@-1:0] npm;                            // products - 1\n",
        "  logic [@PIDW@-1:0] npm;                            // slots of a column block - 1\n"
        "  logic [@PIDW@:0] nl0, nl1, nl2;                    // products of each array (it works in the slots below that)\n"
        "  logic [3*(@PIDW@+1)-1:0] nl;\n")
    rep("  logic            swap;\n", "  logic [2:0]      swap;\n")
    rep("  logic [E-1:0]    ld;\n  logic [(1<<HW)-1:0] ld_hi;\n",
        "".join(f"  logic [E-1:0]    ld{l};\n  logic [(1<<HW)-1:0] ldh{l};\n" for l in lanes))
    rep("  logic [ACW-1:0]  acw;                              // decoded, at row 0\n",
        "".join(f"  logic [ACW{l}-1:0] acw{l}, acw_n{l};                  // decoded, at row 0 of array {l}\n" for l in lanes))
    rep("  logic [@TV@-1:0] t_valid;", "  logic [2:0]      r_use, r_use1, r_use2;            // the arrays that hold a part of the beat read out\n"
        "  logic [@TV@-1:0] t_valid;")
    rep("  logic [LGE:0] li;\n", "  logic [LGE:0] li;\n  logic [1:0]  ll;                                   // the array being loaded\n"
        "  logic        lmore;                                // another array's tile follows in this slot\n")
    rep("  logic [E-1:0]    sk_swap;\n  logic [@XW@*E-1:0] sk_x;\n",
        "".join(f"  logic [E-1:0]    sk_swap{l};\n  logic [18*E-1:0] sk_x{l};\n  logic [48*E-1:0] ad{l};\n" for l in lanes))
    a = t.index("  gemm_skew #(.LGE(LGE)) skew (")
    b = t.index("  gemm_fifo #(")
    inst = ""
    off = 0
    for l, (sfx, nt, _, _) in enumerate(LANES):
        inst += (f"  gemm_skew_{sfx} #(.LGE(LGE)) skew{l} (\n"
                 f"    .clk(clk), .swap(swap[{l}]), .q(xq), .mode(mode), .qpid(xqpid), .qsb(xqsb),\n"
                 f"    .swap_o(sk_swap{l}), .x_o(sk_x{l}));\n"
                 f"  gemm_array_{sfx} #(.LGE(LGE)) array{l} (\n"
                 f"    .clk(clk), .ld(ld{l}), .ld_hi(ldh{l}), .w_d(wbeat), .swap(sk_swap{l}), .x(sk_x{l}), .acw(acw{l}),\n"
                 f"    .r_rd(r_rd), .r_g(r_g), .r_sub(r_sub), .r_v(r_v), .d(ad{l}));\n")
        off += nt
    inst += ("  gemm_outs #(.LGE(LGE)) outs (\n"
             "    .clk(clk), .d0(ad0), .d1(ad1), .d2(ad2), .use_d(r_use2), .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi),\n"
             "    .y(ya));\n")
    t = t[:a] + inst + t[b:]
    rep("  logic [@TW@-1:0]  ptt;                             // the targets: per group {slot, first, negate, enable}\n",
        "".join(f"  logic [@TWL{l}@-1:0] ptt{l};                          // the targets of array {l}: per group {{slot, first, negate, enable}}\n"
                for l in lanes))
    rep("  logic [@PIDW@-1:0] pseg;                           // the loader's product: its weight segment\n",
        "  logic [17:0] psg;                                  // the loader's slot: per array its weight segment\n"
        "  logic [5:0]  pseg;\n  logic [2:0]  ytu;                                  // read-out: the arrays that hold a part of the block\n")
    rep("  assign a_pid = actl[(DL-1)*CW-3 -: @PIDW@];", "  assign a_pid = actl[(DL-1)*CW-5 -: @PIDW@];")
    a = t.index("  always_comb begin\n    case ({mode, a_pid})")
    b = t.index("  always_comb begin\n    case ({mode, lp})")
    t = t[:a] + "".join(f"  always_comb begin\n    case ({{mode, a_pid}})\n@CASE_T{l}@\n      default: ptt{l} = '0;\n"
                        f"    endcase\n  end\n" for l in lanes) + t[b:]
    rep("      default: pseg = '0;\n    endcase\n  end\n",
        "      default: psg = '0;\n    endcase\n  end\n"
        "  assign pseg = (ll == 2'd0) ? psg[5:0] : (ll == 2'd1) ? psg[11:6] : psg[17:12];\n"
        "  always_comb begin\n    case ({mode, ro_rho, ro_ch})\n@CASE_U@\n      default: ytu = '0;\n    endcase\n  end\n")
    rep("      default: npm = '0;\n    endcase\n  end\n",
        "      default: nl = '0;\n    endcase\n  end\n  assign nl0 = nl[@PIDW@:0];\n"
        "  assign nl1 = nl[2*@PIDW@+1:@PIDW@+1];\n  assign nl2 = nl[3*@PIDW@+2:2*@PIDW@+2];\n"
        "  assign npm = @PIDW@'(nl0 - 1'b1);\n")
    rep("  logic        x_take, y_take, start_pass, ro_go, rd_take, a_val, a_cb0, ro_pad;",
        "  logic        x_take, y_take, start_pass, ro_go, rd_take, a_cb0, ro_pad, lnext;\n"
        "  logic [2:0]  a_val, act;")
    rep("  logic [ACW-1:0] acw_n;\n", "")
    rep("  assign a_val      = actl[(DL-1)*CW-1];\n  assign a_cb0      = actl[(DL-1)*CW-2];\n",
        "  assign a_val      = actl[(DL-1)*CW-1 -: 3];\n  assign a_cb0      = actl[(DL-1)*CW-4];\n"
        "  assign act        = {((@PIDW@+1)'(pp) < nl2), ((@PIDW@+1)'(pp) < nl1), ((@PIDW@+1)'(pp) < nl0)};\n"
        "  assign lnext      = (ll == 2'd0) ? ((@PIDW@+1)'(lp) < nl1) : (ll == 2'd1) ? ((@PIDW@+1)'(lp) < nl2) : 1'b0;\n")
    a = t.index("  assign acw_n[KW-1:0] = actl[(DL-2)*CW +: KW];")
    b = t.index("  assign tix = ")
    dec = ""
    for l in lanes:
        dec += (f"  assign acw_n{l}[KW-1:0] = actl[(DL-2)*CW +: KW];\n"
                f"  for (genvar g = 0; g < @NGL{l}@; g++) begin : g_dec{l}\n"
                f"    assign acw_n{l}[KW + @FW@*g]            = a_val[{l}] & ptt{l}[@FW@*g];\n"
                f"    assign acw_n{l}[KW + @FW@*g + 1]        = ptt{l}[@FW@*g + 1];\n"
                f"    assign acw_n{l}[KW + @FW@*g + 2]        = a_cb0 & ptt{l}[@FW@*g + 2];\n"
                f"    assign acw_n{l}[KW + @FW@*g + 3 +: @SB@] = ptt{l}[@FW@*g + 3 +: @SB@];\n"
                f"  end\n")
    t = t[:a] + dec + t[b:]
    rep("actl    <= {actl[(DL-2)*CW-1:0], ((ms == M_RUN) | start_pass), (cc == '0), pp,",
        "actl    <= {actl[(DL-2)*CW-1:0], (act & {3{(ms == M_RUN) | start_pass}}), (cc == '0), pp,")
    rep("    acw     <= acw_n;\n", "".join(f"    acw{l}    <= acw_n{l};\n" for l in lanes)
        + "    r_use1  <= r_use;\n    r_use2  <= r_use1;\n")
    rep("      swap      <= 1'b0;\n", "      swap      <= 3'd0;\n")
    rep("      t_valid   <= '0;\n", "      t_valid   <= '0;\n      ll        <= 2'd0;\n")
    rep("      ld        <= '0;\n      ld_hi     <= '0;\n",
        "".join(f"      ld{l}       <= '0;\n      ldh{l}      <= '0;\n" for l in lanes))
    rep("      swap  <= 1'b0;\n", "      swap  <= 3'd0;\n")
    rep("            swap    <= 1'b1;\n", "            swap    <= act;\n")
    rep("            r_rd  <= ~ro_pad;\n", "            r_rd  <= ~ro_pad;\n            r_use <= ytu;\n")
    a = t.index("      // the weight loader: one burst per tile")
    ldclr = "".join(f"      ld{l}  <= '0;\n      ldh{l} <= '0;\n" for l in lanes).rstrip("\n")
    ldset = "".join(f"            if (ll == 2'd{l}) begin\n              if (~li[LGE]) ld{l}[li[LGE-1:0]] <= 1'b1;\n"
                    f"              else          ldh{l}[hix] <= 1'b1;\n            end\n" for l in lanes).rstrip("\n")
    t = t[:a] + LOADER3.replace("@LDCLR@", ldclr).replace("@LDSET@", ldset)
    return t


def design3(name):
    L, D, BW, FW, SB, GW, PIDW, KP = 2, 4, 4, 5, 2, 4, 5, 2
    grp = ygroups(L)
    lp = [lane_products(m) for m in range(3)]                    # [mode][lane] -> products
    used = [sorted({grp[yb][0] for m in range(3) for p in lp[m][l] for yb, _, _ in p["t"]}) for l in range(3)]
    offs = [0, 2, 6]
    NTT = 10
    cx, cs, cn, cu = [], [], [], []
    ct, cxl = [[], [], []], [[], [], []]
    for m in range(3):
        counts = [len(lp[m][l]) for l in range(3)]
        assert counts[0] >= counts[1] >= counts[2] and max(counts) <= 1 << PIDW
        cn.append(f"      2'd{m}: nl = {3 * (PIDW + 1)}'d{counts[0] | counts[1] << (PIDW + 1) | counts[2] << (2 * PIDW + 2)};")
        for i in range(counts[0]):
            key = f"{2 + PIDW}'d{(m << PIDW) | i}"
            xw = sg = 0
            for l in range(3):
                if i >= counts[l]:
                    continue
                p = lp[m][l][i]
                assert len(p["x"]) <= LANES[l][1]
                xl = 0
                for t, (blk, neg) in enumerate(p["x"]):
                    xw |= ((1 << (BW + 1)) | (int(neg) << BW) | blk) << ((offs[l] + t) * (2 + BW))
                    xl |= ((1 << (BW + 1)) | (int(neg) << BW) | blk) << (t * (2 + BW))
                cxl[l].append(f"      {key}: ptx = {LANES[l][1] * (2 + BW)}'h{xl:x};")
                sg |= p["seg"] << (6 * l)
                tw, groups = 0, set()
                for yb, neg, first in p["t"]:
                    g, sub = grp[yb]
                    assert g not in groups
                    groups.add(g)
                    tw |= (1 | (int(neg) << 1) | (int(first) << 2) | (sub << 3)) << (used[l].index(g) * FW)
                ct[l].append(f"      {key}: ptt{l} = {len(used[l]) * FW}'h{tw:x};")
            cx.append(f"      {key}: ptx = {NTT * (2 + BW)}'h{xw:x};")
            cs.append(f"      {key}: psg = 18'h{sg:x};")
        for yb in range(D * D):
            tu = sum(1 << l for l in range(3) if any(yb == t[0] for p in lp[m][l] for t in p["t"]))
            cu.append(f"      {2 + 2 * L}'d{(m << (2 * L)) | yb}: ytu = 3'd{tu};")
    cy = [f"      {2 * L}'d{yb}: ygs = {GW + SB}'d{(grp[yb][0] << SB) | grp[yb][1]};" for yb in range(D * D)]
    sub = dict(L=L, D=D, DM1=D - 1, NT=NTT, BW=BW, NB=D * D, GW=GW, SB=SB, FW=FW, PIDW=PIDW, XTW=NTT * (2 + BW),
               KP=KP, AWO=5 + KP - L, TV=8, CHP=1 << KP, CHV=D << KP, NAME=name, TITLE=TITLES[name], XW=18, WW=18)
    sub = {k: str(v) for k, v in sub.items()}
    sub.update(CASE_X="\n".join(cx), CASE_S="\n".join(cs), CASE_N="\n".join(cn), CASE_U="\n".join(cu),
               CASE_Y="\n".join(cy))
    sub["HIT"] = _hit(BW, NTT)
    sub["PICK"] = _pick(BW, D * D)
    top = top3()
    while "@ADVANCE@" in top:
        k = top.index("@ADVANCE@")
        col = k - top.rfind("\n", 0, k) - 1
        top = top[:k - col] + _indent(ADVANCE, col) + top[k + len("@ADVANCE@"):]
    parts = [top, XBUF]
    for l, (sfx, nt, ww, uns) in enumerate(LANES):
        sub[f"CASE_T{l}"] = "\n".join(ct[l])
        sub[f"TWL{l}"] = str(len(used[l]) * FW)
        sub[f"NGL{l}"] = str(len(used[l]))
        acc = ""
        for i, g in enumerate(used[l]):
            subs = [grp[yb][1] for m in range(3) for p in lp[m][l] for yb, _, _ in p["t"] if grp[yb][0] == g]
            blk = (ACC.replace("@G@", str(g)).replace("@I@", str(i)).replace("@NBLK@", str(len(set(subs))))
                   .replace("@LGSUB@", str(max(subs).bit_length())))
            a = blk.index("    assign dd[48*(2*")
            blk = (blk[:a] + "    logic        selg;\n    always_ff @(posedge clk)\n"
                   f"      if (r_rd) selg <= (r_g == {GW}'d{g});\n"
                   f"    assign pk[48*{i} +: 48] = selg ? (r_par ? d1 : d0) : 48'd0;\n  end\n")
            acc += blk
        lane = {"S": sfx, "WW": ww, "PW": ww + 18 + int(uns), "PX": 48 - ww - 18 - int(uns),
                "XEXT": "{1'b0, x_in}" if uns else "x_in", "XKIND": "unsigned" if uns else "signed",
                "TWL": len(used[l]) * FW, "NGL": len(used[l]), "ACC": acc.strip("\n"), "CASE_XS": "\n".join(cxl[l]),
                "PKOR": " | ".join(f"pk[48*{i} +: 48]" for i in range(len(used[l])))}
        skew = (SKEW.replace("module gemm_skew ", f"module gemm_skew_{sfx} ").replace("@NT@", str(nt))
                .replace("@XZ@", "2").replace("@XS@", "19")
                .replace("@SUM@", " + ".join(f"tv[18*{t} +: 18]" for t in range(nt))))
        for piece in (skew, ARRAY3, ROW3, CELL3):
            for k in sorted(lane, key=len, reverse=True):
                piece = piece.replace(f"@{k}@", str(lane[k]))
            parts.append(piece)
    parts += [OUTS, scale_text(False), gen.FIFO]
    text = "\n".join(s.strip("\n") + "\n" for s in parts)
    for k in sorted(sub, key=len, reverse=True):
        text = text.replace(f"@{k}@", sub[k])
    left = re.search(r"@[A-Z_0-9]+@", text)
    assert left is None, left.group(0)
    return text


def cycles3():
    """The three-array design's steady-state cycles per job (see the design note)."""
    nb = "(n//e)"
    g = f"min({nb},4)"
    k = f"({g}//4)"                                        # 1 with two levels in use (three arrays work), else 0
    hb = f"({nb}//{g})"
    tb = "(e+max(1,e//8))"
    t1 = f"({tb}+max(lat+2,4,e))"                          # a slot's first tile
    tx = f"({tb}+max(lat+1,3))"                            # every further tile of the slot

    def chunk(c, p, z):
        ro = f"{g}*4*{p}"
        s1, s2, s3 = (f"max({p}+1,{t1}{x})" for x in ("", f"+{tx}", f"+2*{tx}"))
        return (f"(max({c}*{nb}+1,max(lat+2,4)+{tb}+2*{k}*{tx})"
                f"+{hb}*((9*{hb}-1)*{k}*{s3}+7*{hb}*{k}*{s2}+((4+10*min({g}-1,2)-16*{k})*{hb}-1+{k})*{s1})"
                f"+({hb}-1)*max({p}+2*e+5+{ro},{t1}+2*{k}*{tx})+{p}+2*e+{ro}+{z}+6)")
    full = "(16*e)"
    r = f"(batch%{full})"
    p = f"ceil_div({r},4)"
    return (f"(batch//{full})*{chunk(full, '4*e', '9')}"
            f"+min({r},1)*{chunk(r, p, f'max(0,9-4*{p}+{r})')}+1")


def cycles(name):
    """The steady-state cycles per job as the declaration's formula (names n, batch, e, lat); see the design note."""
    if name in THREE:
        return cycles3()
    L = LEVELS[name]
    D = 1 << L
    nb = "(n//e)"
    g = f"min({nb},{D})"                                   # row parts: 2^m
    hb = f"({nb}//{g})"                                    # column blocks (and row blocks) of a part
    np_ = f"(5*{g}-3)" if L == 1 else f"((5*{g}*{g}+5*{g}-2)//2)"      # products: (D / 2^m) * 7^m
    tb = f"(e+max(1,{L}*e//16))"                           # beats of a tile
    load = f"({tb}+max(lat+2,4,e))"                        # from one tile in the shadow registers to the next

    def chunk(c, p, z):
        ro = f"{g}*{D}*{p}"                                # read-out cycles of a row block
        return (f"(max({c}*{nb}+1,max(lat+2,4)+{tb})+{hb}*({np_}*{hb}-1)*max({p}+1,{load})"
                f"+({hb}-1)*max({p}+2*e+5+{ro},{load})+{p}+2*e+{ro}+{z}+6)")
    full = f"({2 * D}*e)"
    r = f"(batch%{full})"
    p = f"ceil_div({r},{D})"
    return (f"(batch//{full})*{chunk(full, '2*e', '7')}"
            f"+min({r},1)*{chunk(r, p, f'max(0,7-{D}*{p}+{r})')}+1")


def declare(name):
    return {"cycles": cycles(name), "layout": layout(LEVELS[name])}


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 2 or argv[0] not in LEVELS:
        print("usage: gen_strassen.py {s1|s2|s2s} OUTDIR", file=sys.stderr)
        return 2
    name, out = argv
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, name + ".sv"), "w") as fh:
        fh.write(design_text(name))
    with open(os.path.join(out, name + ".json"), "w") as fh:
        fh.write(json.dumps(declare(name), indent=1) + "\n")
    print(f"gen_strassen.py: {name}.sv, {name}.json written to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
