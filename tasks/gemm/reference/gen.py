#!/usr/bin/env python3.12
"""Generator of the `gemm` reference designs (own code).

    python3.12 tasks/gemm/reference/gen.py par            # print one design
    python3.12 tasks/gemm/reference/gen.py --write        # write every design and its declaration beside this file
    python3.12 tasks/gemm/reference/gen.py --check        # the files beside this file are what --write would write

A design is one SystemVerilog file, top module `gemm #(LGE, LAT)`, and a declaration `<name>.json`: the steady-state
cycle count as a formula, and the memory layout when it is not the canonical one. The designs follow the hierarchy
rule of the task (README.md, "Scoring"): below the top, every module output is a register or a child's output, and
every child input is driven by a register, a child output, a module input or a constant.

  par   the plain classical array: E x E multiply-accumulate cells, the weight tile double-buffered in the cells
        (a shadow register per cell, swapped by a tag that travels with the activations), activations streamed
        through the array from an on-chip buffer, one two-block accumulator memory per row, the output stage per row.
  fip   the inner-product form (gen_fip.py): half the multipliers per row, two correction terms.
  s1    one level of Strassen on one shared array (gen_strassen.py), the weight-block sums stored in memory.
  s2    two levels of Strassen on three arrays, one per class of leaf products (gen_strassen.py).
  s2s   two levels of Strassen on one shared array (gen_strassen.py).

`--write` and `--check` cover the designs task.json lists (`entries`); a design that is generated but not listed is
printed by name only. A player's entry (an entry with a `player`) is the player's file as submitted, beside these and
written by none of them, so `--write` and `--check` leave it out.
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

CELL = r"""
// One multiply-accumulate cell. The weight is double-buffered: `ld` loads the shadow, `swap_in` (a tag that travels
// with the activations, one cycle ahead of a pass's first vector) moves it into the active register.
module gemm_cell (
  input  logic        clk,
  input  logic        ld,
  input  logic [15:0] w_d,
  input  logic        swap_in,
  input  logic [15:0] x_in,
  input  logic [47:0] s_in,
  output logic        swap_out,
  output logic [15:0] x_out,
  output logic [47:0] s_out
);
  logic [15:0]        w_sh, w_act;
  logic signed [32:0] p;
  assign p = $signed(w_act) * $signed({1'b0, x_in});       // signed weight x unsigned activation, exact
  always_ff @(posedge clk) begin
    if (ld) w_sh <= w_d;
    if (swap_in) w_act <= w_sh;
    swap_out <= swap_in;
    x_out    <= x_in;
    s_out    <= s_in + {{15{p[32]}}, p};
  end
endmodule
"""

SCALE = r"""
// The output stage on one sum, five register stages, none longer than the cell's multiply-accumulate:
//   1  the sum times M, in two halves (the exact sum fits 44 bits: at most 4096 products below 2^31)
//   2  the product
//   3  the product, doubled, shifted right by s: its low 20 bits, and whether it fits them
//   4  rounded (half up) and the zero point added
//   5  clamped
// floor((p + 2^(s-1)) / 2^s) = ((2p >> s) + 1) >> 1 for every s >= 0 (for s = 0: (2p + 1) >> 1 = p).
module gemm_scale (
  input  logic        clk,
  input  logic [47:0] d0, d1,
  input  logic        sel,
  input  logic [15:0] mul,
  input  logic [5:0]  shift,
  input  logic [15:0] zp, lo, hi,
  output logic [15:0] y
);
  logic signed [43:0] a;
  logic signed [38:0] ph;
  logic        [37:0] pl;
  logic signed [59:0] p;
  logic signed [60:0] q;
  logic signed [19:0] q20;
  logic signed [20:0] r, t;
  logic               fit, neg, fit_t, neg_t;
  assign a = sel ? d1[43:0] : d0[43:0];
  assign q = $signed({p, 1'b0}) >>> shift;
  assign r = ($signed({q20[19], q20}) + 21'sd1) >>> 1;
  always_ff @(posedge clk) begin
    ph    <= $signed(a[43:22]) * $signed({1'b0, mul});
    pl    <= a[21:0] * mul;
    p     <= $signed({ph, 22'd0}) + $signed({1'b0, pl});
    q20   <= q[19:0];
    fit   <= (q[60:19] == {42{q[19]}});
    neg   <= q[60];
    t     <= r + $signed({5'd0, zp});
    fit_t <= fit;
    neg_t <= neg;
    if (~fit_t)                         y <= neg_t ? lo : hi;
    else if (t < $signed({5'd0, lo})) y <= lo;
    else if (t > $signed({5'd0, hi})) y <= hi;
    else                                y <= t[15:0];
  end
endmodule
"""

ROW = r"""
// One row of the array: E cells, the row's accumulator memory (two blocks, even and odd vectors, so that one sum
// is read, added and written back per cycle) and its output stage. The accumulate control enters from the row
// above one cycle later per row, as the activations do; the read-out control is the same for every row.
module gemm_row #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic                ld,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [(1<<LGE)-1:0] swap_in,
  input  logic [16*(1<<LGE)-1:0] x_in,
  input  logic                a_rd, a_first,
  input  logic [LGE:0]        a_v,
  input  logic                r_rd,
  input  logic [LGE:0]        r_v,
  input  logic [15:0]         mul,
  input  logic [5:0]          shift,
  input  logic [15:0]         zp, lo, hi,
  output logic [(1<<LGE)-1:0] swap_out,
  output logic [16*(1<<LGE)-1:0] x_out,
  output logic                a_rd_o, a_first_o,
  output logic [LGE:0]        a_v_o,
  output logic [15:0]         y
);
  localparam int E = 1 << LGE;
  logic [48*(E+1)-1:0] s;
  assign s[47:0] = 48'd0;
  for (genvar j = 0; j < E; j++) begin : g_cell
    gemm_cell u (.clk(clk), .ld(ld), .w_d(w_d[16*j +: 16]), .swap_in(swap_in[j]), .x_in(x_in[16*j +: 16]),
                 .s_in(s[48*j +: 48]), .swap_out(swap_out[j]), .x_out(x_out[16*j +: 16]),
                 .s_out(s[48*(j+1) +: 48]));
  end

  logic        r_sel;
  logic [47:0] d0, d1, wd;
  logic        rd0, rd1, wr0, wr1;
  logic [7:0]  ad0, ad1;
  assign wr0 = a_rd_o & ~a_v_o[0];
  assign wr1 = a_rd_o &  a_v_o[0];
  assign rd0 = (a_rd & ~a_v[0]) | (r_rd & ~r_v[0]);
  assign rd1 = (a_rd &  a_v[0]) | (r_rd &  r_v[0]);
  assign ad0 = wr0 ? 8'(a_v_o[LGE:1]) : a_rd ? 8'(a_v[LGE:1]) : 8'(r_v[LGE:1]);
  assign ad1 = wr1 ? 8'(a_v_o[LGE:1]) : a_rd ? 8'(a_v[LGE:1]) : 8'(r_v[LGE:1]);
  assign wd  = a_first_o ? s[48*E +: 48] : (a_v_o[0] ? d1 : d0) + s[48*E +: 48];
  srambank_64x4x48_6t122 m0 (.clk(clk), .ADDRESS(ad0), .wd(wd), .banksel(rd0 | wr0), .read(rd0 & ~wr0),
                             .write(wr0), .dataout(d0));
  srambank_64x4x48_6t122 m1 (.clk(clk), .ADDRESS(ad1), .wd(wd), .banksel(rd1 | wr1), .read(rd1 & ~wr1),
                             .write(wr1), .dataout(d1));
  always_ff @(posedge clk) begin
    a_rd_o    <= a_rd;
    a_first_o <= a_first;
    a_v_o     <= a_v;
    if (r_rd) r_sel <= r_v[0];
  end
  gemm_scale sc (.clk(clk), .d0(d0), .d1(d1), .sel(r_sel), .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi),
                 .y(y));
endmodule
"""

ARRAY = r"""
// The array: E rows; activations, the swap tag and the accumulate control travel down the rows.
module gemm_array #(parameter int LGE = 2) (
  input  logic                clk,
  input  logic [(1<<LGE)-1:0] ld,
  input  logic [16*(1<<LGE)-1:0] w_d,
  input  logic [(1<<LGE)-1:0] swap,
  input  logic [16*(1<<LGE)-1:0] x,
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
  localparam int MEMW = 16 * E;
  logic [E*(E+1)-1:0]     sw;
  logic [MEMW*(E+1)-1:0]  xx;
  logic [E:0]             ard, afi;
  logic [(LGE+1)*(E+1)-1:0] av;
  assign sw[E-1:0]    = swap;
  assign xx[MEMW-1:0] = x;
  assign ard[0]       = a_rd;
  assign afi[0]       = a_first;
  assign av[LGE:0]    = a_v;
  for (genvar i = 0; i < E; i++) begin : g_row
    gemm_row #(.LGE(LGE)) u (
      .clk(clk), .ld(ld[i]), .w_d(w_d), .swap_in(sw[E*i +: E]), .x_in(xx[MEMW*i +: MEMW]),
      .a_rd(ard[i]), .a_first(afi[i]), .a_v(av[(LGE+1)*i +: LGE+1]), .r_rd(r_rd), .r_v(r_v),
      .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi),
      .swap_out(sw[E*(i+1) +: E]), .x_out(xx[MEMW*(i+1) +: MEMW]),
      .a_rd_o(ard[i+1]), .a_first_o(afi[i+1]), .a_v_o(av[(LGE+1)*(i+1) +: LGE+1]),
      .y(y[16*i +: 16]));
  end
endmodule
"""

XBUF = r"""
// The activation buffer: 64 E beats (2 E vectors of up to 32 beats) in 1024-word blocks, 64 bits each.
// `q` is every bank's output and `qsel` the bank that was read: the reader selects.
module gemm_xbuf #(parameter int LGE = 2, parameter int LGB = 0) (
  input  logic                   clk,
  input  logic                   we_v, we_r,
  input  logic [LGE+5:0]         waddr,
  input  logic [16*(1<<LGE)-1:0] wdata,
  input  logic                   rd,
  input  logic [LGE+5:0]         raddr,
  output logic [(16<<LGE)*(1<<LGB)-1:0] q,
  output logic [LGB:0]           qsel
);
  localparam int MEMW = 16 << LGE;
  localparam int AW = LGE + 6;
  logic            we;
  logic [9:0]      wa, ra;
  logic [LGB:0]    wb, rb;
  assign we = we_v & we_r;
  assign wa = 10'(waddr);
  assign ra = 10'(raddr);
  if (LGB == 0) begin : g_one
    assign wb = '0;
    assign rb = '0;
  end else begin : g_many
    assign wb = {1'b0, waddr[AW-1:10]};
    assign rb = {1'b0, raddr[AW-1:10]};
  end
  for (genvar b = 0; b < (1 << LGB); b++) begin : g_bank
    logic bw, br;
    assign bw = we & (wb == b);
    assign br = rd & (rb == b) & ~bw;
    for (genvar k = 0; k < MEMW / 64; k++) begin : g_blk
      srambank_256x4x64_6t122 m (.clk(clk), .ADDRESS(bw ? wa : ra), .wd(wdata[64*k +: 64]), .banksel(bw | br),
                                 .read(br), .write(bw), .dataout(q[MEMW*b + 64*k +: 64]));
    end
  end
  always_ff @(posedge clk)
    if (rd) qsel <= rb;
endmodule
"""

SKEW = r"""
// The input skew: column j of the activation beat (and the swap tag) is delayed j + 1 cycles, so that every cell
// of a row sees its activation one cycle after its left neighbour's sum.
module gemm_skew #(parameter int LGE = 2, parameter int LGB = 0) (
  input  logic                   clk,
  input  logic                   swap,
  input  logic [(16<<LGE)*(1<<LGB)-1:0] q,
  input  logic [LGB:0]           qsel,
  output logic [(1<<LGE)-1:0]    swap_o,
  output logic [16*(1<<LGE)-1:0] x_o
);
  localparam int E = 1 << LGE;
  localparam int MEMW = 16 * E;
  logic [MEMW-1:0] x;
  logic [MEMW*((1<<LGB)+1)-1:0] pick;             // the selected bank's beat, as an OR over the banks
  assign pick[MEMW-1:0] = '0;
  for (genvar b = 0; b < (1 << LGB); b++) begin : g_pick
    assign pick[MEMW*(b+1) +: MEMW] = pick[MEMW*b +: MEMW] | ((qsel == b) ? q[MEMW*b +: MEMW] : '0);
  end
  assign x = pick[MEMW*(1<<LGB) +: MEMW];
  for (genvar j = 0; j < E; j++) begin : g_col
    logic [17*(j+1)-1:0] d;
    if (j == 0) begin : g_first
      always_ff @(posedge clk) d <= {swap, x[15:0]};
    end else begin : g_rest
      always_ff @(posedge clk) d <= {d[17*j-1:0], swap, x[16*j +: 16]};
    end
    assign swap_o[j]      = d[17*j + 16];
    assign x_o[16*j +: 16] = d[17*j +: 16];
  end
endmodule
"""

FIFO = r"""
// The result FIFO: 2^LGD entries and an output register.
module gemm_fifo #(parameter int W = 8, parameter int LGD = 3) (
  input  logic         clk, rst,
  input  logic         push,
  input  logic [W-1:0] din,
  input  logic         pop_ready,
  output logic         valid,
  output logic [W-1:0] dout
);
  localparam int D = 1 << LGD;
  logic [W*D-1:0]     mem;
  logic [W*(D+1)-1:0] pick;                           // the entry at the read pointer, as an OR over the entries
  logic [LGD-1:0] wp, rp;
  logic [LGD:0]   cnt;
  logic           take, direct;
  assign take   = ~valid | pop_ready;                 // the output register is free after this cycle
  assign direct = take & (cnt == '0);                 // a pushed beat goes straight to it
  assign pick[W-1:0] = '0;
  for (genvar i = 0; i < D; i++) begin : g_entry
    always_ff @(posedge clk)
      if (push & ~direct & (wp == i)) mem[W*i +: W] <= din;
    assign pick[W*(i+1) +: W] = pick[W*i +: W] | ((rp == i) ? mem[W*i +: W] : '0);
  end
  always_ff @(posedge clk) begin
    if (take) begin
      if (cnt != '0)  dout <= pick[W*D +: W];
      else if (push)  dout <= din;
    end
    if (rst) begin
      valid <= 1'b0;
      wp    <= '0;
      rp    <= '0;
      cnt   <= '0;
    end else begin
      if (take) valid <= (cnt != '0) | push;
      if (push & ~direct) wp <= wp + 1'b1;
      if (take & (cnt != '0)) rp <= rp + 1'b1;
      cnt <= cnt + {{LGD{1'b0}}, (push & ~direct)} - {{LGD{1'b0}}, (take & (cnt != '0))};
    end
  end
endmodule
"""

PAR_TOP = r"""
// gemm, par: the plain classical array (own code; generated by tasks/gemm/reference/gen.py).
//
// T = E: a weight tile is E x E, one tile row per memory beat. Per job, in chunks of at most 2 E vectors:
// the chunk's activations are written to the on-chip buffer; then, row block by row block, every tile of the block
// is loaded into the cells' shadow registers (one burst per tile) while the previous tile computes, the chunk's
// vectors stream through the array once per tile, the sums accumulate in the row memories, and after the block's
// last tile the sums are read out through the output stage into the result FIFO.
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
  localparam int LGB = (LGE > 4) ? LGE - 4 : 0;      // log2 of the buffer's banks of 1024 beats
  localparam int VW = LGE + 1;                       // a vector index inside a chunk (2 E vectors)
  localparam int DL = E + 2;                         // from a buffer read to row 0's accumulator read
  localparam int DRAIN = 2 * E + 4;                  // from a block's last buffer read to its read-out
  localparam int CAP = 16;                           // result beats under way at most (the FIFO's size)

  // ---- the job
  logic [2:0]  lgq;                                  // log2 (N / E)
  logic [4:0]  nbm;                                  // N / E - 1
  logic [15:0] rem, vbase;
  logic [15:0] mul, zp, lo, hi;
  logic [5:0]  shift;
  logic [VW:0] cnt;                                  // vectors in this chunk, 1 .. 2 E

  // ---- the main sequence
  typedef enum logic [2:0] {M_IDLE, M_INGEST, M_TILE, M_RUN, M_DRAIN, M_RO, M_FLUSH} mstate_t;
  mstate_t     ms;
  logic [VW:0] iv;                                   // ingest: vector
  logic [4:0]  ic;                                   // ingest: beat of the vector
  logic [4:0]  rr, cc;                               // the tile: row block, column block
  logic [VW:0] rv;                                   // the vector being read
  logic [15:0] dcnt;                                 // drain counter

  // ---- registers that drive the children
  logic            swap;
  logic            xb_rd;
  logic [LGE+5:0]  xb_ra;
  logic [E-1:0]    ld;
  logic [MEMW-1:0] wbeat;
  logic [DL*(VW+2)-1:0] actl;                        // the accumulate control on its way to row 0
  logic            r_rd;
  logic [VW-1:0]   r_v;
  logic [20:0]     r_tag;                            // the position (vector, row block) of the beat being read out
  logic [5:0]      t_valid;                          // read-out pipeline: valid, and the beat's position
  logic [6*21-1:0] t_tag;
  logic [4:0]      occ;                              // result beats issued and not yet transferred

  // ---- the weight loader
  typedef enum logic [1:0] {L_IDLE, L_REQ, L_RX} lstate_t;
  lstate_t     ls;
  logic [10:0] tiles;                                // tiles of this chunk not yet requested
  logic [4:0]  lr, lc;
  logic [LGE:0] li;
  logic        sh_full;
  logic [15:0] wave;                                 // cycles until the last swap has passed every cell

  logic [MEMW*(1<<LGB)-1:0] xq;
  logic [LGB:0]    xqsel;
  logic [E-1:0]    sk_swap;
  logic [MEMW-1:0] sk_x, ya;
  logic            f_valid;
  logic [MEMW+20:0] f_dout;

  gemm_xbuf #(.LGE(LGE), .LGB(LGB)) xbuf (
    .clk(clk), .we_v(x_valid), .we_r(x_ready), .waddr({iv[VW-1:0], ic}), .wdata(x_data),
    .rd(xb_rd), .raddr(xb_ra), .q(xq), .qsel(xqsel));
  gemm_skew #(.LGE(LGE), .LGB(LGB)) skew (
    .clk(clk), .swap(swap), .q(xq), .qsel(xqsel), .swap_o(sk_swap), .x_o(sk_x));
  gemm_array #(.LGE(LGE)) array (
    .clk(clk), .ld(ld), .w_d(wbeat), .swap(sk_swap), .x(sk_x),
    .a_rd(actl[DL*(VW+2)-1]), .a_first(actl[DL*(VW+2)-2]), .a_v(actl[DL*(VW+2)-3 -: VW]),
    .r_rd(r_rd), .r_v(r_v), .mul(mul), .shift(shift), .zp(zp), .lo(lo), .hi(hi), .y(ya));
  gemm_fifo #(.W(MEMW + 21), .LGD(4)) fifo (
    .clk(clk), .rst(rst), .push(t_valid[5]), .din({t_tag[5*21 +: 21], ya}), .pop_ready(y_ready),
    .valid(f_valid), .dout(f_dout));
  assign y_valid = f_valid;
  assign y_data  = f_dout[MEMW-1:0];
  assign y_row   = f_dout[MEMW +: 5];
  assign y_vec   = f_dout[MEMW+5 +: 16];

  logic        x_take, y_take, start_pass, ro_go, rd_take;
  logic [VW:0] cnt_n;
  assign x_take     = x_valid & x_ready;
  assign y_take     = y_valid & y_ready;
  assign rd_take    = rd_valid & rd_ready;
  assign start_pass = (ms == M_TILE) & sh_full & ~xb_rd;   // one idle cycle between passes (the row memories)
  assign ro_go      = (ms == M_RO) & (occ < CAP[4:0]);
  assign cnt_n      = (rem > 16'(2 * E)) ? (VW+1)'(2 * E) : rem[VW:0];

  always_ff @(posedge clk) begin
    // the accumulate control's delay line and the read-out pipeline
    actl    <= {actl[(DL-1)*(VW+2)-1:0], ((ms == M_RUN) | start_pass), (cc == 5'd0), (start_pass ? VW'(0) : rv[VW-1:0])};
    t_valid <= {t_valid[4:0], r_rd};
    t_tag   <= {t_tag[5*21-1:0], r_tag};
    if (rd_take) wbeat <= rd_data;

    if (rst) begin
      ms        <= M_IDLE;
      job_ready <= 1'b0;
      x_ready   <= 1'b0;
      swap      <= 1'b0;
      xb_rd     <= 1'b0;
      r_rd      <= 1'b0;
      t_valid   <= 6'd0;
      occ       <= 5'd0;
      ls        <= L_IDLE;
      rq_valid  <= 1'b0;
      rd_ready  <= 1'b0;
      ld        <= '0;
      tiles     <= 11'd0;
      sh_full   <= 1'b0;
      wave      <= 16'd0;
      rq_addr   <= 32'd0;
      rq_len    <= 24'd0;
    end else begin
      swap  <= 1'b0;
      xb_rd <= 1'b0;
      r_rd  <= 1'b0;
      occ   <= occ + {4'd0, ro_go} - {4'd0, y_take};
      if (wave != 16'd0) wave <= wave - 16'd1;

      case (ms)
        M_IDLE: begin
          if (job_valid & job_ready) begin
            job_ready <= 1'b0;
            lgq   <= 3'(job_lgn - 4'(LGE));
            nbm   <= 5'((6'd1 << 3'(job_lgn - 4'(LGE))) - 6'd1);
            rem   <= job_batch;
            vbase <= 16'd0;
            mul   <= job_mul;
            shift <= job_shift;
            zp    <= job_zp;
            lo    <= job_lo;
            hi    <= job_hi;
            ms    <= M_INGEST;
            x_ready <= 1'b1;
            iv    <= '0;
            ic    <= 5'd0;
            cnt   <= (job_batch > 16'(2 * E)) ? (VW+1)'(2 * E) : job_batch[VW:0];
            tiles <= 11'((12'd1 << 3'(job_lgn - 4'(LGE))) << 3'(job_lgn - 4'(LGE)));
            lr    <= 5'd0;
            lc    <= 5'd0;
          end else
            job_ready <= 1'b1;
        end
        M_INGEST: begin
          if (x_take) begin
            if (ic == nbm) begin
              ic <= 5'd0;
              iv <= iv + 1'b1;
              if (iv + 1'b1 == cnt) begin
                x_ready <= 1'b0;
                ms <= M_TILE;
                rr <= 5'd0;
                cc <= 5'd0;
              end
            end else
              ic <= ic + 5'd1;
          end
        end
        M_TILE: begin
          if (start_pass) begin                      // the tile is in the shadow registers: start its pass
            swap    <= 1'b1;
            sh_full <= 1'b0;
            wave    <= 16'(E - 1);
            xb_rd   <= 1'b1;
            xb_ra   <= {VW'(0), cc};
            rv      <= (VW+1)'(1);
            ms      <= (cnt == (VW+1)'(1)) ? ((cc == nbm) ? M_DRAIN : M_TILE) : M_RUN;
            if (cnt == (VW+1)'(1)) cc <= (cc == nbm) ? 5'd0 : cc + 5'd1;
            dcnt    <= 16'(DRAIN);
          end
        end
        M_RUN: begin
          xb_rd <= 1'b1;
          xb_ra <= {rv[VW-1:0], cc};
          rv    <= rv + 1'b1;
          dcnt  <= 16'(DRAIN);
          if (rv + 1'b1 == cnt) begin
            cc <= (cc == nbm) ? 5'd0 : cc + 5'd1;
            ms <= (cc == nbm) ? M_DRAIN : M_TILE;
          end
        end
        M_DRAIN: begin                               // the block's last sums are on their way to the row memories
          dcnt <= dcnt - 16'd1;
          rv   <= '0;
          if (dcnt == 16'd0) ms <= M_RO;
        end
        M_RO: begin
          if (ro_go) begin
            r_rd  <= 1'b1;
            r_v   <= rv[VW-1:0];
            r_tag <= {vbase + 16'(rv), rr};
            rv   <= rv + 1'b1;
            if (rv + 1'b1 == cnt) begin
              if (rr == nbm) ms <= M_FLUSH;
              else begin
                rr <= rr + 5'd1;
                ms <= M_TILE;
              end
            end
          end
        end
        M_FLUSH: begin                               // the chunk's last results leave the output stage
          if (~r_rd & (t_valid == 6'd0)) begin
            vbase <= vbase + 16'(cnt);
            rem   <= rem - 16'(cnt);
            if (rem == 16'(cnt)) begin
              ms <= M_IDLE;
              job_ready <= 1'b1;
            end else begin
              ms      <= M_INGEST;
              x_ready <= 1'b1;
              iv      <= '0;
              ic      <= 5'd0;
              cnt     <= ((rem - 16'(cnt)) > 16'(2 * E)) ? (VW+1)'(2 * E) : (VW+1)'(rem - 16'(cnt));
              tiles   <= 11'((12'd1 << lgq) << lgq);
              lr      <= 5'd0;
              lc      <= 5'd0;
            end
          end
        end
        default: ms <= M_IDLE;
      endcase

      // the weight loader: one burst per tile into the shadow registers, one tile ahead of the array
      ld <= '0;
      case (ls)
        L_IDLE: begin
          if ((tiles != 11'd0) & ~sh_full & ~start_pass & (ms != M_IDLE)) begin
            rq_valid <= 1'b1;
            rq_addr  <= 32'(((32'(lr) << lgq) + 32'(lc)) << LGE);
            rq_len   <= 24'(E);
            ls       <= L_REQ;
          end
        end
        L_REQ: begin
          if (rq_valid & rq_ready) begin
            rq_valid <= 1'b0;
            ls       <= L_RX;
            li       <= '0;
            tiles    <= tiles - 11'd1;
            lc       <= (lc == nbm) ? 5'd0 : lc + 5'd1;
            if (lc == nbm) lr <= lr + 5'd1;
          end
        end
        L_RX: begin
          // a beat may land in the shadow registers only when the last swap has passed (wave = 0)
          rd_ready <= (wave <= 16'd1) & ~(rd_take & (li == (LGE+1)'(E - 1)));
          if (rd_take) begin
            ld[li[LGE-1:0]] <= 1'b1;
            li <= li + 1'b1;
            if (li == (LGE+1)'(E - 1)) begin
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

def par_cycles():
    """par's steady-state cycles per job, as the declaration's formula (names n, batch, e, lat).

    A job runs in chunks of c <= 2 e vectors. A chunk: the activations in (c beats per vector block, or the first
    tile's load when that is longer); per row block its n/e passes, one per `slot` cycles (the c vectors and an idle
    cycle, or the next tile's load: lat, then e beats that must wait for the swap to cross the array); between row
    blocks the array drains and the c sums are read out; a few cycles of pipeline at the end."""
    nb = "(n//e)"
    load = "(e+max(lat+2,4,e))"

    def chunk(c):
        return (f"(max({c}*{nb},max(lat+1,3)+e)+{nb}*({nb}-1)*max({c}+1,{load})"
                f"+({nb}-1)*max(2*{c}+2*e+5,{load})+2*{c}+2*e+13)")
    return f"(batch//(2*e))*{chunk('(2*e)')}+min(batch%(2*e),1)*{chunk('(batch%(2*e))')}+1"


def par_text():
    return "\n".join(s.strip("\n") + "\n" for s in (PAR_TOP, XBUF, SKEW, ARRAY, ROW, CELL, SCALE, FIFO))


NAMES = ("par", "fip", "s1", "s2", "s2s")


def designs():
    """{name: (text function, declaration function)}: par here, the others in the generators beside this file
    (gen_fip.py: the inner-product form; gen_strassen.py: Strassen at one and two levels), which build on par's
    module texts."""
    out = {"par": (par_text, lambda: {"cycles": par_cycles(), "layout": None})}
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    if os.path.isfile(os.path.join(HERE, "gen_fip.py")):
        import gen_fip
        out["fip"] = (gen_fip.design_text, gen_fip.declare)
    if os.path.isfile(os.path.join(HERE, "gen_strassen.py")):
        import gen_strassen
        for name in ("s1", "s2", "s2s"):
            out[name] = (lambda n=name: gen_strassen.design_text(n), lambda n=name: gen_strassen.declare(n))
    return out


def design_text(name):
    return designs()[name][0]()


def declare_text(name):
    return json.dumps(designs()[name][1](), indent=1) + "\n"


def files(names=None):
    out = {}
    for name in names or designs():
        out[f"{name}.sv"] = design_text(name)
        out[f"{name}.json"] = declare_text(name)
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("design", nargs="?", choices=NAMES)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args(argv)
    if args.write or args.check:
        bad = []
        with open(os.path.join(os.path.dirname(HERE), "task.json")) as fh:
            listed = [os.path.basename(e["sv"])[:-3] for e in json.load(fh)["entries"] if "player" not in e]
        for name, text in sorted(files(listed).items()):
            path = os.path.join(HERE, name)
            if args.write:
                with open(path, "w") as fh:
                    fh.write(text)
            elif not os.path.isfile(path) or open(path).read() != text:
                bad.append(name)
        if bad:
            print("gen.py --check: not what the generator writes: " + ", ".join(bad), file=sys.stderr)
            return 1
        print(f"gen.py: {2 * len(listed)} files {'written' if args.write else 'ok'}")
        return 0
    if not args.design:
        ap.error("name a design, or --write / --check")
    sys.stdout.write(design_text(args.design))
    return 0


if __name__ == "__main__":
    sys.exit(main())
