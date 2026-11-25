// matmul as processing in memory: N memory banks, each with one small arithmetic unit at its edge,
// driven in lockstep by one command sequencer (all-bank mode). Modelled on the public description
// of HBM-PIM (an execution unit at the I/O boundary of each bank, register files GRF_A / GRF_B, and
// ordinary DRAM commands that trigger the unit's instructions); simplified, see the end of this text.
//
// Bank r (r = 0 .. N-1) holds, as N columns of AccW bits each:
//   arr0[r]  array row 0: row r of A, written by the host at `start`, each entry sign-extended
//   arr1[r]  array row 1: the results, row r of C
//   rb[r]    the bank's row buffer (the open row), read and written a column at a time
// Unit r: grfa[r] (N entries of W bits: one column of B), grfb[r] (the accumulator),
//   grfc[r] (N entries: the finished results of row r of C), and ONE multiplier.
// Host side: bf, a copy of B shifted one entry per column, so column j sits at entries k*N.
// Entry c of a bank-r vector is at index r*N + c (row-major, as the ports).
//
// The program, one command per cycle, issued to all banks at once (ph = the command):
//   ACT0               rb <= arr0                       (open row 0: row r of A)
//   for j = 0 .. N-1:
//     FILL             grfa <= column j of B (host broadcast write); grfb <= 0;
//                      grfc: cleared at j = 0, else the finished result grfb shifted in at the top
//     RD x N (k)       grfb <= grfb + rb[0] * grfa[0]   (the MAC reads column 0 of the open row);
//                      rb and grfa rotate one column (a burst in column order)
//   LAST               grfc: shift in the last result
//   ACT1               rb <= arr1                       (open row 1)
//   WR                 rb <= grfc                       (write the results into the open row)
//   PRE                arr1 <= rb                       (close the row: back into the array)
//   READ               C <= arr1, done                  (the host reads row 1 of every bank)
// Latency: 1 + N*(N+1) + 5 = N*N + N + 6 cycles from the start edge to done.
//
// Left out: two banks sharing one unit, SIMD lanes and FP16, the stored PIM program (here the
// sequencer is the program), DRAM timing (activate/precharge delays, refresh), the mode-entry
// sequences, more than two rows per bank.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  // the commands
  localparam int ACT0 = 0;
  localparam int FILL = 1;
  localparam int RD   = 2;
  localparam int LAST = 3;
  localparam int ACT1 = 4;
  localparam int WR   = 5;
  localparam int PRE  = 6;
  localparam int READ = 7;

  // the command sequencer
  logic                busy;
  logic [31:0]         ph;      // the current command
  logic [31:0]         j;       // the column of B being broadcast
  logic [31:0]         k;       // the read burst position
  // the host's copy of B
  logic [N*N*W-1:0]    bf;
  // the banks
  logic [N*N*AccW-1:0] arr0, arr1, rb;
  // the units
  logic [N*N*W-1:0]    grfa;
  logic [N*AccW-1:0]   grfb;
  logic [N*N*AccW-1:0] grfc;

  // the sequencer: one command per cycle
  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      ph   <= ACT0;
      j    <= 32'd0;
      k    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      ph   <= ACT0;
      j    <= 32'd0;
      k    <= 32'd0;
    end else if (busy) begin
      if (ph == RD) begin
        if (k == N - 1) begin
          k <= 32'd0;
          if (j == N - 1)
            ph <= LAST;
          else begin
            j  <= j + 32'd1;
            ph <= FILL;
          end
        end else
          k <= k + 32'd1;
      end else if (ph == READ) begin
        busy <= 1'b0;
        done <= 1'b1;
      end else
        ph <= ph + 32'd1;   // ACT0 -> FILL -> RD, LAST -> ACT1 -> WR -> PRE -> READ
    end

  // the host's copy of B: one entry further at every FILL, so column j is at entries k*N
  always_ff @(posedge clk)
    if (start)
      bf <= B;
    else if (busy) begin
      if (ph == FILL)
        bf <= bf >> W;
    end

  for (genvar r = 0; r < N; r++) begin : g_bank
    // unit r: one scalar multiply-accumulate, triggered by every RD. The signed product of the row
    // buffer's column 0 and grfa's entry 0 g, mod 2^AccW, is rb0 * g (g read unsigned) minus
    // rb0 * 2^W when g is negative (g as a signed number is its unsigned value minus 2^W).
    always_ff @(posedge clk)
      if (busy) begin
        if (ph == FILL)
          grfb[r*AccW +: AccW] <= '0;
        else if (ph == RD)
          grfb[r*AccW +: AccW] <= grfb[r*AccW +: AccW]
              + rb[r*N*AccW +: AccW] * {{AccW{1'b0}}, grfa[r*N*W +: W]}
              - (({AccW{grfa[r*N*W + W - 1]}} & rb[r*N*AccW +: AccW]) << W);
      end

    // columns 0 .. N-2 of bank r: the array rows, the row buffer and the unit's register entries
    for (genvar c = 0; c < N - 1; c++) begin : g_col
      always_ff @(posedge clk) begin
        if (start)
          arr0[(r*N+c)*AccW +: AccW] <= {{AccW{A[(r*N+c)*W + W - 1]}}, A[(r*N+c)*W +: W]};
        if (busy) begin
          if (ph == ACT0)
            rb[(r*N+c)*AccW +: AccW] <= arr0[(r*N+c)*AccW +: AccW];
          else if (ph == FILL) begin
            grfa[(r*N+c)*W +: W] <= bf[c*N*W +: W];
            if (j == 0)
              grfc[(r*N+c)*AccW +: AccW] <= '0;
            else
              grfc[(r*N+c)*AccW +: AccW] <= grfc[(r*N+c+1)*AccW +: AccW];
          end else if (ph == RD) begin
            rb[(r*N+c)*AccW +: AccW] <= rb[(r*N+c+1)*AccW +: AccW];
            grfa[(r*N+c)*W +: W] <= grfa[(r*N+c+1)*W +: W];
          end else if (ph == LAST)
            grfc[(r*N+c)*AccW +: AccW] <= grfc[(r*N+c+1)*AccW +: AccW];
          else if (ph == ACT1)
            rb[(r*N+c)*AccW +: AccW] <= arr1[(r*N+c)*AccW +: AccW];
          else if (ph == WR)
            rb[(r*N+c)*AccW +: AccW] <= grfc[(r*N+c)*AccW +: AccW];
          else if (ph == PRE)
            arr1[(r*N+c)*AccW +: AccW] <= rb[(r*N+c)*AccW +: AccW];
          else if (ph == READ)
            C[(r*N+c)*AccW +: AccW] <= arr1[(r*N+c)*AccW +: AccW];
        end
      end
    end

    // the last column of bank r: the rotations wrap to column 0, results enter here
    always_ff @(posedge clk) begin
      if (start)
        arr0[(r*N+N-1)*AccW +: AccW] <= {{AccW{A[(r*N+N-1)*W + W - 1]}}, A[(r*N+N-1)*W +: W]};
      if (busy) begin
        if (ph == ACT0)
          rb[(r*N+N-1)*AccW +: AccW] <= arr0[(r*N+N-1)*AccW +: AccW];
        else if (ph == FILL) begin
          grfa[(r*N+N-1)*W +: W] <= bf[(N-1)*N*W +: W];
          if (j == 0)
            grfc[(r*N+N-1)*AccW +: AccW] <= '0;
          else
            grfc[(r*N+N-1)*AccW +: AccW] <= grfb[r*AccW +: AccW];
        end else if (ph == RD) begin
          rb[(r*N+N-1)*AccW +: AccW] <= rb[r*N*AccW +: AccW];
          grfa[(r*N+N-1)*W +: W] <= grfa[r*N*W +: W];
        end else if (ph == LAST)
          grfc[(r*N+N-1)*AccW +: AccW] <= grfb[r*AccW +: AccW];
        else if (ph == ACT1)
          rb[(r*N+N-1)*AccW +: AccW] <= arr1[(r*N+N-1)*AccW +: AccW];
        else if (ph == WR)
          rb[(r*N+N-1)*AccW +: AccW] <= grfc[(r*N+N-1)*AccW +: AccW];
        else if (ph == PRE)
          arr1[(r*N+N-1)*AccW +: AccW] <= rb[(r*N+N-1)*AccW +: AccW];
        else if (ph == READ)
          C[(r*N+N-1)*AccW +: AccW] <= arr1[(r*N+N-1)*AccW +: AccW];
      end
    end
  end
endmodule
