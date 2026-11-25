// A weight-stationary array: N x N processing elements, PE (k, j) holds the weight B[k][j] for the
// whole product. The rows of A stream through the array: array row k sees column k of A, delayed by
// k cycles (one input delay line per array row, its head broadcast to every PE of that row). The
// partial sums move down the columns, one PE per cycle; the bottom row of PEs leaves the array, one
// output row of C per cycle: it enters C row N-1 while each row already collected moves on (row i
// takes row i+1), so after N such cycles output row r is in C row r.
//
// Registers (flat, row-major, least significant entry first):
//   w   [N*N*W]     the stationary weights, PE (k, j) at w[(k*N+j)*W +: W]; loaded on start only
//   ash [N*N*W]     the rows of A not yet fed: after step t, row t+1 of A is in its row 0
//   dl  [N*N*W]     input delay line k at dl[k*N*W +: N*W], entry e at dl[(k*N+e)*W +: W]; head = entry 0;
//                   A[r][k] enters at entry k and reaches the head k cycles later (entries above k stay 0)
//   ps  [N*N*AccW]  partial sums, PE (k, j) at ps[(k*N+j)*AccW +: AccW]; no enable (every cycle)
//   C   [N*N*AccW]  the output rows, collected from the bottom row of PEs, one per cycle
// After t busy cycles: the head of line k is A[t-k][k] (0 outside the matrix), PE (k, j) holds
// sum_{k' <= k} A[t-1-k][k'] * B[k'][j] once t >= k+1, the bottom row of PEs is output row t-N, and
// for m = t-N collected rows, C rows N-m .. N-1 hold output rows 0 .. m-1. done rises 2N cycles
// after the start, with every row of C collected.
// Every process is an always_ff, every write a nonblocking one at a static window.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  localparam int X = (AccW > W) ? AccW - W : 1;   // the sign extension: entries widened to max(AccW, W+1) bits
  logic [31:0]         t;
  logic                busy;
  logic [N*N*W-1:0]    w, ash, dl;
  logic [N*N*AccW-1:0] ps;

  // control, the weight load and the row feeder
  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      t    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      t    <= 32'd0;
      w    <= B;
      ash  <= A >> (N*W);
    end else if (busy) begin
      t   <= t + 32'd1;
      ash <= ash >> (N*W);
      if (t == N + N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  // input delay line k: cleared with A[0][k] at entry k on start, then shifted towards the head while
  // the next row's entry A[t+1][k] enters at entry k (OR-ed in: the entry shifted into it is 0)
  for (genvar k = 0; k < N; k++) begin : g_line
    always_ff @(posedge clk)
      if (start)
        dl[k*N*W +: N*W] <= A[k*W +: W] << (k*W);
      else if (busy)
        dl[k*N*W +: N*W] <= (dl[k*N*W +: N*W] >> W) | (ash[k*W +: W] << (k*W));
  end

  // array row 0: the head of line 0 times the PE's weight
  for (genvar j = 0; j < N; j++) begin : g_top
    always_ff @(posedge clk)
      ps[j*AccW +: AccW] <= {{X{dl[W-1]}}, dl[0 +: W]} * {{X{w[j*W+W-1]}}, w[j*W +: W]};
  end

  // array rows 1 .. N-1: the partial sum from the PE above plus the head of the row's line times the
  // PE's weight (both operands sign-extended, the sum wrapped at AccW bits)
  for (genvar k = 0; k < N - 1; k++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_col
      always_ff @(posedge clk)
        ps[((k+1)*N+j)*AccW +: AccW] <= ps[(k*N+j)*AccW +: AccW]
            + {{X{dl[(k+1)*N*W+W-1]}}, dl[(k+1)*N*W +: W]}
            * {{X{w[((k+1)*N+j)*W+W-1]}}, w[((k+1)*N+j)*W +: W]};
    end
  end

  // collection: in busy cycles t >= N the bottom row of PEs is output row t-N; it enters C row N-1
  // while every collected row moves one row on (C row i takes C row i+1)
  for (genvar i = 0; i < N - 1; i++) begin : g_crow
    for (genvar j = 0; j < N; j++) begin : g_ccol
      always_ff @(posedge clk)
        if (busy)
          if (t >= N)
            C[(i*N+j)*AccW +: AccW] <= C[((i+1)*N+j)*AccW +: AccW];
    end
  end
  for (genvar j = 0; j < N; j++) begin : g_cout
    always_ff @(posedge clk)
      if (busy)
        if (t >= N)
          C[((N-1)*N+j)*AccW +: AccW] <= ps[((N-1)*N+j)*AccW +: AccW];
  end
endmodule
