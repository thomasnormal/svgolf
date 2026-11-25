// A mesh of small cores, modelled on the public description of a wafer-scale engine (Cerebras, Hot Chips 34):
// an N x N grid of identical cores, each with its own local memory, one multiply-accumulate unit and one input
// link from its north neighbour. There is no controller inside the mesh: a core works exactly when a valid
// message ("wavelet") arrives on its link.
//
// * Core (i, j) holds row i of A in its local memory amem(i, j) (loaded by the host on start) and the accumulator
//   C(i, j). On a valid arriving wavelet b it adds amem(i, j)[0] * b to C(i, j) (both sign-extended, wrapping at
//   AccW bits) and, unless b is flagged last, advances its operand pointer (amem(i, j) >> W). A is read and
//   written only by its own core.
// * A wavelet is {valid, last, payload} (W + 2 bits); the link into core (i, j) is lnk[(i*N+j)*(W+2) +: W+2].
//   The router of core (i, j) forwards its input wavelet to the core south of it, one hop per cycle. The
//   wavelet carries no index: its arrival order stands for k.
// * The edge I/O (the host's stream into the north edge, outside the mesh) sends column j of B into the link of
//   core (0, j), one row k per cycle, the last row flagged, column j starting j cycles after column 0, which
//   starts one cycle after the start edge. So the link into core (i, j) carries B[k][j] with k = t - 1 - i - j at
//   the snapshot t after the start, and core (i, j) has fired min(max(t - 1 - i - j, 0), N) times. The edge
//   keeps one step counter s (saturating) and B over N - 1 zero rows, shifted down one row per cycle; column j
//   reads row N - 1 - j. The skew keeps the cores of a mesh row apart in time: in lockstep they would hold
//   identical registers, which synthesis merges into one per row.
// * done is raised by the far core (N-1, N-1), the last to receive its last wavelet, at the edge of its last
//   multiply-accumulate: done shows at the snapshot 3N - 1 after the start (lat = 3N - 1).
// The reset clears every link (valid bits included), the step counter and done, each directly. Flip-flops only
// (every process an always_ff with nonblocking writes at static windows); every select is static.
// Flat widths: amem has N*N*N*W bits and bs (2N-1)*N*W, above 2^31 for some in-range (N, W).
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  logic [31:0]            s;     // edge I/O: cycles since the start, saturating at 2N - 1
  logic [(2*N-1)*N*W-1:0] bs;    // edge I/O: N - 1 zero rows, then B (row m at bs[m*N*W +: N*W]), shifted down
  logic [N*N*(W+2)-1:0]   lnk;   // the link into core (i, j): lnk[(i*N+j)*(W+2) +: W+2]
  logic [N*N*N*W-1:0]     amem;  // core (i, j)'s local memory: amem[(i*N+j)*N*W +: N*W]

  // edge I/O: the step counter and the rows of B
  always_ff @(posedge clk)
    if (rst)
      s <= N + N - 1;
    else if (start) begin
      s  <= 32'd0;
      bs <= '0;
      bs[(N-1)*N*W +: N*N*W] <= B;
    end else begin
      bs <= bs >> (N*W);
      if (s != N + N - 1)
        s <= s + 32'd1;
    end

  // the far core (N-1, N-1): the arrival of the last-flagged wavelet raises done
  always_ff @(posedge clk)
    if (rst)
      done <= 1'b0;
    else if (start)
      done <= 1'b0;
    else if (lnk[(N*N-1)*(W+2) + W + 1])
      if (lnk[(N*N-1)*(W+2) + W])
        done <= 1'b1;

  // edge I/O, column j: row s - j of B into the link of core (0, j)
  for (genvar j = 0; j < N; j++) begin : g_edge
    always_ff @(posedge clk)
      if (rst)
        lnk[j*(W+2) +: W+2] <= '0;
      else if (s - j < N)
        lnk[j*(W+2) +: W+2] <= {1'b1, s == j + N - 1, bs[((N-1-j)*N+j)*W +: W]};
      else
        lnk[j*(W+2) +: W+2] <= '0;
  end

  // routers: core (i, j) forwards its input wavelet to core (i+1, j)
  for (genvar i = 0; i < N - 1; i++) begin : g_rt_row
    for (genvar j = 0; j < N; j++) begin : g_rt_col
      always_ff @(posedge clk)
        if (rst)
          lnk[((i+1)*N+j)*(W+2) +: W+2] <= '0;
        else
          lnk[((i+1)*N+j)*(W+2) +: W+2] <= lnk[(i*N+j)*(W+2) +: W+2];
    end
  end

  // cores: an arriving valid wavelet triggers one multiply-accumulate and advances the operand pointer
  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_col
      always_ff @(posedge clk)
        if (start) begin
          C[(i*N+j)*AccW +: AccW]  <= '0;
          amem[(i*N+j)*N*W +: N*W] <= A[i*N*W +: N*W];
        end else if (lnk[(i*N+j)*(W+2) + W + 1]) begin
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{amem[(i*N+j)*N*W + W - 1]}}, amem[(i*N+j)*N*W +: W]}
              * {{AccW{lnk[(i*N+j)*(W+2) + W - 1]}}, lnk[(i*N+j)*(W+2) +: W]};
          if (lnk[(i*N+j)*(W+2) + W] == 1'b0)   // the last wavelet does not advance the pointer
            amem[(i*N+j)*N*W +: N*W] <= amem[(i*N+j)*N*W +: N*W] >> W;
        end
    end
  end
endmodule
