// A weight-stationary systolic matrix unit with a weight FIFO, a shifted weight load into shadow
// registers, a swap to the active weights, a skewed data wavefront and per-column accumulators below
// the array. Modelled on the public description of the TPU's matrix multiply unit (Jouppi et al.,
// "In-Datacenter Performance Analysis of a Tensor Processing Unit", ISCA 2017, section 2, Figure 4).
//
// PE(k, j) sits in array row k (the k of the sum) and column j (the j of C). A step is one busy edge;
// t is the step counter (t = 0 in the snapshot right after the start edge).
//   * Weights. `wf` (the weight FIFO) gets B at the start and sends one row per step from its top row
//     (B row N-1 first). The shadow weights `wsh` shift down the array, one row per step: PE(0, j)'s
//     shadow register takes the FIFO's top row, PE(k, j)'s takes PE(k-1, j)'s. After N steps
//     wsh(k, j) = B(k, j), and at t == N every PE copies its shadow weight into its active weight `wac`
//     (the double buffer's swap), sign-extended to AccW bits.
//   * Data. `ub` (the unified buffer) gets A at the start and, from t == N on, sends row t - N of A into
//     the setup unit, one row per step. Data row k is a shift register of N + k entries (entry e moves
//     into entry e-1 each step, entry k of the buffer's row enters at the top entry N+k-1): the k top
//     entries are the setup unit's delay stages for array row k (row k runs k steps behind row 0, the
//     diagonal wavefront; the rows stack into a triangle), and entry N-1-j is PE(k, j)'s data register:
//     PE(k, 0)'s is fed by the last delay stage, PE(k, j+1)'s by PE(k, j)'s (its west neighbour). The
//     setup unit sign-extends each entry to AccW bits as it enters (the extra flops hold copies of the
//     sign bit).
//   * Partial sums move down: ps(0, j) = a * w, ps(k, j) = ps(k-1, j) + a * w at AccW bits (the wrap).
//     PE(k, j) handles row i of A at the edge t = N+1+i+k+j.
//   * Accumulators. Below column j, the N accumulator words C(0..N-1, j) form a rotating file addressed
//     by the input row: in column j's window (LO+j <= t <= HI+j, while busy) each word takes the next
//     word and the last takes the first word plus the column's bottom partial sum (the column's one
//     adder). The start clears them; after the window C(i, j) holds row i of A times column j of B.
//   * done rises at the edge t == LAST = 4N-1, so done shows 4N snapshots after the start's (lat = 4N).
// Flip-flops only, nonblocking writes, every select static. The start loads wf and ub, and clears the
// data rows and the accumulators. The PE registers are not cleared: the swap writes the active weights
// before any data reach them, and a PE's partial sum is rewritten from its column's top before the
// accumulators read it.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  localparam int LO   = 2*N + 1;  // the first accumulate step of column 0
  localparam int HI   = 3*N;      // the last accumulate step of column 0
  localparam int LAST = 4*N - 1;  // the last step

  logic                busy;
  logic [31:0]         t;
  logic [N*N*W-1:0]    wf;    // weight FIFO
  logic [N*N*W-1:0]    wsh;   // shadow weights, PE(k, j) at entry k*N + j
  logic [N*N*AccW-1:0] wac;   // active weights, PE(k, j) at entry k*N + j, sign-extended to AccW bits
  logic [N*N*W-1:0]    ub;    // unified buffer
  // data rows: N*(3N-1)/2 entries, row k entry e at dat[(k*N + k*(k-1)/2 + e)*AccW +: AccW]
  logic [N*(3*N - 1)/2*AccW-1:0] dat;
  logic [N*N*AccW-1:0] ps;    // partial sums, PE(k, j) at entry k*N + j

  // control: the step counter counts on every busy edge, the last one included
  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      t    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      t    <= 32'd0;
    end else if (busy) begin
      t <= t + 32'd1;
      if (t == LAST) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  // the weight FIFO: one row out of the top per step of the weight phase
  always_ff @(posedge clk)
    if (start)
      wf <= B;
    else if (t < N)
      wf <= wf << (N*W);

  // the unified buffer: one row into the setup unit per step of the wavefront phase
  always_ff @(posedge clk)
    if (start)
      ub <= A;
    else if (t >= N)
      ub <= ub >> (N*W);

  // the data rows: every entry but the top one takes the entry above it
  for (genvar k = 0; k < N; k++) begin : g_dk
    for (genvar e = 0; e < N + k - 1; e++) begin : g_de
      always_ff @(posedge clk)
        if (start)
          dat[(k*N + k*(k-1)/2 + e)*AccW +: AccW] <= '0;
        else
          dat[(k*N + k*(k-1)/2 + e)*AccW +: AccW] <= dat[(k*N + k*(k-1)/2 + e + 1)*AccW +: AccW];
    end
  end

  // the setup unit's input: entry k of the buffer's current row, zero outside the wavefront phase
  for (genvar k = 0; k < N; k++) begin : g_dt
    always_ff @(posedge clk)
      if (start)
        dat[(k*N + k*(k-1)/2 + N + k - 1)*AccW +: AccW] <= '0;
      else if (t >= N)
        dat[(k*N + k*(k-1)/2 + N + k - 1)*AccW +: AccW] <= {{AccW{ub[k*W + W - 1]}}, ub[k*W +: W]};
      else
        dat[(k*N + k*(k-1)/2 + N + k - 1)*AccW +: AccW] <= '0;
  end

  // array row 0: the shadow weight from the FIFO, the partial sum from zero
  for (genvar j = 0; j < N; j++) begin : g_p0
    always_ff @(posedge clk)
      begin
        if (t < N)
          wsh[j*W +: W] <= wf[((N-1)*N + j)*W +: W];
        if (t == N)
          wac[j*AccW +: AccW] <= {{AccW{wsh[j*W + W - 1]}}, wsh[j*W +: W]};
        ps[j*AccW +: AccW] <= dat[(N-1-j)*AccW +: AccW] * wac[j*AccW +: AccW];
      end
  end

  // array rows 1 .. N-1 (row k+1): the shadow weight and the partial sum from the PE above
  for (genvar k = 0; k < N - 1; k++) begin : g_pr
    for (genvar j = 0; j < N; j++) begin : g_pc
      always_ff @(posedge clk)
        begin
          if (t < N)
            wsh[((k+1)*N + j)*W +: W] <= wsh[(k*N + j)*W +: W];
          if (t == N)
            wac[((k+1)*N + j)*AccW +: AccW] <= {{AccW{wsh[((k+1)*N + j)*W + W - 1]}}, wsh[((k+1)*N + j)*W +: W]};
          ps[((k+1)*N + j)*AccW +: AccW] <= ps[(k*N + j)*AccW +: AccW]
              + dat[((k+1)*N + (k+1)*k/2 + N-1-j)*AccW +: AccW] * wac[((k+1)*N + j)*AccW +: AccW];
        end
    end
  end

  // the accumulators, words 0 .. N-2 of each column: take the next word in the column's window
  for (genvar i = 0; i < N - 1; i++) begin : g_ar
    for (genvar j = 0; j < N; j++) begin : g_ac
      always_ff @(posedge clk)
        if (start)
          C[(i*N + j)*AccW +: AccW] <= '0;
        else if (busy)
          if (t >= LO + j)
            if (t <= HI + j)
              C[(i*N + j)*AccW +: AccW] <= C[((i+1)*N + j)*AccW +: AccW];
    end
  end

  // the accumulators, word N-1 of each column: the first word plus the bottom partial sum
  for (genvar j = 0; j < N; j++) begin : g_al
    always_ff @(posedge clk)
      if (start)
        C[((N-1)*N + j)*AccW +: AccW] <= '0;
      else if (busy)
        if (t >= LO + j)
          if (t <= HI + j)
            C[((N-1)*N + j)*AccW +: AccW] <= C[j*AccW +: AccW] + ps[((N-1)*N + j)*AccW +: AccW];
  end
endmodule
