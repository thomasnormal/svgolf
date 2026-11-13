// A statically scheduled matrix multiplier: a timetable instead of a control loop.
// Modelled on the public description of a tensor streaming processor: the chip is sliced by function
// (memory, matrix, vector), operands are read from memory onto streams that move every cycle, each slice
// consumes its operands from streams and puts its result on a stream, and every instruction is issued at a
// cycle fixed in advance by the compiler. Here the "compiled program" is the timetable below: one time
// counter t, and every enable is a comparison of t with a constant fixed at elaboration. There is no busy
// flag, no valid bit and no condition that depends on data.
//
// Slices, west to east, each with its own registers and processes:
//   MEM_A  ma: holds A; Read at t = 0 .. N-1 puts column t of A on stream SA (ma shifts by one entry).
//   MEM_B  mb: holds B; Read at t = 0 .. N-1 puts row t of B on stream SB (mb shifts by one row).
//   streams SA, SB: loaded every cycle, no enable.
//   MXM    SP: every cycle, the N x N outer product of the two streams (exact 2W-bit signed products).
//   VXM    ACC: at T_ACC_FIRST loads SP, for T_ACC_FIRST < t <= T_ACC_LAST adds SP (k = t - 2).
//   stream SC: the result stream, loaded from ACC every cycle, no enable.
//   MEM_C  C: Write from stream SC at T_WRITE, once per transaction; done rises at the same edge.
// The counter t starts at 0 on the start edge, counts up and rests at T_IDLE, outside every window.
// Latency: done shows N + 4 cycles after the start edge.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  // The timetable: every cycle number of the schedule (t = cycles after the start edge).
  localparam int T_READ_END  = N;      // MEM reads at t <  T_READ_END
  localparam int T_ACC_FIRST = 2;      // VXM load: products of k = 0 (on SP from t = 2)
  localparam int T_ACC_LAST  = N + 1;  // VXM last accumulate: products of k = N - 1
  localparam int T_WRITE     = N + 3;  // MEM write of C from SC, and done
  localparam int T_IDLE      = N + 4;  // the counter's resting value

  logic [31:0]         t;
  logic [N*N*W-1:0]    ma, mb;    // MEM_A, MEM_B
  logic [N*W-1:0]      sa, sb;    // operand streams
  logic [N*N*2*W-1:0]  sp;        // MXM product stream: exact 2W-bit signed products
  logic [N*N*AccW-1:0] acc;       // VXM accumulator
  logic [N*N*AccW-1:0] sc;        // result stream

  // The time counter: the only control state.
  always_ff @(posedge clk)
    if (rst) begin
      t    <= T_IDLE;
      done <= 1'b0;
    end else if (start) begin
      t    <= 32'd0;
      done <= 1'b0;
    end else begin
      if (t < T_IDLE) t <= t + 32'd1;
      if (t == T_WRITE) done <= 1'b1;
    end

  // MEM_A: holds A; a Read shifts the next column to entry 0 of every row.
  always_ff @(posedge clk)
    if (start) ma <= A;
    else if (t < T_READ_END) ma <= ma >> W;

  // MEM_B: holds B; a Read shifts the next row to row 0.
  always_ff @(posedge clk)
    if (start) mb <= B;
    else if (t < T_READ_END) mb <= mb >> (N*W);

  // Stream SB: row 0 of MEM_B, every cycle.
  always_ff @(posedge clk)
    sb <= mb[N*W-1:0];

  // Result stream SC: the accumulator, every cycle.
  always_ff @(posedge clk)
    sc <= acc;

  // MEM_C: the Write of the result stream, at one cycle of the timetable.
  always_ff @(posedge clk)
    if (t == T_WRITE) C <= sc;

  // Stream SA: lane i is entry 0 of row i of MEM_A, every cycle.
  for (genvar i = 0; i < N; i++) begin : g_sa
    always_ff @(posedge clk)
      sa[i*W +: W] <= ma[i*N*W +: W];
  end

  // MXM: lane (i, j) multiplies SA lane i by SB lane j, every cycle: both sign-extended to 2W bits, so the
  // 2W-bit product is the exact signed product.
  for (genvar i = 0; i < N; i++) begin : g_mxm_row
    for (genvar j = 0; j < N; j++) begin : g_mxm_col
      always_ff @(posedge clk)
        sp[(i*N+j)*(2*W) +: 2*W] <= {{W{sa[i*W + W - 1]}}, sa[i*W +: W]}
            * {{W{sb[j*W + W - 1]}}, sb[j*W +: W]};
    end
  end

  // VXM: lane (i, j) loads, then accumulates, the product stream at the timetable's cycles; each product is
  // sign-extended by AccW bits and the sum is reduced mod 2^AccW by the AccW-bit target.
  for (genvar i = 0; i < N; i++) begin : g_vxm_row
    for (genvar j = 0; j < N; j++) begin : g_vxm_col
      always_ff @(posedge clk)
        if (t == T_ACC_FIRST)
          acc[(i*N+j)*AccW +: AccW] <= {{AccW{sp[(i*N+j)*(2*W) + 2*W - 1]}}, sp[(i*N+j)*(2*W) +: 2*W]};
        else if (t > T_ACC_FIRST)
          if (t <= T_ACC_LAST)
            acc[(i*N+j)*AccW +: AccW] <= acc[(i*N+j)*AccW +: AccW]
                + {{AccW{sp[(i*N+j)*(2*W) + 2*W - 1]}}, sp[(i*N+j)*(2*W) +: 2*W]};
    end
  end
endmodule
