// Attack for task matmul (tests/expected.json, `attacks`; PLAN4.md Gate 3 step 4): the proved reference
// tasks/matmul/reference/matmul_g1.sv with ONE change, a correct-looking design that is wrong for some
// N, W, AccW: the accumulator is 2W bits (`acc`, the width of one product) and C is acc sign-extended to AccW bits by continuous assignments.
// Wrong: AccW > 2W and a dot product outside the signed 2W-bit range, e.g. N >= 2 with every entry the minimum (oracle.py `_faults`: "accumulator truncated to 2W"); right whenever AccW <= 2W, and for N = 1.
// Every check up to the proof passes it; the reference's proof (reference/matmul_g1.lean) must FAIL on it.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  logic [31:0]      k;
  logic             busy;
  logic [N*N*W-1:0] a_sh, b_sh;  // A >> k entries, B >> k rows: A[i][k] at row i's entry 0, B[k][j] at entry j
  logic [N*N*2*W-1:0] acc;        // acc[i][j]: the running sum, 2W bits (the width of one product)

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k    <= 32'd0;
      a_sh <= A;
      b_sh <= B;
    end else if (busy) begin
      k    <= k + 32'd1;
      a_sh <= a_sh >> W;
      b_sh <= b_sh >> (N*W);
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_col
      always_ff @(posedge clk)
        if (start)
          acc[(i*N+j)*2*W +: 2*W] <= '0;
        else if (busy)
          // Each operand sign-extended by 2W copies of its sign bit; the sum is reduced mod 2^2W.
          acc[(i*N+j)*2*W +: 2*W] <= acc[(i*N+j)*2*W +: 2*W]
              + {{2*W{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
              * {{2*W{b_sh[j*W + W - 1]}}, b_sh[j*W +: W]};
      // C[i][j]: acc[i][j] sign-extended to AccW bits (reduced mod 2^AccW when AccW < 2W)
      assign C[(i*N+j)*AccW +: AccW] = {{AccW{acc[(i*N+j)*2*W + 2*W - 1]}}, acc[(i*N+j)*2*W +: 2*W]};
    end
  end
endmodule
