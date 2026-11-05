// Attack for task matmul (tests/expected.json, `attacks`; PLAN4.md Gate 3 step 4): the proved reference
// tasks/matmul/reference/matmul_g1.sv with ONE change, a correct-looking design that is wrong for some
// N, W, AccW: the step counter k starts at 1 on start (`k <= 32'd1`), so the busy phase runs N - 1 steps.
// Wrong: the last product A[i][N-1]*B[N-1][j] never reaches C and done rises one cycle early (after N - 1 steps); for N = 1 done never rises (k = 1 never equals N - 1 = 0 before k wraps). Every N.
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

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k    <= 32'd1;   // steps counted from one
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
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          // Each operand sign-extended by AccW copies of its sign bit; the sum is reduced mod 2^AccW
          // by the assignment (the operands' extra high bits never reach C).
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
              * {{AccW{b_sh[j*W + W - 1]}}, b_sh[j*W +: W]};
    end
  end
endmodule
