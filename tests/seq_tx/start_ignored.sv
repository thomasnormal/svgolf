// expect: the payload is not the task's result
// A NEGATIVE of the clocked post-synthesis check (PLAN4 Gate 2 step 5): tasks/matmul/reference/matmul_g1.sv
// with one change: a start while done = 1 (back-to-back, C2) is ignored, so done stays 1 with the old C
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
    end else if (start && !done) begin
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
        if (start && !done)
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
