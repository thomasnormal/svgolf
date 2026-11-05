// Attack for task matmul (tests/expected.json, `attacks`; PLAN4.md Gate 3 step 4): the proved reference
// tasks/matmul/reference/matmul_g1.sv with ONE change, a correct-looking design that is wrong for some
// N, W, AccW: the W x W product is sign-extended only to 2W bits (`p`, a 2W-bit net), and p is added to the AccW-bit accumulator zero-extended.
// Wrong: AccW > 2W with a negative product (oracle.py `_faults`: "missing sign extension"); right whenever AccW <= 2W, e.g. at (2, 3, 5) and (2, 4, 8).
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
  logic [N*N*2*W-1:0] p;          // p[i][j] = A[i][k]*B[k][j]: a W x W signed product fits in 2W bits

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
      // Each operand sign-extended to 2W bits; the product is reduced mod 2^2W by the assignment.
      assign p[(i*N+j)*2*W +: 2*W] = {{W{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
                                   * {{W{b_sh[j*W + W - 1]}}, b_sh[j*W +: W]};
      always_ff @(posedge clk)
        if (start)
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW] + p[(i*N+j)*2*W +: 2*W];
    end
  end
endmodule
