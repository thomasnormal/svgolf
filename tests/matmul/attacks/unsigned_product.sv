// Attack for task matmul (tests/expected.json, `attacks`; PLAN4.md Gate 3 step 4): the proved reference
// tasks/matmul/reference/matmul_g1.sv with ONE change, a correct-looking design that is wrong for some
// N, W, AccW: the operands are not extended: `C + a * b` with W-bit part-selects, which SystemVerilog zero-extends to the AccW-bit context, an unsigned product.
// Wrong: AccW > W >= 2 with a negative entry (tasks/matmul/oracle.py `_faults`: "unsigned product"); right for W = 1 and for AccW <= W.
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
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          // The product of the two entries, reduced mod 2^AccW by the assignment.
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + a_sh[i*N*W +: W] * b_sh[j*W +: W];
    end
  end
endmodule
