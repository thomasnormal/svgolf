// Attack for task matmul (tests/expected.json, `attacks`; review L-a of 2026-11-08, the decision of 2026-11-09):
// the proved reference tasks/matmul/reference/matmul_g1.sv with ONE change: the control process has an
// ASYNCHRONOUS reset (`always_ff @(posedge clk or posedge rst)`), the same reset values.
// Wrong for the kind: rst is synchronous (C1), and an asynchronous reset acts between clock edges, where the
// protocol has no snapshot; with the other polarity ls-sv would run the body at the release entry, a claimed
// snapshot. The statement refuses it since 2026-11-09 (`TxTask.Disciplined` is `ClockedBy clk none`, as for the
// reactive kind), for every N, W, AccW; the clocked source gate refuses it first, at `source`.
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

  always_ff @(posedge clk or posedge rst)
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
          // Each operand sign-extended by AccW copies of its sign bit; the sum is reduced mod 2^AccW
          // by the assignment (the operands' extra high bits never reach C).
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
              * {{AccW{b_sh[j*W + W - 1]}}, b_sh[j*W +: W]};
    end
  end
endmodule
