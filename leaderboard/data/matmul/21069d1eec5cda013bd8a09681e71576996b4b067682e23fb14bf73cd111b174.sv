// matmul G18: a Cerebras-style wafer of independent small arithmetic cores.
// Every core owns one A operand, one B operand, and its C accumulator. Shared feeder banks
// advance one matrix term per edge and deliver the next operands to each core.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*W-1:0] a_sh, b_next;
  logic [N*N*W-1:0] a_cur, b_cur;

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
      a_sh <= '0;
      b_next <= '0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
      a_sh <= A;
      b_next <= B >> (N*W);
    end else if (busy) begin
      k <= k + 32'd1;
      a_sh <= a_sh >> W;
      b_next <= b_next >> (N*W);
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_core
      always_ff @(posedge clk)
        if (rst) begin
          a_cur[(i*N+j)*W +: W] <= '0;
          b_cur[(i*N+j)*W +: W] <= '0;
          C[(i*N+j)*AccW +: AccW] <= '0;
        end
        else if (start) begin
          a_cur[(i*N+j)*W +: W] <= A[i*N*W +: W];
          b_cur[(i*N+j)*W +: W] <= B[j*W +: W];
          C[(i*N+j)*AccW +: AccW] <= '0;
        end else if (busy) begin
          a_cur[(i*N+j)*W +: W] <= a_sh[i*N*W +: W];
          b_cur[(i*N+j)*W +: W] <= b_next[j*W +: W];
          if (k == 0)
            C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{a_cur[(i*N+j)*W + W - 1]}}, a_cur[(i*N+j)*W +: W]}
              * {{AccW{b_cur[(i*N+j)*W + W - 1]}}, b_cur[(i*N+j)*W +: W]};
          else
            C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
              * {{AccW{b_cur[(i*N+j)*W + W - 1]}}, b_cur[(i*N+j)*W +: W]};
        end
    end
  end
endmodule
