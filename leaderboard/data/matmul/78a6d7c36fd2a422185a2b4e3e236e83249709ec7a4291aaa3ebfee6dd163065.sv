// matmul G20: a timetable of output cores.  The cores keep complete operand banks and use the
// shared step counter as a schedule address instead of shifting the banks between edges.
// This models a statically laid-out time program: at step k every core consumes A[i,k] and B[k,j].
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*W-1:0] a_mem, b_mem;
  logic [N*N*W-1:0] a_pick, b_pick;

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
      a_mem <= A;
      b_mem <= B;
    end else if (busy) begin
      k <= k + 32'd1;
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_col
      assign a_pick[(i*N+j)*W +: W] = a_mem >> (i*N*W + k*W);
      assign b_pick[(i*N+j)*W +: W] = b_mem >> (k*N*W + j*W);
      always_ff @(posedge clk)
        if (rst || start)
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
            + {{AccW{a_pick[(i*N+j)*W+W-1]}}, a_pick[(i*N+j)*W +: W]}
            * {{AccW{b_pick[(i*N+j)*W+W-1]}}, b_pick[(i*N+j)*W +: W]};
    end
  end
endmodule
