// matmul G13: a spatial broadcast timetable.
// Row and column buses hold one outer-product slice per cycle; stationary
// output cells consume the broadcast and the feeder advances the timetable.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*W-1:0] a_next, b_next;
  logic [N*W-1:0] a_bus, b_bus;

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
      a_next <= '0;
      b_next <= '0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
      a_next <= A >> W;
      b_next <= B >> (N*W);
    end else if (busy) begin
      k <= k + 32'd1;
      a_next <= a_next >> W;
      b_next <= b_next >> (N*W);
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  for (genvar i = 0; i < N; i++) begin : g_a_bus
    always_ff @(posedge clk)
      if (rst)
        a_bus[i*W +: W] <= '0;
      else if (start)
        a_bus[i*W +: W] <= A[i*N*W +: W];
      else if (busy)
        a_bus[i*W +: W] <= a_next[i*N*W +: W];
  end

  for (genvar j = 0; j < N; j++) begin : g_b_bus
    always_ff @(posedge clk)
      if (rst)
        b_bus[j*W +: W] <= '0;
      else if (start)
        b_bus[j*W +: W] <= B[j*W +: W];
      else if (busy)
        b_bus[j*W +: W] <= b_next[j*W +: W];
  end

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_cell
      always_ff @(posedge clk)
        if (start)
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
            + {{AccW{a_bus[i*W + W - 1]}}, a_bus[i*W +: W]}
            * {{AccW{b_bus[j*W + W - 1]}}, b_bus[j*W +: W]};
    end
  end
endmodule
