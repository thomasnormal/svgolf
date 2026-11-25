// Gemmini-style tiled mesh modelled on the public element/tile/mesh structure.
// Each generated output element owns skew-register streams for one A row and B column;
// its stationary accumulator consumes one aligned product per busy cycle.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*N*W-1:0] a_skew_bank, b_skew_bank, b_col_bank;
  logic [N*N*N*W-1:0] a_shift_bank, b_shift_bank;
  assign a_shift_bank = a_skew_bank >> W;
  assign b_shift_bank = b_skew_bank >> W;

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
    end else if (busy) begin
      k <= k + 32'd1;
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  for (genvar i = 0; i < N; i++) begin : g_mesh_row
    for (genvar j = 0; j < N; j++) begin : g_mesh_col
      for (genvar q = 0; q < N; q++) begin : g_col_word
        assign b_col_bank[(i*N+j)*N*W + q*W +: W] = B[(q*N+j)*W +: W];
      end
      always_ff @(posedge clk)
        if (rst) begin
          a_skew_bank[(i*N+j)*N*W +: N*W] <= '0;
          b_skew_bank[(i*N+j)*N*W +: N*W] <= '0;
        end else if (start) begin
          a_skew_bank[(i*N+j)*N*W +: N*W] <= A[i*N*W +: N*W];
          b_skew_bank[(i*N+j)*N*W +: N*W] <= b_col_bank[(i*N+j)*N*W +: N*W];
        end else if (busy) begin
          a_skew_bank[(i*N+j)*N*W +: N*W] <= a_shift_bank[(i*N+j)*N*W +: N*W];
          b_skew_bank[(i*N+j)*N*W +: N*W] <= b_shift_bank[(i*N+j)*N*W +: N*W];
        end

      always_ff @(posedge clk)
        if (rst || start)
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
            + {{AccW{a_skew_bank[(i*N+j)*N*W + W - 1]}}, a_skew_bank[(i*N+j)*N*W +: W]}
            * {{AccW{b_skew_bank[(i*N+j)*N*W + W - 1]}}, b_skew_bank[(i*N+j)*N*W +: W]};
    end
  end
endmodule
