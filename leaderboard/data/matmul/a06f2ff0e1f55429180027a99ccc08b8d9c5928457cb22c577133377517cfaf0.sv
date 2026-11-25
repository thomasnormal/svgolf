// svgolf-latency: 4
// Registered 3D cube pipeline: each depth layer owns a partial-sum plane.
// Layer d receives layer d-1 plus its A[i,d]*B[d,j] product; stationary C
// observes the final depth layer after N busy cycles.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*W-1:0] A_mem, B_mem;
  logic [N*N*N*AccW-1:0] cube_acc;

  always_ff @(posedge clk) begin
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
      A_mem <= '0;
      B_mem <= '0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
      A_mem <= A;
      B_mem <= B;
    end else if (busy) begin
      k <= k + 32'd1;
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end
  end

  for (genvar d = 0; d < 1; d++) begin : g_depth_zero
    for (genvar i = 0; i < N; i++) begin : g_row
      for (genvar j = 0; j < N; j++) begin : g_col
        always_ff @(posedge clk) begin
          if (rst || start)
            cube_acc[(d*N*N+i*N+j)*AccW +: AccW] <=
              {{AccW{A[(i*N+d)*W + W - 1]}}, A[(i*N+d)*W +: W]}
              * {{AccW{B[(d*N+j)*W + W - 1]}}, B[(d*N+j)*W +: W]};
        end
      end
    end
  end

  for (genvar d = 1; d < N; d++) begin : g_depth
    for (genvar i = 0; i < N; i++) begin : g_row
      for (genvar j = 0; j < N; j++) begin : g_col
        always_ff @(posedge clk) begin
          if (rst || start)
            cube_acc[(d*N*N+i*N+j)*AccW +: AccW] <=
              {{AccW{A[(i*N+d)*W + W - 1]}}, A[(i*N+d)*W +: W]}
              * {{AccW{B[(d*N+j)*W + W - 1]}}, B[(d*N+j)*W +: W]};
          else if (busy)
            cube_acc[(d*N*N+i*N+j)*AccW +: AccW] <=
              cube_acc[((d-1)*N*N+i*N+j)*AccW +: AccW]
              + {{AccW{A_mem[(i*N+d)*W + W - 1]}}, A_mem[(i*N+d)*W +: W]}
              * {{AccW{B_mem[(d*N+j)*W + W - 1]}}, B_mem[(d*N+j)*W +: W]};
        end
      end
    end
  end

  for (genvar i = 0; i < N; i++) begin : g_output_row
    for (genvar j = 0; j < N; j++) begin : g_output_col
      always_ff @(posedge clk) begin
        if (rst || start)
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy && k == N - 1)
          C[(i*N+j)*AccW +: AccW] <=
            cube_acc[((N-1)*N*N+i*N+j)*AccW +: AccW];
      end
    end
  end
endmodule
