                                                                           
                                                                      
                                                                                       
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*W-1:0] a_bank, b_bank;
  logic [N*N*AccW-1:0] pim_bank;
  assign C = pim_bank;

  always_ff @(posedge clk) begin
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
      a_bank <= '0;
      b_bank <= '0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
      a_bank <= A;
      b_bank <= B;
    end else if (busy) begin
      busy <= (k != N-1);
      done <= (k == N-1);
      k <= k + 32'd1;
      a_bank <= a_bank >> W;
      b_bank <= b_bank >> (N*W);
    end
  end

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_mem
      always_ff @(posedge clk) begin
        if (rst || start)
          pim_bank[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy)
          pim_bank[(i*N+j)*AccW +: AccW] <= pim_bank[(i*N+j)*AccW +: AccW]
            + $signed({{AccW{a_bank[i*N*W + W - 1]}}, a_bank[i*N*W +: W]})
            * $signed({{AccW{b_bank[j*W + W - 1]}}, b_bank[j*W +: W]});
      end
    end
  end
endmodule
