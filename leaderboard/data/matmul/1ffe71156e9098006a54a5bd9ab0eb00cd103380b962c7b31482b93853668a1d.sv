// matmul, G4: four multiply-accumulate steps per PE per cycle.
// `start` captures A and B (zero-extended into registers with three spare entries / rows, so the
// four static windows below stay in range for every N); every busy cycle adds
//   A[i][k..k+3] . B[k..k+3][j]   (entries past N read as 0)
// to C[i][j] and shifts the captured operands by four entries (A) / four rows (B). `done` rises
// after ceil(N/4) busy cycles: latency (N+3)/4 = 1 at the scoring point N = 4.
// The shifts are written as two shifts of half the amount so that no shift amount can wrap at 32 bits.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  logic [31:0]            k;
  logic                   busy;
  logic [(N*N+3)*W-1:0]   a_sh;
  logic [(N*N+3*N)*W-1:0] b_sh;

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
      k    <= k + 32'd4;
      a_sh <= (a_sh >> (2*W)) >> (2*W);
      b_sh <= (b_sh >> (2*N*W)) >> (2*N*W);
      if (k + 32'd4 >= N) begin
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
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
              * {{AccW{b_sh[j*W + W - 1]}}, b_sh[j*W +: W]}
              + {{AccW{a_sh[(i*N+1)*W + W - 1]}}, a_sh[(i*N+1)*W +: W]}
              * {{AccW{b_sh[(N+j)*W + W - 1]}}, b_sh[(N+j)*W +: W]}
              + {{AccW{a_sh[(i*N+2)*W + W - 1]}}, a_sh[(i*N+2)*W +: W]}
              * {{AccW{b_sh[(2*N+j)*W + W - 1]}}, b_sh[(2*N+j)*W +: W]}
              + {{AccW{a_sh[(i*N+3)*W + W - 1]}}, a_sh[(i*N+3)*W +: W]}
              * {{AccW{b_sh[(3*N+j)*W + W - 1]}}, b_sh[(3*N+j)*W +: W]};
    end
  end
endmodule
