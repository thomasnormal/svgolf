// matmul, G2: two multiply-accumulate steps per PE per cycle.
// `start` captures A and B (zero-extended into registers with one spare entry / one spare row, so
// the two static windows below stay in range for every N); every busy cycle adds
//   A[i][k], A[i][k+1] . B[k][j], B[k+1][j]   (entries past N read as 0)
// to C[i][j] and shifts the captured operands by two entries (A) / two rows (B). `done` rises
// after ceil(N/2) busy cycles: latency (N+1)/2 = 2 at the scoring point N = 4.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  logic [31:0]            k;
  logic                   busy;
  logic [(N*N+1)*W-1:0]   a_sh;
  logic [(N*N+N)*W-1:0]   b_sh;

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
      k    <= k + 32'd2;
      a_sh <= a_sh >> (2*W);
      b_sh <= b_sh >> (2*N*W);
      if (k + 32'd2 >= N) begin
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
              * {{AccW{b_sh[(N+j)*W + W - 1]}}, b_sh[(N+j)*W +: W]};
    end
  end
endmodule
