// matmul G1 reference: N*N parallel multiply-accumulate units and one step counter k.
// After `start`, cycle k (k = 0 .. N-1) adds A[i][k]*B[k][j] (signed, wrapping at AccW bits) to
// C[i][j]; `done` rises after the N-th step and stays 1 (C held) until the next `start`.
// Flip-flops only (the FF-only profile): every register is written by nonblocking assignments in
// one always_ff, at a static window. `start` captures A and B into shift registers; each step
// shifts A by one entry and B by one row, so every select is static (no run-time part-select).
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

  // operand shifters and the step counter free-running: loaded on start, stepped in every other cycle
  always_ff @(posedge clk) begin
    if (start) begin
      a_sh <= A;
      b_sh <= B;
      k    <= 32'd0;
    end else begin
      a_sh <= a_sh >> W;
      b_sh <= b_sh >> (N*W);
      k    <= k + 32'd1;
    end
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
    end else if (busy) begin
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end
  end

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_col
      always_ff @(posedge clk)
        if (start)
          C[(i*N+j)*AccW +: AccW] <= '0;
        else
          // free-running accumulate: once the N steps are over b_sh has been shifted out (all zero),
          // so the product is 0 and C holds without a hold multiplexer
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{a_sh[i*N*W + W - 1]}}, a_sh[i*N*W +: W]}
              * {{AccW{b_sh[j*W + W - 1]}}, b_sh[j*W +: W]};
    end
  end
endmodule
