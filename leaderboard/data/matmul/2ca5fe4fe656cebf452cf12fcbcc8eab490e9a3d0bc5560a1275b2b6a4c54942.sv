// Strassen-style 2x2 tile with a parametric shift fallback.  At N=2 the seven transformed
// products are stored in a product bank and recombined into C; other N values use the same
// packed feeder protocol with direct products, keeping the module defined for every N.
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
  logic [AccW-1:0] p0, p1, p2, p3, p4, p5, p6;

  always_ff @(posedge clk)
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
      A_mem <= A_mem >> W;
      B_mem <= B_mem >> (N*W);
      k <= k + 32'd1;
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  if (N == 32'd2) begin : g_strassen
    always_ff @(posedge clk)
      if (rst || start)
        begin
        p6 <=
          ({{AccW{A[2*W-1]}}, A[W +: W]} - {{AccW{A[4*W-1]}}, A[3*W +: W]})
          * ({{AccW{B[3*W-1]}}, B[2*W +: W]} + {{AccW{B[4*W-1]}}, B[3*W +: W]});
        p5 <=
          ({{AccW{A[3*W-1]}}, A[2*W +: W]} - {{AccW{A[W-1]}}, A[0 +: W]})
          * ({{AccW{B[W-1]}}, B[0 +: W]} + {{AccW{B[2*W-1]}}, B[W +: W]});
        p4 <=
          ({{AccW{A[W-1]}}, A[0 +: W]} + {{AccW{A[2*W-1]}}, A[W +: W]})
          * {{AccW{B[4*W-1]}}, B[3*W +: W]};
        p3 <=
          {{AccW{A[4*W-1]}}, A[3*W +: W]}
          * ({{AccW{B[3*W-1]}}, B[2*W +: W]} - {{AccW{B[W-1]}}, B[0 +: W]});
        p2 <=
          {{AccW{A[W-1]}}, A[0 +: W]}
          * ({{AccW{B[2*W-1]}}, B[W +: W]} - {{AccW{B[4*W-1]}}, B[3*W +: W]});
        p1 <=
          ({{AccW{A[3*W-1]}}, A[2*W +: W]} + {{AccW{A[4*W-1]}}, A[3*W +: W]})
          * {{AccW{B[W-1]}}, B[0 +: W]};
        p0 <=
          ({{AccW{A[W-1]}}, A[0 +: W]} + {{AccW{A[4*W-1]}}, A[3*W +: W]})
          * ({{AccW{B[W-1]}}, B[0 +: W]} + {{AccW{B[4*W-1]}}, B[3*W +: W]});
        end

    always_ff @(posedge clk)
      if (rst || start)
        C <= '0;
      else if (busy)
        C <= {p0 - p1 + p2 + p5,
              p1 + p3,
              p2 + p4,
              p0 + p3 - p4 + p6};
  end else begin : g_fallback
    for (genvar i = 0; i < N; i++) begin : g_row
      for (genvar j = 0; j < N; j++) begin : g_col
        always_ff @(posedge clk)
          if (start)
            C[(i*N+j)*AccW +: AccW] <= '0;
          else if (busy)
            C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{A_mem[i*N*W + W - 1]}}, A_mem[i*N*W +: W]}
              * {{AccW{B_mem[j*W + W - 1]}}, B_mem[j*W +: W]};
      end
    end
  end
endmodule
