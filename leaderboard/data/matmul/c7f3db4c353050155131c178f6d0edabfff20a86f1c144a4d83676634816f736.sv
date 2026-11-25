// matmul as a cube: N*N*N multipliers form every product A[i][k]*B[k][j] at once, in the start edge,
// and one registered binary adder tree per output entry (i, j) sums its N products over k.
//
// Per entry (i, j) one binary heap of 2N-1 nodes of AccW bits: node x of entry (i, j) is
// T[((i*N+j)*(2*N-1) + x)*AccW +: AccW]; the internal nodes are 0 .. N-2, node x has the children 2x+1
// and 2x+2; the leaves are N-1 .. 2N-2. Leaf N-1+k is the product register of (i, j, k): the start edge
// writes A[i][k]*B[k][j] into it, both operands sign-extended, read from the ports (A and B are held
// through the transaction), and it holds the product until the next start. Every internal node adds
// its two children in every cycle (a pipelined tree, one level per cycle, no enable), and C[i][j] takes
// the root in every cycle. The heap is L = $clog2(N) levels deep, so the roots are right L cycles
// after the start and C one cycle later: done shows L+1 snapshots after the start's.
// No operand register moves and no counter selects an operand; the step counter t only times done.
// Flip-flops only: every register is written by nonblocking assignments in an always_ff, each process
// at its own static window.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  logic [31:0]                 t;
  logic                        busy;
  logic [N*N*(2*N-1)*AccW-1:0] T;  // the N*N heaps: products at the leaves, partial sums above

  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      t    <= 32'd0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      t    <= 32'd0;
    end else if (busy) begin
      t <= t + 32'd1;
      if (t == $clog2(N)) begin   // the depth of each adder tree
        busy <= 1'b0;
        done <= 1'b1;
      end
    end

  for (genvar i = 0; i < N; i++) begin : g_i
    for (genvar j = 0; j < N; j++) begin : g_j
      // the adder tree: node x <= child 2x+1 + child 2x+2, every cycle
      for (genvar x = 0; x < N - 1; x++) begin : g_node
        always_ff @(posedge clk)
          T[((i*N+j)*(2*N-1) + x)*AccW +: AccW] <=
              T[((i*N+j)*(2*N-1) + 2*x+1)*AccW +: AccW] + T[((i*N+j)*(2*N-1) + 2*x+2)*AccW +: AccW];
      end
      // the cube: one multiplier per (i, j, k), used once per transaction
      for (genvar k = 0; k < N; k++) begin : g_k
        always_ff @(posedge clk)
          if (start)
            T[((i*N+j)*(2*N-1) + N-1+k)*AccW +: AccW] <=
                {{AccW{A[(i*N+k)*W + W-1]}}, A[(i*N+k)*W +: W]}
              * {{AccW{B[(k*N+j)*W + W-1]}}, B[(k*N+j)*W +: W]};
      end
      // the output register of entry (i, j): the root
      always_ff @(posedge clk)
        C[(i*N+j)*AccW +: AccW] <= T[(i*N+j)*(2*N-1)*AccW +: AccW];
    end
  end
endmodule
