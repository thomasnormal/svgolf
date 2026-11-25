// matmul as a program laid out in space: a spatial dataflow pipeline, modelled on the public
// description of the Plasticine reconfigurable dataflow architecture (Prabhakar et al., ISCA 2017).
// The program is Map over (i, j) of Fold over k of A[i][k] * B[k][j] with combine +. It is not
// executed by an instruction loop: it is the wiring of five units, each writing only its own registers.
//   counter chain (cc_)  two chained counters (cc_i, cc_j) walk the Map domain row-major, one item per
//                        cycle, and step the memory units.
//   PMU_A (pa_)          a scratchpad holding A; its read port is row 0, rotated to row cc_i.
//   PMU_B (pb_)          a scratchpad holding B; its read port is entry 0 of every row, rotated to column cc_j.
//   PCU (pcu_)           one compute unit of N SIMD lanes: vector input registers, a map stage of N
//                        multipliers (lane k: A[i][k] * B[k][j]), then a cross-lane reduction tree with one
//                        level per pipeline stage (its nodes kept as a heap, root at node 0, leaves at P-1+k,
//                        leaves N .. P-1 held at 0). A valid bit and a last bit travel with each item.
//   output PMU (C, done) takes one dot product per cycle from the tree's root and writes it in (i, j) order,
//                        shifting C down by one entry; the last item raises done.
// A new (i, j) item enters every cycle, so N*N dot products are in flight in one feed-forward pipeline:
// done shows N*N + clog2(N) + 2 cycles after the start.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  localparam int L = $clog2(N);   // levels of the reduction tree
  localparam int P = 1 << L;      // tree leaves: N rounded up to a power of two

  logic [31:0]             cc_i, cc_j;       // counter chain: the item (i, j) issued this cycle
  logic                    cc_run;
  logic [N*N*W-1:0]        pa_mem;           // PMU_A
  logic [N*N*W-1:0]        pb_mem;           // PMU_B
  logic [N*AccW-1:0]       pcu_va, pcu_vb;   // PCU vector inputs, one AccW-bit word per lane: A[i][k], B[k][j]
  logic [L+1:0]            pcu_vld, pcu_lst; // valid and last bit of stage s (0 inputs, 1 map, ..., L+1 root)
  logic [2*P*AccW-1:0]     pcu_tr;           // the lanes' pipeline registers: tree node n at n*AccW (2P-1 nodes, 1 spare)

  // counter chain
  always_ff @(posedge clk)
    if (rst)
      cc_run <= 1'b0;
    else if (start) begin
      cc_run <= 1'b1;
      cc_i   <= 32'd0;
      cc_j   <= 32'd0;
    end else if (cc_run) begin
      if (cc_j == N - 1) begin
        cc_j <= 32'd0;
        cc_i <= cc_i + 32'd1;
        if (cc_i == N - 1) cc_run <= 1'b0;
      end else
        cc_j <= cc_j + 32'd1;
    end

  // PMU_A: loaded on start; when the inner counter wraps, the next row moves to the read port
  always_ff @(posedge clk)
    if (start)
      pa_mem <= A;
    else if (cc_run) begin
      if (cc_j == N - 1)
        pa_mem <= (pa_mem >> (N*W)) | (pa_mem << ((N-1)*N*W));
    end

  // PMU_B: loaded on start; every row rotates by one entry per item, so entry 0 of row k is B[k][cc_j]
  for (genvar k = 0; k < N; k++) begin : pb_row
    always_ff @(posedge clk)
      if (start)
        pb_mem[k*N*W +: N*W] <= B[k*N*W +: N*W];
      else if (cc_run)
        pb_mem[k*N*W +: N*W] <= (pb_mem[k*N*W +: N*W] >> W) | (pb_mem[k*N*W +: N*W] << ((N-1)*W));
  end

  // PCU control: the valid and last bits of each stage
  always_ff @(posedge clk) begin
    pcu_tr[(P-1+N)*AccW +: (P+1-N)*AccW] <= '0;   // leaves N .. P-1 carry 0 (and the spare node)
    if (rst) begin
      pcu_vld <= '0;
      pcu_lst <= '0;
    end else if (start) begin
      pcu_vld <= '0;
      pcu_lst <= '0;
    end else begin
      pcu_vld <= {pcu_vld[0 +: L+1], cc_run};
      pcu_lst <= {pcu_lst[0 +: L+1], (cc_i == N - 1) & (cc_j == N - 1)};
    end
  end

  // PCU reduction tree: node h adds its two children, one tree level per pipeline stage
  for (genvar h = 0; h < P - 1; h++) begin : pcu_red
    always_ff @(posedge clk)
      pcu_tr[h*AccW +: AccW] <= pcu_tr[(2*h+1)*AccW +: AccW] + pcu_tr[(2*h+2)*AccW +: AccW];
  end

  // PCU lanes: lane k's vector inputs take entry k of each PMU's read port as an AccW-bit word (the
  // signed entry sign-extended by hand, its low AccW bits kept), and its map stage multiplies them
  // (the AccW-bit leaf keeps the product mod 2^AccW)
  for (genvar k = 0; k < N; k++) begin : pcu_lane
    always_ff @(posedge clk) begin
      pcu_va[k*AccW +: AccW] <= {{AccW{pa_mem[k*W+W-1]}}, pa_mem[k*W +: W]};
      pcu_vb[k*AccW +: AccW] <= {{AccW{pb_mem[k*N*W+W-1]}}, pb_mem[k*N*W +: W]};
    end
    always_ff @(posedge clk)
      pcu_tr[(P-1+k)*AccW +: AccW] <= pcu_va[k*AccW +: AccW] * pcu_vb[k*AccW +: AccW];
  end

  // output PMU: one dot product per valid item, written in (i, j) order; the last one raises done
  always_ff @(posedge clk)
    if (rst)
      done <= 1'b0;
    else if (start)
      done <= 1'b0;
    else if (pcu_vld[L+1]) begin
      C <= C >> AccW;
      C[(N*N-1)*AccW +: AccW] <= pcu_tr[0 +: AccW];
      if (pcu_lst[L+1]) done <= 1'b1;
    end
endmodule
