// svGolf task `matmul`: Gemmini's weight-stationary systolic array, translated from its Chisel source into one
// parametric SystemVerilog module.
//
// PROVENANCE. Translated from Gemmini (UC Berkeley), https://github.com/ucb-bar/gemmini, commit
// b82d49cca798a59f010488a6f6de7243f0616536, files src/main/scala/gemmini/PE.scala, Tile.scala, Mesh.scala,
// MeshWithDelays.scala (with Shifter.scala and Util.scala, which it calls), Dataflow.scala and Arithmetic.scala
// (SIntArithmetic), with the preload row order of ExecuteController.scala. Copyright (c) 2018-2019, The Regents of the
// University of California (Regents). Gemmini's licence notice is kept below, as its first condition requires. This
// file is a modified translation, not Gemmini itself, and is not endorsed by the Regents or by Gemmini's authors.
//
// KEPT FROM THE SOURCE:
//  - PE (PE.scala, weight-stationary branch): two W-bit weight registers c1 and c2. On a valid row with propagate = 1
//    the PE loads c1 from d, passes the old c1 down as out_c and multiplies a by c2; with propagate = 0 it loads c2,
//    passes the old c2 and multiplies by c1; on valid = 0 both hold. out_b = a * weight + b (MacUnit), out_a = a.
//  - Tile (Tile.scala): a combinational grid of PEs; here every Tile is 1 x 1, Gemmini's default shape.
//  - Mesh (Mesh.scala): an N x N grid of Tiles with one register stage at each Tile's input: a and valid every cycle,
//    b, d and propagate only when the valid beside them is 1, so the control bits travel beside the data through the
//    same stages (valid and propagate once per anti-diagonal, change 7); the bottom row's b leaves through one output
//    register.
//  - MeshWithDelays (MeshWithDelays.scala): one input buffer per lane, then row lane r of a delayed by r cycles and
//    column lane c of d by c cycles, valid and propagate beside them; the results leave through the reverse skew
//    (column c delayed by N - 1 - c), so a result row is aligned; the role-swap bit in_prop feeds propagate (change 11).
//  - The weight preload (ExecuteController.scala): a pass of N rows through the d lanes, the last row of B first,
//    before the pass that streams the rows of A; the result rows leave in order.
// CHANGES, with reasons:
//  1. Generator parameters fixed: dataflow WS, tileRows = tileColumns = 1, meshRows = meshColumns = N,
//     tile_latency = 0, mesh_output_delay = 1, one shifter bank; inputType = weightType = W-bit signed,
//     outputType = accType = AccW-bit signed (the task's entries and wrap). N = 1 is allowed (Gemmini's
//     configuration asks for at least 2; the array modules do not).
//  2. Only the weight-stationary dataflow: the output-stationary branch of PE.scala, the dataflow control bit and
//     bad_dataflow are left out, and with them the rounding shift (shift, last_s, flip) and the saturating
//     clippedToWidthOf, which only that branch uses. The task's single product needs no in-array accumulator.
//  3. The bias D is the zero matrix: its skew lane is left out (it would delay a constant); the top Tiles' b
//     registers load 0 on valid rows.
//  4. No matmul ids, last flags, tag queues, row counts, flush, request register, ready/valid ports or transposer:
//     they pair result rows with many requests in flight. A step counter issues the two passes, toggles in_prop,
//     writes C from the compute pass's result rows (the preload pass's rows are skipped by timing) and raises done.
//  5. A and B are copied into shift registers at start and stand in for the scratchpad reads, one row per cycle, so
//     every select is static; the input buffers load every cycle instead of on a handshake.
//  6. The skew lanes of a, of d and of the results are each packed as one triangle in a flat vector (lane j: its
//     buffer and j stages; the output lane of column c: N - c registers): a register that nothing reads leaves an
//     undriven bit in the scored netlist, which the post-synthesis check refuses.
//  7. Valid and propagate are the same bit for every column, so Gemmini's per-column lanes and per-Tile registers of
//     them hold one value per anti-diagonal r + c. Synthesis merges such registers, and the merged netlist reads a
//     vector from itself, which the post-synthesis check refuses (a combinational loop to its simulator). So they are
//     kept once per anti-diagonal: wv[k] is the valid k stages after the input buffers (ShiftRegister), and wp[k] the
//     propagate at the input of the Tiles with r + c = k, loaded when the valid beside it is 1 (Mesh.scala's pipe).
//  8. One module, every process an always_ff: PE, Tile and Mesh are generate scopes, not module instances, and each
//     PE's combinational outputs are written into the registers that read them; the d registers are W bits wide (the
//     source carries a W-bit weight sign-extended to the output width and cuts it again at the next register).
//     svGolf's clock-step theorem covers designs whose every process is an always_ff.
//  9. Signed arithmetic is written as explicit sign extension; sums wrap at AccW bits.
// 10. The synchronous reset clears busy, done, the step counter and in_prop; the data registers have no reset, as in
//     Gemmini.
// 11. in_prop is toggled at the start of the preload pass and again at the start of the compute pass, so the preload
//     rows always carry propagate = 1 and the compute rows 0 (Gemmini's controller toggles it once per matmul, with
//     the compute request, and the two weight registers alternate roles).
// 12. During the preload pass the a lanes carry the first row of A, whose products are discarded (Gemmini puts 0 there).
// 13. The output register of a column loads 0 on the rows whose valid bit is 0, where PE.scala leaves the MAC's inputs
//     DontCare (its out_b is then unspecified); on valid rows it loads out_b, as Mesh.scala's ShiftRegister does.
// 14. With AccW < W the source's d registers below the top tile row would be narrower than W; here they are W bits wide
//     (the products modulo 2^AccW are the same).
// Nothing else changed.
//
// Copyright (c) 2018-2019, The Regents of the University of California
// (Regents).  All Rights Reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. Neither the name of the Regents nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
//
// IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
// SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING
// OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS
// BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
// THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
// PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED
// HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE
// MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  // The index of Tile/PE (r, c) is r*N + c. The skew lanes are Gemmini's triangles, packed: row lane j of a and
  // column lane j of d have j + 1 registers, entry m at j*(j+1)/2 + m; the output lane of column c has N - c
  // registers, entry m at (N-1-c)*(N-c)/2 + m. Valid and propagate are the same for every column, so they are kept
  // once per anti-diagonal r + c (the wavefronts wv and wp).
  localparam int T = N*(N+1)/2;
  localparam int TWO_N = 2*N;           // the rows of the two passes
  localparam int FOUR_N = 4*N;          // the last busy step
  localparam int OUT0 = 3*N + 1;        // the step that writes row 0 of C
  logic                busy, in_prop;
  logic [31:0]         step;
  logic [N*N*W-1:0]    a_rows, w_rows;   // stand-ins for the scratchpad reads of A and B
  logic [T*W-1:0]      sk_a, sk_d;       // MeshWithDelays: a_buf / d_buf (entry 0) and the skew stages
  logic [T*AccW-1:0]   sk_o;             // Mesh's output register (entry 0) and MeshWithDelays' reverse skew
  logic [2*N-1:0]      wv;               // valid: wv[0] beside the input buffers, wv[k] delayed by k
  logic                pb;               // propagate beside the input buffers
  logic [2*N-2:0]      wp;               // propagate at the input of the Tiles (r, c) with r + c = k
  logic [N*N*W-1:0]    m_a, m_d;         // Mesh: the a and d registers at each Tile's input
  logic [N*N*AccW-1:0] m_b;              // Mesh: the b register at each Tile's input
  logic [N*N*W-1:0]    c1, c2;           // PE: the two weight registers

  // The controller (ExecuteController's role for one transaction) and MeshWithDelays' in_prop.
  always_ff @(posedge clk)
    if (rst) begin
      busy <= 1'b0; done <= 1'b0; step <= 32'd0; in_prop <= 1'b0;
    end else if (start) begin
      busy <= 1'b1; done <= 1'b0; step <= 32'd0;
      in_prop <= ~in_prop;
      a_rows <= A;
      w_rows <= B;
    end else if (busy) begin
      step <= step + 32'd1;
      if (step == N - 1) in_prop <= ~in_prop;
      if (step < N)  w_rows <= w_rows << (N*W);
      if (step >= N) a_rows <= a_rows >> (N*W);
      if (step == FOUR_N) begin busy <= 1'b0; done <= 1'b1; end
    end

  // MeshWithDelays' valid (not paused) and propagate beside the input buffers, the valid wavefront (Mesh.scala's
  // ShiftRegister of in_valid at each Tile's input), and Tile (0, 0)'s propagate register (Mesh.scala's pipe).
  always_ff @(posedge clk) begin
    wv    <= wv << 1;
    wv[0] <= busy & (step < TWO_N);
    pb    <= in_prop;
    if (wv[0]) wp[0] <= pb;
  end

  // The propagate wavefront: the propagate register at the input of the Tiles (r, c) with r + c = k + 1 loads the
  // one before it when the valid beside it is 1 (Mesh.scala's pipe).
  for (genvar k = 0; k < 2*N - 2; k++) begin : Mesh_prop
    always_ff @(posedge clk)
      if (wv[k+1]) wp[k+1] <= wp[k];
  end

  // MeshWithDelays, row lane r (a_buf[r] and r ShiftRegister stages), and Mesh row r's a registers
  // (Mesh.scala's ShiftRegister at each Tile's input; PE.out_a = in_a).
  for (genvar r = 0; r < N; r++) begin : MeshWithDelays_row
    always_ff @(posedge clk) begin
      sk_a[(r*(r+1)/2)*W +: (r+1)*W] <= sk_a[(r*(r+1)/2)*W +: (r+1)*W] << W;
      sk_a[(r*(r+1)/2)*W +: W]       <= a_rows[r*W +: W];
      m_a[r*N*W +: N*W]  <= m_a[r*N*W +: N*W] << W;
      m_a[r*N*W +: W]    <= sk_a[(r*(r+1)/2 + r)*W +: W];
    end
  end

  // MeshWithDelays, column lane c (d_buf[c] and c stages); Tile (0, c)'s b and d registers (Mesh.scala's pipe: they
  // load when the valid beside them is 1); Mesh's output register of column c and the reverse skew.
  for (genvar c = 0; c < N; c++) begin : MeshWithDelays_col
    always_ff @(posedge clk) begin
      sk_d[(c*(c+1)/2)*W +: (c+1)*W] <= sk_d[(c*(c+1)/2)*W +: (c+1)*W] << W;
      sk_d[(c*(c+1)/2)*W +: W]       <= w_rows[((N-1)*N + c)*W +: W];
      if (wv[c]) begin
        m_b[c*AccW +: AccW] <= '0;
        m_d[c*W +: W]       <= sk_d[(c*(c+1)/2 + c)*W +: W];
      end
      sk_o[((N-1-c)*(N-c)/2)*AccW +: (N-c)*AccW] <= sk_o[((N-1-c)*(N-c)/2)*AccW +: (N-c)*AccW] << AccW;
      // the output register loads PE (N-1, c)'s out_b: its MAC on a valid row, 0 on the others (PE.scala makes the
      // MAC's inputs DontCare when valid = 0; the shift above leaves 0 in entry 0)
      if (wv[N + c])
        sk_o[((N-1-c)*(N-c)/2)*AccW +: AccW] <= m_b[((N-1)*N + c)*AccW +: AccW]
            + {{AccW{m_a[((N-1)*N + c)*W + W-1]}}, m_a[((N-1)*N + c)*W +: W]}
            * (wp[N-1 + c] ? {{AccW{c2[((N-1)*N + c)*W + W-1]}}, c2[((N-1)*N + c)*W +: W]}
                           : {{AccW{c1[((N-1)*N + c)*W + W-1]}}, c1[((N-1)*N + c)*W +: W]});
    end
  end

  // Mesh: the b and d registers at Tile (r+1, c)'s input, fed by PE (r, c) (its out_b = MAC, out_c).
  for (genvar r = 0; r < N - 1; r++) begin : Mesh_pipe
    for (genvar c = 0; c < N; c++) begin : Tile_in
      always_ff @(posedge clk)
        if (wv[r + c + 1]) begin
          m_b[((r+1)*N + c)*AccW +: AccW] <= m_b[(r*N + c)*AccW +: AccW]
              + {{AccW{m_a[(r*N + c)*W + W-1]}}, m_a[(r*N + c)*W +: W]}
              * (wp[r + c] ? {{AccW{c2[(r*N + c)*W + W-1]}}, c2[(r*N + c)*W +: W]}
                           : {{AccW{c1[(r*N + c)*W + W-1]}}, c1[(r*N + c)*W +: W]});
          m_d[((r+1)*N + c)*W +: W] <= wp[r + c] ? c1[(r*N + c)*W +: W] : c2[(r*N + c)*W +: W];
        end
    end
  end

  // Mesh[r].Tile[c]: a 1 x 1 Tile; its PE's weight registers (PE.scala, weight-stationary branch).
  for (genvar r = 0; r < N; r++) begin : Mesh
    for (genvar c = 0; c < N; c++) begin : Tile
      always_ff @(posedge clk)
        if (wv[r + c + 1]) begin
          if (wp[r + c]) c1[(r*N + c)*W +: W] <= m_d[(r*N + c)*W +: W];
          else           c2[(r*N + c)*W +: W] <= m_d[(r*N + c)*W +: W];
        end
    end
  end

  // Collecting the result rows (ExecuteController's write of the response rows), one entry per process.
  for (genvar u = 0; u < N; u++) begin : Out_row
    for (genvar c = 0; c < N; c++) begin : Out_col
      always_ff @(posedge clk)
        if (busy & (step == OUT0 + u))
          C[(u*N + c)*AccW +: AccW] <= sk_o[((N-1-c)*(N-c)/2 + N-1-c)*AccW +: AccW];
    end
  end
endmodule
