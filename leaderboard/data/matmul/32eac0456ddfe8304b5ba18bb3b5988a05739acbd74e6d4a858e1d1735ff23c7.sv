// svGolf task `matmul`: 2-stage pipelined G4 (4 MACs/PE/cycle) with exact 2W-bit signed products,
// 4:2 carry-save compression to (2W+2)-bit (rs, rc) registers, and static N <= 4 accumulator pruning.
// Latency = ceil(N/4) (1 at N = 4). Built on the G4 shift-by-4 operand padding of record 65342538360f
// and the 2-stage product/accumulate split of record e2af800fb366. Parametric in 1 <= N <= 256,
// 1 <= W <= 127, 1 <= AccW <= 64.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
  localparam int PW = 2 * W;
  localparam int SW = 2 * W + 2;

  logic [31:0]            k;
  logic                   busy, drain;
  logic [(N*N+3)*W-1:0]   a_sh, Ap;
  logic [(N*N+3*N)*W-1:0] b_sh, Bp;
  logic [N*N*SW-1:0]      rs, rc;

  assign Ap = {{(3*W){1'b0}}, A};
  assign Bp = {{(3*N*W){1'b0}}, B};

  always_ff @(posedge clk) begin
    if (rst) begin
      busy  <= 1'b0;
      drain <= 1'b0;
      done  <= 1'b0;
      k     <= 32'd0;
    end else if (start) begin
      done <= 1'b0;
      k    <= 32'd4;
      if (N <= 4) begin
        busy  <= 1'b0;
        drain <= 1'b1;
      end else begin
        busy  <= 1'b1;
        drain <= 1'b0;
        a_sh  <= (Ap >> (2*W)) >> (2*W);
        b_sh  <= (Bp >> (2*N*W)) >> (2*N*W);
      end
    end else if (busy && (N > 4)) begin
      k    <= k + 32'd4;
      a_sh <= (a_sh >> (2*W)) >> (2*W);
      b_sh <= (b_sh >> (2*N*W)) >> (2*N*W);
      if (k + 32'd4 >= N) begin
        busy  <= 1'b0;
        drain <= 1'b1;
      end
    end else if (drain) begin
      drain <= 1'b0;
      done  <= 1'b1;
    end
  end

  // Per-PE 4 products (exact 2W-bit signed) + 4:2 CSA -> (rs, rc) + single SW-bit sum on drain/busy!
  logic [N*N*PW-1:0] p0, p1, p2, p3;
  logic [N*N*SW-1:0] x1, y1, s2, c2, s4;

  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_col
      assign p0[(i*N+j)*PW +: PW] =
          {{W{(start || (N <= 4)) ? Ap[(i*N+0)*W + W - 1] : a_sh[(i*N+0)*W + W - 1]}}, (start || (N <= 4)) ? Ap[(i*N+0)*W +: W] : a_sh[(i*N+0)*W +: W]}
        * {{W{(start || (N <= 4)) ? Bp[(0*N+j)*W + W - 1] : b_sh[(0*N+j)*W + W - 1]}}, (start || (N <= 4)) ? Bp[(0*N+j)*W +: W] : b_sh[(0*N+j)*W +: W]};
      assign p1[(i*N+j)*PW +: PW] =
          {{W{(start || (N <= 4)) ? Ap[(i*N+1)*W + W - 1] : a_sh[(i*N+1)*W + W - 1]}}, (start || (N <= 4)) ? Ap[(i*N+1)*W +: W] : a_sh[(i*N+1)*W +: W]}
        * {{W{(start || (N <= 4)) ? Bp[(1*N+j)*W + W - 1] : b_sh[(1*N+j)*W + W - 1]}}, (start || (N <= 4)) ? Bp[(1*N+j)*W +: W] : b_sh[(1*N+j)*W +: W]};
      assign p2[(i*N+j)*PW +: PW] =
          {{W{(start || (N <= 4)) ? Ap[(i*N+2)*W + W - 1] : a_sh[(i*N+2)*W + W - 1]}}, (start || (N <= 4)) ? Ap[(i*N+2)*W +: W] : a_sh[(i*N+2)*W +: W]}
        * {{W{(start || (N <= 4)) ? Bp[(2*N+j)*W + W - 1] : b_sh[(2*N+j)*W + W - 1]}}, (start || (N <= 4)) ? Bp[(2*N+j)*W +: W] : b_sh[(2*N+j)*W +: W]};
      assign p3[(i*N+j)*PW +: PW] =
          {{W{(start || (N <= 4)) ? Ap[(i*N+3)*W + W - 1] : a_sh[(i*N+3)*W + W - 1]}}, (start || (N <= 4)) ? Ap[(i*N+3)*W +: W] : a_sh[(i*N+3)*W +: W]}
        * {{W{(start || (N <= 4)) ? Bp[(3*N+j)*W + W - 1] : b_sh[(3*N+j)*W + W - 1]}}, (start || (N <= 4)) ? Bp[(3*N+j)*W +: W] : b_sh[(3*N+j)*W +: W]};

      // 4:2 CSA on sign-extended (p0, p1, p2, p3) -> (s2, c2) at width SW = 2W+2:
      assign x1[(i*N+j)*SW +: SW] =
          {{2{p0[(i*N+j)*PW + PW - 1]}}, p0[(i*N+j)*PW +: PW]}
        ^ {{2{p1[(i*N+j)*PW + PW - 1]}}, p1[(i*N+j)*PW +: PW]}
        ^ {{2{p2[(i*N+j)*PW + PW - 1]}}, p2[(i*N+j)*PW +: PW]};
      assign y1[(i*N+j)*SW +: SW] =
          (({{2{p0[(i*N+j)*PW + PW - 1]}}, p0[(i*N+j)*PW +: PW]} & {{2{p1[(i*N+j)*PW + PW - 1]}}, p1[(i*N+j)*PW +: PW]})
         | ({{2{p0[(i*N+j)*PW + PW - 1]}}, p0[(i*N+j)*PW +: PW]} & {{2{p2[(i*N+j)*PW + PW - 1]}}, p2[(i*N+j)*PW +: PW]})
         | ({{2{p1[(i*N+j)*PW + PW - 1]}}, p1[(i*N+j)*PW +: PW]} & {{2{p2[(i*N+j)*PW + PW - 1]}}, p2[(i*N+j)*PW +: PW]})) << 1;
      assign s2[(i*N+j)*SW +: SW] =
          x1[(i*N+j)*SW +: SW] ^ y1[(i*N+j)*SW +: SW] ^ {{2{p3[(i*N+j)*PW + PW - 1]}}, p3[(i*N+j)*PW +: PW]};
      assign c2[(i*N+j)*SW +: SW] =
          ((x1[(i*N+j)*SW +: SW] & y1[(i*N+j)*SW +: SW])
         | (x1[(i*N+j)*SW +: SW] & {{2{p3[(i*N+j)*PW + PW - 1]}}, p3[(i*N+j)*PW +: PW]})
         | (y1[(i*N+j)*SW +: SW] & {{2{p3[(i*N+j)*PW + PW - 1]}}, p3[(i*N+j)*PW +: PW]})) << 1;

      assign s4[(i*N+j)*SW +: SW] = rs[(i*N+j)*SW +: SW] + rc[(i*N+j)*SW +: SW];

      always_ff @(posedge clk) begin
        rs[(i*N+j)*SW +: SW] <= s2[(i*N+j)*SW +: SW];
        rc[(i*N+j)*SW +: SW] <= c2[(i*N+j)*SW +: SW];
        if (start && (N > 4))
          C[(i*N+j)*AccW +: AccW] <= '0;
        else if (busy && (N > 4))
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
            + {{AccW{s4[(i*N+j)*SW + SW - 1]}}, s4[(i*N+j)*SW +: SW]};
        else if (drain) begin
          if (N <= 4)
            C[(i*N+j)*AccW +: AccW] <= {{AccW{s4[(i*N+j)*SW + SW - 1]}}, s4[(i*N+j)*SW +: SW]};
          else
            C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
              + {{AccW{s4[(i*N+j)*SW + SW - 1]}}, s4[(i*N+j)*SW +: SW]};
        end
      end
    end
  end
endmodule
