// STYLE: Karatsuba as a RECURSIVE parameterized module (the module instantiates itself with N/2, a generate-if
// ends the recursion; JC-S/Karatsuba_multiplier_HDL karat_mult_recursion.sv, which does integer arithmetic;
// here the GF(2) version: sums are XORs). H = ceil(N/2), operands zero-padded to 2H bits, base case N <= 4.
// Correct for every N; scored as written. Not inside the proof tactics' fragment (module instances, recursion).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  generate
    if (N <= 4) begin : g_base
      logic [2*N-2:0] aw;
      assign aw = {{(N-1){1'b0}}, a};
      always_comb begin
        p = '0;
        for (int i = 0; i < N; i++) begin
          if (b[i]) p = p ^ (aw << i);
        end
      end
    end else begin : g_split
      localparam int H = (N + 1) / 2;
      logic [2*H-1:0] ap, bp;
      assign ap = {{(2*H-N){1'b0}}, a};
      assign bp = {{(2*H-N){1'b0}}, b};
      logic [2*H-2:0] pl, ph, pm;
      clmul_n #(.N(H)) u_l (.a(ap[H-1:0]),   .b(bp[H-1:0]),   .p(pl));
      clmul_n #(.N(H)) u_h (.a(ap[2*H-1:H]), .b(bp[2*H-1:H]), .p(ph));
      clmul_n #(.N(H)) u_m (.a(ap[H-1:0] ^ ap[2*H-1:H]), .b(bp[H-1:0] ^ bp[2*H-1:H]), .p(pm));
      logic [4*H-2:0] t0, t1, t2, pf;
      assign t0 = pl;
      assign t1 = pm ^ pl ^ ph;
      assign t2 = ph;
      assign pf = t0 ^ (t1 << H) ^ (t2 << (2*H));
      assign p = pf[2*N-2:0];
    end
  endgenerate
endmodule
