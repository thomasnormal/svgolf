// STYLE: ONE level of Karatsuba on module instances, the base multiplier a separate module (effanem/set_project
// gf128_karatsuba.v: three gf64_mul instances; parametric here: H = ceil(N/2), the operands zero-padded to 2H bits).
// The base is the procedural shift-and-XOR, as in that repository.
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment (module instances).
module clmul_base #(parameter int M = 8) (
  input  logic [M-1:0]   x, y,
  output logic [2*M-2:0] z
);
  logic [2*M-2:0] xw;
  assign xw = {{(M-1){1'b0}}, x};
  always_comb begin
    z = '0;
    for (int i = 0; i < M; i++) begin
      if (y[i]) z = z ^ (xw << i);
    end
  end
endmodule

module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  localparam int H = (N + 1) / 2;
  logic [2*H-1:0] ap, bp;
  assign ap = {{(2*H-N){1'b0}}, a};
  assign bp = {{(2*H-N){1'b0}}, b};
  logic [2*H-2:0] pl, ph, pm;
  clmul_base #(.M(H)) u_l (.x(ap[H-1:0]),   .y(bp[H-1:0]),   .z(pl));
  clmul_base #(.M(H)) u_h (.x(ap[2*H-1:H]), .y(bp[2*H-1:H]), .z(ph));
  clmul_base #(.M(H)) u_m (.x(ap[H-1:0] ^ ap[2*H-1:H]), .y(bp[H-1:0] ^ bp[2*H-1:H]), .z(pm));
  logic [4*H-2:0] t0, t1, t2, pf;
  assign t0 = pl;
  assign t1 = pm ^ pl ^ ph;
  assign t2 = ph;
  assign pf = t0 ^ (t1 << H) ^ (t2 << (2*H));
  assign p = pf[2*N-2:0];
endmodule
