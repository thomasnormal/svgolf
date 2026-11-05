// STYLE: one level of Karatsuba on module instances (effanem/set_project gf128_karatsuba.v shape), with the base
// multiplier a SEPARATE MODULE written in the generate-for array style (the reference's), so that nothing else
// blocks it: H = ceil(N/2), operands zero-padded to 2H bits by replication, three instances.
// Correct for every N. The question this design asks is only: how far do module instances get?
module clmul_base #(parameter int M = 8) (
  input  logic [M-1:0]   x, y,
  output logic [2*M-2:0] z
);
  logic [M-1:0][M-1:0] r;
  genvar i, j, m;
  generate
    for (j = 0; j < M; j++) begin : g_row0
      assign r[0][j] = x[0] & y[j];
    end
    for (i = 1; i < M; i++) begin : g_row
      for (j = 0; j < M-1; j++) begin : g_bit
        assign r[i][j] = r[i-1][j+1] ^ (x[i] & y[j]);
      end
      assign r[i][M-1] = x[i] & y[M-1];
    end
    for (i = 0; i < M; i++) begin : g_lo
      assign z[i] = r[i][0];
    end
    for (m = 0; m < M-1; m++) begin : g_hi
      assign z[M+m] = r[M-1][m+1];
    end
  endgenerate
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
