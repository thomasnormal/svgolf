module cl2 (input logic [1:0] a, b, output logic [2:0] p);
  assign p[0] = a[0] & b[0];
  assign p[1] = (a[0] & b[1]) ^ (a[1] & b[0]);
  assign p[2] = a[1] & b[1];
endmodule
module clmul_n #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [2:0] lo, hi, mid;
  cl2 u_lo (.a(a[1:0]), .b(b[1:0]), .p(lo));
  cl2 u_hi (.a(a[3:2]), .b(b[3:2]), .p(hi));
  cl2 u_mid(.a(a[1:0]^a[3:2]), .b(b[1:0]^b[3:2]), .p(mid));
  assign p = {1'b0, hi, 3'b0} ^ {2'b0, (mid ^ lo ^ hi), 2'b0} ^ {4'b0, lo};
endmodule
