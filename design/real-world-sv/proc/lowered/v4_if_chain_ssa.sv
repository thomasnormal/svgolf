// always_comb begin t = a; if (c) t = b; y = t ^ a; end   lowered to SSA assigns, per-bit generate
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N-1:0] t__1, t__2, y;
  assign t__1 = a;
  assign t__2 = b[0] ? b : t__1;
  assign y    = t__2 ^ a;
  assign p    = {y, y};
endmodule
