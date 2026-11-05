// A run-time index that leaves the range: k[a[1:0] + 3'd4] is always out of
// range (x): ls-sv's t is x and the if takes the else branch (a & b), Yosys
// resolves the x to t = 1 (a | b), measured with Yosys 0.53.
module oob_runtime #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic [3:0] k;
  logic t;
  assign k = 4'b0101;
  assign t = k[a[1:0] + 3'd4] ? 1'b0 : 1'b1;
  always_comb if (t) y = a | b; else y = a & b;
endmodule
