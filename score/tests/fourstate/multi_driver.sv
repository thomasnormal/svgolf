// Two continuous drivers on one net: IEEE resolves conflicting bits to x.
module multi_driver #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output wire  [N-1:0] y
);
  assign y = a & b;
  assign y = a | b;
endmodule
