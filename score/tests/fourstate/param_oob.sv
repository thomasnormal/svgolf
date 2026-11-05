// A localparam with an x bit from an out-of-range constant select.
module param_oob #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  localparam logic [3:0] P = 4'b0101;
  localparam logic [1:0] K2 = {P[5], 1'b0};
  assign y = (a[1:0] == K2) ? a | b : a & b;
endmodule
