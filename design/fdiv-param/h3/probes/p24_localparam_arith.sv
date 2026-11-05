module p24_localparam_arith #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer OFFV = 2 * W + 3;
  logic [OFFV-1:0] y;
  assign y = '0;
  assign q = '0;
endmodule
