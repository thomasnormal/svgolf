module p02_clog2 #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer NS = $clog2(P);
  logic [NS-1:0] t;
  assign t = a[NS-1:0];
  assign q[NS-1:0] = t;
  assign q[K-1:NS] = '0;
endmodule
