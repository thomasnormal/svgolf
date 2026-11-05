module q09_red_concat_part #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [P-1:0] ma;
  assign ma = {|a[K-2:T], a[T-1:0]};
  assign q[P-1:0] = ma;
  assign q[K-1:P] = '0;
endmodule
