module p25_sized_localparam #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam [W-1:0] ONES = 1;
  assign q[W-1:0] = a[W-1:0] + ONES;
  assign q[K-1:W] = '0;
endmodule
