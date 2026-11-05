module p11_unsized_arith #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic nz;
  logic [W-1:0] ea, x, y;
  assign ea = a[W-1:0];
  assign nz = |ea;
  assign x = nz ? ea : 1;
  assign y = ea + b[W-1:0] + 1;
  assign q[W-1:0] = x ^ y;
  assign q[K-1:W] = '0;
endmodule
