module p14_unpacked #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [P-1:0] r [0:P];
  assign r[0] = a[P-1:0];
  genvar i;
  generate
    for (i = 0; i < P; i = i + 1) begin : g
      assign r[i+1] = r[i] << 1;
    end
  endgenerate
  assign q = {b[K-1:P], r[P]};
endmodule
