module p10_genvar_value #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [P:0] act;
  genvar i;
  generate
    for (i = 0; i < P + 1; i = i + 1) begin : g
      assign act[i] = (a[W-1:0] > i);
    end
  endgenerate
  assign q[P:0] = act;
  assign q[K-1:P+1] = '0;
endmodule
