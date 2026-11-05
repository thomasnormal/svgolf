module p13_cond_generate #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  generate
    if (W > 2) begin : cg
      assign q = a ^ b;
    end else begin : cg2
      assign q = a & b;
    end
  endgenerate
endmodule
