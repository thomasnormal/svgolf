// H2 style S4: parameterized widths with $clog2 (cc_lzc / cva6 style), a localparam, and a generate-if.
module s4_clog2 #(parameter int W = 11) (
  input  logic [W-1:0] m,
  output logic [$clog2(W+1)-1:0] cnt
);
  localparam int CW = $clog2(W + 1);
  logic [W:0] t;
  assign t[0] = 1'b0;
  for (genvar i = 0; i < W; i++) begin : g
    assign t[i + 1] = m[i] | t[i];
  end
  assign cnt = CW'(W) - CW'(t[W]);
endmodule
